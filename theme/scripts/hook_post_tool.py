#!/usr/bin/env python3
"""hook_post_tool.py — PR9-B PostToolUse emitter (CLI + web shared).

Wired via `.claude/settings.local.json` PostToolUse hooks for matchers
`Bash` / `Write` / `Edit`. Fires AFTER every such tool_use, including
those inside `Agent + run_in_background:true` subagents (verified by
PR-V experiment 2026-04-27 — subagent context inherits cwd, loads same
settings, so this hook fires there too).

Stdin payload (provided by Claude Code):
  {
    "session_id": "...",
    "agent_id": "...",       # if subagent
    "agent_type": "general-purpose" / etc.
    "hook_event_name": "PostToolUse",
    "tool_name": "Bash" | "Write" | "Edit",
    "tool_input": {...},
    "tool_response": {"stdout": ..., "stderr": ..., "interrupted": ...},
    "tool_use_id": "toolu_...",
    "duration_ms": ...,
    "transcript_path": ...,
    "cwd": ...,
    ...
  }

Side effects (all best-effort; never abort, exit 0):
  · Bash + `lake build`           → lake-build-{clean,fail} milestone
  · Write/Edit on $STATLEAN_ROOT/MEMORY.md → memory-md-updated (T1 inference;
                                    catches direct writes that bypass
                                    prove_deep_end.py)
  · Write/Edit on Statlean/*.lean → run extract_sorries; sorry-pool-snapshot
                                    with delta vs previous snapshot. If
                                    delta < 0, also emits sorry-proved
                                    {inferred:true, lake_build_pending:true}
                                    so consumers can confirm with the
                                    subsequent lake-build-{clean,fail}.

Idempotency: each emit consults events.jsonl tail; skip if same milestone
name fired within last 30s (prevents flooding when agent does multi-line
shell with lake build inside).

Sandbox resolution (where to write events.jsonl):
  1. $SANDBOX env (web orchestrator passes this when invoking SDK)
  2. fall back to nothing — CLI standalone has no per-job sandbox; hook
     just exits 0 with no side effects (matches CLI users' expectations:
     they tail events.jsonl manually if at all).

This is the T1 path for subagent visibility per Rule 9 Q3 — runs at
SDK-harness level, agent has no opportunity to skip.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path
import datetime as dt

# Hard timeout budget (Claude hook timeout was 10s in settings; stay well under).
HOOK_BUDGET_S = 8

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
EXTRACT_SORRIES = SCRIPTS_DIR / "extract_sorries.py"
STATLEAN_ROOT = SCRIPTS_DIR.parent.parent

DEDUP_WINDOW_MS = 30_000


def _read_payload() -> dict:
    try:
        return json.loads(sys.stdin.read())
    except Exception:
        return {}


def _resolve_sandbox() -> Path | None:
    sb = os.environ.get("SANDBOX") or os.environ.get("STATLEAN_SANDBOX")
    if not sb:
        return None
    p = Path(sb)
    if not p.is_dir():
        return None
    return p


def _recently_emitted(sandbox: Path, name: str) -> bool:
    """Return True if `name` milestone fired within last DEDUP_WINDOW_MS."""
    events = sandbox / "events.jsonl"
    if not events.exists():
        return False
    try:
        lines = events.read_text().splitlines()[-200:]
    except Exception:
        return False
    now = int(dt.datetime.now().timestamp() * 1000)
    for line in reversed(lines):
        try:
            e = json.loads(line)
        except Exception:
            continue
        if e.get("kind") == "sandbox_milestone" and e.get("name") == name:
            ts = e.get("ts", 0)
            if isinstance(ts, (int, float)) and now - ts < DEDUP_WINDOW_MS:
                return True
            break  # older same-name found — no recent emit
    return False


def _emit(sandbox: Path, name: str, details: dict) -> None:
    if _recently_emitted(sandbox, name):
        return
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", name,
                "--details", json.dumps(details),
            ],
            check=False, timeout=HOOK_BUDGET_S,
            capture_output=True,
        )
    except Exception:
        pass


# ── tool-specific handlers ────────────────────────────────────────


def _handle_bash(payload: dict, sandbox: Path) -> None:
    cmd = (payload.get("tool_input") or {}).get("command", "") or ""
    if not cmd:
        return
    response = payload.get("tool_response") or {}
    stdout = response.get("stdout", "") or ""
    stderr = response.get("stderr", "") or ""
    interrupted = bool(response.get("interrupted"))
    session_id = payload.get("session_id", "")
    agent_type = payload.get("agent_type", "main")

    # lake build detection
    if re.search(r"\blake\s+build\b", cmd):
        # Extract module if present (Statlean.X.Y.Z form)
        mod_match = re.search(r"\bStatlean\.[A-Za-z0-9_.]+", cmd)
        module = mod_match.group(0) if mod_match else "unknown"
        # Detect build failure from stdout/stderr
        had_error = (
            interrupted
            or bool(re.search(r"^error:", stdout, flags=re.MULTILINE))
            or bool(re.search(r"^error:", stderr, flags=re.MULTILINE))
            or bool(re.search(r"^.+:\d+:\d+: error:", stdout, flags=re.MULTILINE))
        )
        name = "lake-build-fail" if had_error else "lake-build-clean"
        _emit(sandbox, name, {
            "module": module,
            "observed_via": "hook",
            "session_id": session_id[:16] if session_id else None,
            "agent_type": agent_type,
        })


def _handle_write_or_edit(payload: dict, sandbox: Path) -> None:
    ti = payload.get("tool_input") or {}
    path_str = ti.get("file_path") or ti.get("path") or ""
    if not path_str:
        return
    agent_type = payload.get("agent_type", "main")

    # MEMORY.md branch — fires before the .lean filter so a direct Write/Edit
    # to statlean's MEMORY.md emits memory-md-updated even when the agent
    # bypasses prove_deep_end.py (which already emits this milestone via
    # emit_event.py from its own body — that path uses Python fs.write_text,
    # not the Claude Code Write tool, so this hook does not double-fire).
    # Path resolution is absolute to avoid false positives on
    # ~/.claude/.../MEMORY.md (auto-memory) or any other MEMORY.md the agent
    # might touch outside the statlean repo.
    try:
        memory_md = (STATLEAN_ROOT / "MEMORY.md").resolve()
        if Path(path_str).resolve() == memory_md:
            _emit(sandbox, "memory-md-updated", {
                "observed_via": "hook",
                "inferred": True,
                "agent_type": agent_type,
            })
            return
    except Exception:
        pass

    if not path_str.endswith(".lean"):
        return
    if "/Statlean/" not in path_str:
        return  # not main tree

    # Refresh sorry_list.json + emit pool snapshot
    sl_path = sandbox / "sorry_list.json"
    pre_count = 0
    if sl_path.exists():
        try:
            pre_count = len(json.loads(sl_path.read_text()))
        except Exception:
            pass
    try:
        subprocess.run(
            [
                "python3", str(EXTRACT_SORRIES),
                "--lean-file", path_str,
                "--job-id", sandbox.name,
                "--output", str(sl_path),
            ],
            check=False, timeout=HOOK_BUDGET_S - 1, capture_output=True,
        )
    except Exception:
        return
    post_count = pre_count
    if sl_path.exists():
        try:
            post_count = len(json.loads(sl_path.read_text()))
        except Exception:
            pass

    delta = post_count - pre_count
    rel_file = path_str.replace(str(STATLEAN_ROOT) + "/", "")

    _emit(sandbox, "sorry-pool-snapshot", {
        "count": post_count,
        "delta": delta,
        "file": rel_file,
        "observed_via": "hook",
        "agent_type": agent_type,
    })

    # sorry-proved inference: a .lean Edit/Write that strictly reduces the
    # sorry pool is evidence that at least one sorry was replaced. We mark
    # `inferred: true` and `lake_build_pending: true` so downstream consumers
    # know to confirm with the next lake-build-{clean,fail} milestone — this
    # hook fires synchronously on the Edit, BEFORE the agent re-runs lake
    # build, so the build outcome is not yet known. Only emits on a strict
    # decrease (delta < 0) so additions and no-ops don't trigger; the
    # 30-second `_recently_emitted` dedup blocks bursty re-emits when the
    # agent edits the same file repeatedly.
    if delta < 0:
        _emit(sandbox, "sorry-proved", {
            "inferred": True,
            "delta": delta,
            "file": rel_file,
            "observed_via": "hook",
            "agent_type": agent_type,
            "lake_build_pending": True,
        })


def main() -> None:
    sandbox = _resolve_sandbox()
    if sandbox is None:
        # CLI standalone (no $SANDBOX) → no per-job events.jsonl target;
        # silently exit. CLI users who want emit can set SANDBOX manually.
        sys.exit(0)

    payload = _read_payload()
    tool_name = payload.get("tool_name", "")
    if not tool_name:
        sys.exit(0)

    try:
        if tool_name == "Bash":
            _handle_bash(payload, sandbox)
        elif tool_name in ("Write", "Edit"):
            _handle_write_or_edit(payload, sandbox)
    except Exception:
        # Hooks must never crash the parent agent's tool flow.
        pass

    sys.exit(0)


if __name__ == "__main__":
    main()

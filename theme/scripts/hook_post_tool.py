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
MATCH_PITFALL = SCRIPTS_DIR / "match_pitfall.py"
SAVE_LAST_WRONG = SCRIPTS_DIR / "save_last_wrong_attempt.py"
AUTO_TACTIC = SCRIPTS_DIR / "auto_tactic_pre_pass.py"
STATLEAN_ROOT = SCRIPTS_DIR.parent.parent

DEDUP_WINDOW_MS = 30_000

# Phase 4 (czy port arch fix, 2026-05-01) — T1 escalation budget per call.
# match_pitfall + save_last_wrong_attempt are designed to be fast (<1s);
# 4s ceiling protects the parent hook's 8s budget against pathological
# inputs (e.g. unbounded stderr from a runaway process). auto_tactic spawns
# detached so its long-running cost doesn't count against this budget.
PHASE4_BUDGET_S = 4

# Auto-tactic lockout: once the orchestrator-driven 9-tactic pre-pass
# starts on a sandbox, suppress further spawn attempts for 10 minutes.
# auto_tactic_pre_pass itself caps at 20 sorries × 9 tactics × 10s/tactic
# ≈ 30 min worst case; the lockout ensures we don't stack two passes
# even when the agent makes rapid edits that re-cross the delta>0
# threshold.
AUTO_TACTIC_LOCKOUT_S = 600


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


# ── Phase 4 T1 escalation helpers ──────────────────────────────────
#
# Background: jobmolovhy6getc (2026-05-01) showed that prove-deep.md
# narrative T3 invocations of match_pitfall / save_last_wrong_attempt /
# auto_tactic_pre_pass are unreliable on production traffic — agent ran
# 100+ Bash calls without invoking ANY of these scripts. The fix is to
# call them deterministically from this PostTool hook (T1 — agent has
# no opportunity to skip). Scripts themselves are unchanged; only the
# dispatch fabric (this hook) is added.


def _parse_lake_errors(text: str) -> dict[str, list[dict]]:
    """Parse lake-build stderr into LSP-shape-2 diagnostics keyed by
    file path. Mirrors save_last_wrong_attempt.py's parse_lsp_diagnostics
    shape 2: {severity, message, line, column}.

    Lake build error format:
        /abs/path/file.lean:LINE:COL: error: <message>

    Multi-line errors (continuation lines without `error:`) are appended
    to the most recent error's message.

    Returns: {file_path: [{severity, message, line, column}, ...]}.
    Empty dict if no errors found.
    """
    out: dict[str, list[dict]] = {}
    last_key: tuple[str, int] | None = None  # (file, idx) of most recent err
    err_re = re.compile(r"^(.+\.lean):(\d+):(\d+):\s*error:\s*(.+)$")
    for line in text.splitlines():
        m = err_re.match(line)
        if m:
            f, lineno, col, msg = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
            out.setdefault(f, []).append({
                "severity": "error",
                "line": lineno,
                "column": col,
                "message": msg,
            })
            last_key = (f, len(out[f]) - 1)
        elif last_key is not None and line.strip():
            # Continuation line — append to last error's message (cap to keep tidy).
            f, idx = last_key
            cur = out[f][idx]["message"]
            if len(cur) < 800:
                out[f][idx]["message"] = cur + "\n" + line.rstrip()
    return out


def _call_match_pitfall(sandbox: Path, error_text: str) -> None:
    """Best-effort call to match_pitfall.py. Script itself emits the
    `pitfall-matched` milestone (with hint) when a rule matches; we
    just invoke and drop output."""
    if not MATCH_PITFALL.exists():
        return
    if not error_text:
        return
    try:
        subprocess.run(
            [
                "python3", str(MATCH_PITFALL),
                "--error-text", error_text[:4000],
                "--sandbox", str(sandbox),
            ],
            check=False, timeout=PHASE4_BUDGET_S,
            capture_output=True,
        )
    except Exception:
        pass


def _call_save_last_wrong_attempt(sandbox: Path, file_path: str, errors: list[dict]) -> None:
    """Best-effort call to save_last_wrong_attempt.py. Writes annotated
    `last_wrong_attempt.lean` artifact + emits milestone.

    save_last_wrong_attempt.py:319 only emits the milestone when
    `--sorry-id` is non-empty (czy parity — lastWrongAttempt.ts requires
    a target sorry to attach the failed-attempt to). The T1 hook path
    doesn't see a real sorry_id (lake build stderr has only file:line),
    so we synthesize an observability-only `auto:<basename>:<line>`
    identifier. Downstream consumers that expect real sorry IDs filter
    on the `auto:` prefix; the milestone otherwise carries the same
    structured payload as a T2 narrative-driven invocation.
    """
    if not SAVE_LAST_WRONG.exists():
        return
    if not Path(file_path).is_file():
        return
    if not errors:
        return
    first_line = errors[0].get("line", 0)
    sorry_id = f"auto:{Path(file_path).name}:{first_line}"
    try:
        subprocess.run(
            [
                "python3", str(SAVE_LAST_WRONG),
                "--sandbox", str(sandbox),
                "--content", file_path,
                "--diagnostics", json.dumps(errors),
                "--fail-type", "edit",
                "--sorry-id", sorry_id,
            ],
            check=False, timeout=PHASE4_BUDGET_S,
            capture_output=True,
        )
    except Exception:
        pass


def _maybe_spawn_auto_tactic(sandbox: Path) -> None:
    """Spawn auto_tactic_pre_pass.py detached when sorry pool grows.
    Runs in background — its 9-tactic ladder × N sorries can take
    minutes, far exceeding the hook's 8s budget. Lockout file prevents
    redundant spawns when the agent makes rapid sorry-pool-changing
    edits.

    Note: auto_tactic_pre_pass itself uses python subprocess to invoke
    `lake build` for each tactic attempt; subprocess builds do NOT
    re-trigger this hook (PostTool hooks fire only on agent's tool
    calls, not on script-spawned subprocesses), so there's no risk of
    a hook-recursion loop.
    """
    if not AUTO_TACTIC.exists():
        return
    lock = sandbox / ".auto_tactic.lock"
    try:
        if lock.exists():
            mtime = lock.stat().st_mtime
            if (dt.datetime.now().timestamp() - mtime) < AUTO_TACTIC_LOCKOUT_S:
                return
    except Exception:
        pass
    try:
        lock.touch()
    except Exception:
        pass
    try:
        # Detached spawn — do NOT wait. auto_tactic emits its own
        # milestones (auto-tactic-fired / sorry-proved) as it goes.
        # Pipe stdout/stderr to log files in sandbox so failures are
        # diagnosable without polluting the agent's tool stream.
        log = sandbox / ".auto_tactic.log"
        with open(log, "ab") as f:
            subprocess.Popen(
                [
                    "python3", str(AUTO_TACTIC),
                    "--sandbox", str(sandbox),
                    "--statlean-root", str(STATLEAN_ROOT),
                ],
                stdout=f, stderr=subprocess.STDOUT,
                start_new_session=True,
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

        # Phase 4 T1 escalation: on lake-build-fail, fire match_pitfall +
        # save_last_wrong_attempt deterministically. The narrative T3
        # path (agent calling these via prove-deep.md instructions) is
        # unreliable on production traffic; this hook ensures the czy
        # port arsenal actually triggers when needed. See module
        # docstring for jobmolovhy6getc evidence.
        if had_error:
            combined = (stdout or "") + "\n" + (stderr or "")
            # match_pitfall is fast (regex over ≤4000 chars); always call.
            _call_match_pitfall(sandbox, combined)
            # save_last_wrong_attempt: only if we can identify a failing
            # Statlean .lean file in the error stream. Each file gets
            # its own annotated artifact, but we cap at the first file
            # to keep hook latency bounded — multiple failing files in
            # one build is rare and the agent gets the most-relevant one.
            for fpath, errs in _parse_lake_errors(combined).items():
                if "/Statlean/" in fpath and fpath.endswith(".lean") and Path(fpath).is_file():
                    _call_save_last_wrong_attempt(sandbox, fpath, errs)
                    break


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

    # Phase 4 T1 escalation: when sorry pool GROWS (delta>0, e.g. skeleton
    # write or fresh decomposition), fire auto_tactic_pre_pass detached.
    # M5's 9-tactic ladder closes any sorry that yields to rfl/decide/
    # ring/linarith/omega/norm_num/simp/aesop/trivial — typically the
    # trivial cases skeletons leave behind ("isProbability θ := by sorry"
    # → infer_instance / decide). On main agent edits this catches new
    # work; subagents inherit the same hook so dispatch_helper-driven
    # decompositions also get the pre-pass.
    if delta > 0:
        _maybe_spawn_auto_tactic(sandbox)


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

#!/usr/bin/env python3
"""extract_web_probe.py — bundle the side-effect chain for one
helper-web-probe Task sub-agent's output (H5 slice).

Per `docs/H5_WEB_PROBE_SPEC.md`. Replaces the narrative
"agent should: parse JSON, validate, write yaml fields, emit event"
chain with a single named script. Per CLAUDE.md Rule 9 §3 (T-tier):
T2 single-script bundling. Agent invokes once per sub-problem; script
enforces all sub-steps atomically.

Inputs (mirrors czy `SearchSubAgent.webProbe` `:196-242`):
  - The helper-web-probe Task subagent emits a JSON object to stdout.
    Format per spec §3.2 / SKILL.md Output Contract:
        {
          "sub_problem_id": "...",
          "generated_query": "...",
          "web_hits": [{"title": "...", "url": "...", "snippet": "..."}],
          "web_fetch_content": "...",
          "findings": "...",
          "suggestion": "...",
          "assembled_context": "## Web Probe ..."
        }
  - The orchestrator reads the subagent output and passes it via
    `--subagent-json-file` (file path; avoids shell-quoting hazards).

Side-effects (atomic under flock):
  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Locates the targeted sorry by `--sub-problem-id`
  - Reads SKILL JSON output from `--subagent-json-file`
  - On parse fail / non-object root / missing assembled_context field
    → verdict=parse_error, yaml unchanged, exit 2
  - On `web_hits=[]` AND `web_fetch_content=""` (empty-hits fast-path)
    → verdict=`empty`, write webprobe_context="", exit 0 (D-5 deliberate +1)
  - On non-empty assembled_context → OVERWRITE webprobe_context with
    assembled_context text (clamped to 3000 chars per D-7 + R8),
    emit milestone verdict=`completed`
  - Emits one `web-probe-completed` milestone with payload per spec §4.2

**D-5 semantic (deliberate +1 deviation per spec §11 D-5).** When
web_hits==[] and web_fetch_content=="", emit verdict=`empty` and write
webprobe_context="" rather than writing the hardcoded fast-path text.
The fast-path "Try a different approach" text is not actionable for the
prover; writing it would appear as a real finding when it isn't.

**D-7 semantic (overwrite-on-each-call).** Each invocation OVERWRITES
the prior webprobe_context on the targeted sorry row. czy parity — czy's
in-memory assembledContext is per-call, not accumulated.

Rule 3 Layer 1 invariant: mutates ONLY `webprobe_context` on the targeted
sorry row. All other fields (locked theorem signature, file, line, theorem,
parent_id, children, state, history_log, coverage_state, references,
done_reason, citation_verified, informal_round, coverage_stable,
assumption_hints, assumption_analysis) are untouched. Test L1.7 enforces.

Exit codes:
  0  — operation applied successfully (completed | empty)
  2  — validation error (sub-problem not found, malformed input, missing
       assembled_context field)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/extract_web_probe.py \\
        --sub-problem-id <id> \\
        --subagent-json-file /path/to/subagent-output.json \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]

    # Consume-once clear (D-7):
    python3 theme/scripts/extract_web_probe.py \\
        --sub-problem-id <id> \\
        --clear-context \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

# Renderer-level cap: assembled_context deep-fetch block truncated to 2000 chars
# (czy `renderWebProbeContext` `:664`: `fetchedContent.trim().slice(0, 2000)`)
ASSEMBLED_CONTEXT_MAX_CHARS = 3000

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# ── Fence stripping (czy safeParseJson / stripJsonFences) ─────────────

_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def _unwrap_fenced_json(s: str) -> str:
    """Strip markdown fences if present (mirrors extract_assumption.py)."""
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── Verdict sentinels ────────────────────────────────────────────────

VERDICT_COMPLETED = "completed"
VERDICT_EMPTY = "empty"
VERDICT_PARSE_ERROR = "parse_error"
VERDICT_CLEARED = "cleared"


# ── Parse + validate ─────────────────────────────────────────────────


def parse_subagent_output(raw_text: str) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    """Parse helper-web-probe subagent JSON output.

    Returns `(parsed_dict, error)`:
      - On success: `(dict, None)` — validated shape
      - On parse failure: `(None, error_message)` — caller exits 2

    Required fields: assembled_context (str), findings (str), suggestion (str).
    Optional but tracked: generated_query (str), web_hits (list),
    web_fetch_content (str).
    """
    unwrapped = _unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return None, "subagent output is empty after unwrap"
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return None, f"subagent output is not valid JSON: {e}"
    if not isinstance(parsed, dict):
        return None, f"subagent output root must be object, got {type(parsed).__name__}"

    # assembled_context is the critical field; missing → parse_error
    if "assembled_context" not in parsed:
        return None, "missing required field: assembled_context"
    if not isinstance(parsed["assembled_context"], str):
        return None, (
            f"assembled_context must be str, got "
            f"{type(parsed['assembled_context']).__name__}"
        )

    # Graceful defaults for optional fields (spec L1.9, L1.10)
    if "findings" not in parsed or not isinstance(parsed.get("findings"), str):
        parsed["findings"] = "(no findings)"
    if "suggestion" not in parsed or not isinstance(parsed.get("suggestion"), str):
        parsed["suggestion"] = ""
    if "generated_query" not in parsed or not isinstance(parsed.get("generated_query"), str):
        parsed["generated_query"] = ""
    if "web_hits" not in parsed or not isinstance(parsed.get("web_hits"), list):
        parsed["web_hits"] = []
    if "web_fetch_content" not in parsed or not isinstance(parsed.get("web_fetch_content"), str):
        parsed["web_fetch_content"] = ""

    return parsed, None


# ── Core ──────────────────────────────────────────────────────────────


def apply_web_probe(
    backlog_path: Path,
    sub_problem_id: str,
    subagent_text: str,
) -> Tuple[Dict[str, Any], int]:
    """Apply web probe extraction under flock + atomic write.

    Returns (milestone_payload, exit_code).
    exit_code 0 = success; 2 = validation/parse error.

    Raises ValueError on sub_problem_id not found.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    started_ms = int(time.time() * 1000)

    parsed, parse_err = parse_subagent_output(subagent_text)

    if parse_err is not None:
        # parse_error: yaml unchanged, return exit_code=2
        elapsed = int(time.time() * 1000) - started_ms
        payload: Dict[str, Any] = {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "query_used": None,
            "hits_count": 0,
            "whitelisted_fetched_count": 0,
            "findings_excerpt": None,
            "context_length": 0,
            "took_ms": elapsed,
            "parse_error": parse_err[:200],
        }
        return payload, 2

    assert parsed is not None

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            raise ValueError(f"sub_problem_id not in sorry_items: {sub_problem_id}")

        assembled_context: str = parsed["assembled_context"]
        web_hits: List[Any] = parsed["web_hits"]
        web_fetch_content: str = parsed["web_fetch_content"]
        generated_query: str = parsed["generated_query"]
        findings: str = parsed["findings"]

        hits_count = len(web_hits)

        # D-5: empty-hits fast-path — if no hits and no fetched content,
        # emit verdict=empty and write "" to webprobe_context.
        # This matches the D-5 deliberate +1 deviation: the hardcoded
        # fast-path text is not written (it's not actionable for the prover).
        is_empty = (hits_count == 0 and not web_fetch_content.strip())

        if is_empty:
            # Overwrite with empty string (consume-once: clear previous stale)
            for it in items:
                if it.get("id") == sub_problem_id:
                    it["webprobe_context"] = ""
                    break
            atomic_write_yaml(backlog_path, data)

            elapsed = int(time.time() * 1000) - started_ms
            payload = {
                "sub_problem_id": sub_problem_id,
                "verdict": VERDICT_EMPTY,
                "query_used": generated_query or "(unknown)",
                "hits_count": 0,
                "whitelisted_fetched_count": 0,
                "findings_excerpt": None,
                "context_length": 0,
                "took_ms": elapsed,
            }
            return payload, 0

        # Non-empty: clamp assembled_context to ASSEMBLED_CONTEXT_MAX_CHARS (R8)
        context_to_write = assembled_context[:ASSEMBLED_CONTEXT_MAX_CHARS]

        # Count how many URLs were actually deep-fetched
        # (rough estimate: count "--- https:" URL headers in web_fetch_content)
        fetched_count = web_fetch_content.count("\n\n--- ") if web_fetch_content else 0

        # Layer 1 invariant: mutate ONLY webprobe_context on targeted row
        for it in items:
            if it.get("id") == sub_problem_id:
                it["webprobe_context"] = context_to_write
                break

        atomic_write_yaml(backlog_path, data)

        elapsed = int(time.time() * 1000) - started_ms
        findings_excerpt = _truncate(findings, 200) if findings else None
        payload = {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_COMPLETED,
            "query_used": generated_query or "(unknown)",
            "hits_count": hits_count,
            "whitelisted_fetched_count": fetched_count,
            "findings_excerpt": findings_excerpt,
            "context_length": len(context_to_write),
            "took_ms": elapsed,
        }
        return payload, 0


def apply_clear_context(
    backlog_path: Path,
    sub_problem_id: str,
) -> Tuple[bool, Optional[str]]:
    """Clear webprobe_context for consume-once semantic (D-7).

    Returns (success, error_message). No milestone emitted on clear.
    """
    if not backlog_path.exists():
        return False, f"backlog not found: {backlog_path}"

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            return False, f"sub_problem_id not in sorry_items: {sub_problem_id}"

        for it in items:
            if it.get("id") == sub_problem_id:
                it["webprobe_context"] = ""
                break

        atomic_write_yaml(backlog_path, data)

    return True, None


# ── CLI ───────────────────────────────────────────────────────────────


def _truncate(s: Optional[str], n: int = 200) -> Optional[str]:
    if s is None or s == "":
        return None
    return s if len(s) <= n else s[: n - 1] + "…"


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort."""
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", name,
                "--details", json.dumps(details, ensure_ascii=False),
            ],
            check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(
            f"[extract_web_probe] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Spec §4.2 invariants asserted before emit."""
    verdict = payload["verdict"]
    if verdict == VERDICT_COMPLETED:
        assert payload["context_length"] >= 1, (
            f"completed verdict requires context_length >= 1, "
            f"got {payload['context_length']}"
        )
        assert payload["findings_excerpt"] is not None, (
            "completed verdict requires non-null findings_excerpt"
        )
    elif verdict == VERDICT_EMPTY:
        assert payload["context_length"] == 0, (
            f"empty verdict requires context_length == 0, "
            f"got {payload['context_length']}"
        )
        assert payload["findings_excerpt"] is None, (
            f"empty verdict requires null findings_excerpt, "
            f"got {payload['findings_excerpt']!r}"
        )
    elif verdict == VERDICT_PARSE_ERROR:
        assert payload["context_length"] == 0, (
            f"parse_error verdict requires context_length == 0"
        )
        assert payload["findings_excerpt"] is None, (
            "parse_error verdict requires null findings_excerpt"
        )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--sub-problem-id",
        required=True,
        help="The sorry_item id whose webprobe_context will be written.",
    )
    p.add_argument(
        "--subagent-json-file",
        default=None,
        help=(
            "Path to a file containing the helper-web-probe subagent's "
            "JSON output. Required unless --clear-context is given."
        ),
    )
    p.add_argument(
        "--clear-context",
        action="store_true",
        default=False,
        help="Clear webprobe_context to '' (consume-once, D-7). No milestone emitted.",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    # ── --clear-context path ─────────────────────────────────────────
    if args.clear_context:
        try:
            success, err = apply_clear_context(backlog_path, args.sub_problem_id)
        except yaml.YAMLError as e:
            print(f"[extract_web_probe] yaml parse failed: {e}", file=sys.stderr)
            return 3
        except OSError as e:
            print(f"[extract_web_probe] IO failure: {e}", file=sys.stderr)
            return 4
        if not success:
            print(f"[extract_web_probe] clear-context failed: {err}", file=sys.stderr)
            return 2
        print(
            f"[extract_web_probe] cleared webprobe_context for "
            f"sub={args.sub_problem_id}"
        )
        return 0

    # ── --subagent-json-file path ────────────────────────────────────
    if not args.subagent_json_file:
        print(
            "[extract_web_probe] --subagent-json-file is required when "
            "--clear-context is not given",
            file=sys.stderr,
        )
        return 2

    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[extract_web_probe] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[extract_web_probe] read failed: {e}", file=sys.stderr)
        return 4

    try:
        payload, exit_code = apply_web_probe(
            backlog_path=backlog_path,
            sub_problem_id=args.sub_problem_id,
            subagent_text=subagent_text,
        )
    except ValueError as e:
        print(f"[extract_web_probe] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[extract_web_probe] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[extract_web_probe] IO failure: {e}", file=sys.stderr)
        return 4

    if exit_code == 0:
        _validate_payload(payload)
        _emit(sandbox, "web-probe-completed", payload)
        print(
            f"[extract_web_probe] sub={args.sub_problem_id} "
            f"verdict={payload['verdict']} "
            f"hits={payload['hits_count']} "
            f"context_length={payload['context_length']}"
        )
    else:
        # parse_error: emit milestone but return exit_code=2
        _emit(sandbox, "web-probe-completed", payload)
        print(
            f"[extract_web_probe] parse_error: sub={args.sub_problem_id} "
            f"error={payload.get('parse_error', '?')}",
            file=sys.stderr,
        )

    return exit_code


if __name__ == "__main__":
    sys.exit(main())

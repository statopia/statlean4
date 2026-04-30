#!/usr/bin/env python3
"""extract_assumption.py — bundle the side-effect chain for one
helper-assumption Task sub-agent's output (H7 slice).

Per `docs/H7_HELPER_ASSUMPTION_SPEC.md`. Replaces the narrative
"agent should: parse JSON, validate, write yaml fields, emit event"
chain with a single named script. Per CLAUDE.md Rule 9 §3 (T-tier):
T2 single-script bundling. Agent invokes once per sub-problem; script
enforces all sub-steps atomically.

Inputs (mirrors czy `AssumptionSubAgent.diagnose` `:74-132`):
  - The helper-assumption Task subagent emits a JSON object to stdout.
    Format per czy `helperAssumptionSubAgent.ts:32-60` DIAGNOSE_SYSTEM:
        {
          "missingAssumptions": [
            "Natural language statement of missing assumption 1",
            "Natural language statement of missing assumption 2"
          ],
          "analysis": "Brief explanation of why stuck and what fixes."
        }
  - The orchestrator reads the subagent output and pipes it via
    `--subagent-json-file` (file path; we don't take stdin to avoid
    shell-quoting hazards on JSON containing newlines).

Side-effects (atomic under flock):
  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Locates the targeted sorry by `--sub-problem-id`
  - Reads SKILL JSON output from `--subagent-json-file`
  - On parse fail / non-object root / missing fields → verdict=parse_error,
    yaml unchanged, milestone emitted
  - On `missingAssumptions == []` → verdict=`empty`, write
    `assumption_analysis = analysis` ONLY (NOT assumption_hints), milestone
  - On non-empty → trim each hint to ≤400 chars (czy `:114-118`), strip
    empty, **OVERWRITE** `assumption_hints` with the new list (NOT
    append per D-1), set `assumption_analysis = analysis`, atomic write,
    milestone verdict=`extracted`
  - Emits one `assumption-extracted` milestone with payload schema
    matching spec §4

**D-1 semantic (per spec §10).** OVERWRITE-on-each-call, NOT
FIFO-accumulate. czy `helperAssumptionSubAgent.ts:74-132` returns
`missingAssumptionNLs: list[str]` per call — czy emits a per-call list
and never persists across calls in any global structure. Cross-round
chain semantic in czy emerges through description-enrichment +
re-autoformalize cycle (H4's territory), NOT yaml accumulation.
Second-call's list FULLY REPLACES first's. L1.6 + L1.8 + L1.10 enforce.

**D-2 semantic.** Model selection via SDK-bridge runtime inheritance
(Task tool inherits parent claude session's model — same as E4 / E11 /
slice 03 helper SKILLs). NO explicit model choice in SKILL.md.

Rule 3 Layer 1 invariant (per `record_retreat.py:11-13` precedent):
mutates ONLY `assumption_hints` + `assumption_analysis` on the targeted
sorry row. Locked theorem signature / file / line / theorem / parent_id
/ children / state / history_log / coverage_state / coverage_citation /
references / done_reason / citation_verified / informal_round /
coverage_stable / detailed_proof_plan / direct_assembly / proof_sketch
untouched. Test L1.7 enforces.

Exit codes:
  0  — extraction applied successfully (extracted | empty)
  2  — validation error (sub-problem not found, malformed input)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/extract_assumption.py \\
        --sub-problem-id <id> \\
        --subagent-json-file /path/to/subagent-output.json \\
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

sys.path.insert(0, str(SCRIPTS_DIR))
from _assumption_types import (  # noqa: E402
    AssumptionDiagnoseResult,
    build_finding_summary,
    trim_analysis,
    trim_hint,
)
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# ── JSON unwrap (czy safeParseJson `:167-178`) ────────────────────────


# Mirrors `extract_references.py:_FENCE_RE` and `verify_citation.py:_FENCE_RE`
# byte-faithfully. czy `helperAssumptionSubAgent.ts:171` strips
# `/```(?:json)?\\s*/g` and `/```\\s*$/g` — our regex captures any
# fenced block and returns the inner text.
_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def unwrap_fenced_json(s: str) -> str:
    """LLMs often wrap JSON output in markdown fences. czy strips with
    `/```(?:json)?\\s*\\n?([\\s\\S]*?)\\n?```/`. We mirror byte-for-byte.
    If no fence present, return input unchanged.
    """
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── Validation / parse ────────────────────────────────────────────────


# Sentinel verdicts emitted in the milestone payload. The script itself
# emits only the first three; `task_dispatch_failure` is reserved for
# caller-emitted use (D-5).
VERDICT_EXTRACTED = "extracted"
VERDICT_EMPTY = "empty"
VERDICT_PARSE_ERROR = "parse_error"
VERDICT_TASK_DISPATCH_FAILURE = "task_dispatch_failure"  # reserved (D-5)


def parse_subagent_output(raw_text: str) -> Tuple[Optional[AssumptionDiagnoseResult], Optional[str]]:
    """Parse helper-assumption subagent JSON output.

    Returns `(result, error)`:
      - On success: `(AssumptionDiagnoseResult, None)`
      - On parse failure: `(None, error_message)` — caller emits
        verdict=`parse_error`, yaml unchanged.

    Parse contract (czy `:108-120`):
      - Strip markdown fence (czy `safeParseJson` `:167-178`).
      - JSON.parse → expect object root (NOT array, NOT scalar; czy `:169` returns null on non-object).
      - `missingAssumptions` → must be array of strings (czy `:114-118`):
          * non-string entries silently dropped
          * empty / whitespace-only strings dropped
          * each entry trimmed + clipped to 400 chars
      - `analysis` → string trimmed + clipped to 400 chars; missing field defaults to "" (czy `:120` `typeof === "string" ? ... : ""`).

    NOTE: czy `:108-112` swallows ALL parse failures and returns
    `emptyResult()` — the caller (HelperAgent) treats as "diagnostician
    failed silently." H7's port elevates the parse failure into an
    explicit `parse_error` verdict so observability can distinguish
    "diagnostician ran and found nothing" from "diagnostician failed."
    The yaml remains unchanged in either case (czy parity at the
    persistence level).
    """
    unwrapped = unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return None, "subagent output is empty after unwrap"
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return None, f"subagent output is not valid JSON: {e}"
    if not isinstance(parsed, dict):
        # czy `:169` `JSON.parse` returns the parsed value; czy then
        # accesses `.missingAssumptions` which is undefined on non-object
        # root. We make the failure explicit at the parse boundary.
        return None, (
            f"subagent output root must be object, got "
            f"{type(parsed).__name__}"
        )

    raw_missing = parsed.get("missingAssumptions")
    if raw_missing is None:
        # Defensive: czy `:114-118` `Array.isArray` short-circuits to []
        # on missing/non-array `missingAssumptions`. We mirror that
        # behavior — missing field is treated as empty list (NOT a parse
        # error). The caller decides whether to write analysis-only.
        nls: List[str] = []
    elif not isinstance(raw_missing, list):
        return None, (
            f"missingAssumptions must be array, got "
            f"{type(raw_missing).__name__}"
        )
    else:
        # czy `:115-117`: filter to non-empty strings, trim each, clip to 400.
        nls = []
        for entry in raw_missing:
            if not isinstance(entry, str):
                continue
            cleaned = trim_hint(entry)
            if cleaned:  # drop empty / whitespace-only after trim
                nls.append(cleaned)

    raw_analysis = parsed.get("analysis")
    # czy `:120` `typeof parsed.analysis === "string" ? trim().slice : ""`
    analysis = trim_analysis(raw_analysis) if isinstance(raw_analysis, str) else ""

    finding_summary = build_finding_summary(nls, analysis)

    return AssumptionDiagnoseResult(
        missing_assumption_nls=nls,
        analysis=analysis,
        finding_summary=finding_summary,
    ), None


# ── Core ──────────────────────────────────────────────────────────────


def apply_extraction(
    backlog_path: Path,
    sub_problem_id: str,
    subagent_text: str,
) -> Dict[str, Any]:
    """Apply extraction under flock + atomic write. Returns the milestone
    payload dict (caller emits it).

    Raises ValueError on validation failure (sub_problem_id missing).

    D-1 OVERWRITE semantic: `assumption_hints` is REPLACED with the
    latest call's per-call list (NOT appended). czy parity — czy returns
    `missingAssumptionNLs: list[str]` per call, doesn't accumulate.
    Read-modify-write under flock + atomic write so the field replacement
    is observable in one yaml mutation.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    started_ms = int(time.time() * 1000)

    result, parse_err = parse_subagent_output(subagent_text)

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            raise ValueError(f"sub_problem_id not in sorry_items: {sub_problem_id}")

        # Capture pre-write hint count for telemetry. previous_hint_count
        # is informational only (D-1 invariant: post-write count equals
        # the per-call list size, not previous + new).
        previous_hints = list(item.get("assumption_hints") or [])
        previous_hint_count = len(previous_hints)

        if parse_err is not None:
            # parse_error: yaml unchanged, milestone with parse_error verdict.
            elapsed = int(time.time() * 1000) - started_ms
            return {
                "sub_problem_id": sub_problem_id,
                "verdict": VERDICT_PARSE_ERROR,
                "added_hints_count": 0,
                "previous_hint_count": previous_hint_count,
                "current_hint_count": previous_hint_count,
                "excerpt": None,
                "analysis_excerpt": None,
                "took_ms": elapsed,
                "parse_error": parse_err[:200],
            }

        assert result is not None  # mypy / defensive — parse_err==None implies result present

        if not result.missing_assumption_nls:
            # verdict=empty: assumption_analysis updated only (NOT
            # assumption_hints). Per spec §3.3 step 7: "Update
            # assumption_analysis (latest analysis text) only."
            # Note: assumption_hints is preserved on `empty` per spec
            # explicit wording — only updates analysis.
            #
            # Wait — re-reading spec §7.1 L1.8: "empty new list overwrites
            # non-empty existing → final length 0; verdict=`empty`".
            # That contradicts §3.3 step 7. Resolution: L1.8 is the
            # authoritative behavior (empty IS overwrite), and §3.3 step 7
            # was incomplete. The D-1 OVERWRITE semantic is consistent —
            # second-call's list FULLY REPLACES first's, EVEN when the
            # second-call's list is empty. So we DO overwrite to []
            # on `empty` verdict.
            for it in items:
                if it.get("id") == sub_problem_id:
                    it["assumption_hints"] = []
                    it["assumption_analysis"] = result.analysis
                    break
            atomic_write_yaml(backlog_path, data)

            elapsed = int(time.time() * 1000) - started_ms
            return {
                "sub_problem_id": sub_problem_id,
                "verdict": VERDICT_EMPTY,
                "added_hints_count": 0,
                "previous_hint_count": previous_hint_count,
                "current_hint_count": 0,
                "excerpt": None,
                "analysis_excerpt": _truncate(result.analysis, 200),
                "took_ms": elapsed,
            }

        # verdict=extracted: OVERWRITE assumption_hints with the new list
        # + update assumption_analysis.
        for it in items:
            if it.get("id") == sub_problem_id:
                # Layer 1 invariant: only these two fields are mutated.
                # All other fields on this row stay byte-identical.
                it["assumption_hints"] = list(result.missing_assumption_nls)
                it["assumption_analysis"] = result.analysis
                break

        atomic_write_yaml(backlog_path, data)

        elapsed = int(time.time() * 1000) - started_ms
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_EXTRACTED,
            "added_hints_count": len(result.missing_assumption_nls),
            "previous_hint_count": previous_hint_count,
            "current_hint_count": len(result.missing_assumption_nls),
            "excerpt": _truncate(result.finding_summary, 200),
            "analysis_excerpt": _truncate(result.analysis, 200),
            "took_ms": elapsed,
        }


# ── CLI ───────────────────────────────────────────────────────────────


def _truncate(s: Optional[str], n: int = 200) -> Optional[str]:
    if s is None or s == "":
        return None
    return s if len(s) <= n else s[: n - 1] + "…"


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort
    (matches record_retreat / extract_references / verify_citation
    pattern)."""
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
            f"[extract_assumption] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Spec §4 invariants asserted before emit.

      - verdict=`extracted` → added_hints_count >= 1; excerpt non-null
      - verdict=`empty` → added_hints_count == 0; excerpt is None;
        analysis_excerpt may be non-null (LLM analyzed but found nothing)
      - verdict=`parse_error` → added_hints_count == 0; excerpt is None;
        analysis_excerpt is None
      - current_hint_count == added_hints_count (D-1 OVERWRITE: post-write
        count equals per-call list size, NOT previous + new)
    """
    verdict = payload["verdict"]
    if verdict == VERDICT_EXTRACTED:
        assert payload["added_hints_count"] >= 1, (
            f"extracted verdict requires added_hints_count >= 1, "
            f"got {payload['added_hints_count']}"
        )
        assert payload["excerpt"] is not None, (
            "extracted verdict requires non-null excerpt"
        )
    elif verdict == VERDICT_EMPTY:
        assert payload["added_hints_count"] == 0, (
            f"empty verdict requires added_hints_count == 0, "
            f"got {payload['added_hints_count']}"
        )
        assert payload["excerpt"] is None, (
            f"empty verdict requires null excerpt, got {payload['excerpt']!r}"
        )
    elif verdict == VERDICT_PARSE_ERROR:
        assert payload["added_hints_count"] == 0, (
            f"parse_error verdict requires added_hints_count == 0"
        )
        assert payload["excerpt"] is None, (
            "parse_error verdict requires null excerpt"
        )
        assert payload["analysis_excerpt"] is None, (
            "parse_error verdict requires null analysis_excerpt"
        )
    # D-1 OVERWRITE invariant — current_hint_count equals the per-call
    # list size (added_hints_count), NOT previous + new.
    assert payload["current_hint_count"] == payload["added_hints_count"], (
        f"OVERWRITE invariant violated: current_hint_count="
        f"{payload['current_hint_count']} != added_hints_count="
        f"{payload['added_hints_count']}"
    )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--sub-problem-id",
        required=True,
        help="The sorry_item id whose assumption_hints/analysis will be written.",
    )
    p.add_argument(
        "--subagent-json-file",
        required=True,
        help="path to a file containing the helper-assumption subagent's JSON output",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()

    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[extract_assumption] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[extract_assumption] read failed: {e}", file=sys.stderr)
        return 4

    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        payload = apply_extraction(
            backlog_path=backlog_path,
            sub_problem_id=args.sub_problem_id,
            subagent_text=subagent_text,
        )
    except ValueError as e:
        print(f"[extract_assumption] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[extract_assumption] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[extract_assumption] IO failure: {e}", file=sys.stderr)
        return 4

    _validate_payload(payload)
    _emit(sandbox, "assumption-extracted", payload)

    print(
        f"assumption extracted: sub={args.sub_problem_id} "
        f"verdict={payload['verdict']} "
        f"added={payload['added_hints_count']} "
        f"prev={payload['previous_hint_count']} "
        f"current={payload['current_hint_count']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

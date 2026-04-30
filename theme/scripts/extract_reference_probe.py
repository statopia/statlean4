#!/usr/bin/env python3
"""extract_reference_probe.py — bundle the side-effect chain for one
helper-reference-probe Task sub-agent's output (H6 slice).

Per `docs/H6_REFERENCE_PROBE_SPEC.md`. Replaces the narrative
"agent should: parse JSON, validate, write yaml fields, emit event"
chain with a single named script. Per CLAUDE.md Rule 9 §3 (T-tier):
T2 single-script bundling. Agent invokes once per stuck sub-problem;
script enforces all sub-steps atomically.

Inputs (mirrors czy `ReferenceSubAgent.referenceProbe` `:312-376`):
  - The helper-reference-probe Task subagent emits a JSON object to stdout.
    Format per czy `helperReferenceSubAgent.ts:106-119` REFERENCE_PROBE_SYSTEM:
        {
          "matchedPassage": "...",
          "analysis": "explain how this passage connects — ≤300 chars",
          "suggestion": "concrete next step: which Lean tactic, ≤500 chars"
        }
  - The orchestrator reads the subagent output and pipes it via
    `--subagent-json-file` (file path; we don't take stdin to avoid
    shell-quoting hazards on JSON containing newlines).

Side-effects (atomic under flock):
  - Checks `paper_body.txt` existence + length (< 10 chars → skip, exit 0,
    verdict=skipped_no_reference, referenceprobe_findings NOT written)
  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Locates the targeted sorry by `--sub-problem-id`
  - Reads SKILL JSON output from `--subagent-json-file`
  - Defensive parse: strip markdown fences, retry. Failure →
    verdict=parse_error, yaml unchanged, milestone emitted, exit 2.
  - Clamps fields (czy `:355-357`):
      matchedPassage ≤ 500 chars
      analysis       ≤ 300 chars
      suggestion     ≤ 500 chars
  - Builds assembledContext (czy `buildAssembledContext` `:520-540`):
      all-empty → fallback string "Reference probe found no content ..."
      else → join non-empty sections, cap 3000 chars with "..."
  - Builds findingSummary (≤200 chars) for milestone payload (D-5)
  - Appends finding_entry to referenceprobe_findings[] (D-2 accumulate
    semantics, max 10 entries — oldest dropped on overflow)
  - Atomic yaml write under lock
  - Emits one `reference-probe-completed` milestone

**D-2 semantic (per spec §11):** ACCUMULATE-on-each-call (NOT overwrite).
Each call appends a new entry. Max 10 entries; oldest dropped when exceeded.
Rationale: reference probe is more expensive (large pdfProofBody input);
findings from round N still carry useful signal in round N+2.
Contrast with H7 `assumption_hints` which uses OVERWRITE semantics.

**D-3 semantic (per spec §11):** `assembledContext` is written to yaml
ONLY. It is NOT injected into the prover prompt in H6-mvp (faithful
reproduction of czy gap: `proofLoop.ts:1314 helperContext: undefined`).
Injection is the H6-prover-inject follow-on slice.

Rule 3 Layer 1 invariant (per `record_retreat.py:11-13` precedent):
mutates ONLY `referenceprobe_findings` on the targeted sorry row. Locked
theorem signature / file / line / theorem / parent_id / children / state /
history_log / coverage_state / coverage_citation / references /
assumption_hints / assumption_analysis / alternative_path / library_hit
untouched. Test L1.7 enforces.

Exit codes:
  0  — success (probed | probed_no_content | skipped_no_reference)
  2  — validation error (sub-problem not found, malformed JSON, missing json file)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/extract_reference_probe.py \\
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
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# ── Field clamping caps (czy `:355-357`) ─────────────────────────────

MATCHED_PASSAGE_MAX = 500   # czy `:355` `.slice(0, 500)`
ANALYSIS_MAX = 300          # czy `:356` `.slice(0, 300)`
SUGGESTION_MAX = 500        # czy `:357` `.slice(0, 500)`
ASSEMBLED_CONTEXT_MAX = 3000   # czy `buildAssembledContext` `:540`
FINDING_SUMMARY_MAX = 200   # D-5 observability cap
MAX_FINDINGS_PER_ITEM = 10  # D-2 accumulate cap (oldest dropped on overflow)

# Minimum paper_body.txt length for reference probe to fire (czy `:319-321`)
PAPER_BODY_MIN_CHARS = 10

# ── Verdict sentinels ─────────────────────────────────────────────────

VERDICT_PROBED = "probed"
VERDICT_PROBED_NO_CONTENT = "probed_no_content"
VERDICT_SKIPPED_NO_REFERENCE = "skipped_no_reference"
VERDICT_PARSE_ERROR = "parse_error"


# ── JSON unwrap (mirrors czy safeParseJson / extract_assumption.py) ───

_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def unwrap_fenced_json(s: str) -> str:
    """LLMs often wrap JSON output in markdown fences. czy strips with
    `/```(?:json)?\\s*\\n?([\\s\\S]*?)\\n?```/`. Mirror byte-for-byte.
    If no fence present, return input unchanged.
    """
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── buildAssembledContext (czy `:520-540`) ────────────────────────────


def build_assembled_context(
    matched_passage: str,
    analysis: str,
    suggestion: str,
) -> str:
    """Port of czy `buildAssembledContext` (`helperReferenceSubAgent.ts:520-540`).

    - All three empty → return fallback string.
    - Otherwise: join non-empty sections (separated by "\\n\\n"), cap at
      3000 chars using `total[:2997] + "..."` (L1.10 assertion:
      `len == 3000 AND assembledContext[-3:] == "..."`)
    """
    if not matched_passage and not analysis and not suggestion:
        return "Reference probe found no content directly relevant to the current stuck point."

    parts: List[str] = []
    if matched_passage:
        parts.append(f"**Matched passage**:\n{matched_passage}")
    if analysis:
        parts.append(f"**Why it might help**:\n{analysis}")
    if suggestion:
        parts.append(f"**Suggested next step**:\n{suggestion}")

    total = "\n\n".join(parts)
    if len(total) <= ASSEMBLED_CONTEXT_MAX:
        return total
    # Cap at 3000 chars: total[:2997] + "..." per L1.10 spec requirement
    return total[:2997] + "..."


# ── findingSummary builder (D-5 observability) ────────────────────────


def build_finding_summary(analysis: str, suggestion: str) -> str:
    """Build a ≤200 char finding_summary for the milestone payload.

    D-5 deliberate +1 deviation: czy's ReferenceProbeResult has a
    `findingSummary?: string` field (`:75`) but it is never populated by
    `referenceProbe`. H6 builds it from the LLM response fields for
    observability.

    Priority: analysis first, then suggestion prefix, then fallback.
    """
    if analysis:
        return analysis[:FINDING_SUMMARY_MAX]
    if suggestion:
        prefix = "Suggestion: "
        remaining = FINDING_SUMMARY_MAX - len(prefix)
        return prefix + suggestion[:remaining]
    return "Reference probe: matched passage found"


# ── Parse subagent output ─────────────────────────────────────────────


def parse_subagent_output(
    raw_text: str,
) -> Tuple[Optional[Dict[str, str]], Optional[str]]:
    """Parse helper-reference-probe subagent JSON output.

    Returns `(fields_dict, error)`:
      - On success: `({"matchedPassage": ..., "analysis": ..., "suggestion": ...}, None)`
        with fields clamped per czy `:355-357`.
      - On parse failure: `(None, error_message)`.

    The returned fields dict always has all three keys (defaulting to "").
    Clamping is applied here per czy `:355-357`.
    """
    unwrapped = unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return None, "subagent output is empty after unwrap"
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return None, f"subagent output is not valid JSON: {e}"
    if not isinstance(parsed, dict):
        return None, (
            f"subagent output root must be object (flat JSON), got "
            f"{type(parsed).__name__}. "
            f"(If E4 SKILL was mistakenly dispatched, it returns an array — wrong skill.)"
        )

    # Extract fields with "" fallback; strip + clamp per czy `:355-357`.
    matched_passage = str(parsed.get("matchedPassage") or "").strip()[:MATCHED_PASSAGE_MAX]
    analysis = str(parsed.get("analysis") or "").strip()[:ANALYSIS_MAX]
    suggestion = str(parsed.get("suggestion") or "").strip()[:SUGGESTION_MAX]

    return {
        "matchedPassage": matched_passage,
        "analysis": analysis,
        "suggestion": suggestion,
    }, None


# ── Core apply function ───────────────────────────────────────────────


def apply_extraction(
    backlog_path: Path,
    sub_problem_id: str,
    subagent_text: str,
    sandbox: Optional[Path] = None,
) -> Dict[str, Any]:
    """Apply reference probe extraction under flock + atomic write.
    Returns the milestone payload dict (caller emits it).

    Raises ValueError on validation failure (sub_problem_id missing).

    D-2 ACCUMULATE semantic: appends new finding_entry to
    `referenceprobe_findings[]`, max 10 entries (oldest dropped).

    NOTE: paper_body.txt check is done OUTSIDE this function (in main)
    so that skipped_no_reference path does not require a backlog lock.
    This mirrors the spec's design: early return before yaml mutation
    (czy `:319-321`).
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    started_ms = int(time.time() * 1000)

    fields, parse_err = parse_subagent_output(subagent_text)

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            raise ValueError(f"sub_problem_id not in sorry_items: {sub_problem_id}")

        stuck_rounds = int(item.get("stuck_rounds") or 0)

        if parse_err is not None:
            # parse_error: yaml unchanged (no write), milestone payload built.
            elapsed = int(time.time() * 1000) - started_ms
            return {
                "sub_problem_id": sub_problem_id,
                "stuck_rounds": stuck_rounds,
                "verdict": VERDICT_PARSE_ERROR,
                "matched_passage_len": 0,
                "suggestion_len": 0,
                "assembled_context_len": 0,
                "finding_summary": "",
                "findings_total": len(item.get("referenceprobe_findings") or []),
                "took_ms": elapsed,
                "parse_error": parse_err[:200],
            }

        assert fields is not None  # parse_err==None implies fields present

        matched_passage = fields["matchedPassage"]
        analysis = fields["analysis"]
        suggestion = fields["suggestion"]

        assembled_context = build_assembled_context(matched_passage, analysis, suggestion)
        finding_summary = build_finding_summary(analysis, suggestion)

        # Determine verdict before write
        if matched_passage or suggestion:
            verdict = VERDICT_PROBED
        else:
            verdict = VERDICT_PROBED_NO_CONTENT

        # Build finding entry
        finding_entry: Dict[str, Any] = {
            "assembledContext": assembled_context,
            "matchedPassage": matched_passage if matched_passage else None,
            "analysis": analysis if analysis else None,
            "suggestion": suggestion if suggestion else None,
            "finding_summary": finding_summary,
            "stuck_rounds": stuck_rounds,
            "timestamp": int(time.time() * 1000),
        }

        # D-2: append with max-10-cap (oldest dropped on overflow)
        # Locate the item again for mutation (locked_backlog yields a mutable dict)
        for it in items:
            if it.get("id") == sub_problem_id:
                findings = list(it.get("referenceprobe_findings") or [])
                findings.append(finding_entry)
                # Pop oldest if over cap
                while len(findings) > MAX_FINDINGS_PER_ITEM:
                    findings.pop(0)
                it["referenceprobe_findings"] = findings
                break

        atomic_write_yaml(backlog_path, data)

        # Read back the final findings length for milestone payload
        final_item = next((it for it in (data.get("sorry_items") or []) if it.get("id") == sub_problem_id), None)
        findings_total = len((final_item or {}).get("referenceprobe_findings") or [])

        elapsed = int(time.time() * 1000) - started_ms
        return {
            "sub_problem_id": sub_problem_id,
            "stuck_rounds": stuck_rounds,
            "verdict": verdict,
            "matched_passage_len": len(matched_passage),
            "suggestion_len": len(suggestion),
            "assembled_context_len": len(assembled_context),
            "finding_summary": finding_summary,
            "findings_total": findings_total,
            "took_ms": elapsed,
        }


# ── CLI helpers ───────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort
    (matches record_retreat / extract_references / extract_assumption
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
            f"[extract_reference_probe] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Spec §4 invariants asserted before emit.

      - verdict=`probed` → matched_passage_len + suggestion_len > 0
      - verdict=`probed_no_content` → matched_passage_len == 0 AND suggestion_len == 0
      - verdict=`skipped_no_reference` → assembled_context_len == 0 (no write)
      - assembled_context_len <= 3000 (always, enforced by build_assembled_context)
    """
    verdict = payload["verdict"]
    if verdict == VERDICT_PROBED:
        assert payload["matched_passage_len"] + payload["suggestion_len"] > 0, (
            f"probed verdict requires matched_passage_len + suggestion_len > 0, "
            f"got {payload['matched_passage_len']} + {payload['suggestion_len']}"
        )
    elif verdict == VERDICT_PROBED_NO_CONTENT:
        assert payload["matched_passage_len"] == 0 and payload["suggestion_len"] == 0, (
            f"probed_no_content verdict requires both lens == 0, "
            f"got {payload['matched_passage_len']} + {payload['suggestion_len']}"
        )
    elif verdict == VERDICT_SKIPPED_NO_REFERENCE:
        assert payload["assembled_context_len"] == 0, (
            f"skipped_no_reference requires assembled_context_len == 0, "
            f"got {payload['assembled_context_len']}"
        )
    assert payload["assembled_context_len"] <= ASSEMBLED_CONTEXT_MAX, (
        f"assembled_context_len {payload['assembled_context_len']} > {ASSEMBLED_CONTEXT_MAX}"
    )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--sub-problem-id",
        required=True,
        help="The sorry_item id whose referenceprobe_findings will be appended.",
    )
    p.add_argument(
        "--subagent-json-file",
        required=True,
        help="path to a file containing the helper-reference-probe subagent's JSON output",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone + paper_body.txt check")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()

    sandbox = Path(args.sandbox).resolve()
    backlog_path = Path(args.backlog_path).resolve()

    # Step 2 (spec §3.4): check paper_body.txt existence + length.
    # If absent or < 10 chars → emit skipped_no_reference; exit 0; NO yaml write.
    # Mirrors czy `:319-321` early return before LLM call.
    paper_body_path = sandbox / "paper_body.txt"
    if not paper_body_path.exists() or len(paper_body_path.read_text(encoding="utf-8", errors="replace")) < PAPER_BODY_MIN_CHARS:
        payload: Dict[str, Any] = {
            "sub_problem_id": args.sub_problem_id,
            "stuck_rounds": 0,
            "verdict": VERDICT_SKIPPED_NO_REFERENCE,
            "matched_passage_len": 0,
            "suggestion_len": 0,
            "assembled_context_len": 0,
            "finding_summary": "",
            "findings_total": 0,
            "took_ms": 0,
        }
        _validate_payload(payload)
        _emit(sandbox, "reference-probe-completed", payload)
        print(
            f"[extract_reference_probe] paper_body.txt absent or too short "
            f"(< {PAPER_BODY_MIN_CHARS} chars); verdict=skipped_no_reference"
        )
        return 0

    # Step 3: read subagent JSON file
    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[extract_reference_probe] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[extract_reference_probe] read failed: {e}", file=sys.stderr)
        return 4

    try:
        payload = apply_extraction(
            backlog_path=backlog_path,
            sub_problem_id=args.sub_problem_id,
            subagent_text=subagent_text,
            sandbox=sandbox,
        )
    except ValueError as e:
        print(f"[extract_reference_probe] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[extract_reference_probe] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[extract_reference_probe] IO failure: {e}", file=sys.stderr)
        return 4

    _validate_payload(payload)

    # parse_error: emit milestone and exit 2
    if payload["verdict"] == VERDICT_PARSE_ERROR:
        _emit(sandbox, "reference-probe-completed", payload)
        print(
            f"[extract_reference_probe] parse error: sub={args.sub_problem_id} "
            f"err={payload.get('parse_error', '(unknown)')!r}",
            file=sys.stderr,
        )
        return 2

    _emit(sandbox, "reference-probe-completed", payload)

    print(
        f"reference probe: sub={args.sub_problem_id} "
        f"verdict={payload['verdict']} "
        f"matched_passage_len={payload['matched_passage_len']} "
        f"suggestion_len={payload['suggestion_len']} "
        f"assembled_context_len={payload['assembled_context_len']} "
        f"findings_total={payload['findings_total']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

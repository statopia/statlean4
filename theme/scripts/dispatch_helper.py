#!/usr/bin/env python3
"""dispatch_helper.py — H4 stuck-recovery dispatch orchestrator.

Per `docs/H4_DISPATCH_HELPER_SPEC.md`. T2 single-script bundling:
ports czy's `recoverStuckNode` (`controlAgent.ts:517-559`) +
`HelperAgent.run` dispatch table (`helperAgent.ts:34-202`) into one
named script. Caller (prove-deep.md narrative) invokes once per stuck
sub-problem; script reads the agent-supplied marker file, walks the
CALL_ORDER table, dispatches per-marker helpers, emits one
`helper-dispatched` milestone summarising the outcome.

In MVP, only `need:assumption` wires to a real helper
(`extract_assumption.py`, H7). `need:websearch` (H5) and
`need:reference` (H6) emit `not-yet-ported` per-marker payloads. When
the deferred slices land, replace the placeholder branches in
`_dispatch_one_marker` with subprocess invocations of their scripts —
no dispatcher rework needed.

Workflow (per spec §3.3):
  1. Validate sub_problem_id exists in sorry_backlog.yaml (lock briefly to read).
  2. Read marker file from --marker-file.
  3. Parse marker line; allow-list filter; if empty → emit
     verdict=`no_helpers_needed`, exit 0.
  4. Normalize markers (collapse {websearch, reference, assumption} → [need:full]).
  5. CALL_ORDER lookup for sorted marker tuple.
  6. For each agent in dispatch list:
     - "websearch" → invoke extract_web_probe.py subprocess (H5);
       capture exit code; on non-zero record verdict=helper_script_failed
     - "reference" → placeholder: ported=False, reason=h6_deferred
     - "assumption" → invoke extract_assumption.py subprocess (H7);
       capture exit code; on non-zero record verdict=helper_script_failed
  7. Aggregate per-marker results.
  8. Emit single `helper-dispatched` milestone.
  9. Layer 1 invariant: dispatcher itself writes ZERO yaml. Helper
     scripts (H7) own their own yaml writes under their own flock.

Verdict taxonomy (spec §4):
  - "dispatched"            — at least one ported helper actually ran
  - "no_helpers_needed"     — marker decider returned empty list
  - "all_deferred"          — markers decided but all map to placeholders
  - "marker_decider_failed" — marker file empty/missing/no valid markers
  - "parse_error"           — sub_problem_id missing in yaml, or other
                              validation failure (exit code 2)

Exit codes:
  0 — milestone emitted (any verdict except parse_error)
  2 — validation / parse_error (sub_problem_id missing, marker file unreadable, etc.)

CLI:
    python3 theme/scripts/dispatch_helper.py \\
        --sub-problem-id <id> \\
        --marker-file /path/to/marker.txt \\
        --assumption-json-file /path/to/assumption.json \\
        --sandbox /path/to/sandbox \\
        [--backlog-path PATH]

`--assumption-json-file` is required ONLY when `need:assumption` (or
`need:full`) is one of the markers; otherwise it may be omitted (the
dispatcher records helper_script_failed for that branch with reason
`missing_assumption_json`).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
EXTRACT_ASSUMPTION = SCRIPTS_DIR / "extract_assumption.py"
EXTRACT_WEB_PROBE = SCRIPTS_DIR / "extract_web_probe.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import locked_backlog  # noqa: E402

# ── CALL_ORDER table — verbatim port from czy helperAgent.ts:34-41 ────

# Type: sorted-comma-joined-marker-tuple → ordered list of agent names.
# czy uses a Map<string, readonly (...)>; Python dict is the same shape.
# The lookup key is built by `_tuple_sort` (mirrors czy `tupleSort` :386).
CALL_ORDER: Dict[str, List[str]] = {
    "need:websearch": ["websearch"],
    "need:reference": ["reference"],
    "need:assumption": ["assumption"],
    "need:reference,need:websearch": ["websearch", "reference"],
    "need:assumption,need:websearch": ["websearch", "assumption"],
    "need:full": ["websearch", "reference", "assumption"],
}

VALID_MARKERS = frozenset(
    ("need:full", "need:assumption", "need:websearch", "need:reference")
)

# ── Verdict sentinels ────────────────────────────────────────────────

VERDICT_DISPATCHED = "dispatched"
VERDICT_NO_HELPERS = "no_helpers_needed"
VERDICT_ALL_DEFERRED = "all_deferred"
VERDICT_MARKER_FAILED = "marker_decider_failed"
VERDICT_PARSE_ERROR = "parse_error"

# Per-marker verdict sub-codes
PER_MARKER_EXTRACTED = "extracted"
PER_MARKER_NOT_YET_PORTED = "not-yet-ported"
PER_MARKER_HELPER_SCRIPT_FAILED = "helper_script_failed"

# Reasons for not-yet-ported
# H5 (websearch) is now wired via _dispatch_websearch; REASON_H5_DEFERRED kept
# as a deprecated alias for tests/callers that may still reference it
# (post H5 §8 code review S3.1 fixup acknowledged the constant became dead in
# production code paths but breaking the import is unnecessary churn).
REASON_H5_DEFERRED = "h5_deferred"  # deprecated; do not use in new code
REASON_H6_DEFERRED = "h6_deferred"


# ── Pure helpers (czy normalizeMarkers + tupleSort) ──────────────────


def normalize_markers(markers: List[str]) -> List[str]:
    """Collapse {websearch + reference + assumption} → [need:full].

    Verbatim port of czy `helperAgent.ts:371-384`. Note that
    `need:full` already in the set short-circuits to `[need:full]`.
    """
    s = set(markers)
    if "need:full" in s:
        return ["need:full"]
    if "need:websearch" in s and "need:reference" in s and "need:assumption" in s:
        return ["need:full"]
    return list(markers)


def tuple_sort(markers: List[str]) -> str:
    """Sort and comma-join markers for CALL_ORDER lookup.

    czy `helperAgent.ts:386-388` `[...markers].sort().join(",")`. JS
    `Array.sort()` defaults to lexicographic; Python `sorted()` matches
    on ASCII strings.
    """
    return ",".join(sorted(markers))


def parse_marker_file(text: str) -> List[str]:
    """Parse SKILL stdout: one line, comma-separated markers.

    czy `controlAgent.ts:377-380`:
        const text = extractTextContent(resp).trim();
        const markers = text.split(",").map((m) => m.trim()).filter(Boolean);

    Empty input (or whitespace-only) → []. Allow-list filter is applied
    by the caller after parsing so we can distinguish "no markers" from
    "all markers stripped" in the verdict.
    """
    text = (text or "").strip()
    if not text:
        return []
    return [m.strip() for m in text.split(",") if m.strip()]


def filter_to_allowlist(markers: List[str]) -> List[str]:
    """Strip markers not in VALID_MARKERS.

    czy `controlAgent.ts:380` `markers.filter((m) => valid.has(m))`.
    Order-preserving + duplicate-preserving (czy uses Array.filter
    which preserves both); de-dupe happens implicitly when normalize
    builds the Set later.
    """
    return [m for m in markers if m in VALID_MARKERS]


# ── Per-marker dispatch arms ─────────────────────────────────────────


def _dispatch_assumption(
    sub_problem_id: str,
    sandbox: Path,
    backlog_path: Path,
    assumption_json_file: Optional[Path],
) -> Dict[str, Any]:
    """Run extract_assumption.py subprocess (H7).

    Returns per-marker result dict matching spec §4 schema:
      { marker, agent, ported, verdict, subprocess_exit_code, ... }

    The subprocess writes its OWN milestone (`assumption-extracted`)
    and mutates yaml under its own flock. The dispatcher records only
    the exit code + verdict in this branch's result.
    """
    base: Dict[str, Any] = {
        "marker": "need:assumption",
        "agent": "assumption",
        "ported": True,
    }

    if assumption_json_file is None:
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": "missing_assumption_json",
        })
        return base

    if not assumption_json_file.is_file():
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": f"assumption_json_file_not_found:{assumption_json_file.name}",
        })
        return base

    cmd = [
        sys.executable,
        str(EXTRACT_ASSUMPTION),
        "--sub-problem-id", sub_problem_id,
        "--subagent-json-file", str(assumption_json_file),
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog_path),
    ]
    try:
        # Capture both stdout and stderr; we surface H7's summary line
        # via the per-marker-result payload, not by passing through.
        # Don't `check=True` — non-zero exit is a recordable outcome,
        # not an exception.
        completed = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired:
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": "timeout",
        })
        return base
    except (OSError, subprocess.SubprocessError) as e:
        # FileNotFoundError (extract_assumption.py absent), permission
        # denied, etc. Loud failure per CLAUDE.md Rule 9 anti-swallow:
        # we record the reason explicitly rather than silently returning
        # a generic verdict.
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": f"subprocess_error:{type(e).__name__}",
        })
        return base

    rc = completed.returncode
    base["subprocess_exit_code"] = rc
    if rc == 0:
        base["verdict"] = PER_MARKER_EXTRACTED
    else:
        base["verdict"] = PER_MARKER_HELPER_SCRIPT_FAILED
        # Capture a short stderr excerpt so the milestone tells us why.
        stderr_excerpt = (completed.stderr or "").strip()
        if stderr_excerpt:
            base["stderr_excerpt"] = stderr_excerpt[:400]
    return base


def _dispatch_websearch(
    sub_problem_id: str,
    sandbox: Path,
    backlog_path: Path,
    webprobe_json_file: Optional[Path],
) -> Dict[str, Any]:
    """Run extract_web_probe.py subprocess (H5).

    Returns per-marker result dict matching spec §4 schema.
    Mirrors _dispatch_assumption pattern for H7.
    """
    base: Dict[str, Any] = {
        "marker": "need:websearch",
        "agent": "websearch",
        "ported": True,
    }

    if webprobe_json_file is None:
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": "missing_webprobe_json",
        })
        return base

    if not webprobe_json_file.is_file():
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": f"webprobe_json_file_not_found:{webprobe_json_file.name}",
        })
        return base

    cmd = [
        sys.executable,
        str(EXTRACT_WEB_PROBE),
        "--sub-problem-id", sub_problem_id,
        "--subagent-json-file", str(webprobe_json_file),
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog_path),
    ]
    try:
        completed = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=120,
        )
    except subprocess.TimeoutExpired:
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": "timeout",
        })
        return base
    except (OSError, subprocess.SubprocessError) as e:
        base.update({
            "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
            "subprocess_exit_code": None,
            "reason": f"subprocess_error:{type(e).__name__}",
        })
        return base

    rc = completed.returncode
    base["subprocess_exit_code"] = rc
    if rc == 0:
        base["verdict"] = PER_MARKER_EXTRACTED
    else:
        base["verdict"] = PER_MARKER_HELPER_SCRIPT_FAILED
        stderr_excerpt = (completed.stderr or "").strip()
        if stderr_excerpt:
            base["stderr_excerpt"] = stderr_excerpt[:400]
    return base


def _placeholder_reference() -> Dict[str, Any]:
    return {
        "marker": "need:reference",
        "agent": "reference",
        "ported": False,
        "verdict": PER_MARKER_NOT_YET_PORTED,
        "reason": REASON_H6_DEFERRED,
    }


def _per_marker_results_from_call_order(
    markers_normalized: List[str],
    agents_to_call: List[str],
    sub_problem_id: str,
    sandbox: Path,
    backlog_path: Path,
    assumption_json_file: Optional[Path],
    webprobe_json_file: Optional[Path] = None,
) -> List[Dict[str, Any]]:
    """Walk the dispatch list, invoke per-agent arm, build per_marker_results.

    spec §4 invariant: `len(per_marker_results) == len(markers_decided after normalization)`.
    For `need:full` (collapses 3 markers → 1, fans out to 3 agents), the
    per-marker list mirrors the agents_to_call order (websearch, reference,
    assumption). The `marker` field on each entry shows the agent's
    ORIGINAL marker (before normalization) so consumers can trace which
    decision-marker each result corresponds to.

    For other CALL_ORDER entries (single or 2-marker), the per-marker
    list aligns 1:1 with markers_normalized.
    """
    results: List[Dict[str, Any]] = []
    for agent in agents_to_call:
        if agent == "assumption":
            results.append(_dispatch_assumption(
                sub_problem_id=sub_problem_id,
                sandbox=sandbox,
                backlog_path=backlog_path,
                assumption_json_file=assumption_json_file,
            ))
        elif agent == "websearch":
            # H5: real subprocess invocation (replaces _placeholder_websearch)
            results.append(_dispatch_websearch(
                sub_problem_id=sub_problem_id,
                sandbox=sandbox,
                backlog_path=backlog_path,
                webprobe_json_file=webprobe_json_file,
            ))
        elif agent == "reference":
            results.append(_placeholder_reference())
        else:
            # Unknown agent name — should not happen given CALL_ORDER is
            # a closed set, but guard anyway.
            results.append({
                "marker": f"unknown:{agent}",
                "agent": agent,
                "ported": False,
                "verdict": PER_MARKER_HELPER_SCRIPT_FAILED,
                "reason": f"unknown_agent:{agent}",
            })
    return results


def _classify_overall_verdict(
    markers_decided: List[str],
    per_marker_results: List[Dict[str, Any]],
) -> str:
    """Pick the overall verdict for the milestone.

    Rules per spec §4:
      - markers_decided == [] → no_helpers_needed
      - any per_marker_results[i].ported == True (i.e. helper subprocess
        was invoked) → dispatched. "Invoked, not succeeded" is the
        criterion — a helper that runs and exits non-zero still yields
        dispatched with the per-marker subprocess_exit_code recorded.
        (Spec §4 + H4 §8 code review S4.1 — corrected from earlier
        "AND verdict==extracted" comment which was inaccurate.)
      - all per_marker_results[i].ported == False (only placeholders)
        → all_deferred
      - all ported helpers ran but all failed (exit != 0) → still
        "dispatched" (the dispatcher fired the helpers; the failures
        are recorded per-marker). This matches spec §4 "at least one
        helper actually ran" semantic — invocation, not success.
    """
    assert markers_decided, "_classify_overall_verdict precondition: filtered marker list must be non-empty (empty/invalid paths exit before this call)"
    any_ported = any(r.get("ported") for r in per_marker_results)
    if any_ported:
        return VERDICT_DISPATCHED
    return VERDICT_ALL_DEFERRED


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Spec §4 invariants asserted before emit. T2 fail-loud."""
    verdict = payload["verdict"]
    markers_decided = payload["markers_decided"]
    agents_called = payload["agents_called"]
    per_marker_results = payload["per_marker_results"]

    # len(per_marker_results) == len(agents_called); each agent produced
    # exactly one entry. (Note: spec §4 says "len == markers_decided
    # after normalization"; agents_called IS the post-normalization
    # dispatch list, so this is the same invariant.)
    assert len(per_marker_results) == len(agents_called), (
        f"per_marker_results len {len(per_marker_results)} != "
        f"agents_called len {len(agents_called)}"
    )

    if verdict == VERDICT_DISPATCHED:
        assert agents_called, (
            f"dispatched verdict requires non-empty agents_called"
        )
        assert any(r.get("ported") for r in per_marker_results), (
            f"dispatched verdict requires at least one ported result"
        )
    elif verdict == VERDICT_NO_HELPERS:
        assert markers_decided == [], (
            f"no_helpers_needed requires markers_decided==[], got {markers_decided}"
        )
        assert agents_called == [], (
            f"no_helpers_needed requires agents_called==[], got {agents_called}"
        )
    elif verdict == VERDICT_ALL_DEFERRED:
        assert markers_decided, (
            f"all_deferred requires non-empty markers_decided"
        )
        assert all(not r.get("ported") for r in per_marker_results), (
            f"all_deferred requires every per_marker_result ported==False"
        )
    elif verdict == VERDICT_MARKER_FAILED:
        assert markers_decided == [], (
            f"marker_decider_failed requires markers_decided==[]"
        )
        assert agents_called == [], (
            f"marker_decider_failed requires agents_called==[]"
        )
    elif verdict == VERDICT_PARSE_ERROR:
        # parse_error is emitted from main() before/around helper invocation;
        # markers/agents are []
        assert agents_called == [], (
            f"parse_error requires agents_called==[]"
        )


# ── Sub-problem existence check ──────────────────────────────────────


def _validate_sub_problem_exists(
    backlog_path: Path,
    sub_problem_id: str,
) -> Tuple[bool, Optional[str]]:
    """Return (True, None) if sub_problem_id exists in sorry_items;
    else (False, error_message).

    Held briefly under flock so concurrent helper writes don't race
    the existence check (the helper itself locks again on its own —
    see L1.10 invariant test). Releasing the lock between this check
    and the helper subprocess is intentional: H7 needs to re-acquire.
    """
    if not backlog_path.exists():
        return False, f"backlog not found: {backlog_path}"
    try:
        with locked_backlog(backlog_path) as data:
            items = data.get("sorry_items") or []
            for it in items:
                if it.get("id") == sub_problem_id:
                    return True, None
            return False, f"sub_problem_id not in sorry_items: {sub_problem_id}"
    except yaml.YAMLError as e:
        return False, f"yaml parse failed: {e}"
    except OSError as e:
        return False, f"backlog read failed: {e}"


# ── Milestone emit ───────────────────────────────────────────────────


def _emit_milestone(sandbox: Path, payload: Dict[str, Any]) -> None:
    """Best-effort emit of helper-dispatched milestone.

    Mirrors `extract_assumption.py:_emit` pattern (record_retreat /
    extract_references / verify_citation precedent). Logs but doesn't
    abort on emit_event failure — the dispatcher's success or failure
    is signalled via exit code, milestone is observability.
    """
    try:
        subprocess.run(
            [
                sys.executable, str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", "helper-dispatched",
                "--details", json.dumps(payload, ensure_ascii=False),
            ],
            check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(
            f"[dispatch_helper] emit_event helper-dispatched failed: {e}",
            file=sys.stderr,
        )


# ── CLI ──────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--sub-problem-id",
        required=True,
        help="The sorry_item id whose stuck recovery is being dispatched.",
    )
    p.add_argument(
        "--marker-file",
        required=True,
        help="Path to file containing the decide-helper-markers SKILL stdout.",
    )
    p.add_argument(
        "--assumption-json-file",
        required=False,
        default=None,
        help=(
            "Path to file containing helper-assumption Task subagent JSON output. "
            "Required when need:assumption (or need:full) is one of the decided markers."
        ),
    )
    p.add_argument(
        "--webprobe-json-file",
        required=False,
        default=None,
        help=(
            "Path to file containing helper-web-probe Task subagent JSON output. "
            "Required when need:websearch (or need:full) is one of the decided markers. "
            "H5 slice; mirrors --assumption-json-file pattern."
        ),
    )
    p.add_argument(
        "--sandbox",
        required=True,
        help="Per-job sandbox dir (for emit_event milestone).",
    )
    p.add_argument(
        "--backlog-path",
        default=str(BACKLOG_DEFAULT),
        help="Path to sorry_backlog.yaml (default: theme/input/sorry_backlog.yaml).",
    )
    p.add_argument(
        "--stuck-rounds",
        type=int,
        default=0,
        help="Current stuck_rounds value for the sorry (informational; flows into milestone payload).",
    )
    return p.parse_args()


def _build_milestone_payload(
    sub_problem_id: str,
    stuck_rounds: int,
    markers_decided: List[str],
    markers_normalized: List[str],
    agents_called: List[str],
    per_marker_results: List[Dict[str, Any]],
    verdict: str,
    started_ms: int,
    parse_error: Optional[str] = None,
) -> Dict[str, Any]:
    payload: Dict[str, Any] = {
        "sub_problem_id": sub_problem_id,
        "stuck_rounds": stuck_rounds,
        "markers_decided": list(markers_decided),
        "markers_normalized": list(markers_normalized),
        "agents_called": list(agents_called),
        "per_marker_results": list(per_marker_results),
        "verdict": verdict,
        "took_ms": int(time.time() * 1000) - started_ms,
    }
    if parse_error is not None:
        payload["parse_error"] = parse_error[:200]
    return payload


def main() -> int:
    args = _parse_args()
    started_ms = int(time.time() * 1000)

    sandbox = Path(args.sandbox).resolve()
    backlog_path = Path(args.backlog_path).resolve()

    # Step 1: validate sub_problem_id exists in yaml
    ok, err = _validate_sub_problem_exists(backlog_path, args.sub_problem_id)
    if not ok:
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=[],
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_PARSE_ERROR,
            started_ms=started_ms,
            parse_error=err,
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(f"[dispatch_helper] {err}", file=sys.stderr)
        return 2

    # Step 2: read marker file
    marker_path = Path(args.marker_file).resolve()
    if not marker_path.is_file():
        err = f"marker file not found: {marker_path}"
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=[],
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_PARSE_ERROR,
            started_ms=started_ms,
            parse_error=err,
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(f"[dispatch_helper] {err}", file=sys.stderr)
        return 2

    try:
        marker_text = marker_path.read_text(encoding="utf-8")
    except OSError as e:
        err = f"marker file read failed: {e}"
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=[],
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_PARSE_ERROR,
            started_ms=started_ms,
            parse_error=err,
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(f"[dispatch_helper] {err}", file=sys.stderr)
        return 2

    # Step 3: parse marker line, allow-list filter
    raw_markers = parse_marker_file(marker_text)
    filtered = filter_to_allowlist(raw_markers)

    if not raw_markers:
        # Empty marker file → "no helpers needed" (czy parity: empty
        # response from `_llmDecideHelper` after filter is the
        # "skip helper" signal; here we elevate empty before-filter as
        # the same condition).
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=[],
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_NO_HELPERS,
            started_ms=started_ms,
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(f"[dispatch_helper] no markers in marker file; verdict=no_helpers_needed")
        return 0

    if not filtered:
        # All markers were invalid (allow-list stripped everything).
        # czy parity: `_llmDecideHelper` `:381-383` throws on empty
        # filtered list → caller (this dispatcher) records as marker
        # decider failure.
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=[],
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_MARKER_FAILED,
            started_ms=started_ms,
            parse_error=f"no valid markers after allow-list filter: raw={raw_markers}",
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(
            f"[dispatch_helper] marker decider produced no valid markers "
            f"(raw={raw_markers}); verdict=marker_decider_failed"
        )
        return 0

    # Step 4: normalize (collapse 3-marker set to need:full)
    markers_normalized = normalize_markers(filtered)

    # Step 5: CALL_ORDER lookup
    key = tuple_sort(markers_normalized)
    agents_to_call = list(CALL_ORDER.get(key, []))

    if not agents_to_call:
        # No matching CALL_ORDER entry — valid markers but unmapped
        # combination (e.g. `need:assumption,need:reference` without
        # websearch). czy `helperAgent.ts:82` falls back to []. We record
        # marker_decider_failed so observability can flag the unmapped combination.
        payload = _build_milestone_payload(
            sub_problem_id=args.sub_problem_id,
            stuck_rounds=args.stuck_rounds,
            markers_decided=[],
            markers_normalized=markers_normalized,
            agents_called=[],
            per_marker_results=[],
            verdict=VERDICT_MARKER_FAILED,
            started_ms=started_ms,
            parse_error=f"no CALL_ORDER entry for normalized markers: {markers_normalized}",
        )
        _validate_payload(payload)
        _emit_milestone(sandbox, payload)
        print(
            f"[dispatch_helper] no CALL_ORDER entry for {markers_normalized}; "
            f"verdict=marker_decider_failed"
        )
        return 0

    # Step 6: dispatch per-agent
    assumption_json_file: Optional[Path] = None
    if args.assumption_json_file:
        assumption_json_file = Path(args.assumption_json_file).resolve()

    webprobe_json_file: Optional[Path] = None
    if args.webprobe_json_file:
        webprobe_json_file = Path(args.webprobe_json_file).resolve()

    per_marker_results = _per_marker_results_from_call_order(
        markers_normalized=markers_normalized,
        agents_to_call=agents_to_call,
        sub_problem_id=args.sub_problem_id,
        sandbox=sandbox,
        backlog_path=backlog_path,
        assumption_json_file=assumption_json_file,
        webprobe_json_file=webprobe_json_file,
    )

    # Step 7: classify overall verdict
    verdict = _classify_overall_verdict(filtered, per_marker_results)

    # Step 8: emit milestone
    payload = _build_milestone_payload(
        sub_problem_id=args.sub_problem_id,
        stuck_rounds=args.stuck_rounds,
        markers_decided=filtered,
        markers_normalized=markers_normalized,
        agents_called=agents_to_call,
        per_marker_results=per_marker_results,
        verdict=verdict,
        started_ms=started_ms,
    )
    _validate_payload(payload)
    _emit_milestone(sandbox, payload)

    # Short stdout summary so the agent / log readers see the outcome
    print(
        f"[dispatch_helper] sub={args.sub_problem_id} verdict={verdict} "
        f"markers={filtered} agents={agents_to_call} "
        f"took_ms={payload['took_ms']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

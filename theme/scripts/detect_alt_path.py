#!/usr/bin/env python3
"""detect_alt_path.py — bundle the side-effect chain for alignment-phase
alternative proof path detection (H2 slice; per docs/H2_DETECT_ALT_PATH_SPEC.md).

Verbatim port of czy's `detectAlternativePath` method
(`helperReferenceSubAgent.ts:244-296`) + caller integration
(`helperAgent.ts:303-317`) into the SDK-bridge narrative-pipe pattern.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. The agent
narrative dispatches the `detect-alt-path` Task subagent (T3 — agent
decides), captures stdout JSON to a file, then invokes THIS script
with --subagent-json-file. This script enforces all sub-steps atomically:
  - 3-gate defensive check (G1 reference results, G2 paper body len, G3 cache)
  - JSON parse + markdown-fence strip (mirrors czy `safeParseJson:475-484`)
  - 9-field validation (3 bool + 5 str + 1 list[str])
  - Atomic yaml write (alternative_path field on targeted parent only)
  - Single `alt-path-detected` milestone emit

D-2 wire choice: `alternative_path = null` for "no alternative" (czy returns
`emptyAlternative()` full-zeroed struct; SDK-bridge prefers null). Both
encode "no alternative detected" — same semantic, cleaner yaml wire.

D-3 first-detection-wins: if parent already has `alternative_path` non-null,
emit milestone verdict=`cached` and exit 0 without re-dispatching.
Mirrors czy `proofLoop.ts:886` `!cachedAltPath` guard.

D-4 NL string clamps (+1 deviation from czy, documented): czy relies on
`max_tokens: 1500` to bound total output; H2 adds explicit per-field
clamps as defense against pathological LLM output:
  - NL string fields (description, efficiency_reason, current_path_coverage,
    alternative_path_coverage, approach_name): clamped to 800 chars each
  - key_tools[i]: clamped to 200 chars each
Precedent: E4 clamps assessment to 1000 chars; H7 clamps hints to 400 chars;
E11 clamps citation_excerpt to 300 chars; H4 clamps blocker to 200 chars;
slice 03 clamps assessment to 1000 chars.

Layer 1 invariant: mutates ONLY `alternative_path` on the targeted parent
sorry_item. Locked theorem signature / file / line / theorem / parent_id /
children / state / history_log / coverage_state / references / done_reason /
citation_verified / informal_round / coverage_stable / assumption_hints /
assumption_analysis / detailed_proof_plan / direct_assembly / proof_sketch
are untouched. Test L1.10 enforces.

Exit codes:
  0  — success (all verdicts including cached / no_alternative / no_reference_results
       / no_reference_text exit 0; only structural failures exit non-zero)
  2  — validation error (parent not found, no children, malformed input)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/detect_alt_path.py \\
        --parent-id <node id> \\
        --subagent-json-file /path/to/_alt_path_<parent_id>_<ts>.json \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--paper-body-path /path/to/paper_body.txt] \\
        [--backlog-path PATH] \\
        [--bypass-skill --gate-only] (for testing: skips reading subagent json)

Note: --bypass-skill --gate-only is for L1 gate tests only. When set,
the script performs gate checks but skips the SKILL JSON read entirely.
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


# ── Constants (czy parity) ────────────────────────────────────────────

# czy `:259` max_tokens: 1500 (implicit NL output bound). H2 adds
# explicit per-field clamps (D-4 +1 deviation, documented in header).
NL_FIELD_MAX_CHARS = 800    # per NL string field (D-4)
KEY_TOOL_MAX_CHARS = 200    # per key_tools[i] (D-4)

# czy `:250-252` minimum reference text length (hasUsableRef gate G2)
MIN_PAPER_BODY_CHARS = 10   # czy parity

# Verdicts for the alt-path-detected milestone (7 discriminator values)
VERDICT_DETECTED = "detected"
VERDICT_NO_ALTERNATIVE = "no_alternative"
VERDICT_CACHED = "cached"
VERDICT_NO_REFERENCE_RESULTS = "no_reference_results"
VERDICT_NO_REFERENCE_TEXT = "no_reference_text"
VERDICT_PARSE_ERROR = "parse_error"
VERDICT_SKILL_DISPATCH_FAILED = "skill_dispatch_failed"


# ── JSON fence strip (mirrors czy `safeParseJson:475-484`) ────────────


_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def _unwrap_fenced_json(s: str) -> str:
    """Strip markdown code fences. Mirrors czy `:347-350` / `safeParseJson`."""
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── String clamps (D-4 +1 deviation — zie header) ─────────────────────


def _clamp_str(s: str, max_chars: int) -> str:
    """Clamp string to max_chars, appending ellipsis if truncated."""
    if len(s) <= max_chars:
        return s
    return s[:max_chars - 1] + "…"


def _truncate(s: Optional[str], n: int) -> Optional[str]:
    """Truncate for milestone excerpts. Returns None for empty/None input."""
    if not s:
        return None
    return s if len(s) <= n else s[:n - 1] + "…"


# ── Parse SKILL JSON output ────────────────────────────────────────────


def parse_skill_output(raw_text: str) -> Tuple[bool, Dict[str, Any], Optional[str]]:
    """Parse detect-alt-path SKILL JSON output.

    Returns (ok, parsed_dict, error_msg):
      - On success: (True, validated_dict, None)
      - On parse failure: (False, {}, error_msg)

    Field validation mirrors czy `:283-291`:
      - hasAlternative, isMoreEfficient, recommendSwitch → bool coerce
      - approachName, description, currentPathCoverage,
        alternativePathCoverage, efficiencyReason → str coerce + clamp 800
      - keyTools → list[str], fallback [] on non-list; each item clamped 200
    """
    unwrapped = _unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return False, {}, "subagent output is empty after unwrap"

    try:
        raw = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return False, {}, f"JSON decode failed: {e}"

    if not isinstance(raw, dict):
        return False, {}, f"root must be object, got {type(raw).__name__}"

    # czy `:283-291` field coercions
    result: Dict[str, Any] = {
        "hasAlternative": bool(raw.get("hasAlternative", False)),
        "approachName": _clamp_str(str(raw.get("approachName") or ""), NL_FIELD_MAX_CHARS),
        "description": _clamp_str(str(raw.get("description") or ""), NL_FIELD_MAX_CHARS),
        "keyTools": (
            [_clamp_str(str(t), KEY_TOOL_MAX_CHARS) for t in raw["keyTools"]
             if t is not None]
            if isinstance(raw.get("keyTools"), list)
            else []
        ),
        "currentPathCoverage": _clamp_str(str(raw.get("currentPathCoverage") or ""), NL_FIELD_MAX_CHARS),
        "alternativePathCoverage": _clamp_str(str(raw.get("alternativePathCoverage") or ""), NL_FIELD_MAX_CHARS),
        "isMoreEfficient": bool(raw.get("isMoreEfficient", False)),
        "efficiencyReason": _clamp_str(str(raw.get("efficiencyReason") or ""), NL_FIELD_MAX_CHARS),
        "recommendSwitch": bool(raw.get("recommendSwitch", False)),
    }
    return True, result, None


# ── Gate checks (G1, G2, G3) ──────────────────────────────────────────


def check_gate_g1(parent_children: List[str], items: List[Dict[str, Any]]) -> bool:
    """G1: czy parity per `helperAgent.ts:304` `referenceResults.length > 0`.

    czy's gate fires when E4 produced ≥1 result for the parent's
    sub-problems, REGARDLESS of whether the per-sub-problem
    assessment text is empty. A child classified by E4 as
    `coverage: "no_coverage"` with `coverage_assessment: ""` still
    counts (E4 ran on it; coverageResults entry exists).

    SDK-bridge equivalent: `≥1 child has a non-empty references[]
    list`. The presence of any reference entry indicates E4 has
    processed that child. The previous implementation gated on
    "non-empty assessment text" — H2 §8 code review S2.2 caught
    that as drift from czy parity (a no-coverage child with empty
    assessment was wrongly excluded).
    """
    by_id = {it.get("id"): it for it in items}
    for child_id in parent_children:
        child = by_id.get(child_id)
        if child is None:
            continue
        if child.get("references"):
            return True
    return False


def check_gate_g2(paper_body: str) -> bool:
    """G2: paper_body.strip() length >= MIN_PAPER_BODY_CHARS (10).

    Mirrors czy `:250-252` `!referenceText || referenceText.trim().length < 10`.
    """
    return len(paper_body.strip()) >= MIN_PAPER_BODY_CHARS


def check_gate_g3(parent: Dict[str, Any]) -> bool:
    """G3 (cache miss): parent.alternative_path is null/None.

    Mirrors czy `proofLoop.ts:886` `!cachedAltPath` first-detection-wins.
    Returns True when NOT cached (safe to proceed), False when cached.
    """
    return parent.get("alternative_path") is None


# ── Core apply ────────────────────────────────────────────────────────


def apply_alt_path_detection(
    backlog_path: Path,
    parent_id: str,
    subagent_text: Optional[str],
    paper_body: str,
    *,
    gate_only: bool = False,
) -> Dict[str, Any]:
    """Apply alt-path detection under flock + atomic write.

    Returns the milestone payload dict (caller emits it).
    Raises ValueError on validation failure (parent missing, no children).

    gate_only=True: perform only gate checks, skip SKILL JSON processing.
    Used in L1 gate tests (L1.8, L1.9, L1.11).
    """
    started_ms = int(time.time() * 1000)

    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        current_children: List[str] = list(parent.get("children") or [])
        if not current_children:
            raise ValueError(
                f"parent {parent_id} has no children; "
                "alt-path detection runs on parents only"
            )

        # Validate state precondition: parent should be INACTIVE_WAIT
        # (alignment-loop precondition, per slice 03 parity).
        # Warn but don't abort — defensive, alignment loop may call
        # before state transition in edge cases.
        parent_state = parent.get("state", "")
        if parent_state not in ("INACTIVE_WAIT", "INITIALIZED"):
            print(
                f"[detect_alt_path] WARNING: parent {parent_id} state={parent_state!r} "
                f"(expected INACTIVE_WAIT); proceeding defensively",
                file=sys.stderr,
            )

        elapsed_fn = lambda: int(time.time() * 1000) - started_ms  # noqa: E731

        # ── G3: first-detection-wins cache check (czy :886) ───────────
        if not check_gate_g3(parent):
            # Already cached — read existing value for milestone
            cached_val = parent.get("alternative_path")
            cached_has_alt = bool(
                cached_val.get("has_alternative") if isinstance(cached_val, dict) else False
            )
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_CACHED,
                "has_alternative": cached_has_alt,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        # ── G2: paper body length check (czy :250-252) ────────────────
        if not check_gate_g2(paper_body):
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_NO_REFERENCE_TEXT,
                "has_alternative": None,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        # ── G1: reference results presence check (czy helperAgent.ts:304) ──
        if not check_gate_g1(current_children, items):
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_NO_REFERENCE_RESULTS,
                "has_alternative": None,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        if gate_only:
            # All gates passed but we're in gate-only mode (tests only)
            return {
                "parent_id": parent_id,
                "verdict": "_gates_passed",
                "has_alternative": None,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        # ── SKILL JSON missing (skill_dispatch_failed) ─────────────────
        if subagent_text is None:
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_SKILL_DISPATCH_FAILED,
                "has_alternative": None,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        # ── Parse SKILL JSON ───────────────────────────────────────────
        ok, parsed, parse_err = parse_skill_output(subagent_text)
        if not ok:
            # parse_error: yaml unchanged (czy :293-295 catch-all)
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_PARSE_ERROR,
                "has_alternative": None,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
                "parse_error": (parse_err or "")[:200],
            }

        # ── Step 7: hasAlternative=false → write null (D-2 wire choice) ──
        has_alternative = parsed["hasAlternative"]
        if not has_alternative:
            # Write alternative_path=null on parent (D-2: null wire for "no alternative")
            for it in items:
                if it.get("id") == parent_id:
                    it["alternative_path"] = None
                    break
            atomic_write_yaml(backlog_path, data)
            return {
                "parent_id": parent_id,
                "verdict": VERDICT_NO_ALTERNATIVE,
                "has_alternative": False,
                "recommend_switch": False,
                "approach_name_excerpt": None,
                "description_excerpt": None,
                "key_tools_count": 0,
                "current_path_coverage_excerpt": None,
                "alternative_path_coverage_excerpt": None,
                "took_ms": elapsed_fn(),
            }

        # ── Step 9-10: hasAlternative=true → build and write object ────
        alt_path_obj = {
            "has_alternative": True,
            "approach_name": parsed["approachName"],
            "description": parsed["description"],
            "key_tools": parsed["keyTools"],
            "current_path_coverage": parsed["currentPathCoverage"],
            "alternative_path_coverage": parsed["alternativePathCoverage"],
            "is_more_efficient": parsed["isMoreEfficient"],
            "efficiency_reason": parsed["efficiencyReason"],
            "recommend_switch": parsed["recommendSwitch"],
        }

        for it in items:
            if it.get("id") == parent_id:
                it["alternative_path"] = alt_path_obj
                break

        atomic_write_yaml(backlog_path, data)

        elapsed = elapsed_fn()
        return {
            "parent_id": parent_id,
            "verdict": VERDICT_DETECTED,
            "has_alternative": True,
            "recommend_switch": parsed["recommendSwitch"],
            "approach_name_excerpt": _truncate(parsed["approachName"], 80),
            "description_excerpt": _truncate(parsed["description"], 200),
            "key_tools_count": len(parsed["keyTools"]),
            "current_path_coverage_excerpt": _truncate(parsed["currentPathCoverage"], 200),
            "alternative_path_coverage_excerpt": _truncate(parsed["alternativePathCoverage"], 200),
            "took_ms": elapsed,
        }


# ── Payload validation (spec §4 invariants) ────────────────────────────


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Assert spec §4 milestone payload invariants before emit.

    Catches bugs in apply_alt_path_detection before they reach
    events.jsonl. Assertion failure is a code bug, not a user error.
    """
    verdict = payload["verdict"]
    if verdict == VERDICT_DETECTED:
        assert payload["has_alternative"] is True, (
            f"detected verdict requires has_alternative=True"
        )
        assert payload["approach_name_excerpt"] is not None, (
            "detected verdict requires non-null approach_name_excerpt"
        )
        assert payload["description_excerpt"] is not None, (
            "detected verdict requires non-null description_excerpt"
        )
    elif verdict == VERDICT_NO_ALTERNATIVE:
        assert payload["has_alternative"] is False, (
            "no_alternative verdict requires has_alternative=False"
        )
        assert payload["approach_name_excerpt"] is None, (
            "no_alternative verdict requires null approach_name_excerpt"
        )
        assert payload["recommend_switch"] is False, (
            "no_alternative verdict requires recommend_switch=False"
        )
    elif verdict in (
        VERDICT_PARSE_ERROR, VERDICT_SKILL_DISPATCH_FAILED,
        VERDICT_NO_REFERENCE_RESULTS, VERDICT_NO_REFERENCE_TEXT,
    ):
        assert payload["has_alternative"] is None, (
            f"{verdict} verdict requires has_alternative=None"
        )
        assert payload["recommend_switch"] is False, (
            f"{verdict} verdict requires recommend_switch=False"
        )
        # All excerpt fields must be None for error verdicts
        for field in ("approach_name_excerpt", "description_excerpt",
                      "current_path_coverage_excerpt", "alternative_path_coverage_excerpt"):
            assert payload[field] is None, (
                f"{verdict} verdict requires null {field}"
            )
    # cached verdict: has_alternative may be True (existing cached value)
    # or False; approach_name_excerpt is None (we don't re-emit cached content)
    elif verdict == VERDICT_CACHED:
        assert payload["approach_name_excerpt"] is None, (
            "cached verdict requires null approach_name_excerpt (no re-emit of cached content)"
        )


# ── Emit helper ───────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort.
    Mirrors extract_assumption / record_retreat pattern.
    """
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
            f"[detect_alt_path] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


# ── CLI ───────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--subagent-json-file",
        required=False,
        default=None,
        help=(
            "path to a file containing the detect-alt-path subagent's JSON output "
            "(required unless --bypass-skill is set)"
        ),
    )
    p.add_argument(
        "--sandbox",
        required=True,
        help="Absolute path to the job sandbox for emit_event milestone.",
    )
    p.add_argument(
        "--paper-body-path",
        default=None,
        help=(
            "Path to paper_body.txt (G2 check). "
            "Defaults to $SANDBOX/paper_body.txt if not supplied."
        ),
    )
    p.add_argument(
        "--backlog-path",
        default=str(BACKLOG_DEFAULT),
        help="Path to sorry_backlog.yaml (default: theme/input/sorry_backlog.yaml)",
    )
    p.add_argument(
        "--bypass-skill",
        action="store_true",
        help="Skip reading subagent JSON file (gate-only mode for tests).",
    )
    p.add_argument(
        "--gate-only",
        action="store_true",
        help=(
            "Combined with --bypass-skill: run gate checks only, "
            "no yaml write, emit gate-check milestone. For L1 tests."
        ),
    )
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    # ── Resolve paper body (G2 input) ──────────────────────────────────
    if args.paper_body_path:
        paper_body_path = Path(args.paper_body_path).resolve()
    else:
        paper_body_path = sandbox / "paper_body.txt"

    if paper_body_path.exists():
        try:
            paper_body = paper_body_path.read_text(encoding="utf-8")
        except OSError as e:
            print(f"[detect_alt_path] read paper_body failed: {e}", file=sys.stderr)
            paper_body = ""
    else:
        paper_body = ""

    # ── Resolve subagent JSON ──────────────────────────────────────────
    gate_only = args.bypass_skill and args.gate_only
    bypass_skill = args.bypass_skill

    subagent_text: Optional[str] = None
    if not bypass_skill:
        if not args.subagent_json_file:
            print(
                "[detect_alt_path] --subagent-json-file is required unless --bypass-skill",
                file=sys.stderr,
            )
            return 2

        json_path = Path(args.subagent_json_file).resolve()
        if not json_path.is_file():
            print(
                f"[detect_alt_path] subagent json file not found: {json_path}",
                file=sys.stderr,
            )
            # skill_dispatch_failed: file missing means agent didn't dispatch SKILL
            # We still need to emit the milestone — call apply with None
            subagent_text = None
            # Fall through to apply_alt_path_detection with None
        else:
            try:
                subagent_text = json_path.read_text(encoding="utf-8")
            except OSError as e:
                print(f"[detect_alt_path] read subagent json failed: {e}", file=sys.stderr)
                return 4

    try:
        payload = apply_alt_path_detection(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            subagent_text=subagent_text,
            paper_body=paper_body,
            gate_only=gate_only,
        )
    except ValueError as e:
        print(f"[detect_alt_path] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[detect_alt_path] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[detect_alt_path] IO failure: {e}", file=sys.stderr)
        return 4

    # ── Validate payload invariants before emit ────────────────────────
    if payload.get("verdict") != "_gates_passed":
        _validate_payload(payload)
        _emit(sandbox, "alt-path-detected", payload)

    verdict = payload.get("verdict", "unknown")
    has_alt = payload.get("has_alternative")
    recommend = payload.get("recommend_switch", False)
    excerpt = payload.get("approach_name_excerpt", "")

    print(
        f"alt-path-detection: parent={args.parent_id} "
        f"verdict={verdict} "
        f"has_alternative={has_alt} "
        f"recommend_switch={recommend}"
        + (f" approach={excerpt!r}" if excerpt else "")
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

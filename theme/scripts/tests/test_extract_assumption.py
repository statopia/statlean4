"""H7 L1 unit tests for extract_assumption.py.

Coverage matrix per `docs/H7_HELPER_ASSUMPTION_SPEC.md` §7.1:
  L1.1 happy path: 2 missingAssumptions + analysis → assumption_hints=[2]
       + assumption_analysis set + milestone verdict=`extracted`
  L1.2 markdown-fenced JSON unwraps
  L1.3 malformed JSON → verdict=`parse_error`, yaml unchanged
  L1.4 non-object root (e.g. []) → verdict=`parse_error`
  L1.5 missing `analysis` field → analysis defaults to ""; verdict still
       `extracted` if missingAssumptions non-empty
  L1.6 OVERWRITE existing 3-hint list with 2-hint new list → final
       length 2 (NOT 5; NOT append). previous_hint_count=3.
  L1.7 Layer 1 invariant: protected fields byte-identical post-write
  L1.8 empty new list overwrites non-empty existing → final length 0;
       verdict=`empty`
  L1.9 sub_problem_id missing in yaml → exit 2 (validation)
  L1.10 flock concurrency: second invocation FULLY REPLACES first
        (second-wins overwrite per D-1)

All tests use mock LLM JSON strings; no live LLM calls.
"""
from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from extract_assumption import (  # noqa: E402
    apply_extraction,
    parse_subagent_output,
    unwrap_fenced_json,
    VERDICT_EMPTY,
    VERDICT_EXTRACTED,
    VERDICT_PARSE_ERROR,
)
from _assumption_types import (  # noqa: E402
    ASSUMPTION_ANALYSIS_MAX_CHARS,
    ASSUMPTION_HINT_MAX_CHARS,
    AssumptionDiagnoseResult,
    build_finding_summary,
    trim_analysis,
    trim_hint,
)
from _history_log_types import migrate_item_v1_to_v2  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_assumption.py"


# ── Fixture: backlog with one stuck sub-problem ──────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _one_stuck_subproblem_backlog() -> List[Dict[str, Any]]:
    """Pre-migrated v2 row representing a stuck sub-problem. All v2
    fields populated so Layer 1 invariant tests have something to
    enforce against."""
    return [
        {
            "id": "sub.s1", "file": "X.lean", "line": 5,
            "theorem": "stuck_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 3,
            "references": [], "coverage_state": "needs_proof",
            "attempts": 0, "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "assumption_hints": [], "assumption_analysis": "",
        },
    ]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _make_backlog(_one_stuck_subproblem_backlog(), p)
    return p


# ── Fence unwrap helpers (companion to L1.2) ─────────────────────────


def test_unwrap_fenced_json_strips_json_fence() -> None:
    raw = "```json\n{\"a\": 1}\n```"
    assert unwrap_fenced_json(raw).strip() == '{"a": 1}'


def test_unwrap_fenced_json_strips_bare_fence() -> None:
    raw = "```\n{\"a\": 1}\n```"
    assert unwrap_fenced_json(raw).strip() == '{"a": 1}'


def test_unwrap_fenced_json_passes_through_when_no_fence() -> None:
    assert unwrap_fenced_json('{"a": 1}') == '{"a": 1}'


# ── L1.1 happy path ──────────────────────────────────────────────────


def test_l1_1_happy_path_two_assumptions_plus_analysis(
    backlog: Path, sandbox: Path
) -> None:
    """2 missingAssumptions + analysis → assumption_hints=[2 items],
    assumption_analysis set, milestone verdict=`extracted`,
    added_hints_count=2."""
    subagent_json = json.dumps({
        "missingAssumptions": [
            "the function f is Lipschitz continuous on a compact set K",
            "the random variables X_i are pairwise independent",
        ],
        "analysis": "Without Lipschitz continuity, the modulus-of-continuity step cannot bound |f(x)-f(y)|.",
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)

    assert payload["verdict"] == VERDICT_EXTRACTED
    assert payload["added_hints_count"] == 2
    assert payload["previous_hint_count"] == 0
    assert payload["current_hint_count"] == 2
    assert payload["excerpt"] is not None
    assert "Missing:" in payload["excerpt"]
    assert payload["analysis_excerpt"] is not None

    # Round-trip — yaml should reflect the writes
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    s1 = by_id["sub.s1"]
    assert s1["assumption_hints"] == [
        "the function f is Lipschitz continuous on a compact set K",
        "the random variables X_i are pairwise independent",
    ]
    assert "Lipschitz" in s1["assumption_analysis"]


# ── L1.2 markdown fence ──────────────────────────────────────────────


def test_l1_2_markdown_fenced_json_unwraps(
    backlog: Path, sandbox: Path
) -> None:
    """LLM output wrapped in ```json ... ``` fence still parses."""
    fenced = "```json\n" + json.dumps({
        "missingAssumptions": ["X is integrable"],
        "analysis": "X integrability needed for finite expectation.",
    }) + "\n```"
    payload = apply_extraction(backlog, "sub.s1", fenced)
    assert payload["verdict"] == VERDICT_EXTRACTED
    assert payload["added_hints_count"] == 1

    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == ["X is integrable"]


# ── L1.3 malformed JSON ──────────────────────────────────────────────


def test_l1_3_malformed_json_yields_parse_error_verdict(
    backlog: Path
) -> None:
    """Malformed JSON → verdict=`parse_error`; yaml unchanged."""
    pre_data = yaml.safe_load(backlog.read_text())
    payload = apply_extraction(backlog, "sub.s1", "not json at all {[}")
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert payload["added_hints_count"] == 0
    assert payload["excerpt"] is None
    assert payload["analysis_excerpt"] is None
    assert "parse_error" in payload  # error-detail field present

    # yaml unchanged — assumption_hints / assumption_analysis preserved
    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data


def test_l1_3_empty_subagent_output_is_parse_error(backlog: Path) -> None:
    """Empty stdout file → verdict=`parse_error` (not `empty`)."""
    payload = apply_extraction(backlog, "sub.s1", "")
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert payload["added_hints_count"] == 0


# ── L1.4 non-object root ─────────────────────────────────────────────


def test_l1_4_non_object_root_array_is_parse_error(backlog: Path) -> None:
    """JSON array root (instead of object) → parse_error."""
    payload = apply_extraction(backlog, "sub.s1", "[]")
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert "must be object" in payload.get("parse_error", "")


def test_l1_4_non_object_root_scalar_is_parse_error(backlog: Path) -> None:
    """JSON scalar root (e.g. number) → parse_error."""
    payload = apply_extraction(backlog, "sub.s1", "42")
    assert payload["verdict"] == VERDICT_PARSE_ERROR


def test_l1_4_non_object_root_string_is_parse_error(backlog: Path) -> None:
    """JSON string root → parse_error."""
    payload = apply_extraction(backlog, "sub.s1", '"just a string"')
    assert payload["verdict"] == VERDICT_PARSE_ERROR


# ── L1.5 missing `analysis` field ────────────────────────────────────


def test_l1_5_missing_analysis_field_defaults_to_empty(
    backlog: Path
) -> None:
    """czy `:120` `typeof === 'string' ? trim().slice : ''` — missing
    field defaults to "". Verdict still `extracted` if missingAssumptions
    non-empty."""
    subagent_json = json.dumps({
        "missingAssumptions": ["X is measurable"],
        # No `analysis` field
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)
    assert payload["verdict"] == VERDICT_EXTRACTED
    assert payload["added_hints_count"] == 1
    # Analysis defaults to "" → analysis_excerpt is None (no truncate of empty)
    assert payload["analysis_excerpt"] is None

    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == ["X is measurable"]
    assert s1["assumption_analysis"] == ""


def test_l1_5_missing_assumptions_field_treated_as_empty_list(
    backlog: Path
) -> None:
    """czy `:114-118` `Array.isArray` short-circuits on missing
    missingAssumptions → empty list. Treated as `empty` verdict."""
    subagent_json = json.dumps({
        "analysis": "All hypotheses appear to be present.",
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)
    assert payload["verdict"] == VERDICT_EMPTY
    assert payload["added_hints_count"] == 0
    assert payload["analysis_excerpt"] is not None


def test_l1_5_non_array_missing_assumptions_is_parse_error(
    backlog: Path
) -> None:
    """missingAssumptions present but not an array → parse_error."""
    subagent_json = json.dumps({
        "missingAssumptions": "not an array",
        "analysis": "x",
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)
    assert payload["verdict"] == VERDICT_PARSE_ERROR


# ── L1.6 OVERWRITE existing hints (D-1 the headline test) ────────────


def test_l1_6_overwrite_replaces_three_hints_with_two(
    tmp_path: Path
) -> None:
    """**D-1 OVERWRITE invariant.** Existing 3-hint list + new call
    returns 2-hint list → post-write `assumption_hints[]` length == 2
    (NOT 5; NOT append). previous_hint_count=3 in milestone."""
    backlog = tmp_path / "sorry_backlog.yaml"
    items = _one_stuck_subproblem_backlog()
    items[0]["assumption_hints"] = [
        "first existing hint",
        "second existing hint",
        "third existing hint",
    ]
    items[0]["assumption_analysis"] = "old analysis text"
    _make_backlog(items, backlog)

    subagent_json = json.dumps({
        "missingAssumptions": [
            "new hint A",
            "new hint B",
        ],
        "analysis": "fresh analysis from this call",
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)

    assert payload["verdict"] == VERDICT_EXTRACTED
    assert payload["added_hints_count"] == 2  # length of NEW list
    assert payload["previous_hint_count"] == 3
    assert payload["current_hint_count"] == 2  # OVERWRITE: NOT 5
    # OVERWRITE invariant: current == added (D-1 — per-call list size)
    assert payload["current_hint_count"] == payload["added_hints_count"]

    # yaml: only the 2 new hints survive; analysis replaced
    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == ["new hint A", "new hint B"]
    assert s1["assumption_analysis"] == "fresh analysis from this call"
    # Old hints absent (no append, no merge)
    assert "first existing hint" not in s1["assumption_hints"]
    assert "old analysis text" not in s1["assumption_analysis"]


# ── L1.7 Layer 1 invariant ───────────────────────────────────────────


def test_l1_7_protected_fields_byte_identical_post_write(
    backlog: Path
) -> None:
    """Rule 3 Layer 1: `extract_assumption.py` mutates ONLY
    `assumption_hints` + `assumption_analysis`. All other fields on the
    targeted row stay byte-identical.

    Note: H1 may have added detailed_proof_plan / direct_assembly /
    proof_sketch in parallel; if present, they're protected too. This
    test detects-then-asserts so it doesn't break if H1 hasn't landed.
    """
    pre_data = yaml.safe_load(backlog.read_text())
    pre = copy.deepcopy(
        next(it for it in pre_data["sorry_items"] if it["id"] == "sub.s1")
    )

    subagent_json = json.dumps({
        "missingAssumptions": ["X is bounded"],
        "analysis": "Bounded support enables compactness arguments.",
    })
    apply_extraction(backlog, "sub.s1", subagent_json)

    post_data = yaml.safe_load(backlog.read_text())
    s1_post = next(it for it in post_data["sorry_items"] if it["id"] == "sub.s1")

    # Schema-relevant locked fields (E4 / E11 / slice 03 / A1 / H1 union).
    # If H1 hasn't landed, detailed_proof_plan etc. won't be in `pre` —
    # we use pre.get() so the assertion handles either case.
    PROTECTED = (
        # Slice 1 (signature)
        "id", "file", "line", "theorem", "type",
        "depth", "priority", "estimated_lines",
        # v2 state machine
        "state", "parent_id", "children", "history_log",
        "dependencies", "unlocks", "stuck_rounds",
        # E4 helper-reference
        "references", "coverage_state",
        # A1 restrategize counter
        "attempts",
        # E11 citation-verify
        "citation_verified",
        # Slice 03 InformalAgent
        "informal_round", "coverage_stable",
        # H1 elaborate-plan (if present in tree)
        "detailed_proof_plan", "direct_assembly", "proof_sketch",
    )
    for k in PROTECTED:
        if k in pre:
            assert s1_post.get(k) == pre.get(k), (
                f"protected field {k} changed: pre={pre.get(k)!r} post={s1_post.get(k)!r}"
            )

    # Mutated fields ARE different
    assert s1_post["assumption_hints"] == ["X is bounded"]
    assert s1_post["assumption_hints"] != pre.get("assumption_hints", [])


# ── L1.8 empty new list overwrites non-empty (D-1 corner) ────────────


def test_l1_8_empty_new_list_overwrites_non_empty_existing(
    tmp_path: Path
) -> None:
    """Start with 4 hints; new call returns []; post-write
    `assumption_hints == []` (overwrite is full replacement);
    milestone verdict=`empty`.

    This is the D-1 corner case — czy parity says even an empty
    response is per-call-list semantics (list of length 0), so it
    REPLACES the prior list. Cross-round chain semantic doesn't live
    in yaml accumulation."""
    backlog = tmp_path / "sorry_backlog.yaml"
    items = _one_stuck_subproblem_backlog()
    items[0]["assumption_hints"] = ["a", "b", "c", "d"]
    items[0]["assumption_analysis"] = "previous round's analysis"
    _make_backlog(items, backlog)

    subagent_json = json.dumps({
        "missingAssumptions": [],
        "analysis": "All hypotheses now appear to be stated.",
    })
    payload = apply_extraction(backlog, "sub.s1", subagent_json)
    assert payload["verdict"] == VERDICT_EMPTY
    assert payload["added_hints_count"] == 0
    assert payload["previous_hint_count"] == 4
    assert payload["current_hint_count"] == 0  # empty REPLACES non-empty
    assert payload["excerpt"] is None  # empty verdict → no excerpt
    assert payload["analysis_excerpt"] is not None  # but analysis present

    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == []  # full replacement
    assert s1["assumption_analysis"] == "All hypotheses now appear to be stated."


def test_l1_8_empty_with_no_analysis_yields_empty_verdict_no_field_loss(
    tmp_path: Path
) -> None:
    """Edge: missingAssumptions=[] AND analysis missing/empty.
    Verdict still `empty`; assumption_analysis becomes "" (overwrite)."""
    backlog = tmp_path / "sorry_backlog.yaml"
    items = _one_stuck_subproblem_backlog()
    items[0]["assumption_hints"] = ["existing"]
    items[0]["assumption_analysis"] = "old"
    _make_backlog(items, backlog)

    payload = apply_extraction(backlog, "sub.s1", json.dumps({"missingAssumptions": []}))
    assert payload["verdict"] == VERDICT_EMPTY
    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == []
    assert s1["assumption_analysis"] == ""  # overwritten with empty


# ── L1.9 sub_problem_id missing in yaml ──────────────────────────────


def test_l1_9_sub_problem_id_not_in_yaml_raises(backlog: Path) -> None:
    """Caller passes a sub_problem_id not present in sorry_items[] →
    apply_extraction raises ValueError. CLI translates to exit 2."""
    with pytest.raises(ValueError, match="sub_problem_id not in sorry_items"):
        apply_extraction(
            backlog, "ghost.sub.id", json.dumps({
                "missingAssumptions": ["x"], "analysis": "y",
            }),
        )


def test_l1_9_sub_problem_id_missing_via_subprocess_exits_2(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    json_file = tmp_path / "sub.json"
    json_file.write_text(json.dumps({
        "missingAssumptions": ["x"], "analysis": "y",
    }))
    result = subprocess.run(
        [
            "python3", str(EXTRACT),
            "--sub-problem-id", "ghost.sub.id",
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 2
    assert "sub_problem_id not in sorry_items" in result.stderr


# ── L1.10 flock concurrency: second-wins overwrite ───────────────────


def test_l1_10_second_invocation_replaces_first(
    backlog: Path
) -> None:
    """Two sequential invocations on the same sub_problem_id; second
    call's list FULLY REPLACES first's per D-1 overwrite semantic.
    Final state == second call's missingAssumptionNLs.

    True concurrent test would need multiprocessing; here we test
    serial second-wins under flock — which is the same outcome at the
    persistence layer (flock guarantees serialization regardless of
    actual interleaving). Adapted from extract_references' L1.9 idem-
    potence test."""
    first = json.dumps({
        "missingAssumptions": [
            "first call hint A",
            "first call hint B",
            "first call hint C",
        ],
        "analysis": "first call analysis",
    })
    p1 = apply_extraction(backlog, "sub.s1", first)
    assert p1["verdict"] == VERDICT_EXTRACTED
    assert p1["added_hints_count"] == 3

    # Second invocation — different list. Should FULLY REPLACE first's,
    # NOT merge / not append.
    second = json.dumps({
        "missingAssumptions": [
            "second call only hint",
        ],
        "analysis": "second call analysis",
    })
    p2 = apply_extraction(backlog, "sub.s1", second)
    assert p2["verdict"] == VERDICT_EXTRACTED
    assert p2["added_hints_count"] == 1
    assert p2["previous_hint_count"] == 3  # first call's list was here
    assert p2["current_hint_count"] == 1  # OVERWRITE: NOT 4

    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == ["second call only hint"]
    assert "first call hint A" not in s1["assumption_hints"]
    assert s1["assumption_analysis"] == "second call analysis"


# ── parse_subagent_output unit tests (defensive) ─────────────────────


def test_parse_drops_non_string_entries() -> None:
    """czy `:115-117`: filter to non-empty strings. Non-string entries
    silently dropped (don't make the whole call parse_error)."""
    raw = json.dumps({
        "missingAssumptions": [
            "valid string hint",
            42,            # number — dropped
            None,          # null — dropped
            ["nested"],    # array — dropped
            {"k": "v"},    # object — dropped
            "another valid",
        ],
        "analysis": "x",
    })
    result, err = parse_subagent_output(raw)
    assert err is None
    assert result is not None
    assert result.missing_assumption_nls == ["valid string hint", "another valid"]


def test_parse_drops_empty_and_whitespace_strings() -> None:
    """Empty / whitespace-only strings dropped after trim (czy `:115`)."""
    raw = json.dumps({
        "missingAssumptions": ["", "   ", "\t\n", "real hint", "  "],
        "analysis": "x",
    })
    result, err = parse_subagent_output(raw)
    assert err is None
    assert result is not None
    assert result.missing_assumption_nls == ["real hint"]


def test_parse_truncates_long_hints_to_400_chars() -> None:
    """czy `:117` `.slice(0, 400)` — each hint clipped to 400 chars."""
    long = "x" * 500
    raw = json.dumps({"missingAssumptions": [long], "analysis": "x"})
    result, err = parse_subagent_output(raw)
    assert err is None
    assert result is not None
    assert len(result.missing_assumption_nls[0]) == ASSUMPTION_HINT_MAX_CHARS


def test_parse_truncates_long_analysis_to_400_chars() -> None:
    """czy `:120` `.slice(0, 400)` — analysis clipped to 400 chars."""
    long = "y" * 500
    raw = json.dumps({"missingAssumptions": [], "analysis": long})
    result, err = parse_subagent_output(raw)
    assert err is None
    assert result is not None
    assert len(result.analysis) == ASSUMPTION_ANALYSIS_MAX_CHARS


def test_build_finding_summary_two_hints_no_overflow() -> None:
    """czy `:160-165` byte-faithful. Two hints, no `(+N more)` suffix."""
    s = build_finding_summary(["a" * 50, "b" * 50], "ignored")
    assert s.startswith("Missing: ")
    assert "more" not in s


def test_build_finding_summary_overflow_appends_count() -> None:
    """3+ hints → first 2 plus `(+N more)` suffix."""
    s = build_finding_summary(["a", "b", "c", "d"], "ignored")
    assert "(+2 more)" in s


def test_build_finding_summary_empty_falls_back_to_analysis() -> None:
    """czy `:161` — empty list returns analysis truncated to 300."""
    s = build_finding_summary([], "an analysis sentence")
    assert s == "an analysis sentence"


# ── Migration test (companion to slice 03 / E4 / E11 idempotence) ────


def test_migration_adds_assumption_fields_idempotently() -> None:
    """v1 → v2 with H7's two new fields. Idempotent: running twice
    leaves the item byte-identical to a single migration."""
    v1_item: Dict[str, Any] = {
        "id": "x", "file": "X.lean", "line": 1, "theorem": "x_thm",
        "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
    }
    migrate_item_v1_to_v2(v1_item)
    assert v1_item["assumption_hints"] == []
    assert v1_item["assumption_analysis"] == ""

    snap = copy.deepcopy(v1_item)
    migrate_item_v1_to_v2(v1_item)
    assert v1_item == snap


def test_migration_preserves_existing_assumption_fields() -> None:
    """If a yaml already has H7 fields populated (e.g. mid-job recovery),
    migration must NOT clobber them."""
    item = {
        "id": "x",
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [],
        "assumption_hints": ["pre-existing hint"],
        "assumption_analysis": "pre-existing analysis",
    }
    migrate_item_v1_to_v2(item)
    assert item["assumption_hints"] == ["pre-existing hint"]
    assert item["assumption_analysis"] == "pre-existing analysis"


# ── trim helpers ─────────────────────────────────────────────────────


def test_trim_hint_caps_at_400() -> None:
    assert len(trim_hint("z" * 1000)) == ASSUMPTION_HINT_MAX_CHARS


def test_trim_hint_strips_whitespace() -> None:
    assert trim_hint("  hello world  \n") == "hello world"


def test_trim_analysis_caps_at_400() -> None:
    assert len(trim_analysis("z" * 1000)) == ASSUMPTION_ANALYSIS_MAX_CHARS


def test_trim_analysis_strips_whitespace() -> None:
    assert trim_analysis("  hi  ") == "hi"


# ── Sentinel test ────────────────────────────────────────────────────


def test_module_present_marker() -> None:
    """Sentinel test — guards against the test file being silently
    excluded from collection (mirrors slice-1 pattern)."""
    assert True

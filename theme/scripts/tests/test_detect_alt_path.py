"""H2 L1 unit tests for detect_alt_path.py.

Coverage matrix per `docs/H2_DETECT_ALT_PATH_SPEC.md` §8.1:

  L1.1  parse valid JSON with hasAlternative=true + all 9 fields populated
  L1.2  parse valid JSON with hasAlternative=false + empty other fields
  L1.3  parse markdown-fenced JSON (```json ... ```)
  L1.4  parse malformed JSON → exit 2, verdict=parse_error, yaml unchanged
  L1.5  parse JSON with recommendSwitch=true but hasAlternative=false
  L1.6  parse JSON with keyTools not a list → fallback to []
  L1.7  parse JSON with all NL strings >800 chars → clamped to 800
  L1.8  G1 fail — parent has 0 children with non-empty coverage_assessment
  L1.9  G2 fail — sandbox paper_body.txt is 5 chars (< 10 threshold)
  L1.10 locked-signature invariant + Layer 1 byte-identity
  L1.11 G3 cache hit — parent's alternative_path already set

All L1 tests use mock JSON strings; no live LLM calls.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest
import yaml

import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from detect_alt_path import (  # noqa: E402
    apply_alt_path_detection,
    check_gate_g1,
    check_gate_g2,
    check_gate_g3,
    parse_skill_output,
    NL_FIELD_MAX_CHARS,
    KEY_TOOL_MAX_CHARS,
    VERDICT_DETECTED,
    VERDICT_NO_ALTERNATIVE,
    VERDICT_CACHED,
    VERDICT_NO_REFERENCE_RESULTS,
    VERDICT_NO_REFERENCE_TEXT,
    VERDICT_PARSE_ERROR,
    VERDICT_SKILL_DISPATCH_FAILED,
)
from _history_log_types import migrate_item_v1_to_v2  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent.parent


# ── Fixtures and helpers ──────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _parent_with_children() -> Dict[str, Any]:
    """A v2 parent row with 2 children that have reference results (G1 pass)."""
    return {
        "id": "thm.main",
        "file": "Main.lean",
        "line": 10,
        "theorem": "main_theorem",
        "type": "ready",
        "depth": 0,
        "priority": 50,
        "estimated_lines": 100,
        "dependencies": [],
        "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["thm.sub1", "thm.sub2"],
        "parent_id": None,
        "history_log": [],
        "stuck_rounds": 0,
        "attempts": 0,
        "references": [],
        "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": 1,
        "coverage_stable": False,
        "detailed_proof_plan": None,
        "direct_assembly": None,
        "proof_sketch": None,
        "assumption_hints": [],
        "assumption_analysis": "",
        "alternative_path": None,
    }


def _child_with_references(child_id: str, parent_id: str, coverage: str = "no_coverage") -> Dict[str, Any]:
    """A v2 child row with E4 reference results."""
    return {
        "id": child_id,
        "file": "Main.lean",
        "line": 20,
        "theorem": f"sub_thm_{child_id}",
        "type": "ready",
        "depth": 1,
        "priority": 50,
        "estimated_lines": 30,
        "dependencies": [],
        "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": parent_id,
        "history_log": [],
        "stuck_rounds": 0,
        "attempts": 0,
        "references": [
            {
                "ref_id": "ref_001",
                "coverage": coverage,
                "coverage_assessment": "This step is covered by Borel-Cantelli lemma application.",
            }
        ],
        "coverage_state": coverage,
        "citation_verified": False,
        "informal_round": 0,
        "coverage_stable": False,
        "detailed_proof_plan": None,
        "direct_assembly": None,
        "proof_sketch": None,
        "assumption_hints": [],
        "assumption_analysis": "",
        "alternative_path": None,
    }


def _child_no_references(child_id: str, parent_id: str) -> Dict[str, Any]:
    """A v2 child with NO reference results (G1 fail when all children are this)."""
    child = _child_with_references(child_id, parent_id)
    child["references"] = []
    return child


def _full_backlog_with_references(tmp_path: Path) -> Path:
    """Backlog with parent + 2 children + reference results (all gates pass)."""
    p = tmp_path / "sorry_backlog.yaml"
    parent = _parent_with_children()
    child1 = _child_with_references("thm.sub1", "thm.main", "no_coverage")
    child2 = _child_with_references("thm.sub2", "thm.main", "partial_coverage")
    _make_backlog([parent, child1, child2], p)
    return p


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    return _full_backlog_with_references(tmp_path)


@pytest.fixture
def paper_body(tmp_path: Path) -> str:
    """Default: 500-char valid paper body (G2 pass)."""
    return "The Strong Law of Large Numbers can be proved using the Borel-Cantelli lemma. " * 6


def _valid_alt_path_json(has_alternative: bool = True) -> str:
    """Build valid 9-field JSON as the SKILL would output."""
    return json.dumps({
        "hasAlternative": has_alternative,
        "approachName": "Borel-Cantelli + 4th Moment Method",
        "description": "Instead of reverse-martingale, use Borel-Cantelli lemma with 4th moment bound for the SLLN. Truncate X_i at level n, apply Chebyshev to the truncated sum, then Borel-Cantelli.",
        "keyTools": [
            "MeasureTheory.measure_limsup_eq_zero",
            "Finset.sum_div",
        ],
        "currentPathCoverage": "2/2 sub-problems need_proof under current martingale plan.",
        "alternativePathCoverage": "Both truncation lemma and moment bound are cited by the reference.",
        "isMoreEfficient": True,
        "efficiencyReason": "Reference directly proves the truncation bound and 4th moment calculation; Borel-Cantelli application is a direct library call. Saves 2-3 sub-lemmas vs martingale convergence path.",
        "recommendSwitch": True,
    })


# ── L1.1: happy path — hasAlternative=true, all 9 fields ─────────────


def test_l1_1_happy_path_detected(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """Valid JSON with hasAlternative=true: yaml alternative_path populated,
    milestone verdict=detected, all snake_case fields present."""
    payload = apply_alt_path_detection(
        backlog, "thm.main", _valid_alt_path_json(True), paper_body
    )

    assert payload["verdict"] == VERDICT_DETECTED
    assert payload["has_alternative"] is True
    assert payload["recommend_switch"] is True
    assert payload["approach_name_excerpt"] is not None
    assert "Borel-Cantelli" in payload["approach_name_excerpt"]
    assert payload["description_excerpt"] is not None
    assert payload["key_tools_count"] == 2

    # Round-trip: yaml should have alternative_path populated
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    parent = by_id["thm.main"]

    alt = parent["alternative_path"]
    assert alt is not None
    assert isinstance(alt, dict)
    # All 9 snake_case fields present
    assert alt["has_alternative"] is True
    assert alt["approach_name"] == "Borel-Cantelli + 4th Moment Method"
    assert isinstance(alt["description"], str) and len(alt["description"]) > 0
    assert isinstance(alt["key_tools"], list) and len(alt["key_tools"]) == 2
    assert isinstance(alt["current_path_coverage"], str)
    assert isinstance(alt["alternative_path_coverage"], str)
    assert alt["is_more_efficient"] is True
    assert isinstance(alt["efficiency_reason"], str)
    assert alt["recommend_switch"] is True


# ── L1.2: hasAlternative=false → yaml null (D-2 wire choice) ─────────


def test_l1_2_has_alternative_false_writes_null(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """hasAlternative=false: yaml alternative_path=null (NOT a dict with
    has_alternative: false). Milestone verdict=no_alternative. D-2 wire."""
    payload = apply_alt_path_detection(
        backlog, "thm.main", _valid_alt_path_json(False), paper_body
    )

    assert payload["verdict"] == VERDICT_NO_ALTERNATIVE
    assert payload["has_alternative"] is False
    assert payload["recommend_switch"] is False
    assert payload["approach_name_excerpt"] is None

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    parent = by_id["thm.main"]
    # D-2: null wire, NOT {has_alternative: false, ...}
    assert parent["alternative_path"] is None


# ── L1.3: markdown-fenced JSON unwrap (czy safeParseJson:475-484) ─────


def test_l1_3_markdown_fenced_json_unwraps(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """LLM output wrapped in ```json ... ``` fence still parses correctly."""
    fenced = "```json\n" + _valid_alt_path_json(True) + "\n```"
    payload = apply_alt_path_detection(backlog, "thm.main", fenced, paper_body)

    assert payload["verdict"] == VERDICT_DETECTED
    assert payload["has_alternative"] is True

    final = yaml.safe_load(backlog.read_text())
    parent = next(it for it in final["sorry_items"] if it["id"] == "thm.main")
    assert parent["alternative_path"] is not None


# ── L1.4: malformed JSON → parse_error, yaml unchanged ───────────────


def test_l1_4_malformed_json_parse_error(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """Malformed JSON: verdict=parse_error, yaml unchanged (alternative_path stays None)."""
    pre_data = yaml.safe_load(backlog.read_text())

    payload = apply_alt_path_detection(
        backlog, "thm.main", "not json at all {[}", paper_body
    )

    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert payload["has_alternative"] is None
    assert payload["recommend_switch"] is False
    assert payload["approach_name_excerpt"] is None
    assert "parse_error" in payload

    # yaml unchanged
    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data


# ── L1.5: recommendSwitch=true but hasAlternative=false ──────────────


def test_l1_5_recommend_switch_without_has_alternative(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """recommendSwitch=true AND hasAlternative=false: hasAlternative gates the
    wire choice. yaml writes null (gated by hasAlternative=false). D-2 parity."""
    contradictory = json.dumps({
        "hasAlternative": False,
        "approachName": "",
        "description": "",
        "keyTools": [],
        "currentPathCoverage": "",
        "alternativePathCoverage": "",
        "isMoreEfficient": False,
        "efficiencyReason": "",
        "recommendSwitch": True,  # contradicts hasAlternative=False but valid JSON
    })
    payload = apply_alt_path_detection(backlog, "thm.main", contradictory, paper_body)

    # hasAlternative=False gates → no_alternative regardless of recommendSwitch
    assert payload["verdict"] == VERDICT_NO_ALTERNATIVE
    assert payload["has_alternative"] is False
    assert payload["recommend_switch"] is False  # not propagated when no_alternative

    final = yaml.safe_load(backlog.read_text())
    parent = next(it for it in final["sorry_items"] if it["id"] == "thm.main")
    assert parent["alternative_path"] is None


# ── L1.6: keyTools not a list → fallback to [] ───────────────────────


def test_l1_6_key_tools_not_list_fallback_empty(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """keyTools non-list: czy parity Array.isArray → fallback []; verdict=detected
    (if hasAlternative=true); yaml key_tools == []."""
    bad_key_tools = json.dumps({
        "hasAlternative": True,
        "approachName": "Some Approach",
        "description": "Some description.",
        "keyTools": "not-a-list",  # string instead of array
        "currentPathCoverage": "partial",
        "alternativePathCoverage": "full",
        "isMoreEfficient": True,
        "efficiencyReason": "Fewer steps.",
        "recommendSwitch": True,
    })
    payload = apply_alt_path_detection(backlog, "thm.main", bad_key_tools, paper_body)

    assert payload["verdict"] == VERDICT_DETECTED
    assert payload["key_tools_count"] == 0

    final = yaml.safe_load(backlog.read_text())
    parent = next(it for it in final["sorry_items"] if it["id"] == "thm.main")
    assert parent["alternative_path"]["key_tools"] == []


# ── L1.7: NL strings >800 chars → clamped to 800 (D-4) ──────────────


def test_l1_7_nl_strings_over_limit_are_clamped(backlog: Path, sandbox: Path, paper_body: str) -> None:
    """NL strings longer than 800 chars are clamped to 800 (D-4 clamp)."""
    long_str = "x" * 2000
    oversized = json.dumps({
        "hasAlternative": True,
        "approachName": long_str,
        "description": long_str,
        "keyTools": ["a" * 500, "b" * 10],
        "currentPathCoverage": long_str,
        "alternativePathCoverage": long_str,
        "isMoreEfficient": True,
        "efficiencyReason": long_str,
        "recommendSwitch": True,
    })
    payload = apply_alt_path_detection(backlog, "thm.main", oversized, paper_body)

    assert payload["verdict"] == VERDICT_DETECTED

    final = yaml.safe_load(backlog.read_text())
    parent = next(it for it in final["sorry_items"] if it["id"] == "thm.main")
    alt = parent["alternative_path"]

    # All NL string fields clamped to NL_FIELD_MAX_CHARS
    for field in ("approach_name", "description", "current_path_coverage",
                  "alternative_path_coverage", "efficiency_reason"):
        assert len(alt[field]) <= NL_FIELD_MAX_CHARS, (
            f"field {field!r} not clamped: length {len(alt[field])}"
        )

    # key_tools[i] clamped to KEY_TOOL_MAX_CHARS
    for tool in alt["key_tools"]:
        assert len(tool) <= KEY_TOOL_MAX_CHARS, (
            f"key_tools entry not clamped: length {len(tool)}"
        )


# ── L1.8: G1 fail — no children with non-empty coverage_assessment ────


def test_l1_8_g1_fail_no_reference_results(tmp_path: Path, sandbox: Path) -> None:
    """G1 fail: parent's children have no coverage_assessment → verdict=no_reference_results.
    Uses --bypass-skill --gate-only mode; yaml unchanged."""
    parent = _parent_with_children()
    # Children with empty references (G1 fails)
    child1 = _child_no_references("thm.sub1", "thm.main")
    child2 = _child_no_references("thm.sub2", "thm.main")
    bl = tmp_path / "sorry_backlog.yaml"
    _make_backlog([parent, child1, child2], bl)

    pre_data = yaml.safe_load(bl.read_text())
    paper_body = "Non-trivial proof text that exceeds ten chars easily."

    payload = apply_alt_path_detection(
        bl, "thm.main", None, paper_body, gate_only=True
    )

    # G3 passes (alternative_path is None), G2 passes (body long enough)
    # G1 fails (no reference assessments)
    assert payload["verdict"] == VERDICT_NO_REFERENCE_RESULTS
    assert payload["has_alternative"] is None
    assert payload["recommend_switch"] is False

    post_data = yaml.safe_load(bl.read_text())
    assert post_data == pre_data


# ── L1.9: G2 fail — paper_body too short (< 10 chars) ────────────────


def test_l1_9_g2_fail_paper_body_too_short(backlog: Path, sandbox: Path) -> None:
    """G2 fail: paper_body.strip() < 10 chars → verdict=no_reference_text."""
    pre_data = yaml.safe_load(backlog.read_text())

    # 5-char body: below MIN_PAPER_BODY_CHARS=10
    payload = apply_alt_path_detection(
        backlog, "thm.main", None, "short", gate_only=True
    )

    assert payload["verdict"] == VERDICT_NO_REFERENCE_TEXT
    assert payload["has_alternative"] is None

    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data


# ── L1.10: Layer 1 byte-identity invariant ───────────────────────────


def test_l1_10_layer1_byte_identity(tmp_path: Path, sandbox: Path) -> None:
    """Layer 1 invariant: after detect_alt_path writes alternative_path,
    ALL other fields on the targeted parent + ALL child fields stay
    byte-identical to their pre-write values.

    Uses a maximally-populated parent (locked sig, populated history_log,
    references, coverage_citation, detailed_proof_plan, assumption_hints).
    """
    parent = _parent_with_children()
    # Populate protected fields
    parent["history_log"] = [{"iteration": 1, "decomposition": ["thm.sub1"], "results": []}]
    parent["detailed_proof_plan"] = "Step 1: apply martingale convergence."
    parent["direct_assembly"] = "apply MartingaleConvergence at h1 h2"
    parent["proof_sketch"] = "brief martingale argument"
    parent["assumption_hints"] = ["f is bounded", "X_i are iid"]
    parent["assumption_analysis"] = "Missing boundedness constraint."
    parent["coverage_citation"] = "Theorem 3.1 in reference"

    child1 = _child_with_references("thm.sub1", "thm.main", "no_coverage")
    child1["coverage_citation"] = "cited in §2.3"
    child2 = _child_with_references("thm.sub2", "thm.main", "partial_coverage")

    bl = tmp_path / "sorry_backlog.yaml"
    _make_backlog([parent, child1, child2], bl)

    # Snapshot pre-write state
    pre_data = yaml.safe_load(bl.read_text())
    pre_items = {it["id"]: copy.deepcopy(it) for it in pre_data["sorry_items"]}

    paper_body = "Extended proof text covering multiple lines of the reference. " * 10
    payload = apply_alt_path_detection(
        bl, "thm.main", _valid_alt_path_json(True), paper_body
    )
    assert payload["verdict"] == VERDICT_DETECTED

    post_data = yaml.safe_load(bl.read_text())
    post_items = {it["id"]: it for it in post_data["sorry_items"]}

    # Check parent: only alternative_path changed
    pre_parent = pre_items["thm.main"]
    post_parent = post_items["thm.main"]
    for field in pre_parent:
        if field == "alternative_path":
            # This field IS expected to change
            continue
        assert pre_parent[field] == post_parent[field], (
            f"parent field {field!r} changed unexpectedly: "
            f"{pre_parent[field]!r} → {post_parent[field]!r}"
        )

    # Check children: entirely unchanged
    for child_id in ("thm.sub1", "thm.sub2"):
        pre_child = pre_items[child_id]
        post_child = post_items[child_id]
        for field in pre_child:
            assert pre_child[field] == post_child[field], (
                f"child {child_id!r} field {field!r} changed unexpectedly: "
                f"{pre_child[field]!r} → {post_child[field]!r}"
            )


# ── L1.11: G3 cache hit — alternative_path already set ───────────────


def test_l1_11_g3_cache_hit_first_detection_wins(tmp_path: Path, sandbox: Path) -> None:
    """G3 (first-detection-wins): parent already has non-null alternative_path →
    verdict=cached, SKILL not dispatched, yaml UNCHANGED.
    Mirrors czy proofLoop.ts:886 `!cachedAltPath` guard."""
    parent = _parent_with_children()
    existing_alt = {
        "has_alternative": True,
        "approach_name": "Previously Detected Approach",
        "description": "A previously cached alternative.",
        "key_tools": ["lemma_A"],
        "current_path_coverage": "low",
        "alternative_path_coverage": "high",
        "is_more_efficient": True,
        "efficiency_reason": "Fewer steps.",
        "recommend_switch": True,
    }
    parent["alternative_path"] = existing_alt

    child1 = _child_with_references("thm.sub1", "thm.main", "no_coverage")
    child2 = _child_with_references("thm.sub2", "thm.main", "partial_coverage")
    bl = tmp_path / "sorry_backlog.yaml"
    _make_backlog([parent, child1, child2], bl)

    pre_data = yaml.safe_load(bl.read_text())
    paper_body = "Sufficient paper body text for G2 pass." * 3

    payload = apply_alt_path_detection(
        bl, "thm.main",
        None,  # subagent_text is irrelevant — should not be read on cache hit
        paper_body,
    )

    assert payload["verdict"] == VERDICT_CACHED
    assert payload["approach_name_excerpt"] is None  # per spec §4
    assert payload["has_alternative"] is True  # from existing cached value

    # yaml UNCHANGED (first-detection-wins: cache preserved)
    post_data = yaml.safe_load(bl.read_text())
    assert post_data == pre_data, "yaml must be unchanged on cache hit"


# ── Unit tests for parse_skill_output ────────────────────────────────


def test_parse_skill_output_valid_full() -> None:
    """parse_skill_output returns (True, validated, None) on valid input."""
    ok, result, err = parse_skill_output(_valid_alt_path_json(True))
    assert ok is True
    assert err is None
    assert result["hasAlternative"] is True
    assert isinstance(result["keyTools"], list)
    assert len(result["keyTools"]) == 2


def test_parse_skill_output_empty_string() -> None:
    """Empty input → parse failure."""
    ok, result, err = parse_skill_output("")
    assert ok is False
    assert err is not None


def test_parse_skill_output_non_object_root() -> None:
    """Array root → parse failure."""
    ok, result, err = parse_skill_output("[1, 2, 3]")
    assert ok is False


def test_parse_skill_output_bare_fence() -> None:
    """Bare ``` fence (no json tag) is also stripped."""
    bare = "```\n" + _valid_alt_path_json(False) + "\n```"
    ok, result, err = parse_skill_output(bare)
    assert ok is True
    assert result["hasAlternative"] is False


# ── Unit tests for gate functions ─────────────────────────────────────


def test_check_gate_g1_pass_with_assessment() -> None:
    """G1 passes when at least one child has non-empty coverage_assessment."""
    items = [
        {"id": "child.1", "references": [{"coverage_assessment": "covered by BC lemma"}]},
    ]
    assert check_gate_g1(["child.1"], items) is True


def test_check_gate_g1_pass_with_empty_assessment_text() -> None:
    """G1 passes when ≥1 child has any references[] entry — czy parity.

    czy `helperAgent.ts:304` checks `referenceResults.length > 0`
    REGARDLESS of assessment text content. H2 §8 code review S2.2
    fix: a child with `coverage: no_coverage` and empty assessment
    text still counts (E4 ran on it, coverageResults entry exists).
    """
    items = [
        {"id": "child.1", "references": [{"coverage_assessment": ""}]},
        {"id": "child.2", "references": []},
    ]
    # child.1 has a reference entry (even with empty text) → gate passes
    assert check_gate_g1(["child.1", "child.2"], items) is True


def test_check_gate_g1_fail_no_references() -> None:
    """G1 fails when E4 has not run on any child (no references field).

    Distinct from the empty-assessment case: here NO child has any
    references[] entry. This is the only case czy's gate would also
    reject — `referenceResults.length === 0`.
    """
    items = [
        {"id": "child.1", "references": []},
        {"id": "child.2"},  # references field absent
    ]
    assert check_gate_g1(["child.1", "child.2"], items) is False


def test_check_gate_g2_pass() -> None:
    """G2 passes for body >= 10 chars."""
    assert check_gate_g2("This is a valid proof text.") is True


def test_check_gate_g2_fail_short() -> None:
    """G2 fails for body < 10 chars."""
    assert check_gate_g2("short") is False
    assert check_gate_g2("   ") is False
    assert check_gate_g2("") is False


def test_check_gate_g3_pass_when_null() -> None:
    """G3 passes (no cache) when alternative_path is None."""
    assert check_gate_g3({"alternative_path": None}) is True
    assert check_gate_g3({}) is True  # missing key → None (migrate default)


def test_check_gate_g3_fail_when_populated() -> None:
    """G3 fails (cache hit) when alternative_path is a non-null dict."""
    assert check_gate_g3({"alternative_path": {"has_alternative": True}}) is False

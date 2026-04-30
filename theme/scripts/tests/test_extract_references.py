"""E4 L1 unit tests for extract_references.py.

Coverage matrix per `docs/E4_REFERENCE_SUBAGENT_SPEC.md` §7.1:
  L1.1 valid LLM JSON array → references[] populated correctly
  L1.2 malformed JSON → exit 2; yaml unchanged; no milestone
  L1.3 markdown-fenced JSON → unwrapped per czy regex
  L1.4 locked-signature invariant — sig + parent_id + children +
       history_log byte-identical post-write
  L1.5 partial_coverage downgrade — matching_statement ignored when
       coverage != cited_by_reference
  L1.6 unknown coverage value coalesces to no_coverage
  L1.7 empty pdfProofBody (--pdf-proof-body-len < 10) → exit 2
  L1.8 migration idempotence (v1 → v2 with 3 new fields; v2 → no-op)
  L1.9 milestone payload validation (covered+partial+no_coverage ==
       sub_problem_count; references list len matches)
  L1.10 parent_id missing in yaml → exit 2

All tests use mock LLM JSON strings; no live LLM calls.
"""
from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from extract_references import (  # noqa: E402
    apply_extraction,
    parse_subagent_output,
    unwrap_fenced_json,
)
from _reference_types import (  # noqa: E402
    ReferenceEntry,
    aggregate_coverage_state,
    coalesce_coverage,
    make_coverage_citation,
)
from _history_log_types import migrate_item_v1_to_v2, migrate_yaml_v1_to_v2  # noqa: E402


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_references.py"


# ── Fixture: sandbox + backlog with one parent + 2 children ──────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _two_child_parent_backlog() -> List[Dict[str, Any]]:
    return [
        {
            "id": "parent.one", "file": "X.lean", "line": 1,
            "theorem": "parent_one_thm", "type": "blocked", "depth": 0,
            "priority": 50, "estimated_lines": 100,
            "dependencies": [], "unlocks": [],
            "state": "INACTIVE_WAIT", "children": ["parent.one.s1", "parent.one.s2"],
            "parent_id": None, "history_log": [], "stuck_rounds": 0,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "parent.one.s1", "file": "X.lean", "line": 5,
            "theorem": "s1_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 0,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "parent.one.s2", "file": "X.lean", "line": 10,
            "theorem": "s2_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 0,
            "references": [], "coverage_state": "needs_proof",
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
    _make_backlog(_two_child_parent_backlog(), p)
    return p


# ── L1.3 (helper test of the unwrap function itself) ─────────────────


def test_unwrap_fenced_json_strips_json_fence() -> None:
    raw = "```json\n[{\"a\": 1}]\n```"
    assert unwrap_fenced_json(raw).strip() == '[{"a": 1}]'


def test_unwrap_fenced_json_strips_bare_fence() -> None:
    raw = "```\n[1,2,3]\n```"
    assert unwrap_fenced_json(raw).strip() == "[1,2,3]"


def test_unwrap_fenced_json_passes_through_when_no_fence() -> None:
    assert unwrap_fenced_json("[1,2,3]") == "[1,2,3]"


# ── L1.1 valid JSON ──────────────────────────────────────────────────


def test_l1_1_parse_valid_llm_json_populates_references(
    backlog: Path, sandbox: Path
) -> None:
    subagent_json = json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "cited_by_reference",
            "assessment": "claim/theorem/hyp/concl/judgment OK",
            "matching_statement": "Theorem 2.1 in [Foo'23]: ...",
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "no_coverage",
            "assessment": "no relevant statement in PDF",
            "matching_statement": None,
        },
    ])
    entries, coverage_state, citation = apply_extraction(
        backlog, "parent.one", subagent_json
    )
    assert len(entries) == 2
    assert entries[0].coverage == "cited_by_reference"
    assert entries[0].matching_statement == "Theorem 2.1 in [Foo'23]: ..."
    assert entries[0].replacement_statement == "Theorem 2.1 in [Foo'23]: ..."
    assert entries[1].coverage == "no_coverage"
    assert entries[1].matching_statement is None
    assert coverage_state == "cited_by_reference"
    assert citation == "-- cited from reference: Theorem 2.1 in [Foo'23]: ..."

    # Round-trip — yaml should reflect the writes
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    p = by_id["parent.one"]
    assert len(p["references"]) == 2
    assert p["references"][0]["coverage"] == "cited_by_reference"
    assert p["coverage_state"] == "cited_by_reference"
    assert p["coverage_citation"] == "-- cited from reference: Theorem 2.1 in [Foo'23]: ..."


# ── L1.2 malformed JSON ──────────────────────────────────────────────


def test_l1_2_malformed_json_raises_validation_error(backlog: Path) -> None:
    with pytest.raises(ValueError, match="not valid JSON"):
        apply_extraction(backlog, "parent.one", "not json at all {[}")
    # yaml unchanged — still has the original 2 children entries empty
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["parent.one"]["references"] == []
    assert by_id["parent.one"]["coverage_state"] == "needs_proof"


def test_l1_2_non_array_root_raises(backlog: Path) -> None:
    with pytest.raises(ValueError, match="must be array"):
        apply_extraction(backlog, "parent.one", '{"key": "value"}')


# ── L1.3 markdown fence ──────────────────────────────────────────────


def test_l1_3_markdown_fenced_json_unwraps(backlog: Path) -> None:
    fenced = "```json\n" + json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "no_coverage",
            "assessment": "x",
            "matching_statement": None,
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "no_coverage",
            "assessment": "x",
            "matching_statement": None,
        },
    ]) + "\n```"
    entries, _, _ = apply_extraction(backlog, "parent.one", fenced)
    assert len(entries) == 2


# ── L1.4 locked-signature invariant ──────────────────────────────────


def test_l1_4_signature_invariant_preserved(backlog: Path) -> None:
    """The 8 protected fields (per Rule 3 Layer 1 + the v2 state-machine
    fields) are byte-identical post-write. Only references / coverage_state /
    coverage_citation may change."""
    pre_data = yaml.safe_load(backlog.read_text())
    pre = copy.deepcopy(
        next(it for it in pre_data["sorry_items"] if it["id"] == "parent.one")
    )
    subagent_json = json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "cited_by_reference",
            "assessment": "ok",
            "matching_statement": "Lemma X",
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "partial_coverage",
            "assessment": "ok",
            "matching_statement": None,
        },
    ])
    apply_extraction(backlog, "parent.one", subagent_json)
    post = yaml.safe_load(backlog.read_text())
    p_post = next(it for it in post["sorry_items"] if it["id"] == "parent.one")

    PROTECTED = ("id", "file", "line", "theorem", "state", "parent_id",
                 "children", "history_log", "type", "depth", "priority",
                 "estimated_lines", "dependencies", "unlocks", "stuck_rounds")
    for k in PROTECTED:
        assert p_post.get(k) == pre.get(k), f"protected field {k} changed"


# ── L1.5 partial_coverage downgrade ──────────────────────────────────


def test_l1_5_matching_statement_ignored_when_partial(backlog: Path) -> None:
    """czy `:446-448`: matching_statement is meaningful ONLY when
    cited_by_reference. If LLM emits it for partial_coverage anyway,
    drop it."""
    subagent_json = json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "partial_coverage",
            "assessment": "ok",
            "matching_statement": "should be dropped",
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "no_coverage",
            "assessment": "ok",
            "matching_statement": None,
        },
    ])
    entries, coverage_state, citation = apply_extraction(
        backlog, "parent.one", subagent_json
    )
    assert entries[0].matching_statement is None
    assert entries[0].replacement_statement is None
    assert coverage_state == "partial_coverage"
    assert citation is None  # no citation when no entry is cited_by_reference


# ── L1.6 unknown coverage value ──────────────────────────────────────


def test_l1_6_unknown_coverage_coalesces_to_no_coverage(backlog: Path) -> None:
    subagent_json = json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "covered",  # ← invalid value
            "assessment": "ok",
            "matching_statement": "X",
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "fully_relevant",  # ← invalid
            "assessment": "ok",
            "matching_statement": None,
        },
    ])
    entries, coverage_state, _ = apply_extraction(backlog, "parent.one", subagent_json)
    assert entries[0].coverage == "no_coverage"
    assert entries[0].matching_statement is None  # also dropped
    assert entries[1].coverage == "no_coverage"
    assert coverage_state == "needs_proof"


def test_coalesce_coverage_handles_non_strings() -> None:
    assert coalesce_coverage(None) == "no_coverage"
    assert coalesce_coverage(42) == "no_coverage"
    assert coalesce_coverage(["a"]) == "no_coverage"
    assert coalesce_coverage("CITED_BY_REFERENCE") == "cited_by_reference"  # case insensitive


# ── L1.7 empty body — CLI level ──────────────────────────────────────


def test_l1_7_empty_pdf_proof_body_exits_2(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    json_file = tmp_path / "subagent.json"
    json_file.write_text(json.dumps([
        {"subProblemId": "parent.one.s1", "coverage": "no_coverage",
         "assessment": "x", "matching_statement": None},
        {"subProblemId": "parent.one.s2", "coverage": "no_coverage",
         "assessment": "x", "matching_statement": None},
    ]))
    result = subprocess.run(
        [
            "python3", str(EXTRACT),
            "--parent-id", "parent.one",
            "--subagent-json-file", str(json_file),
            "--pdf-proof-body-len", "5",  # < 10 → refuse
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 2
    assert "pdf_proof_body_len" in result.stderr


# ── L1.8 migration idempotence ───────────────────────────────────────


def test_l1_8_migrate_v1_to_v2_adds_three_fields_idempotently() -> None:
    v1_item: Dict[str, Any] = {
        "id": "x", "file": "X.lean", "line": 1, "theorem": "x_thm",
        "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
    }
    migrate_item_v1_to_v2(v1_item)
    # Slice 1 fields
    assert v1_item["state"] == "INITIALIZED"
    assert v1_item["children"] == []
    assert v1_item["parent_id"] is None
    assert v1_item["history_log"] == []
    # E4 fields
    assert v1_item["references"] == []
    assert v1_item["coverage_state"] == "needs_proof"
    assert "coverage_citation" not in v1_item

    # Idempotent: running again is a no-op
    snap = copy.deepcopy(v1_item)
    migrate_item_v1_to_v2(v1_item)
    assert v1_item == snap


def test_l1_8_already_v2_with_partial_e4_fields_completes_them() -> None:
    """A v2 item that's missing only the E4 fields gets them
    completed without losing existing fields."""
    item = {
        "id": "x",
        "state": "INITIALIZED", "children": ["y"], "parent_id": None,
        "history_log": [{"iteration": 1}],
        "references": [{"sub_problem_id": "y", "coverage": "cited_by_reference",
                        "assessment": "x"}],
        # coverage_state intentionally absent
    }
    migrate_item_v1_to_v2(item)
    assert item["state"] == "INITIALIZED"  # unchanged
    assert item["children"] == ["y"]  # unchanged
    assert item["history_log"] == [{"iteration": 1}]  # unchanged
    assert item["references"] == [{"sub_problem_id": "y", "coverage": "cited_by_reference",
                                    "assessment": "x"}]  # unchanged
    assert item["coverage_state"] == "needs_proof"  # filled in


# ── L1.9 milestone payload partition ─────────────────────────────────


def test_l1_9_milestone_payload_partition_holds_via_subprocess(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """End-to-end: run script via subprocess, read events.jsonl,
    confirm covered+partial+no_coverage == sub_problem_count + payload
    schema fields present."""
    json_file = tmp_path / "subagent.json"
    json_file.write_text(json.dumps([
        {"subProblemId": "parent.one.s1", "coverage": "cited_by_reference",
         "assessment": "ok", "matching_statement": "Thm 1"},
        {"subProblemId": "parent.one.s2", "coverage": "partial_coverage",
         "assessment": "ok", "matching_statement": None},
    ]))
    result = subprocess.run(
        [
            "python3", str(EXTRACT),
            "--parent-id", "parent.one",
            "--subagent-json-file", str(json_file),
            "--pdf-proof-body-len", "1024",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr

    events_path = sandbox / "events.jsonl"
    assert events_path.is_file()
    lines = events_path.read_text().strip().splitlines()
    milestones = [json.loads(l) for l in lines if json.loads(l).get("kind") == "sandbox_milestone"]
    ext = [m for m in milestones if m.get("name") == "reference-extracted"]
    assert len(ext) == 1
    payload = ext[0]["details"]
    assert payload["sub_problem_count"] == 2
    # Partition invariant
    assert payload["covered_count"] + payload["partial_count"] + payload["no_coverage_count"] == 2
    assert payload["covered_count"] == 1
    assert payload["partial_count"] == 1
    assert payload["no_coverage_count"] == 0
    assert payload["coverage_state"] == "cited_by_reference"
    assert len(payload["references"]) == 2
    assert payload["pdf_proof_body_len"] == 1024


# ── L1.10 parent_id missing ──────────────────────────────────────────


def test_l1_10_parent_id_not_in_yaml_raises(backlog: Path) -> None:
    with pytest.raises(ValueError, match="parent_id not in sorry_items"):
        apply_extraction(backlog, "ghost.parent", json.dumps([]))


def test_l1_10_parent_with_no_children_raises(tmp_path: Path) -> None:
    """A parent with no children means the agent dispatched
    helper-reference inappropriately (no sub-problems to assess).
    Refuse rather than silently no-op."""
    backlog = tmp_path / "b.yaml"
    _make_backlog([{
        "id": "lonely", "file": "X.lean", "line": 1, "theorem": "x",
        "type": "ready", "depth": 0, "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [], "state": "INITIALIZED",
        "children": [], "parent_id": None, "history_log": [],
        "stuck_rounds": 0, "references": [], "coverage_state": "needs_proof",
    }], backlog)
    with pytest.raises(ValueError, match="no children"):
        apply_extraction(backlog, "lonely", json.dumps([]))


# ── Bonus coverage on the helpers (no L# in spec; defensive) ─────────


def test_aggregate_coverage_state_precedence() -> None:
    e1 = ReferenceEntry("a", "no_coverage", "x")
    e2 = ReferenceEntry("b", "partial_coverage", "x")
    e3 = ReferenceEntry("c", "cited_by_reference", "x", matching_statement="m")

    assert aggregate_coverage_state([]) == "needs_proof"
    assert aggregate_coverage_state([e1]) == "needs_proof"
    assert aggregate_coverage_state([e1, e2]) == "partial_coverage"
    assert aggregate_coverage_state([e1, e2, e3]) == "cited_by_reference"
    # Order doesn't matter — cited_by_reference wins
    assert aggregate_coverage_state([e3, e2, e1]) == "cited_by_reference"


def test_subagent_omits_subproblem_falls_back_to_no_coverage() -> None:
    """czy `:435-441` — if the subagent didn't return a record for an
    expected sub-problem id, default to no_coverage with an honest
    reason in assessment."""
    raw = json.dumps([
        {"subProblemId": "parent.one.s1", "coverage": "cited_by_reference",
         "assessment": "ok", "matching_statement": "T1"},
        # parent.one.s2 omitted by the LLM
    ])
    entries = parse_subagent_output(raw, ["parent.one.s1", "parent.one.s2"])
    assert len(entries) == 2
    assert entries[1].sub_problem_id == "parent.one.s2"
    assert entries[1].coverage == "no_coverage"
    assert "did not return" in entries[1].assessment


def test_subagent_id_case_insensitive_match() -> None:
    """czy R2 mitigation — LLM may upcase or pad ids; we trim+lower."""
    raw = json.dumps([
        {"subProblemId": "  PARENT.ONE.S1  ",  # nasty casing/padding
         "coverage": "no_coverage", "assessment": "x", "matching_statement": None},
        {"subProblemId": "parent.one.s2",
         "coverage": "no_coverage", "assessment": "x", "matching_statement": None},
    ])
    entries = parse_subagent_output(raw, ["parent.one.s1", "parent.one.s2"])
    assert len(entries) == 2
    # canonical id preserved (we don't propagate the LLM's casing)
    assert entries[0].sub_problem_id == "parent.one.s1"


def test_make_coverage_citation_format() -> None:
    """Byte-for-byte czy match. Any consumer that splits on ': ' must
    work on either source."""
    assert make_coverage_citation("Theorem 5.2") == "-- cited from reference: Theorem 5.2"


def test_per_child_coverage_state_propagated_to_child_rows(
    backlog: Path, sandbox: Path
) -> None:
    """F2 fix (post 2026-04-30 L3): E4 must propagate per-child
    coverage_state from parent.references[] to each child row's
    coverage_state field. Without this, E11 R7 + slice 03 read
    `needs_proof` from children regardless of E4's actual labelling
    and never fire cited paths in production."""
    subagent_json = json.dumps([
        {
            "subProblemId": "parent.one.s1",
            "coverage": "cited_by_reference",
            "assessment": "ok",
            "matching_statement": "Lemma X",
        },
        {
            "subProblemId": "parent.one.s2",
            "coverage": "partial_coverage",
            "assessment": "x",
            "matching_statement": None,
        },
    ])
    apply_extraction(backlog, "parent.one", subagent_json)
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    # Each child gets per-child coverage_state propagated
    assert by_id["parent.one.s1"]["coverage_state"] == "cited_by_reference"
    assert by_id["parent.one.s2"]["coverage_state"] == "partial_coverage"
    # cited_by_reference child also gets per-child citation
    assert "coverage_citation" in by_id["parent.one.s1"]
    # partial_coverage child does NOT (matching_statement was dropped per L1.5)
    assert "coverage_citation" not in by_id["parent.one.s2"]


def test_per_child_propagation_clears_stale_citation_on_re_run(
    backlog: Path, sandbox: Path
) -> None:
    """If a child was previously cited but a re-run downgrades it,
    the stale per-child coverage_citation must be cleared."""
    # Run 1: s1 cited
    apply_extraction(backlog, "parent.one", json.dumps([
        {"subProblemId": "parent.one.s1", "coverage": "cited_by_reference",
         "assessment": "ok", "matching_statement": "X"},
        {"subProblemId": "parent.one.s2", "coverage": "no_coverage",
         "assessment": "x", "matching_statement": None},
    ]))
    final1 = yaml.safe_load(backlog.read_text())
    by_id1 = {it["id"]: it for it in final1["sorry_items"]}
    assert "coverage_citation" in by_id1["parent.one.s1"]

    # Run 2: s1 downgraded to no_coverage
    apply_extraction(backlog, "parent.one", json.dumps([
        {"subProblemId": "parent.one.s1", "coverage": "no_coverage",
         "assessment": "second look: no", "matching_statement": None},
        {"subProblemId": "parent.one.s2", "coverage": "no_coverage",
         "assessment": "x", "matching_statement": None},
    ]))
    final2 = yaml.safe_load(backlog.read_text())
    by_id2 = {it["id"]: it for it in final2["sorry_items"]}
    assert by_id2["parent.one.s1"]["coverage_state"] == "no_coverage"
    assert "coverage_citation" not in by_id2["parent.one.s1"], (
        "stale citation must be cleared on downgrade"
    )


def test_module_present_marker() -> None:
    """Sentinel test — guards against the test file being silently
    excluded from collection (mirrors slice-1 pattern)."""
    assert True

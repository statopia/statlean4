"""H3 L1 unit tests for extract_library_coverage.py.

Coverage matrix per `docs/H3_LIBRARY_COVERAGE_SPEC.md` §8.1:
  L1.1 valid JSON with one cited_by_library entry → child.coverage_state=
       "cited_by_library"; child.library_hit.name==matched_name;
       milestone verdict=="partial" (1 of 2 covered)
  L1.2 all entries needs_proof → no coverage_state changed;
       library_hit absent; milestone verdict=="none_covered"
  L1.3 all entries cited_by_library → all children updated;
       milestone verdict=="all_covered"; cited_by_library_count==len(children)
  L1.4 idempotent re-run with same name → second run is no-op;
       yaml byte-identical post-run; no duplicate state change
  L1.5 idempotent re-run with different name → existing library_hit
       overwritten with new name; log warning emitted
  L1.6 sub_problem_id not in backlog → entry skipped; skipped_count=1;
       other children unaffected
  L1.7 JSON parse failure (malformed file) → exit 2; verdict=parse_error;
       yaml byte-identical to pre-call state
  L1.8 Layer 1 field allowlist → run with one cited_by_library hit;
       assert state/done_reason/file/line/history_log unchanged
  L1.9 cited_by_reference child is NOT overwritten → pre-set
       child.coverage_state=="cited_by_reference"; H3 entry says
       needs_proof → field preserved; no library_hit written

All tests use mock SKILL JSON strings; no live LLM calls.
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

from extract_library_coverage import (  # noqa: E402
    apply_extraction,
    parse_skill_output,
    unwrap_fenced_json,
)
from _library_types import MatchedLemma, LibraryCoverageResult  # noqa: E402
from _history_log_types import migrate_item_v1_to_v2  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_library_coverage.py"


# ── Fixture builders ─────────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _parent_with_two_children() -> List[Dict[str, Any]]:
    """Pre-migrated v2 rows: one parent (INACTIVE_WAIT) + two children
    (needs_proof). All v2 fields populated so Layer 1 tests have something
    to enforce against."""
    parent: Dict[str, Any] = {
        "id": "parent.thm",
        "file": "Parent.lean", "line": 10,
        "theorem": "parent_theorem", "type": "ready", "depth": 0,
        "priority": 50, "estimated_lines": 60,
        "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["child.A", "child.B"],
        "parent_id": None, "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    child_a: Dict[str, Any] = {
        "id": "child.A",
        "file": "ChildA.lean", "line": 5,
        "theorem": "child_a_thm", "type": "ready", "depth": 1,
        "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": "parent.thm", "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    child_b: Dict[str, Any] = {
        "id": "child.B",
        "file": "ChildB.lean", "line": 8,
        "theorem": "child_b_thm", "type": "ready", "depth": 1,
        "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": "parent.thm", "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    return [parent, child_a, child_b]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _make_backlog(_parent_with_two_children(), p)
    return p


# ── unwrap helpers ────────────────────────────────────────────────────


def test_unwrap_strips_json_fence() -> None:
    raw = "```json\n[]\n```"
    assert unwrap_fenced_json(raw).strip() == "[]"


def test_unwrap_strips_bare_fence() -> None:
    raw = "```\n[]\n```"
    assert unwrap_fenced_json(raw).strip() == "[]"


def test_unwrap_passthrough_no_fence() -> None:
    assert unwrap_fenced_json("[]") == "[]"


# ── L1.1 one cited_by_library entry ──────────────────────────────────


def test_l1_1_one_cited_by_library_entry(backlog: Path) -> None:
    """Valid JSON with 1 cited_by_library + 1 needs_proof.
    child.A → cited_by_library; child.B → unchanged (needs_proof).
    verdict == "partial"."""
    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "cited_by_library",
            "matched_name": "MeasureTheory.integral_nonneg",
            "matched_source": "mathlib",
            "matched_location": "Mathlib/Measure/Foo.lean:42",
            "matched_kind": "lemma",
            "candidates_queried": ["integral_nonneg"],
            "reasoning": "Conclusion check passes.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": ["condExp_add"],
            "reasoning": "No matching candidate.",
        },
    ])

    covered, needs_proof, skipped, verdict = apply_extraction(
        backlog, "parent.thm", skill_json
    )

    assert covered == 1
    assert needs_proof == 1
    assert skipped == 0
    assert verdict == "partial"

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    # child.A — updated
    a = by_id["child.A"]
    assert a["coverage_state"] == "cited_by_library"
    assert a["library_hit"]["name"] == "MeasureTheory.integral_nonneg"
    assert a["library_hit"]["source"] == "mathlib"
    assert a["library_hit"]["kind"] == "lemma"

    # child.B — untouched
    b = by_id["child.B"]
    assert b["coverage_state"] == "needs_proof"
    assert b.get("library_hit") is None


# ── L1.2 all needs_proof ─────────────────────────────────────────────


def test_l1_2_all_needs_proof(backlog: Path) -> None:
    """All entries needs_proof → no coverage_state changed;
    library_hit absent; verdict == "none_covered"."""
    pre_data = yaml.safe_load(backlog.read_text())
    pre_str = yaml.safe_dump(pre_data, sort_keys=False, allow_unicode=True)

    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
    ])

    covered, needs_proof, skipped, verdict = apply_extraction(
        backlog, "parent.thm", skill_json
    )

    assert covered == 0
    assert needs_proof == 2
    assert skipped == 0
    assert verdict == "none_covered"

    post_data = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in post_data["sorry_items"]}

    assert by_id["child.A"]["coverage_state"] == "needs_proof"
    assert by_id["child.A"].get("library_hit") is None
    assert by_id["child.B"]["coverage_state"] == "needs_proof"
    assert by_id["child.B"].get("library_hit") is None


# ── L1.3 all cited_by_library ────────────────────────────────────────


def test_l1_3_all_cited_by_library(backlog: Path) -> None:
    """All entries cited_by_library → all children updated;
    verdict == "all_covered"; cited_by_library_count == 2."""
    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "cited_by_library",
            "matched_name": "Finset.sum_comm",
            "matched_source": "mathlib",
            "matched_location": None,
            "matched_kind": "lemma",
            "candidates_queried": ["sum_comm"],
            "reasoning": "Match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "cited_by_library",
            "matched_name": "MeasureTheory.lintegral_mono",
            "matched_source": "mathlib",
            "matched_location": "Mathlib/Foo.lean:99",
            "matched_kind": "theorem",
            "candidates_queried": ["lintegral_mono"],
            "reasoning": "Match.",
        },
    ])

    covered, needs_proof, skipped, verdict = apply_extraction(
        backlog, "parent.thm", skill_json
    )

    assert covered == 2
    assert needs_proof == 0
    assert skipped == 0
    assert verdict == "all_covered"

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    assert by_id["child.A"]["coverage_state"] == "cited_by_library"
    assert by_id["child.A"]["library_hit"]["name"] == "Finset.sum_comm"
    assert by_id["child.B"]["coverage_state"] == "cited_by_library"
    assert by_id["child.B"]["library_hit"]["name"] == "MeasureTheory.lintegral_mono"


# ── L1.4 idempotent re-run same name ─────────────────────────────────


def test_l1_4_idempotent_same_name(backlog: Path) -> None:
    """Second run with same matched_name is no-op; yaml byte-identical."""
    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "cited_by_library",
            "matched_name": "Finset.sum_comm",
            "matched_source": "mathlib",
            "matched_location": None,
            "matched_kind": "lemma",
            "candidates_queried": ["sum_comm"],
            "reasoning": "Match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
    ])

    # First run
    apply_extraction(backlog, "parent.thm", skill_json)
    after_first = backlog.read_text()

    # Second run (same JSON, same name)
    apply_extraction(backlog, "parent.thm", skill_json)
    after_second = backlog.read_text()

    # yaml should be byte-identical between first and second run
    assert after_first == after_second


# ── L1.5 idempotent re-run different name → overwrite ─────────────────


def test_l1_5_different_name_overwrites(backlog: Path, capsys) -> None:
    """Second run with different matched_name overwrites existing library_hit."""
    skill_first = json.dumps([{
        "sub_problem_id": "child.A",
        "coverage": "cited_by_library",
        "matched_name": "Finset.sum_comm",
        "matched_source": "mathlib",
        "matched_location": None,
        "matched_kind": "lemma",
        "candidates_queried": ["sum_comm"],
        "reasoning": "Match first.",
    }, {
        "sub_problem_id": "child.B",
        "coverage": "needs_proof",
        "matched_name": None,
        "matched_source": None,
        "matched_location": None,
        "matched_kind": None,
        "candidates_queried": [],
        "reasoning": "No match.",
    }])

    skill_second = json.dumps([{
        "sub_problem_id": "child.A",
        "coverage": "cited_by_library",
        "matched_name": "Finset.sum_nonneg",  # different name
        "matched_source": "mathlib",
        "matched_location": None,
        "matched_kind": "lemma",
        "candidates_queried": ["sum_nonneg"],
        "reasoning": "Match second.",
    }, {
        "sub_problem_id": "child.B",
        "coverage": "needs_proof",
        "matched_name": None,
        "matched_source": None,
        "matched_location": None,
        "matched_kind": None,
        "candidates_queried": [],
        "reasoning": "No match.",
    }])

    apply_extraction(backlog, "parent.thm", skill_first)
    apply_extraction(backlog, "parent.thm", skill_second)

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["child.A"]["library_hit"]["name"] == "Finset.sum_nonneg"

    # Warning should have been emitted to stderr
    captured = capsys.readouterr()
    assert "overwrite" in captured.err


# ── L1.6 sub_problem_id not in backlog ───────────────────────────────


def test_l1_6_unknown_sub_problem_id_skipped(backlog: Path) -> None:
    """Entry with unknown sub_problem_id skipped; skipped_count=1;
    other children unaffected."""
    skill_json = json.dumps([
        {
            "sub_problem_id": "ghost.id",  # not in backlog
            "coverage": "cited_by_library",
            "matched_name": "SomeLemma",
            "matched_source": "mathlib",
            "matched_location": None,
            "matched_kind": "lemma",
            "candidates_queried": [],
            "reasoning": "Match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
    ])

    covered, needs_proof, skipped, verdict = apply_extraction(
        backlog, "parent.thm", skill_json
    )

    assert skipped == 1
    assert covered == 0
    assert needs_proof == 1

    # child.B unaffected
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["child.B"]["coverage_state"] == "needs_proof"
    assert by_id["child.B"].get("library_hit") is None


# ── L1.7 JSON parse failure → exit 2 ────────────────────────────────


def test_l1_7_malformed_json_parse_failure(backlog: Path) -> None:
    """Malformed JSON → ValueError raised by apply_extraction;
    yaml byte-identical to pre-call state."""
    pre_text = backlog.read_text()

    with pytest.raises(ValueError, match="not valid JSON"):
        apply_extraction(backlog, "parent.thm", "not json {{{")

    # yaml unchanged
    assert backlog.read_text() == pre_text


def test_l1_7_malformed_json_subprocess_exits_2(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """CLI: malformed JSON → exit 2."""
    json_file = tmp_path / "malformed.json"
    json_file.write_text("not json {{{")

    result = subprocess.run(
        [
            "python3", str(EXTRACT),
            "--parent-id", "parent.thm",
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 2


# ── L1.8 Layer 1 field allowlist ────────────────────────────────────


def test_l1_8_layer1_field_allowlist(backlog: Path) -> None:
    """Run with one cited_by_library hit; assert state/done_reason/file/
    line/history_log unchanged (byte-by-byte diff on every other field).

    Rule 3 Layer 1: extract_library_coverage.py mutates ONLY
    coverage_state + library_hit on child sorry_items. All other fields
    on the targeted row stay byte-identical."""
    pre_data = yaml.safe_load(backlog.read_text())
    # Pre-snapshot for each item keyed by id
    pre_by_id = {
        it["id"]: copy.deepcopy(it) for it in pre_data["sorry_items"]
    }

    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "cited_by_library",
            "matched_name": "MeasureTheory.integral_nonneg",
            "matched_source": "mathlib",
            "matched_location": None,
            "matched_kind": "lemma",
            "candidates_queried": ["integral_nonneg"],
            "reasoning": "Match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
    ])

    apply_extraction(backlog, "parent.thm", skill_json)

    post_data = yaml.safe_load(backlog.read_text())
    post_by_id = {it["id"]: it for it in post_data["sorry_items"]}

    # Fields that MUST NOT be touched (Rule 3 Layer 1 allowlist)
    PROTECTED = (
        "id", "file", "line", "theorem", "type",
        "depth", "priority", "estimated_lines",
        "state", "parent_id", "children", "history_log",
        "dependencies", "unlocks",
        "references",
        "attempts", "citation_verified",
        "informal_round", "coverage_stable",
        "assumption_hints", "assumption_analysis",
        "alternative_path",
    )

    for item_id in ("child.A", "child.B", "parent.thm"):
        pre = pre_by_id[item_id]
        post = post_by_id[item_id]
        for k in PROTECTED:
            if k in pre:
                assert post.get(k) == pre.get(k), (
                    f"item {item_id}: protected field '{k}' changed: "
                    f"pre={pre.get(k)!r} post={post.get(k)!r}"
                )

    # Mutated fields on child.A ARE different
    a_post = post_by_id["child.A"]
    assert a_post["coverage_state"] == "cited_by_library"
    assert a_post["library_hit"]["name"] == "MeasureTheory.integral_nonneg"


# ── L1.9 cited_by_reference not overwritten ──────────────────────────


def test_l1_9_cited_by_reference_not_overwritten(tmp_path: Path) -> None:
    """Pre-set child.A with coverage_state == "cited_by_reference" (set by
    E4). H3 entry says needs_proof → field preserved; no library_hit
    written. H3 never downgrades a cited_by_reference back to needs_proof."""
    backlog = tmp_path / "sorry_backlog.yaml"
    items = _parent_with_two_children()
    # Pre-set child.A as cited_by_reference (E4 already ran)
    items[1]["coverage_state"] = "cited_by_reference"
    items[1]["coverage_citation"] = "-- cited from reference: some theorem"
    _make_backlog(items, backlog)

    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "needs_proof",  # H3 says no library match
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "No match.",
        },
    ])

    apply_extraction(backlog, "parent.thm", skill_json)

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    # child.A must remain cited_by_reference (not downgraded to needs_proof)
    assert by_id["child.A"]["coverage_state"] == "cited_by_reference"
    assert by_id["child.A"].get("library_hit") is None


def test_l1_9b_cited_by_reference_not_overwritten_when_skill_says_library(
    tmp_path: Path,
) -> None:
    """Pre-set child.A as cited_by_reference; H3 SKILL says
    cited_by_library. Spec §5 rule 2: H3 NEVER overwrites
    cited_by_reference (E4 territory). H3 §8 code review S3.1 fixup
    — the guard previously missing only covered the
    needs_proof-from-SKILL case, not the cited_by_library-from-SKILL
    case. This test exercises the second scenario.
    """
    backlog = tmp_path / "sorry_backlog.yaml"
    items = _parent_with_two_children()
    items[1]["coverage_state"] = "cited_by_reference"
    items[1]["coverage_citation"] = "-- cited from reference: some theorem"
    _make_backlog(items, backlog)

    skill_json = json.dumps([
        {
            "sub_problem_id": "child.A",
            "coverage": "cited_by_library",  # H3 found a candidate
            "matched_name": "Mathlib.SomeLemma",
            "matched_source": "mathlib",
            "matched_location": "/foo/bar.lean#L42",
            "matched_kind": "theorem",
            "candidates_queried": ["Mathlib.SomeLemma"],
            "reasoning": "match.",
        },
        {
            "sub_problem_id": "child.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": [],
            "reasoning": "no match.",
        },
    ])

    apply_extraction(backlog, "parent.thm", skill_json)

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    # child.A must STILL be cited_by_reference (NOT overwritten to library)
    assert by_id["child.A"]["coverage_state"] == "cited_by_reference"
    assert by_id["child.A"].get("library_hit") is None
    # E4's coverage_citation must survive
    assert "some theorem" in by_id["child.A"].get("coverage_citation", "")


# ── parse_skill_output unit tests ────────────────────────────────────


def test_parse_valid_array() -> None:
    raw = json.dumps([{
        "sub_problem_id": "sp.1",
        "coverage": "needs_proof",
        "matched_name": None,
        "matched_source": None,
        "matched_location": None,
        "matched_kind": None,
        "candidates_queried": [],
        "reasoning": "None.",
    }])
    results = parse_skill_output(raw, ["sp.1"])
    assert len(results) == 1
    assert results[0].sub_problem_id == "sp.1"
    assert results[0].coverage == "needs_proof"


def test_parse_non_array_raises() -> None:
    with pytest.raises(ValueError, match="must be array"):
        parse_skill_output('{"coverage": "needs_proof"}', [])


def test_parse_empty_string_raises() -> None:
    with pytest.raises(ValueError, match="empty"):
        parse_skill_output("", [])


def test_parse_malformed_json_raises() -> None:
    with pytest.raises(ValueError, match="not valid JSON"):
        parse_skill_output("{not json", [])


def test_parse_cited_entry_builds_matched_lemma() -> None:
    raw = json.dumps([{
        "sub_problem_id": "sp.A",
        "coverage": "cited_by_library",
        "matched_name": "Finset.sum_comm",
        "matched_source": "mathlib",
        "matched_location": "Mathlib/Algebra/Foo.lean:10",
        "matched_kind": "lemma",
        "candidates_queried": ["sum_comm"],
        "reasoning": "Match.",
    }])
    results = parse_skill_output(raw, ["sp.A"])
    assert len(results) == 1
    r = results[0]
    assert r.coverage == "cited_by_library"
    assert r.matched_lemma is not None
    assert r.matched_lemma.name == "Finset.sum_comm"
    assert r.matched_lemma.source == "mathlib"
    assert r.matched_lemma.location == "Mathlib/Algebra/Foo.lean:10"


def test_parse_drops_non_dict_entries() -> None:
    raw = json.dumps([
        {"sub_problem_id": "sp.A", "coverage": "needs_proof",
         "matched_name": None, "matched_source": None,
         "matched_location": None, "matched_kind": None,
         "candidates_queried": [], "reasoning": "No."},
        "not a dict",
        42,
    ])
    results = parse_skill_output(raw, ["sp.A"])
    assert len(results) == 1


# ── MatchedLemma tests ───────────────────────────────────────────────


def test_matched_lemma_to_yaml_drops_none_fields() -> None:
    m = MatchedLemma(name="Foo.bar", source="mathlib")
    d = m.to_yaml()
    assert "location" not in d
    assert "kind" not in d
    assert d["name"] == "Foo.bar"
    assert d["source"] == "mathlib"


def test_matched_lemma_to_yaml_keeps_present_fields() -> None:
    m = MatchedLemma(
        name="Foo.bar", source="statlean",
        location="Foo/Bar.lean:5", kind="theorem"
    )
    d = m.to_yaml()
    assert d["location"] == "Foo/Bar.lean:5"
    assert d["kind"] == "theorem"


def test_matched_lemma_from_yaml_round_trip() -> None:
    m = MatchedLemma(name="X.y", source="mathlib", location="X/Y.lean:1", kind="lemma")
    m2 = MatchedLemma.from_yaml(m.to_yaml())
    assert m == m2


# ── Migration test ───────────────────────────────────────────────────


def test_migration_adds_library_hit_field_idempotently() -> None:
    """v1 → v2 migration: library_hit defaults to None."""
    item: Dict[str, Any] = {
        "id": "x", "file": "X.lean", "line": 1, "theorem": "x_thm",
        "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
    }
    migrate_item_v1_to_v2(item)
    assert "library_hit" in item
    assert item["library_hit"] is None

    # Idempotent: second call is no-op
    import copy
    snap = copy.deepcopy(item)
    migrate_item_v1_to_v2(item)
    assert item == snap


def test_migration_preserves_existing_library_hit() -> None:
    """Existing library_hit (e.g. from mid-job recovery) is NOT clobbered."""
    item = {
        "id": "x",
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [],
        "library_hit": {"name": "pre.existing.Lemma", "source": "mathlib"},
    }
    migrate_item_v1_to_v2(item)
    assert item["library_hit"] == {"name": "pre.existing.Lemma", "source": "mathlib"}


# ── Sentinel test ────────────────────────────────────────────────────


def test_module_present_marker() -> None:
    """Sentinel test — guards against the test file being silently
    excluded from collection (mirrors slice-1 pattern)."""
    assert True

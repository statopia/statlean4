"""Slice 03 L1 unit tests for refine_decomposition.py.

Coverage matrix per `docs/SLICE_03_INFORMAL_AGENT_SPEC.md` §7.1.

Verdict branches:
  L1.1 round 0 first-refinement entry — script accepts (children non-empty)
  L1.2 informal_round at cap (>=2) — verdict=cap_reached
  L1.3 coverage_stable already true — would be a no-op; covered by L1.4/L1.5
  L1.4 all children cited_by_library + verified — converged_pre_dispatch
  L1.5 all children DONE+done_reason — converged_pre_dispatch
  L1.6 parent has no children — exit 2
  L1.7 LLM noAdjustment + informal_round > 0 — verdict=noAdjustment
  L1.8 LLM proposes refined decomposition (1 added, 1 removed, 1 kept)
  L1.9 LLM returns malformed JSON — verdict=parse_error, yaml unchanged
  L1.10 KEPT children's theorem field byte-identical (Layer 1)
  L1.11 LLM rephrases a kept child's description — refusal silent
  L1.12 flock — concurrent refine on different parents serializes
  L1.13 atomic write — preserves file mode 0o644
  L1.14 replacement_statement substitution semantic (delegated to SKILL —
        we test only the script's diff/write behavior)
  L1.15 citation_verified=false treated as needs-refinement (script
        accepts the child as still-non-converged)
  L1.16 history_log NOT touched by refine (czy parity — refine doesn't
        write history_log; only retreat / restrategize do)

Total 16 L1 cases (subdivided into ~20 functions).
"""
from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from multiprocessing import Process
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from refine_decomposition import (  # noqa: E402
    INFORMAL_ROUND_CAP,
    _all_children_converged,
    _diff_subproblems,
    _unwrap_fenced_json,
    apply_refinement,
    parse_subagent_output,
)


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
REFINE = SCRIPTS_DIR / "refine_decomposition.py"


# ── Fixtures ─────────────────────────────────────────────────────────


def _parent_with_three_children(
    informal_round: int = 0,
    coverage_stable: bool = False,
    child_overrides: Optional[Dict[str, Dict[str, Any]]] = None,
) -> List[Dict[str, Any]]:
    """v2 backlog with parent + 3 children. Each child defaults to
    INITIALIZED + needs_proof; per-child fields can be overridden."""
    parent = {
        "id": "p", "file": "Statlean/Foo.lean", "line": 1,
        "theorem": "p_thm", "type": "blocked",
        "depth": 0, "priority": 50, "estimated_lines": 100,
        "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["p.s1", "p.s2", "p.s3"],
        "parent_id": None,
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": informal_round,
        "coverage_stable": coverage_stable,
    }
    children = []
    for cid in ("p.s1", "p.s2", "p.s3"):
        ch = {
            "id": cid, "file": "Statlean/Foo.lean", "line": 5,
            "theorem": cid + "_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
        }
        if child_overrides and cid in child_overrides:
            ch.update(child_overrides[cid])
        children.append(ch)
    return [parent] + children


def _write_backlog(path: Path, items: List[Dict[str, Any]]) -> None:
    data = {"schema_version": 2, "version": "v100", "sorry_items": items}
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _by_id(backlog: Path, item_id: str) -> Dict[str, Any]:
    data = yaml.safe_load(backlog.read_text())
    return next(it for it in data["sorry_items"] if it["id"] == item_id)


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _write_backlog(p, _parent_with_three_children())
    return p


# ── Helpers / unit tests ─────────────────────────────────────────────


def test_unwrap_fenced_json_strips_fence() -> None:
    assert _unwrap_fenced_json('```json\n{"a":1}\n```').strip() == '{"a":1}'


def test_unwrap_fenced_json_passthrough() -> None:
    assert _unwrap_fenced_json('{"a":1}') == '{"a":1}'


def test_parse_subagent_handles_empty() -> None:
    ok, parsed = parse_subagent_output("")
    assert not ok
    assert "empty" in parsed["error"].lower()


def test_parse_subagent_handles_invalid_json() -> None:
    ok, parsed = parse_subagent_output("not json at all {")
    assert not ok
    assert "decode" in parsed["error"].lower()


def test_parse_subagent_handles_array_root() -> None:
    ok, parsed = parse_subagent_output("[1,2,3]")
    assert not ok
    assert "not object" in parsed["error"]


def test_diff_kept_removed_added() -> None:
    kept, removed, added = _diff_subproblems(
        ["a", "b", "c"],
        [{"id": "a"}, {"id": "c"}, {"id": "d"}],
    )
    assert kept == ["a", "c"]
    assert removed == ["b"]
    assert [sp["id"] for sp in added] == ["d"]


def test_all_converged_when_all_done() -> None:
    items = _parent_with_three_children(child_overrides={
        "p.s1": {"state": "DONE", "done_reason": "library_verified"},
        "p.s2": {"state": "DONE", "done_reason": "reference_axiom"},
        "p.s3": {"state": "DONE", "done_reason": "library_verified"},
    })
    assert _all_children_converged(["p.s1", "p.s2", "p.s3"], items)


def test_all_converged_when_cited_and_verified() -> None:
    items = _parent_with_three_children(child_overrides={
        "p.s1": {"coverage_state": "cited_by_library", "citation_verified": True},
        "p.s2": {"coverage_state": "cited_by_reference", "citation_verified": True},
        "p.s3": {"state": "DONE", "done_reason": "library_verified"},
    })
    assert _all_children_converged(["p.s1", "p.s2", "p.s3"], items)


def test_not_all_converged_when_one_unverified() -> None:
    items = _parent_with_three_children(child_overrides={
        "p.s1": {"coverage_state": "cited_by_library", "citation_verified": True},
        "p.s2": {"coverage_state": "cited_by_reference", "citation_verified": False},
        "p.s3": {"state": "DONE", "done_reason": "library_verified"},
    })
    assert not _all_children_converged(["p.s1", "p.s2", "p.s3"], items)


# ── L1.1 round 0 entry ───────────────────────────────────────────────


def test_l1_1_round_0_entry_with_children_accepted(backlog: Path) -> None:
    """First refinement: informal_round=0, parent has children. Script
    accepts (cap check passes 0 < 2)."""
    refined_json = json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "split p.s2 into smaller pieces",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.new1", "description": "new", "action": "prove", "dependencies": []},
            {"id": "p.new2", "description": "new2", "action": "prove", "dependencies": []},
        ],
    })
    payload = apply_refinement(backlog, "p", refined_json)
    assert payload["verdict"] == "refined"
    assert payload["informal_round_post"] == 1


# ── L1.2 cap_reached ─────────────────────────────────────────────────


def test_l1_2_cap_reached_at_2(tmp_path: Path) -> None:
    """informal_round=2 → script returns cap_reached without
    dispatching LLM (czy parity 3 total InformalAgent invocations)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _parent_with_three_children(informal_round=INFORMAL_ROUND_CAP))
    payload = apply_refinement(p, "p", "ANY-INPUT-IGNORED")
    assert payload["verdict"] == "cap_reached"
    assert payload["informal_round_post"] == INFORMAL_ROUND_CAP

    # yaml unchanged on cap_reached
    item = _by_id(p, "p")
    assert item["informal_round"] == INFORMAL_ROUND_CAP
    assert item["children"] == ["p.s1", "p.s2", "p.s3"]


def test_l1_2_cap_reached_above(tmp_path: Path) -> None:
    """informal_round > cap also returns cap_reached (defensive)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _parent_with_three_children(informal_round=99))
    payload = apply_refinement(p, "p", "{}")
    assert payload["verdict"] == "cap_reached"


# ── L1.4 / L1.5 converged_pre_dispatch ───────────────────────────────


def test_l1_4_all_cited_library_verified_converges(tmp_path: Path) -> None:
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children(child_overrides={
        cid: {"coverage_state": "cited_by_library", "citation_verified": True}
        for cid in ("p.s1", "p.s2", "p.s3")
    })
    _write_backlog(p, items)
    payload = apply_refinement(p, "p", "ANY-INPUT-IGNORED")
    assert payload["verdict"] == "converged_pre_dispatch"
    assert _by_id(p, "p")["coverage_stable"] is True


def test_l1_5_all_done_converges(tmp_path: Path) -> None:
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children(child_overrides={
        "p.s1": {"state": "DONE", "done_reason": "library_verified"},
        "p.s2": {"state": "DONE", "done_reason": "reference_axiom"},
        "p.s3": {"state": "DONE", "done_reason": "library_verified"},
    })
    _write_backlog(p, items)
    payload = apply_refinement(p, "p", "ANY-INPUT-IGNORED")
    assert payload["verdict"] == "converged_pre_dispatch"


# ── L1.6 no children ─────────────────────────────────────────────────


def test_l1_6_no_children_raises(tmp_path: Path) -> None:
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    items[0]["children"] = []  # parent has no children
    _write_backlog(p, items)
    with pytest.raises(ValueError, match="no children"):
        apply_refinement(p, "p", "{}")


# ── L1.7 noAdjustment ────────────────────────────────────────────────


def test_l1_7_no_adjustment_after_round_1(tmp_path: Path) -> None:
    """LLM noAdjustment + informal_round > 0 → coverage_stable=true."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _parent_with_three_children(informal_round=1))
    payload = apply_refinement(p, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": True,
        "decisionReason": "current decomposition is fine",
        "subProblems": [],
    }))
    assert payload["verdict"] == "noAdjustment"
    assert _by_id(p, "p")["coverage_stable"] is True
    # informal_round NOT bumped
    assert _by_id(p, "p")["informal_round"] == 1


def test_l1_7_no_adjustment_at_round_0_ignored(backlog: Path) -> None:
    """czy `:840-843`: noAdjustment is meaningless on the FIRST
    refinement round (informal_round=0). Script falls through to
    treating the proposed subProblems as the answer (or
    parse_error if subProblems is empty)."""
    payload = apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": True,  # ignored at round 0
        "decisionReason": "x",
        "subProblems": [],  # empty → parse_error
    }))
    # Empty subProblems list → parse_error verdict
    assert payload["verdict"] == "parse_error"


# ── L1.8 refined decomposition ───────────────────────────────────────


def test_l1_8_refined_diff_applied(backlog: Path) -> None:
    """LLM proposes: keep p.s1, drop p.s2 + p.s3, add p.new1 + p.new2."""
    payload = apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": False,
        "decisionReason": "rebuild decomposition",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.new1", "description": "new1", "action": "prove", "dependencies": []},
            {"id": "p.new2", "description": "new2", "action": "prove", "dependencies": ["p.s1"]},
        ],
    }))
    assert payload["verdict"] == "refined"
    assert payload["informal_round_post"] == 1
    assert set(payload["diff"]["kept"]) == {"p.s1"}
    assert set(payload["diff"]["removed"]) == {"p.s2", "p.s3"}
    assert set(payload["diff"]["added"]) == {"p.new1", "p.new2"}

    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["p"]["children"] == ["p.s1", "p.new1", "p.new2"]
    assert by_id["p"]["informal_round"] == 1
    assert "p.s2" not in by_id, "dropped child should be removed"
    assert "p.s3" not in by_id
    # new children have correct shape
    assert by_id["p.new1"]["state"] == "INITIALIZED"
    assert by_id["p.new1"]["parent_id"] == "p"
    assert by_id["p.new1"]["depth"] == 1
    assert by_id["p.new1"]["informal_round"] == 0
    assert by_id["p.new2"]["dependencies"] == ["p.s1"]


# ── L1.9 parse_error ─────────────────────────────────────────────────


def test_l1_9_malformed_json_returns_parse_error(backlog: Path) -> None:
    payload = apply_refinement(backlog, "p", "not valid json {[}")
    assert payload["verdict"] == "parse_error"
    # yaml unchanged
    item = _by_id(backlog, "p")
    assert item["children"] == ["p.s1", "p.s2", "p.s3"]
    assert item["informal_round"] == 0


def test_l1_9_non_object_root_returns_parse_error(backlog: Path) -> None:
    payload = apply_refinement(backlog, "p", "[1,2,3]")
    assert payload["verdict"] == "parse_error"


def test_l1_9_missing_subproblems_returns_parse_error(backlog: Path) -> None:
    payload = apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": False,
        "decisionReason": "x",
        # subProblems missing
    }))
    assert payload["verdict"] == "parse_error"


def test_l1_9_subproblems_missing_id_returns_parse_error(backlog: Path) -> None:
    payload = apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": False,
        "decisionReason": "x",
        "subProblems": [{"description": "no id"}],
    }))
    assert payload["verdict"] == "parse_error"


# ── L1.10 / L1.11 Layer 1 invariant on KEPT children ─────────────────


def test_l1_10_kept_children_theorem_byte_identical(backlog: Path) -> None:
    """Even when the LLM rephrases a kept child's description, the
    yaml's `theorem` field stays unchanged. Layer 1 D-6 contract."""
    pre_p_s1 = copy.deepcopy(_by_id(backlog, "p.s1"))
    apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": False,
        "decisionReason": "x",
        "subProblems": [
            # LLM rephrased p.s1's description here — must be IGNORED
            {"id": "p.s1", "description": "REPHRASED-SHOULD-BE-IGNORED",
             "action": "prove", "dependencies": []},
            {"id": "p.s2", "description": "s2", "action": "prove", "dependencies": []},
            {"id": "p.s3", "description": "s3", "action": "prove", "dependencies": []},
        ],
    }))
    post_p_s1 = _by_id(backlog, "p.s1")
    # All fields byte-identical (no diff was applied since same children list)
    assert post_p_s1 == pre_p_s1


def test_l1_11_dropped_then_re_added_is_treated_as_new(backlog: Path) -> None:
    """If the LLM drops p.s1 then a future round re-adds an id 'p.s1',
    it's a NEW child (defaults), NOT a resurrection of the old one.
    This test only checks the diff semantic; no resurrection logic."""
    apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True,
        "noAdjustment": False,
        "decisionReason": "drop s1",
        "subProblems": [
            {"id": "p.s2", "description": "s2", "action": "prove", "dependencies": []},
            {"id": "p.s3", "description": "s3", "action": "prove", "dependencies": []},
        ],
    }))
    # p.s1 now removed
    final = yaml.safe_load(backlog.read_text())
    ids = {it["id"] for it in final["sorry_items"]}
    assert "p.s1" not in ids


# ── L1.12 flock concurrency ──────────────────────────────────────────


def _spawn_refine(p_path: str, parent: str, json_payload: str) -> int:
    try:
        from refine_decomposition import apply_refinement as _apply
        _apply(Path(p_path), parent, json_payload)
        return 0
    except Exception:
        return 2


def test_l1_12_concurrent_refine_different_parents_serializes(
    tmp_path: Path,
) -> None:
    """Two parents, two concurrent processes calling refine —
    flock serializes; both writes succeed without corruption."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    items.extend([
        {
            "id": "q", "file": "Statlean/Bar.lean", "line": 1,
            "theorem": "q_thm", "type": "blocked", "depth": 0,
            "priority": 50, "estimated_lines": 100,
            "dependencies": [], "unlocks": [],
            "state": "INACTIVE_WAIT", "children": ["q.s1"],
            "parent_id": None, "history_log": [],
            "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
        },
        {
            "id": "q.s1", "file": "Statlean/Bar.lean", "line": 5,
            "theorem": "q_s1_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "q",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
        },
    ])
    _write_backlog(p, items)

    j_p = json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "x",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.s2", "description": "s2", "action": "prove", "dependencies": []},
            {"id": "p.new", "description": "new", "action": "prove", "dependencies": []},
        ],
    })
    j_q = json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "y",
        "subProblems": [
            {"id": "q.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "q.new", "description": "new", "action": "prove", "dependencies": []},
        ],
    })

    pp = Process(target=_spawn_refine, args=(str(p), "p", j_p))
    pq = Process(target=_spawn_refine, args=(str(p), "q", j_q))
    pp.start()
    pq.start()
    pp.join(timeout=10)
    pq.join(timeout=10)
    assert pp.exitcode == 0 and pq.exitcode == 0

    final = yaml.safe_load(p.read_text())
    assert final.get("schema_version") == 2  # well-formed; no torn writes
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["p"]["informal_round"] == 1
    assert by_id["q"]["informal_round"] == 1
    assert "p.new" in by_id and "q.new" in by_id


# ── L1.13 file mode preservation ─────────────────────────────────────


def test_l1_13_preserves_file_mode_644(backlog: Path) -> None:
    os.chmod(backlog, 0o644)
    apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "x",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.s2", "description": "s2", "action": "prove", "dependencies": []},
            {"id": "p.s3", "description": "s3", "action": "prove", "dependencies": []},
            {"id": "p.new", "description": "new", "action": "prove", "dependencies": []},
        ],
    }))
    assert (os.stat(backlog).st_mode & 0o777) == 0o644


# ── L1.15 citation_verified=false treated as needs-refinement ────────


def test_l1_15_partial_or_unverified_does_not_short_circuit(
    tmp_path: Path,
) -> None:
    """A child with cited_by_reference + citation_verified=false is
    NOT counted as converged; refinement proceeds to dispatch."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children(child_overrides={
        "p.s1": {"coverage_state": "cited_by_reference", "citation_verified": True},
        "p.s2": {"coverage_state": "cited_by_reference", "citation_verified": False},
        # p.s3 stays default needs_proof
    })
    _write_backlog(p, items)
    # converged_pre_dispatch should NOT fire
    refined_json = json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "address s2 coverage gap",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.s2", "description": "s2", "action": "prove", "dependencies": []},
            {"id": "p.s3", "description": "s3", "action": "prove", "dependencies": []},
            {"id": "p.s2_helper", "description": "bridge gap",
             "action": "prove", "dependencies": ["p.s2"]},
        ],
    })
    payload = apply_refinement(p, "p", refined_json)
    assert payload["verdict"] == "refined"
    assert "p.s2_helper" in payload["diff"]["added"]


# ── L1.16 history_log NOT touched ────────────────────────────────────


def test_l1_16_history_log_not_touched(backlog: Path) -> None:
    """refine_decomposition does NOT write history_log (czy parity:
    only retreat / restrategize / decompose write history)."""
    pre_history = list(_by_id(backlog, "p")["history_log"])
    apply_refinement(backlog, "p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "x",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.new", "description": "new", "action": "prove", "dependencies": []},
        ],
    }))
    post_history = _by_id(backlog, "p")["history_log"]
    assert post_history == pre_history  # unchanged


# ── Subprocess-level: milestone payload validation ────────────────────


def test_milestone_emits_via_subprocess(
    backlog: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """End-to-end via subprocess: confirm informal-round milestone
    fires with payload schema correct."""
    json_file = tmp_path / "subagent.json"
    json_file.write_text(json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "test",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.new", "description": "new", "action": "prove", "dependencies": []},
        ],
    }))
    result = subprocess.run(
        [
            "python3", str(REFINE),
            "--parent-id", "p",
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr

    events = sandbox / "events.jsonl"
    assert events.is_file()
    milestones = [
        json.loads(line)
        for line in events.read_text().strip().splitlines()
        if json.loads(line).get("kind") == "sandbox_milestone"
    ]
    ir = [m for m in milestones if m.get("name") == "informal-round"]
    assert len(ir) == 1
    payload = ir[0]["details"]
    assert payload["parent_id"] == "p"
    assert payload["verdict"] == "refined"
    assert payload["informal_round_post"] == 1
    assert "diff" in payload


def test_module_present_marker() -> None:
    assert True

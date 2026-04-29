"""A1 L1 unit tests for restrategize_node.py.

Coverage matrix per `docs/A1_RESTRATEGIZE_SPEC.md` §8.1:
  L1.1 applies to parent with no children → exit 2
  L1.2 applies to non-existent parent_id → exit 2
  L1.3 clears all children (BFS, recursive descendants)
  L1.4 bumps attempts (0→1, then 1→2 across calls)
  L1.5 resets stuck_rounds (3→0)
  L1.6 locked-signature invariant — 14 protected fields preserved
  L1.7 history_log entry shape (retreat_reason byte-format, iteration,
       decomposition, results)
  L1.8 proved children captured in results (DONE only; INITIALIZED/
       ACTIVE_PROVING children are cleared but NOT recorded as proved)
  L1.9 atomic write — preserves file mode 0o644
  L1.10 flock — concurrent restrategize serializes
  L1.11 milestone payload validation (cleared_children_count ==
        decomposition_count; proved_children is separate informational)
  L1.12 unrelated siblings preserved

Plus boundary tests:
  - attempts >= 3 → script refuses (caller should retreat instead)
  - retreat after restrategize correctly resets attempts (slice-2
    coupling — covered in test_record_retreat.py separately)
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from multiprocessing import Process
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from restrategize_node import (  # noqa: E402
    ATTEMPTS_RETREAT_THRESHOLD,
    _build_history_entry,
    apply_restrategize,
)


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
RESTRAT = SCRIPTS_DIR / "restrategize_node.py"


# ── Fixtures ─────────────────────────────────────────────────────────


def _write_backlog(path: Path, items: List[Dict[str, Any]]) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _parent_with_three_children(stuck_rounds: int = 3,
                                 attempts: int = 0) -> List[Dict[str, Any]]:
    return [
        {
            "id": "p", "file": "X.lean", "line": 10,
            "theorem": "p_thm", "type": "blocked",
            "depth": 0, "priority": 50, "estimated_lines": 100,
            "dependencies": [], "unlocks": [],
            "state": "INACTIVE_WAIT",
            "children": ["p.s1", "p.s2", "p.s3"],
            "parent_id": None,
            "history_log": [],
            "stuck_rounds": stuck_rounds,
            "attempts": attempts,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "p.s1", "file": "X.lean", "line": 12,
            "theorem": "p_s1_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "DONE", "done_reason": "proved",
            "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "p.s2", "file": "X.lean", "line": 15,
            "theorem": "p_s2_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED",
            "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 3, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "p.s3", "file": "X.lean", "line": 18,
            "theorem": "p_s3_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED",
            "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 1, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
        },
    ]


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


# ── L1.1 / L1.2 validation errors ────────────────────────────────────


def test_l1_1_parent_with_no_children_raises(tmp_path: Path) -> None:
    p = tmp_path / "b.yaml"
    _write_backlog(p, [{
        "id": "lonely", "file": "X.lean", "line": 1, "theorem": "x",
        "type": "ready", "depth": 0, "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 3, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
    }])
    with pytest.raises(ValueError, match="no children"):
        apply_restrategize(p, "lonely")


def test_l1_2_non_existent_parent_raises(backlog: Path) -> None:
    with pytest.raises(ValueError, match="parent_id not in sorry_items"):
        apply_restrategize(backlog, "ghost.parent")


def test_l1_attempts_at_threshold_raises(tmp_path: Path) -> None:
    """Boundary: attempts=3 → script refuses (caller should retreat).
    This is the script-level enforcement of the agent-layer gate."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _parent_with_three_children(
        attempts=ATTEMPTS_RETREAT_THRESHOLD,
    ))
    with pytest.raises(ValueError, match="should call record_retreat"):
        apply_restrategize(p, "p")


# ── L1.3 clear all descendants ───────────────────────────────────────


def test_l1_3_clears_all_descendants_recursive(tmp_path: Path) -> None:
    """A 3-level tree: parent → mid → leaf. Restrategize on parent
    clears mid AND leaf (BFS recursive). Parent itself stays."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    # Replace s1's row with "s1 has its own grandchild"
    items[1]["state"] = "INACTIVE_WAIT"
    items[1]["children"] = ["p.s1.g1"]
    items.append({
        "id": "p.s1.g1", "file": "X.lean", "line": 20,
        "theorem": "g1_thm", "type": "ready", "depth": 2,
        "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "p.s1",
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
    })
    _write_backlog(p, items)

    apply_restrategize(p, "p")
    final = yaml.safe_load(p.read_text())
    ids = {it["id"] for it in final["sorry_items"]}
    assert "p" in ids, "parent must survive (D-2 deviation)"
    assert "p.s1" not in ids
    assert "p.s2" not in ids
    assert "p.s3" not in ids
    assert "p.s1.g1" not in ids, "grandchild not cleared by BFS"


def test_l1_3_parent_state_resets(backlog: Path) -> None:
    apply_restrategize(backlog, "p")
    p = _by_id(backlog, "p")
    assert p["state"] == "INITIALIZED"
    assert p["children"] == []
    assert p["stuck_rounds"] == 0  # L1.5


# ── L1.4 bumps attempts ──────────────────────────────────────────────


def test_l1_4_bumps_attempts_first_call(backlog: Path) -> None:
    apply_restrategize(backlog, "p")
    assert _by_id(backlog, "p")["attempts"] == 1


def test_l1_4_bumps_attempts_second_call_after_re_decompose(tmp_path: Path) -> None:
    """Apply restrategize → re-add children (simulating a new
    decompose round) → restrategize again. attempts: 0→1→2."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _parent_with_three_children())
    apply_restrategize(p, "p")
    assert _by_id(p, "p")["attempts"] == 1

    # Manually re-add children to simulate a new decompose_node call
    data = yaml.safe_load(p.read_text())
    parent = next(it for it in data["sorry_items"] if it["id"] == "p")
    parent["state"] = "INACTIVE_WAIT"
    parent["children"] = ["p.t1"]
    parent["stuck_rounds"] = 3
    data["sorry_items"].append({
        "id": "p.t1", "file": "X.lean", "line": 25, "theorem": "t1_thm",
        "type": "ready", "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": "p",
        "history_log": [], "stuck_rounds": 3, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
    })
    p.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))

    apply_restrategize(p, "p")
    assert _by_id(p, "p")["attempts"] == 2


# ── L1.6 locked-signature invariant ──────────────────────────────────


def test_l1_6_protected_fields_byte_identical(backlog: Path) -> None:
    """The fields that DEFINE the parent's locked identity must be
    byte-identical post-restrategize. State, children, stuck_rounds,
    attempts, history_log are EXPECTED to change (allow-listed)."""
    pre = dict(_by_id(backlog, "p"))
    apply_restrategize(backlog, "p")
    post = _by_id(backlog, "p")
    PROTECTED = ("id", "file", "line", "theorem", "type", "depth",
                 "priority", "estimated_lines", "dependencies", "unlocks",
                 "parent_id", "references", "coverage_state")
    for k in PROTECTED:
        assert post.get(k) == pre.get(k), (
            f"protected field {k} changed: {pre.get(k)!r} → {post.get(k)!r}"
        )


# ── L1.7 history entry shape ─────────────────────────────────────────


def test_l1_7_history_entry_byte_format(backlog: Path) -> None:
    """The retreat_reason string is the load-bearing 'this is a
    restrategize event' marker. Byte-format must be:
    'restrategize: cleared N children, M proved'"""
    apply_restrategize(backlog, "p")
    p = _by_id(backlog, "p")
    assert len(p["history_log"]) == 1
    h = p["history_log"][0]
    assert h["iteration"] == 1
    assert h["decomposition"] == ["p.s1", "p.s2", "p.s3"]
    # p.s1 was DONE in fixture → 1 proved
    assert h["retreat_reason"] == "restrategize: cleared 3 children, 1 proved"
    assert h["used_references"] == []
    assert h["used_assumptions"] == []
    # decision_reason absent (unlike retreat which carries free-text)
    assert "decision_reason" not in h


def test_l1_7_iteration_continues_across_retreat(tmp_path: Path) -> None:
    """history_log is the union of retreat + restrategize events.
    Iteration counter advances across both."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    # Pre-seed history_log with one prior retreat entry
    items[0]["history_log"] = [{
        "iteration": 1, "decomposition": ["p.old"],
        "results": [], "used_references": [], "used_assumptions": [],
        "retreat_reason": "old retreat",
    }]
    _write_backlog(p, items)
    apply_restrategize(p, "p")
    h = _by_id(p, "p")["history_log"]
    assert len(h) == 2
    assert h[0]["iteration"] == 1
    assert h[1]["iteration"] == 2


# ── L1.8 proved children captured ────────────────────────────────────


def test_l1_8_only_done_children_in_results(backlog: Path) -> None:
    """Fixture: p.s1 = DONE, p.s2 / p.s3 = INITIALIZED. Only s1 in
    results. INITIALIZED/ACTIVE_PROVING children get CLEARED but NOT
    recorded as proved."""
    apply_restrategize(backlog, "p")
    h = _by_id(backlog, "p")["history_log"][0]
    assert len(h["results"]) == 1
    assert h["results"][0] == {"sub_problem_id": "p.s1", "status": "proved"}


def test_l1_8_no_proved_children(tmp_path: Path) -> None:
    """All children INITIALIZED → results is empty array."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    items[1]["state"] = "INITIALIZED"  # was DONE
    items[1].pop("done_reason", None)
    _write_backlog(p, items)
    apply_restrategize(p, "p")
    h = _by_id(p, "p")["history_log"][0]
    assert h["results"] == []
    assert h["retreat_reason"] == "restrategize: cleared 3 children, 0 proved"


# ── L1.9 file mode preservation ──────────────────────────────────────


def test_l1_9_preserves_file_mode_644(backlog: Path) -> None:
    os.chmod(backlog, 0o644)
    apply_restrategize(backlog, "p")
    assert (os.stat(backlog).st_mode & 0o777) == 0o644


def test_l1_9_preserves_unusual_mode(backlog: Path) -> None:
    os.chmod(backlog, 0o600)
    apply_restrategize(backlog, "p")
    assert (os.stat(backlog).st_mode & 0o777) == 0o600


# ── L1.10 flock — concurrent restrategize serializes ─────────────────


def _spawn_restrategize(p: str, parent: str) -> int:
    """Subprocess wrapper for concurrent test."""
    try:
        from restrategize_node import apply_restrategize as _apply
        _apply(Path(p), parent)
        return 0
    except ValueError:
        return 2


def test_l1_10_concurrent_restrategize_serializes(tmp_path: Path) -> None:
    """Two processes calling restrategize on different parents
    interleave under flock without corrupting yaml. Test mirrors slice
    2's test_flock_serializes_concurrent_retreats."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    # Add a second independent parent
    items.extend([
        {
            "id": "q", "file": "Y.lean", "line": 1,
            "theorem": "q_thm", "type": "blocked",
            "depth": 0, "priority": 50, "estimated_lines": 100,
            "dependencies": [], "unlocks": [],
            "state": "INACTIVE_WAIT", "children": ["q.s1"],
            "parent_id": None, "history_log": [],
            "stuck_rounds": 3, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
        },
        {
            "id": "q.s1", "file": "Y.lean", "line": 5,
            "theorem": "q_s1_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "q",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
        },
    ])
    _write_backlog(p, items)

    p1 = Process(target=_spawn_restrategize, args=(str(p), "p"))
    p2 = Process(target=_spawn_restrategize, args=(str(p), "q"))
    p1.start()
    p2.start()
    p1.join(timeout=10)
    p2.join(timeout=10)
    assert p1.exitcode == 0 and p2.exitcode == 0

    final = yaml.safe_load(p.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    # Both parents now INITIALIZED with attempts=1
    assert by_id["p"]["state"] == "INITIALIZED"
    assert by_id["p"]["attempts"] == 1
    assert by_id["q"]["state"] == "INITIALIZED"
    assert by_id["q"]["attempts"] == 1
    # Yaml is well-formed (no torn writes)
    assert "schema_version" in final


# ── L1.11 milestone payload via subprocess ───────────────────────────


def test_l1_11_milestone_invariant_via_subprocess(
    backlog: Path, sandbox: Path
) -> None:
    result = subprocess.run(
        [
            "python3", str(RESTRAT),
            "--parent-id", "p",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr

    events = sandbox / "events.jsonl"
    assert events.is_file()
    milestones = [
        json.loads(l) for l in events.read_text().strip().splitlines()
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    rs = [m for m in milestones if m.get("name") == "restrategize-triggered"]
    assert len(rs) == 1
    payload = rs[0]["details"]
    # Payload schema (per spec §4)
    assert payload["parent_id"] == "p"
    assert payload["iteration"] == 1
    assert payload["attempts"] == 1
    assert payload["decomposition"] == ["p.s1", "p.s2", "p.s3"]
    assert payload["proved_children"] == ["p.s1"]
    # Spec §4 invariant (post-fixup): cleared count == decomposition count
    assert payload["cleared_children_count"] == 3
    assert payload["cleared_children_count"] == len(payload["decomposition"])


# ── L1.12 unrelated siblings preserved ───────────────────────────────


def test_l1_12_unrelated_top_level_sibling_preserved(tmp_path: Path) -> None:
    """A top-level sibling of `p` (not in p's tree) must survive
    restrategize on p untouched in its DEFINING fields."""
    p = tmp_path / "b.yaml"
    items = _parent_with_three_children()
    items.append({
        "id": "sibling", "file": "Z.lean", "line": 1,
        "theorem": "sibling_thm", "type": "ready", "depth": 0,
        "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
    })
    _write_backlog(p, items)

    pre_sibling = dict(_by_id(p, "sibling"))
    apply_restrategize(p, "p")
    post_sibling = _by_id(p, "sibling")

    DEFINING = ("id", "file", "line", "theorem", "type", "depth",
                "priority", "estimated_lines", "dependencies", "unlocks",
                "state", "children", "parent_id", "history_log",
                "stuck_rounds", "attempts")
    for k in DEFINING:
        assert post_sibling.get(k) == pre_sibling.get(k), (
            f"sibling field {k} perturbed: {pre_sibling.get(k)!r} → {post_sibling.get(k)!r}"
        )


# ── _build_history_entry unit tests ──────────────────────────────────


def test_build_history_entry_no_proved() -> None:
    e = _build_history_entry(iteration=1, decomposition=["a", "b"], proved_children=[])
    assert e["retreat_reason"] == "restrategize: cleared 2 children, 0 proved"
    assert e["results"] == []


def test_build_history_entry_some_proved() -> None:
    e = _build_history_entry(
        iteration=2, decomposition=["a", "b", "c"], proved_children=["b"],
    )
    assert e["retreat_reason"] == "restrategize: cleared 3 children, 1 proved"
    assert e["results"] == [{"sub_problem_id": "b", "status": "proved"}]


def test_module_present_marker() -> None:
    assert True

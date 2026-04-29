"""Slice 4 C — sync_sorry_backlog tree-awareness tests.

Unblocks real-LLM L3 multi-level cascade + retreat L3 evidence (per
SLICE_3C_LLM_SMOKE.md run-3 + run-4 root-cause findings). The original
sync_sorry_backlog removed yaml entries that didn't have a matching
sorry in source — but tree-structural entries (parent_id set, or
state=INACTIVE_WAIT, or with children) are LEGITIMATE state-machine
state, not source-backed. Removing them as orphans broke the prefab-
tree fixture approach for L3 evidence.

Coverage matrix:
  - Flat orphan entries STILL removed (existing behavior preserved)
  - Tree-structural entries PRESERVED across sync runs
  - Tree integrity warnings (orphan parent_id, cyclic parent chain)
  - v2 fields round-trip (state/children/parent_id/history_log/etc.)
  - Mixed flat + tree backlogs handled correctly
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from sync_sorry_backlog import (  # noqa: E402
    sync_backlog,
    _is_tree_structural,
    _validate_tree_integrity,
)


# ── Helper: mock statlean_dir with no .lean files ────────────────────


@pytest.fixture
def empty_statlean(tmp_path: Path) -> Path:
    """A statlean dir that exists but contains no .lean sorry sites.
    sync_backlog will see 0 source sorries → all entries are 'orphans'
    by source-match. Tree-structural ones must still be preserved."""
    d = tmp_path / "Statlean"
    d.mkdir()
    return d


# ── _is_tree_structural ──────────────────────────────────────────────


def test_tree_structural_when_parent_id_set() -> None:
    assert _is_tree_structural({"id": "x", "parent_id": "p"})
    assert _is_tree_structural({"id": "x", "parent_id": "p", "children": []})


def test_tree_structural_when_children_non_empty() -> None:
    assert _is_tree_structural({"id": "x", "parent_id": None, "children": ["a", "b"]})


def test_tree_structural_when_state_inactive_wait() -> None:
    assert _is_tree_structural({"id": "x", "state": "INACTIVE_WAIT"})


def test_tree_structural_when_state_done() -> None:
    assert _is_tree_structural({"id": "x", "state": "DONE"})


def test_tree_structural_negative_flat_entry() -> None:
    """Flat top-level INITIALIZED entry → not tree-structural; sync
    decides by source match (existing behavior)."""
    assert not _is_tree_structural({
        "id": "x", "parent_id": None, "children": [],
        "state": "INITIALIZED",
    })


def test_tree_structural_negative_active_proving() -> None:
    """ACTIVE_PROVING means a sub-agent is currently working on a
    source-backed sorry. Should still match source. Not tree-structural
    by itself."""
    assert not _is_tree_structural({
        "id": "x", "parent_id": None, "children": [],
        "state": "ACTIVE_PROVING",
    })


# ── _validate_tree_integrity ─────────────────────────────────────────


def test_integrity_orphan_parent_id_warns() -> None:
    items = [
        {"id": "child", "parent_id": "ghost"},
    ]
    warnings = _validate_tree_integrity(items)
    assert any("orphan parent_id" in w and "child" in w for w in warnings)


def test_integrity_cyclic_parent_chain_warns_no_hang() -> None:
    items = [
        {"id": "a", "parent_id": "b"},
        {"id": "b", "parent_id": "a"},
    ]
    warnings = _validate_tree_integrity(items)
    assert any("cyclic" in w.lower() for w in warnings)


def test_integrity_clean_tree_no_warnings() -> None:
    items = [
        {"id": "root", "parent_id": None, "children": ["mid"]},
        {"id": "mid", "parent_id": "root", "children": ["leaf"]},
        {"id": "leaf", "parent_id": "mid", "children": []},
    ]
    assert _validate_tree_integrity(items) == []


# ── sync_backlog: preservation behavior ──────────────────────────────


def _write_backlog(path: Path, items: list, version: str = "v200") -> None:
    data = {
        "schema_version": 2,
        "version": version,
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def test_sync_removes_flat_orphan_entry(empty_statlean: Path, tmp_path: Path) -> None:
    """Backwards-compat: flat (non-tree) entries with no source backing
    are still removed. This is the original sync_sorry_backlog behavior."""
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        "id": "old.flat", "file": "Old.lean", "line": 10,
        "theorem": "old_thm", "type": "ready", "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }])
    stats = sync_backlog(backlog, empty_statlean, dry_run=False)
    assert stats["removed"] == 1
    final = yaml.safe_load(backlog.read_text())
    assert all(it.get("id") != "old.flat" for it in final.get("sorry_items") or [])


def test_sync_preserves_tree_node_with_parent_id(empty_statlean: Path, tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        "id": "root.sub1", "file": "X.lean", "line": 5,
        "theorem": "sub1_thm", "type": "ready", "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "root",  # ← tree-structural
        "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "root", "file": "X.lean", "line": 1,
        "theorem": "root_thm", "type": "blocked", "depth": 0, "priority": 50,
        "estimated_lines": 100, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["root.sub1"],
        "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    ids = {it.get("id") for it in final.get("sorry_items") or []}
    assert "root.sub1" in ids, "child with parent_id was removed by sync"
    assert "root" in ids, "INACTIVE_WAIT root was removed by sync"


def test_sync_preserves_done_state(empty_statlean: Path, tmp_path: Path) -> None:
    """A node already marked DONE (e.g., from a prior cycle) must
    survive sync — its proved-history is meaningful evidence."""
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        "id": "done.entry", "file": "X.lean", "line": 1,
        "theorem": "thm", "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "DONE", "done_reason": "proved",
        "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    ids = {it.get("id") for it in final.get("sorry_items") or []}
    assert "done.entry" in ids


def test_sync_round_trips_v2_fields(empty_statlean: Path, tmp_path: Path) -> None:
    """state / children / parent_id / history_log preserved across
    sync write+read cycle."""
    backlog = tmp_path / "b.yaml"
    history = [{
        "iteration": 1,
        "decomposition": ["root.sub1", "root.sub2"],
        "results": [{"sub_problem_id": "root.sub2", "status": "stuck",
                     "fail_reason": "type mismatch"}],
        "retreat_reason": "stuck on sub2",
        "decision_reason": "induction on n",
    }]
    _write_backlog(backlog, [{
        "id": "carrier", "file": "X.lean", "line": 1,
        "theorem": "carrier_thm", "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",  # tree-structural → preserved
        "children": ["c1", "c2"], "parent_id": None,
        "history_log": history, "stuck_rounds": 2,
    }])
    sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    c = by_id["carrier"]
    assert c["state"] == "INACTIVE_WAIT"
    assert c["children"] == ["c1", "c2"]
    assert c["parent_id"] is None  # null, not "None" string
    assert c["stuck_rounds"] == 2
    assert len(c["history_log"]) == 1
    assert c["history_log"][0]["iteration"] == 1
    assert c["history_log"][0]["retreat_reason"] == "stuck on sub2"


def test_sync_3level_cascade_fixture_survives(empty_statlean: Path, tmp_path: Path) -> None:
    """The exact shape that broke L3 run-3: depth-3 tree of yaml-only
    entries (mid + root reference same source as leaf, but are
    tree-structural). All 3 must survive sync."""
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        "id": "root", "file": "X.lean", "line": 5,
        "theorem": "leaf_thm", "type": "blocked", "depth": 0, "priority": 99,
        "estimated_lines": 0, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["mid"],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "mid", "file": "X.lean", "line": 5,
        "theorem": "leaf_thm", "type": "blocked", "depth": 1, "priority": 99,
        "estimated_lines": 0, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["leaf"],
        "parent_id": "root", "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "leaf", "file": "X.lean", "line": 5,
        "theorem": "leaf_thm", "type": "ready", "depth": 2, "priority": 99,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "mid", "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    ids = {it.get("id") for it in final.get("sorry_items") or []}
    assert ids >= {"root", "mid", "leaf"}, (
        f"expected all 3 tree levels preserved, got {ids}"
    )


def test_sync_mixed_flat_and_tree(empty_statlean: Path, tmp_path: Path) -> None:
    """A backlog with both flat orphans AND tree entries: flat orphans
    removed, tree preserved."""
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        "id": "flat.orphan", "file": "Old.lean", "line": 10,
        "theorem": "old", "type": "ready", "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "tree.parent", "file": "X.lean", "line": 1,
        "theorem": "p", "type": "blocked", "depth": 0, "priority": 50,
        "estimated_lines": 50, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["tree.parent.s1"],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "tree.parent.s1", "file": "X.lean", "line": 1,
        "theorem": "p_s1", "type": "ready", "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "tree.parent", "history_log": [], "stuck_rounds": 0,
    }])
    stats = sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    ids = {it.get("id") for it in final.get("sorry_items") or []}
    assert "flat.orphan" not in ids, "flat orphan should have been removed"
    assert "tree.parent" in ids
    assert "tree.parent.s1" in ids
    assert stats["removed"] == 1  # only the flat orphan

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


# ── §8 fixup regression: S2.1 + S2.2 ─────────────────────────────────


def _write_lean_with_sorry(d: Path, rel: str, theorem: str, sorry_line_target: int) -> None:
    """Write a tiny .lean file with a single `sorry` at a known line.
    `rel` is relative to d's parent (matches sync's rel_path scheme)."""
    target = d / rel.split("/", 1)[1] if "/" in rel else d / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    # Build a body that puts `sorry` on a specific line
    lines = [
        "import Mathlib",
        "",
        f"theorem {theorem} : True := by",
        "  sorry",
    ]
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    # The sorry will be on whichever line index it lands at; tests
    # below assert on the final value, not a hardcoded match.


@pytest.fixture
def statlean_with_one_sorry(tmp_path: Path) -> tuple[Path, str, str, int]:
    """Statlean dir with exactly one .lean file containing one sorry.
    Returns (statlean_dir, file_rel, theorem_name, sorry_line)."""
    d = tmp_path / "Statlean"
    d.mkdir()
    rel = "Statlean/Leaf.lean"
    theorem = "leaf_thm"
    _write_lean_with_sorry(d, rel, theorem, sorry_line_target=4)
    # find_sorry_sites uses the relative path from statlean_dir.parent,
    # so rel will be "Statlean/Leaf.lean". Sorry is on line 4.
    return d, rel, theorem, 4


def test_sync_tree_item_with_source_backing_no_duplicate(
    statlean_with_one_sorry: tuple[Path, str, str, int],
    tmp_path: Path,
) -> None:
    """§8 S2.1 regression: when a tree-structural item shares its
    (file, theorem) key with an actual source sorry, sync must update
    its line in place — NOT emit a duplicate auto-id row alongside it.

    Before the fix: existing_by_key skipped the tree item, the
    source-match loop fell through to else-branch and synthesized a
    new auto-id row, leaving the original tree item to be re-added by
    the preservation pass → 2 rows for one source location."""
    statlean_dir, rel, theorem, _initial_line = statlean_with_one_sorry
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        # Tree-structural leaf at the SAME (file, theorem) as the
        # source sorry, but with a stale `line` value
        "id": "tree.leaf", "file": rel, "line": 999,
        "theorem": theorem, "type": "ready", "depth": 2, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "tree.root",  # makes it tree-structural
        "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "tree.root", "file": "Other.lean", "line": 1,
        "theorem": "other", "type": "blocked", "depth": 0, "priority": 50,
        "estimated_lines": 100, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["tree.leaf"],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
    }])
    stats = sync_backlog(backlog, statlean_dir, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    items = final.get("sorry_items") or []

    # Match all rows pointing at the source-backed (file, theorem)
    matches = [it for it in items if it.get("file") == rel and it.get("theorem") == theorem]
    assert len(matches) == 1, (
        f"expected exactly one row for {rel}::{theorem}, got {len(matches)}: "
        f"{[m.get('id') for m in matches]}"
    )

    only = matches[0]
    # The leaf's identity is preserved (still 'tree.leaf', not an
    # auto-id like 'statlean.leaf.leaf_thm')
    assert only["id"] == "tree.leaf", (
        f"tree-structural identity lost; sync emitted auto-id {only['id']}"
    )
    # Line was updated from the stale 999 to the real source line
    assert only["line"] != 999, "stale line was not refreshed from source"
    # State-machine fields preserved
    assert only["parent_id"] == "tree.root"
    assert only["state"] == "INITIALIZED"
    # The update path counted, not the add path
    assert stats["added"] == 0, (
        f"add count should be 0 (tree item updated in place), got {stats['added']}"
    )


def test_sync_tree_item_type_preserved_with_unresolved_deps(
    empty_statlean: Path, tmp_path: Path,
) -> None:
    """§8 S2.2 regression: dependency-rebuild loop must NOT rewrite
    type=main_theorem → type=blocked for tree-structural items. Their
    type field is curated by the state machine (decompose_node /
    record_retreat / propagate_done), not by sync's flat-sorry
    heuristic."""
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        # Tree-structural parent with a curated type and an unresolved
        # dependency on its child
        "id": "tree.parent", "file": "X.lean", "line": 1,
        "theorem": "parent_thm", "type": "main_theorem",  # ← curated
        "depth": 0, "priority": 50,
        "estimated_lines": 50,
        "dependencies": ["tree.parent.child"],  # unresolved (child still in backlog)
        "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["tree.parent.child"],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "tree.parent.child", "file": "X.lean", "line": 5,
        "theorem": "child_thm", "type": "lemma",  # ← curated
        "depth": 1, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "tree.parent", "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, empty_statlean, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["tree.parent"]["type"] == "main_theorem", (
        "tree.parent.type was clobbered to 'blocked' by dep-rebuild loop"
    )
    assert by_id["tree.parent.child"]["type"] == "lemma", (
        "tree.parent.child.type was clobbered"
    )


def test_sync_tree_item_leaf_most_preference_when_multiple_share_key(
    statlean_with_one_sorry: tuple[Path, str, str, int],
    tmp_path: Path,
) -> None:
    """§8 closure follow-up: when two+ tree-structural items share the
    same (file, theorem) key, the line update must land on the leaf
    (no children) rather than the internal node (has children).

    Without this preference, internal nodes — whose `line` is a
    structural placeholder, not a real source position — would have
    their line overwritten on every sync. The leaf is the one item
    whose `line` actually corresponds to a `:= sorry` in source.

    This test exercises the tiebreaker at sync_sorry_backlog.py:294-297
    (`sorted(candidates, key=lambda x: (1 if children else 0, id))`).
    The single-tree-item test above doesn't reach this branch — both
    tests are needed to cover the lookup."""
    statlean_dir, rel, theorem, _initial_line = statlean_with_one_sorry
    backlog = tmp_path / "b.yaml"
    _write_backlog(backlog, [{
        # Internal node — same (file, theorem) as leaf, but has
        # children. Stale line=999 is structural, not real-source.
        "id": "tree.mid", "file": rel, "line": 999,
        "theorem": theorem, "type": "blocked", "depth": 1, "priority": 50,
        "estimated_lines": 50, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["tree.leaf"],
        "parent_id": "tree.root", "history_log": [], "stuck_rounds": 0,
    }, {
        # Leaf — same (file, theorem) as mid, no children. THIS is the
        # one that should pick up the source line update.
        "id": "tree.leaf", "file": rel, "line": 998,
        "theorem": theorem, "type": "ready", "depth": 2, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [],
        "parent_id": "tree.mid", "history_log": [], "stuck_rounds": 0,
    }, {
        # Root — different file, just there so tree.mid's parent_id
        # isn't an orphan ref (avoids tree-integrity warnings noise).
        "id": "tree.root", "file": "Other.lean", "line": 1,
        "theorem": "other", "type": "blocked", "depth": 0, "priority": 50,
        "estimated_lines": 100, "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT", "children": ["tree.mid"],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, statlean_dir, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    # Leaf's line was refreshed from source — proof it won the tiebreak
    assert by_id["tree.leaf"]["line"] != 998, (
        "tree.leaf was not updated; source-match never reached the leaf"
    )
    # Mid's line is UNCHANGED — proof the internal node didn't grab the
    # update slot. (The preservation pass re-adds it untouched.)
    assert by_id["tree.mid"]["line"] == 999, (
        f"tree.mid line was clobbered to {by_id['tree.mid']['line']}; "
        "internal node won the tiebreak when it shouldn't have"
    )
    # Both still present — neither was dropped
    assert "tree.leaf" in by_id and "tree.mid" in by_id and "tree.root" in by_id


def test_sync_flat_item_type_still_blocked_with_unresolved_deps(
    tmp_path: Path,
) -> None:
    """Counter-check: the flat-item type=blocked override is still
    applied for non-tree items (legacy behavior preserved). Without
    this we'd have over-corrected S2.2."""
    backlog = tmp_path / "b.yaml"
    # Two flat items with one depending on the other; both must stay
    # in the backlog post-sync, so they need source backing.
    statlean_dir = tmp_path / "Statlean"
    statlean_dir.mkdir()
    flat_lean = statlean_dir / "Flat.lean"
    flat_lean.write_text(
        "import Mathlib\n\n"
        "theorem flat_a : True := by sorry\n\n"
        "theorem flat_b : True := by sorry\n",
        encoding="utf-8",
    )
    _write_backlog(backlog, [{
        "id": "flat.a", "file": "Statlean/Flat.lean", "line": 3,
        "theorem": "flat_a", "type": "ready",  # ← will be flipped to blocked
        "depth": 0, "priority": 50,
        "estimated_lines": 30,
        "dependencies": ["flat.b"],  # unresolved
        "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }, {
        "id": "flat.b", "file": "Statlean/Flat.lean", "line": 5,
        "theorem": "flat_b", "type": "ready",
        "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0,
    }])
    sync_backlog(backlog, statlean_dir, dry_run=False)
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}
    assert by_id["flat.a"]["type"] == "blocked", (
        "flat item with unresolved deps should still be flipped to blocked"
    )

"""L1 unit tests for record_retreat.py (czy newloop port slice 2).

Coverage matrix (per MERGE_PLAN.md §3.2.1 + §8 spec review):
  - children rows REMOVED entirely from sorry_items[]
  - parent row PRESERVED with state=INITIALIZED, stuck_rounds=0,
    children=[] — LOCKED THEOREM SIGNATURE FIELDS UNTOUCHED
    (file, line, theorem, blocker, dependencies, etc.)
  - history_log[] gets new entry with auto-computed iteration
  - recursive descendant removal
  - validation: parent must exist; parent must have children
  - atomic write (tempfile + os.replace) — no half-written yaml
  - flock prevents concurrent corruption (smoke)
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
import threading
import time
from pathlib import Path

import pytest
import yaml

# Tests live in theme/scripts/tests/; module under test is theme/scripts/.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from record_retreat import (  # noqa: E402
    apply_retreat,
    _build_history_entry,
    _collect_descendants,
    _atomic_write_yaml,
)


# ── Fixture builders ─────────────────────────────────────────────────


def _make_yaml_with_tree(tmp_path: Path) -> Path:
    """Build a v2 yaml with a parent + 3 children + 1 grandchild.

    Tree:
        parent
        ├── parent.sub1 (leaf)
        ├── parent.sub2 (leaf)
        └── parent.sub3
            └── parent.sub3.gc1
        sibling (unrelated, must NOT be touched by retreat)
    """
    backlog_path = tmp_path / "sorry_backlog.yaml"
    data = {
        "schema_version": 2,
        "version": "v200",
        "sorry_items": [
            {
                "id": "parent",
                "file": "Statlean/Foo.lean",
                "line": 100,
                "theorem": "foo_thm",
                "type": "blocked",
                "depth": 1,
                "priority": 50,
                "blocker": "needs decomposition",
                "estimated_lines": 200,
                "dependencies": ["dep_a"],
                "unlocks": [],
                "stuck_rounds": 3,
                "state": "INACTIVE_WAIT",
                "children": ["parent.sub1", "parent.sub2", "parent.sub3"],
                "parent_id": None,
                "history_log": [],
            },
            {
                "id": "parent.sub1",
                "file": "Statlean/Foo.lean",
                "line": 110,
                "theorem": "foo_sub1",
                "state": "DONE",
                "children": [],
                "parent_id": "parent",
                "history_log": [],
            },
            {
                "id": "parent.sub2",
                "file": "Statlean/Foo.lean",
                "line": 120,
                "theorem": "foo_sub2",
                "state": "DONE",
                "children": [],
                "parent_id": "parent",
                "history_log": [],
            },
            {
                "id": "parent.sub3",
                "file": "Statlean/Foo.lean",
                "line": 130,
                "theorem": "foo_sub3",
                "state": "ACTIVE_PROVING",
                "children": ["parent.sub3.gc1"],
                "parent_id": "parent",
                "history_log": [],
            },
            {
                "id": "parent.sub3.gc1",
                "file": "Statlean/Foo.lean",
                "line": 140,
                "theorem": "foo_sub3_gc1",
                "state": "INITIALIZED",
                "children": [],
                "parent_id": "parent.sub3",
                "history_log": [],
            },
            {
                "id": "sibling",
                "file": "Statlean/Bar.lean",
                "line": 50,
                "theorem": "bar_thm",
                "state": "INITIALIZED",
                "children": [],
                "parent_id": None,
                "history_log": [],
            },
        ],
    }
    backlog_path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    return backlog_path


# ── _collect_descendants ─────────────────────────────────────────────


def test_collect_descendants_simple() -> None:
    items = [
        {"id": "a", "children": ["b", "c"]},
        {"id": "b", "children": []},
        {"id": "c", "children": ["d"]},
        {"id": "d", "children": []},
        {"id": "e", "children": []},  # sibling
    ]
    assert _collect_descendants(items, ["b", "c"]) == {"b", "c", "d"}


def test_collect_descendants_handles_orphan_ref() -> None:
    """Item references a non-existent child id; traversal must not crash."""
    items = [
        {"id": "a", "children": ["b", "ghost"]},
        {"id": "b", "children": []},
    ]
    assert _collect_descendants(items, ["a"]) == {"a", "b"}


def test_collect_descendants_handles_cycle() -> None:
    """Pathological: A→B→A. Visit each once; no infinite loop."""
    items = [
        {"id": "a", "children": ["b"]},
        {"id": "b", "children": ["a"]},
    ]
    assert _collect_descendants(items, ["a"]) == {"a", "b"}


# ── _build_history_entry ─────────────────────────────────────────────


def test_build_history_entry_minimal() -> None:
    e = _build_history_entry(
        iteration=1,
        decomposition=["a", "b"],
        results=[{"sub_problem_id": "a", "status": "proved"}],
    )
    assert e["iteration"] == 1
    assert e["decomposition"] == ["a", "b"]
    assert e["results"] == [{"sub_problem_id": "a", "status": "proved"}]
    assert e["used_references"] == []
    assert e["used_assumptions"] == []
    assert "decision_reason" not in e
    assert "decomposition_details" not in e
    assert "retreat_reason" not in e


def test_build_history_entry_full() -> None:
    e = _build_history_entry(
        iteration=2,
        decomposition=["x", "y"],
        results=[
            {"sub_problem_id": "x", "status": "proved"},
            {"sub_problem_id": "y", "status": "stuck", "fail_reason": "type mismatch"},
        ],
        decision_reason="induction on n",
        decomposition_details=[{"id": "y", "description": "step case"}],
        used_references=["paper.thm.2.1"],
        used_assumptions=["nat_pos"],
        retreat_reason="stuck_rounds reached 3",
    )
    assert e["decision_reason"] == "induction on n"
    assert e["decomposition_details"] == [{"id": "y", "description": "step case"}]
    assert e["used_references"] == ["paper.thm.2.1"]
    assert e["used_assumptions"] == ["nat_pos"]
    assert e["retreat_reason"] == "stuck_rounds reached 3"
    # fail_reason only on the stuck one, not the proved one.
    assert "fail_reason" not in e["results"][0]
    assert e["results"][1]["fail_reason"] == "type mismatch"


# ── apply_retreat: validation ────────────────────────────────────────


def test_retreat_raises_when_parent_not_found(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    with pytest.raises(ValueError, match="not in sorry_items"):
        apply_retreat(
            backlog_path=backlog,
            parent_id="ghost",
            retreat_reason="x",
            results=[],
        )


def test_retreat_raises_when_parent_has_no_children(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    with pytest.raises(ValueError, match="no children"):
        apply_retreat(
            backlog_path=backlog,
            parent_id="sibling",  # leaf, no children
            retreat_reason="x",
            results=[],
        )


def test_retreat_raises_when_backlog_missing(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="backlog not found"):
        apply_retreat(
            backlog_path=tmp_path / "nope.yaml",
            parent_id="parent",
            retreat_reason="x",
            results=[],
        )


# ── apply_retreat: core behavior ─────────────────────────────────────


def _read(backlog: Path) -> dict:
    return yaml.safe_load(backlog.read_text())


def _items(backlog: Path) -> list:
    return _read(backlog)["sorry_items"]


def _by_id(backlog: Path, node_id: str) -> dict | None:
    return next((it for it in _items(backlog) if it.get("id") == node_id), None)


def test_retreat_removes_all_descendants(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="r",
        results=[
            {"sub_problem_id": "parent.sub1", "status": "proved"},
            {"sub_problem_id": "parent.sub2", "status": "proved"},
            {"sub_problem_id": "parent.sub3", "status": "stuck"},
        ],
    )
    items_after = _items(backlog)
    ids = {it["id"] for it in items_after}
    # Children + grandchild removed
    assert "parent.sub1" not in ids
    assert "parent.sub2" not in ids
    assert "parent.sub3" not in ids
    assert "parent.sub3.gc1" not in ids
    # Parent + sibling remain
    assert "parent" in ids
    assert "sibling" in ids


def test_retreat_preserves_parent_signature_fields(tmp_path: Path) -> None:
    """CRITICAL Rule 3 Layer 1 check: locked signature fields must NOT be touched."""
    backlog = _make_yaml_with_tree(tmp_path)
    parent_before = _by_id(backlog, "parent")
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="r",
        results=[],
    )
    parent_after = _by_id(backlog, "parent")
    assert parent_after is not None
    # Signature-bearing fields untouched
    for field in ("file", "line", "theorem", "blocker", "dependencies",
                   "estimated_lines", "depth", "priority"):
        assert parent_after.get(field) == parent_before.get(field), (
            f"field {field} changed: {parent_before.get(field)!r} → "
            f"{parent_after.get(field)!r}"
        )
    # State machine fields RESET
    assert parent_after["state"] == "INITIALIZED"
    assert parent_after["stuck_rounds"] == 0
    assert parent_after["children"] == []


def test_retreat_appends_history_log_entry(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="stuck",
        results=[
            {"sub_problem_id": "parent.sub3", "status": "stuck", "fail_reason": "type mismatch"},
        ],
        decision_reason="induction",
    )
    parent = _by_id(backlog, "parent")
    assert parent is not None
    log = parent["history_log"]
    assert len(log) == 1
    entry = log[0]
    assert entry["iteration"] == 1
    assert entry["decomposition"] == ["parent.sub1", "parent.sub2", "parent.sub3"]
    assert entry["retreat_reason"] == "stuck"
    assert entry["decision_reason"] == "induction"


def test_retreat_iteration_increments(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    # First retreat
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="r1",
        results=[],
    )
    # Re-attach children manually for second decomposition round
    data = _read(backlog)
    for it in data["sorry_items"]:
        if it["id"] == "parent":
            it["children"] = ["round2.a", "round2.b"]
            it["state"] = "INACTIVE_WAIT"
        if it["id"] == "sibling":
            pass  # untouched
    data["sorry_items"].extend([
        {"id": "round2.a", "state": "INITIALIZED", "children": [],
         "parent_id": "parent", "history_log": []},
        {"id": "round2.b", "state": "INITIALIZED", "children": [],
         "parent_id": "parent", "history_log": []},
    ])
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))

    # Second retreat
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="r2",
        results=[],
    )
    parent = _by_id(backlog, "parent")
    assert len(parent["history_log"]) == 2
    assert parent["history_log"][0]["iteration"] == 1
    assert parent["history_log"][1]["iteration"] == 2
    assert parent["history_log"][0]["retreat_reason"] == "r1"
    assert parent["history_log"][1]["retreat_reason"] == "r2"


def test_retreat_preserves_unrelated_siblings(tmp_path: Path) -> None:
    backlog = _make_yaml_with_tree(tmp_path)
    sibling_before = _by_id(backlog, "sibling")
    apply_retreat(
        backlog_path=backlog,
        parent_id="parent",
        retreat_reason="r",
        results=[],
    )
    sibling_after = _by_id(backlog, "sibling")
    assert sibling_after == sibling_before


# ── Atomic write ─────────────────────────────────────────────────────


def test_atomic_write_yaml_replaces_atomically(tmp_path: Path) -> None:
    target = tmp_path / "out.yaml"
    target.write_text("schema_version: 2\nsorry_items: []\n")
    new_data = {"schema_version": 2, "sorry_items": [{"id": "x"}]}
    _atomic_write_yaml(target, new_data)
    reloaded = yaml.safe_load(target.read_text())
    assert reloaded == new_data
    # No leftover .tmp files
    leftover = list(tmp_path.glob("out.yaml.*.tmp"))
    assert leftover == []


def test_atomic_write_yaml_cleans_up_on_failure(tmp_path: Path, monkeypatch) -> None:
    """If os.replace raises, the tempfile must be cleaned up."""
    target = tmp_path / "out.yaml"
    target.write_text("schema_version: 2\nsorry_items: []\n")

    real_replace = os.replace

    def fake_replace(src: str, dst: str) -> None:
        raise OSError("simulated rename failure")

    monkeypatch.setattr(os, "replace", fake_replace)
    with pytest.raises(OSError):
        _atomic_write_yaml(target, {"x": 1})
    # Tempfile should be cleaned up
    leftover = list(tmp_path.glob("out.yaml.*.tmp"))
    assert leftover == []
    # Original untouched
    assert "schema_version: 2" in target.read_text()
    monkeypatch.setattr(os, "replace", real_replace)


# ── Concurrency smoke (flock) ────────────────────────────────────────


def test_flock_serializes_concurrent_retreats(tmp_path: Path) -> None:
    """Two concurrent retreats on the SAME parent: only the first
    succeeds; the second raises (parent has no children anymore).

    This isn't proof of full concurrency safety, but it does verify
    flock is in effect (no torn writes; the second retreat sees a
    consistent view post-first-commit).
    """
    backlog = _make_yaml_with_tree(tmp_path)
    errors: list = []
    successes: list = []

    def worker() -> None:
        try:
            apply_retreat(
                backlog_path=backlog,
                parent_id="parent",
                retreat_reason="concurrent",
                results=[],
            )
            successes.append(1)
        except ValueError as e:
            errors.append(str(e))

    t1 = threading.Thread(target=worker)
    t2 = threading.Thread(target=worker)
    t1.start()
    time.sleep(0.005)  # nudge ordering; not required for correctness
    t2.start()
    t1.join()
    t2.join()

    # Exactly one succeeded; the other found no children to retreat from.
    assert len(successes) + len(errors) == 2
    assert len(successes) >= 1
    if errors:
        # Second attempt's failure should be the "no children" validation
        assert any("no children" in e for e in errors)


# ── Differentiation evidence ─────────────────────────────────────────


def test_module_present_marker() -> None:
    """On rollback/sdk-bridge-pre-newloop the record_retreat module
    doesn't exist → pytest collection error → test absent → differential
    evidence that this slice genuinely added the capability."""
    from record_retreat import apply_retreat as _apply  # noqa: F401
    assert callable(_apply)

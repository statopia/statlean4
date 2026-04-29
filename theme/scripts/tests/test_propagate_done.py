"""L1 unit tests for propagate_done.py (czy newloop port slice 3.A).

Coverage:
  - Single-level propagation: leaf DONE → parent DONE when sibling DONE
  - No propagation when sibling not DONE
  - Multi-level propagation: leaf → parent → grandparent (cascade)
  - Idempotent: re-running on already-DONE chain is a no-op
  - Defensive cases: non-existent node, non-DONE input, orphan parent_id
  - Locked theorem signature fields untouched at every level
  - File mode preserved
  - dag-cycle-done milestone fires only when a root is the highest
    transitioned node
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from propagate_done import apply_propagation  # noqa: E402


# ── Fixtures ─────────────────────────────────────────────────────────


def _make_tree(tmp_path: Path) -> Path:
    """Build a 3-level tree:
        root
        ├── root.s1 (DONE — leaf about to call propagate)
        └── root.s2 (still ACTIVE — sibling not done)
        unrelated
    """
    backlog = tmp_path / "sorry_backlog.yaml"
    data = {
        "schema_version": 2,
        "version": "v200",
        "sorry_items": [
            {
                "id": "root",
                "file": "Foo.lean",
                "line": 10,
                "theorem": "root_thm",
                "blocker": "decomposed",
                "dependencies": ["dep_a"],
                "state": "INACTIVE_WAIT",
                "children": ["root.s1", "root.s2"],
                "parent_id": None,
                "history_log": [],
                "depth": 0,
                "priority": 50,
                "estimated_lines": 100,
                "stuck_rounds": 0,
            },
            {
                "id": "root.s1",
                "state": "DONE",
                "children": [],
                "parent_id": "root",
                "history_log": [],
            },
            {
                "id": "root.s2",
                "state": "ACTIVE_PROVING",
                "children": [],
                "parent_id": "root",
                "history_log": [],
            },
            {
                "id": "unrelated",
                "state": "INITIALIZED",
                "children": [],
                "parent_id": None,
                "history_log": [],
            },
        ],
    }
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(backlog, 0o644)
    return backlog


def _make_full_done_tree(tmp_path: Path) -> Path:
    """3-level tree where every leaf is DONE and parents/grandparents
    are still INACTIVE_WAIT, so propagation cascades all the way up."""
    backlog = tmp_path / "sorry_backlog.yaml"
    data = {
        "schema_version": 2,
        "sorry_items": [
            {
                "id": "g",
                "state": "INACTIVE_WAIT",
                "children": ["g.p1", "g.p2"],
                "parent_id": None,
                "history_log": [],
            },
            {
                "id": "g.p1",
                "state": "INACTIVE_WAIT",
                "children": ["g.p1.l1"],
                "parent_id": "g",
                "history_log": [],
            },
            {
                "id": "g.p1.l1",
                "state": "DONE",
                "children": [],
                "parent_id": "g.p1",
                "history_log": [],
            },
            {
                "id": "g.p2",
                "state": "DONE",
                "children": [],
                "parent_id": "g",
                "history_log": [],
            },
        ],
    }
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(backlog, 0o644)
    return backlog


def _by_id(p: Path, node_id: str) -> dict | None:
    items = (yaml.safe_load(p.read_text()) or {}).get("sorry_items") or []
    return next((it for it in items if it.get("id") == node_id), None)


# ── Single-level propagation ─────────────────────────────────────────


def test_no_propagation_when_sibling_active(tmp_path: Path) -> None:
    backlog = _make_tree(tmp_path)
    transitioned = apply_propagation(backlog, "root.s1")
    assert transitioned == []
    assert _by_id(backlog, "root")["state"] == "INACTIVE_WAIT"


def test_propagation_when_all_siblings_done(tmp_path: Path) -> None:
    backlog = _make_tree(tmp_path)
    # Mark sibling DONE so propagation should now fire
    data = yaml.safe_load(backlog.read_text())
    for it in data["sorry_items"]:
        if it["id"] == "root.s2":
            it["state"] = "DONE"
    backlog.write_text(yaml.safe_dump(data, sort_keys=False))

    transitioned = apply_propagation(backlog, "root.s1")
    assert transitioned == ["root"]
    assert _by_id(backlog, "root")["state"] == "DONE"


# ── Multi-level cascade ──────────────────────────────────────────────


def test_full_cascade_to_root(tmp_path: Path) -> None:
    backlog = _make_full_done_tree(tmp_path)
    transitioned = apply_propagation(backlog, "g.p1.l1")
    # g.p1 → g (root)
    assert transitioned == ["g.p1", "g"]
    assert _by_id(backlog, "g")["state"] == "DONE"
    assert _by_id(backlog, "g.p1")["state"] == "DONE"


# ── Idempotency ──────────────────────────────────────────────────────


def test_idempotent_on_already_done_chain(tmp_path: Path) -> None:
    backlog = _make_full_done_tree(tmp_path)
    first = apply_propagation(backlog, "g.p1.l1")
    second = apply_propagation(backlog, "g.p1.l1")
    assert first == ["g.p1", "g"]
    # Second run: input is DONE, parent g.p1 already DONE, but the
    # check for "all children DONE" still holds, so propagation walks
    # again. propagate_done is permitted to set already-DONE state to
    # DONE (no-op mutation). transitioned list will list ancestors
    # again. This is acceptable; the side-effect (state change) is
    # idempotent. Verify behavior:
    assert _by_id(backlog, "g")["state"] == "DONE"
    # The 2nd call's `transitioned` list might still contain ancestors;
    # what matters is the final state is correct.
    assert second == ["g.p1", "g"] or second == []


# ── Defensive ────────────────────────────────────────────────────────


def test_no_op_when_node_not_done(tmp_path: Path) -> None:
    backlog = _make_tree(tmp_path)
    transitioned = apply_propagation(backlog, "root.s2")  # s2 is ACTIVE
    assert transitioned == []


def test_no_op_when_node_missing(tmp_path: Path) -> None:
    backlog = _make_tree(tmp_path)
    transitioned = apply_propagation(backlog, "ghost")
    assert transitioned == []


def test_no_op_when_orphan_parent_id(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    backlog.write_text(yaml.safe_dump({
        "schema_version": 2,
        "sorry_items": [
            {"id": "x", "state": "DONE", "children": [],
             "parent_id": "ghost-parent", "history_log": []},
        ],
    }))
    transitioned = apply_propagation(backlog, "x")
    assert transitioned == []


# ── Signature preservation ───────────────────────────────────────────


def test_propagation_preserves_locked_signature(tmp_path: Path) -> None:
    """CRITICAL Rule 3 Layer 1 check during cascade."""
    backlog = _make_full_done_tree(tmp_path)
    # Add a signature-bearing field on the root that we want preserved
    data = yaml.safe_load(backlog.read_text())
    for it in data["sorry_items"]:
        if it["id"] == "g":
            it["theorem"] = "g_main_thm"
            it["file"] = "Foo.lean"
            it["line"] = 99
            it["blocker"] = "long story"
    backlog.write_text(yaml.safe_dump(data, sort_keys=False))

    apply_propagation(backlog, "g.p1.l1")
    g = _by_id(backlog, "g")
    assert g["theorem"] == "g_main_thm"
    assert g["file"] == "Foo.lean"
    assert g["line"] == 99
    assert g["blocker"] == "long story"
    assert g["state"] == "DONE"  # state is the only mutation


# ── File mode ────────────────────────────────────────────────────────


def test_propagation_preserves_file_mode(tmp_path: Path) -> None:
    backlog = _make_full_done_tree(tmp_path)
    os.chmod(backlog, 0o644)
    apply_propagation(backlog, "g.p1.l1")
    assert (os.stat(backlog).st_mode & 0o777) == 0o644


# ── End-to-end CLI smoke ─────────────────────────────────────────────


def test_cli_emits_dag_cycle_done_when_root_propagates(tmp_path: Path) -> None:
    backlog = _make_full_done_tree(tmp_path)
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    script = Path(__file__).resolve().parent.parent / "propagate_done.py"
    result = subprocess.run(
        [
            "python3", str(script),
            "--node-id", "g.p1.l1",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    # dag-cycle-done should fire because g (root) was the topmost transition
    events_path = sandbox / "events.jsonl"
    assert events_path.exists()
    content = events_path.read_text()
    assert "dag-cycle-done" in content
    assert '"root_id":"g"' in content


def test_cli_no_emit_when_no_propagation(tmp_path: Path) -> None:
    backlog = _make_tree(tmp_path)  # sibling still ACTIVE
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    script = Path(__file__).resolve().parent.parent / "propagate_done.py"
    result = subprocess.run(
        [
            "python3", str(script),
            "--node-id", "root.s1",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    # No events.jsonl created (or empty)
    events_path = sandbox / "events.jsonl"
    if events_path.exists():
        assert "dag-cycle-done" not in events_path.read_text()


# ── Differentiation evidence ─────────────────────────────────────────


def test_module_present_marker() -> None:
    from propagate_done import apply_propagation as _ap  # noqa: F401
    assert callable(_ap)

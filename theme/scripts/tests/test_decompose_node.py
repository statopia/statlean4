"""L1 unit tests for decompose_node.py (czy newloop port slice 3.A).

Coverage:
  - Sub-rows inserted with correct defaults (state=INITIALIZED,
    children=[], parent_id=parent.id, history_log=[], stuck_rounds=0,
    depth=parent.depth+1)
  - Parent state → INACTIVE_WAIT, parent.children = new ids
  - Locked theorem signature fields (file/line/theorem/blocker/
    dependencies/etc.) on the parent UNTOUCHED (Rule 3 Layer 1)
  - Validation:
    * parent must exist
    * parent state must be INITIALIZED (not INACTIVE_WAIT/ACTIVE_PROVING/DONE)
    * sub-problem id collision (with existing item) rejected
    * duplicate ids within the request rejected
    * empty sub_problems list rejected
    * missing required field (id) rejected
  - decision_reason persisted as `_pending_decision_reason` for
    later record_retreat consumption
  - File mode preserved (slice 2 fix carries over)
  - End-to-end via subprocess produces the right yaml + emits subtasks-split
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from decompose_node import (  # noqa: E402
    apply_decomposition,
    _build_sub_item,
)


# ── Fixtures ─────────────────────────────────────────────────────────


def _make_v2_yaml(tmp_path: Path) -> Path:
    """Single parent in INITIALIZED state, ready for decomposition."""
    backlog = tmp_path / "sorry_backlog.yaml"
    data = {
        "schema_version": 2,
        "version": "v200",
        "sorry_items": [
            {
                "id": "foo",
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
                "stuck_rounds": 0,
                "state": "INITIALIZED",
                "children": [],
                "parent_id": None,
                "history_log": [],
            },
            {
                "id": "bar",  # unrelated sibling
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
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(backlog, 0o644)
    return backlog


def _read(p: Path) -> dict:
    return yaml.safe_load(p.read_text())


def _items(p: Path) -> list:
    return _read(p)["sorry_items"]


def _by_id(p: Path, node_id: str) -> dict | None:
    return next((it for it in _items(p) if it.get("id") == node_id), None)


# ── _build_sub_item ──────────────────────────────────────────────────


def test_build_sub_item_minimal_inherits_parent_fields() -> None:
    parent = {
        "id": "p",
        "file": "Foo.lean",
        "depth": 2,
    }
    sub = _build_sub_item(parent, {"id": "p.s1"})
    assert sub["id"] == "p.s1"
    assert sub["file"] == "Foo.lean"  # inherited
    assert sub["depth"] == 3  # parent + 1
    assert sub["theorem"] == "p.s1"  # default = id
    assert sub["state"] == "INITIALIZED"
    assert sub["children"] == []
    assert sub["parent_id"] == "p"
    assert sub["history_log"] == []
    assert sub["stuck_rounds"] == 0
    assert sub["source"] == "decomposed from p"


def test_build_sub_item_overrides() -> None:
    parent = {"id": "p", "file": "Foo.lean", "depth": 0}
    sub = _build_sub_item(
        parent,
        {
            "id": "p.s1",
            "file": "OtherFile.lean",
            "line": 42,
            "theorem": "lemma_x",
            "priority": 80,
            "blocker": "needs concept Y",
        },
    )
    assert sub["file"] == "OtherFile.lean"
    assert sub["line"] == 42
    assert sub["theorem"] == "lemma_x"
    assert sub["priority"] == 80
    assert sub["blocker"] == "needs concept Y"


# ── Validation ───────────────────────────────────────────────────────


def test_decompose_raises_when_parent_not_found(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    with pytest.raises(ValueError, match="not in sorry_items"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="ghost",
            sub_problems=[{"id": "ghost.s1"}],
        )


def test_decompose_raises_when_parent_not_initialized(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    # Mutate parent state directly
    data = _read(backlog)
    for it in data["sorry_items"]:
        if it["id"] == "foo":
            it["state"] = "INACTIVE_WAIT"
    backlog.write_text(yaml.safe_dump(data, sort_keys=False))

    with pytest.raises(ValueError, match="only INITIALIZED nodes"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="foo",
            sub_problems=[{"id": "foo.s1"}],
        )


def test_decompose_raises_on_id_collision_with_existing(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    with pytest.raises(ValueError, match="collides with existing"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="foo",
            sub_problems=[{"id": "bar"}],  # bar already in yaml
        )


def test_decompose_raises_on_duplicate_within_request(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    with pytest.raises(ValueError, match="duplicate sub-problem id"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="foo",
            sub_problems=[{"id": "foo.s1"}, {"id": "foo.s1"}],
        )


def test_decompose_raises_on_empty_list(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    with pytest.raises(ValueError, match="non-empty"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="foo",
            sub_problems=[],
        )


def test_decompose_raises_on_missing_id_field(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    with pytest.raises(ValueError, match="missing required field"):
        apply_decomposition(
            backlog_path=backlog,
            parent_id="foo",
            sub_problems=[{"theorem": "no_id"}],
        )


# ── Core behavior ────────────────────────────────────────────────────


def test_decompose_inserts_sub_rows(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    new_ids = apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[
            {"id": "foo.s1", "theorem": "foo_s1", "blocker": "step 1"},
            {"id": "foo.s2", "theorem": "foo_s2", "blocker": "step 2"},
        ],
    )
    assert new_ids == ["foo.s1", "foo.s2"]
    s1 = _by_id(backlog, "foo.s1")
    s2 = _by_id(backlog, "foo.s2")
    assert s1 is not None
    assert s2 is not None
    assert s1["state"] == "INITIALIZED"
    assert s1["parent_id"] == "foo"
    assert s1["children"] == []
    assert s1["history_log"] == []
    assert s1["stuck_rounds"] == 0
    assert s1["depth"] == 2  # parent.depth=1 + 1
    assert s2["theorem"] == "foo_s2"
    assert s2["blocker"] == "step 2"


def test_decompose_mutates_parent_correctly(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[{"id": "foo.s1"}, {"id": "foo.s2"}],
    )
    parent = _by_id(backlog, "foo")
    assert parent is not None
    assert parent["state"] == "INACTIVE_WAIT"
    assert parent["children"] == ["foo.s1", "foo.s2"]


def test_decompose_preserves_parent_signature_fields(tmp_path: Path) -> None:
    """CRITICAL Rule 3 Layer 1 check."""
    backlog = _make_v2_yaml(tmp_path)
    parent_before = dict(_by_id(backlog, "foo"))
    apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[{"id": "foo.s1"}],
    )
    parent_after = _by_id(backlog, "foo")
    for field in ("file", "line", "theorem", "blocker", "dependencies",
                   "estimated_lines", "depth", "priority"):
        assert parent_after[field] == parent_before[field], (
            f"signature field {field} drifted: {parent_before[field]!r} → "
            f"{parent_after[field]!r}"
        )


def test_decompose_persists_decision_reason(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[{"id": "foo.s1"}],
        decision_reason="induction on n",
    )
    parent = _by_id(backlog, "foo")
    assert parent.get("_pending_decision_reason") == "induction on n"


def test_decompose_does_not_touch_unrelated_siblings(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    bar_before = dict(_by_id(backlog, "bar"))
    apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[{"id": "foo.s1"}],
    )
    bar_after = _by_id(backlog, "bar")
    # Compare the fields that DEFINE the sibling. E4's idempotent
    # migration may add references=[]/coverage_state="needs_proof" on
    # the read path; that's a harmless additive default, not a
    # perturbation of the sibling's meaning.
    DEFINING = ("id", "file", "line", "theorem", "type", "depth",
                "priority", "estimated_lines", "dependencies", "unlocks",
                "state", "children", "parent_id", "history_log",
                "stuck_rounds")
    for k in DEFINING:
        assert bar_after.get(k) == bar_before.get(k), (
            f"sibling field {k} was perturbed by decompose"
        )


def test_decompose_preserves_file_mode(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    os.chmod(backlog, 0o644)
    apply_decomposition(
        backlog_path=backlog,
        parent_id="foo",
        sub_problems=[{"id": "foo.s1"}],
    )
    assert (os.stat(backlog).st_mode & 0o777) == 0o644


# ── End-to-end CLI smoke ─────────────────────────────────────────────


def test_decompose_cli_emits_subtasks_split(tmp_path: Path) -> None:
    backlog = _make_v2_yaml(tmp_path)
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    script = Path(__file__).resolve().parent.parent / "decompose_node.py"
    sub_problems = [{"id": "foo.cli1", "theorem": "foo_cli1"}]
    result = subprocess.run(
        [
            "python3", str(script),
            "--parent-id", "foo",
            "--sub-problems-json", json.dumps(sub_problems),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr
    events_path = sandbox / "events.jsonl"
    assert events_path.exists()
    content = events_path.read_text()
    assert "subtasks-split" in content
    assert '"parent_id":"foo"' in content
    # Yaml has the new sub
    assert _by_id(backlog, "foo.cli1") is not None
    assert _by_id(backlog, "foo")["state"] == "INACTIVE_WAIT"


# ── Differentiation evidence ─────────────────────────────────────────


def test_module_present_marker() -> None:
    from decompose_node import apply_decomposition as _apd  # noqa: F401
    assert callable(_apd)

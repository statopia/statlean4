"""L2 integration smoke for slice 3.B narrative wiring (czy newloop port).

Mimics the prove-deep.md Phase 2 narrative path through subprocess
invocations of the actual scripts. NO LLM is invoked — we drive the
state machine ourselves to verify the wiring is correct end-to-end:

  decompose_node → process_sorry_result(stuck × 3) → record_retreat
  → read_history_log → second decompose_node → process_sorry_result(proved)
  → propagate_done (auto-fired by process_sorry_result)

Asserts:
  - Each script's emit lands in events.jsonl with the correct name
  - yaml state evolves through every transition correctly
  - history_log carries decision_reason from first decompose into second
    decompose's "Previous attempt history" prompt prefix
  - propagate_done cascades root to DONE/done_by_dependency

This is the L2 smoke per MERGE_PLAN.md §4.3. The L3 A/B harness against
real LLM runs is a separate session (user-invoked) — see
docs/SLICE_3C_LLM_SMOKE.md for that procedure.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
DECOMPOSE_NODE = SCRIPTS_DIR / "decompose_node.py"
RECORD_RETREAT = SCRIPTS_DIR / "record_retreat.py"
READ_HISTORY = SCRIPTS_DIR / "read_history_log.py"
PROPAGATE_DONE = SCRIPTS_DIR / "propagate_done.py"


def _run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kwargs)


def _setup_initial_yaml(path: Path) -> None:
    """Single top-level sorry, INITIALIZED, ready for decomposition."""
    data = {
        "schema_version": 2,
        "version": "v200",
        "sorry_items": [
            {
                "id": "lemma_x",
                "file": "Statlean/X.lean",
                "line": 50,
                "theorem": "lemma_x_thm",
                "type": "blocked",
                "depth": 0,
                "priority": 50,
                "blocker": "needs decomposition",
                "estimated_lines": 200,
                "dependencies": [],
                "unlocks": [],
                "stuck_rounds": 0,
                "state": "INITIALIZED",
                "children": [],
                "parent_id": None,
                "history_log": [],
            }
        ],
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(path, 0o644)


def _events(sandbox: Path) -> list[dict]:
    """Read all event objects from <sandbox>/events.jsonl."""
    p = sandbox / "events.jsonl"
    if not p.exists():
        return []
    return [
        json.loads(line)
        for line in p.read_text().splitlines()
        if line.strip()
    ]


def _by_id(backlog: Path, node_id: str) -> dict | None:
    items = (yaml.safe_load(backlog.read_text()) or {}).get("sorry_items") or []
    return next((it for it in items if it.get("id") == node_id), None)


@pytest.mark.skipif(
    os.environ.get("CI_SKIP_INTEGRATION") == "1",
    reason="integration smoke disabled in this env",
)
def test_full_decompose_retreat_redecompose_proved_chain(tmp_path: Path) -> None:
    """End-to-end smoke: every slice 3.A/B script in narrative order.

    Skipped if CI_SKIP_INTEGRATION=1 (faster CI runs); otherwise runs the
    full chain in <1s using subprocess calls (no LLM).
    """
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    _setup_initial_yaml(backlog)

    # ── Step 1: First decomposition (initial round) ─────────────────
    r = _run([
        "python3", str(DECOMPOSE_NODE),
        "--parent-id", "lemma_x",
        "--sub-problems-json", json.dumps([
            {"id": "lemma_x.s1", "theorem": "x_s1", "blocker": "step a"},
            {"id": "lemma_x.s2", "theorem": "x_s2", "blocker": "step b"},
        ]),
        "--decision-reason", "first try: split by inductive structure",
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
    ])
    assert r.returncode == 0, r.stderr

    parent = _by_id(backlog, "lemma_x")
    assert parent["state"] == "INACTIVE_WAIT"
    assert parent["children"] == ["lemma_x.s1", "lemma_x.s2"]
    assert parent["_pending_decision_reason"] == "first try: split by inductive structure"
    s1 = _by_id(backlog, "lemma_x.s1")
    assert s1["state"] == "INITIALIZED"
    assert s1["parent_id"] == "lemma_x"

    # ── Step 2: Both children get stuck (× 3 rounds) ─────────────────
    # Simulate the prove-deep narrative: each stuck reports bumps
    # stuck_rounds via process_sorry_result.py. We invoke the helper
    # directly because process_sorry_result has subprocess deps that
    # aren't relevant to this smoke.
    sys.path.insert(0, str(SCRIPTS_DIR))
    from _yaml_io import locked_backlog, atomic_write_yaml  # noqa: E402

    for round_n in range(3):
        with locked_backlog(backlog) as data:
            for it in data["sorry_items"]:
                if it["id"] == "lemma_x.s1":
                    it["stuck_rounds"] = it.get("stuck_rounds", 0) + 1
                if it["id"] == "lemma_x.s2":
                    it["stuck_rounds"] = it.get("stuck_rounds", 0) + 1
            atomic_write_yaml(backlog, data)

    s1_after = _by_id(backlog, "lemma_x.s1")
    assert s1_after["stuck_rounds"] == 3

    # ── Step 3: Retreat fires (per narrative: stuck_rounds≥3) ───────
    r = _run([
        "python3", str(RECORD_RETREAT),
        "--parent-id", "lemma_x",
        "--retreat-reason", "stuck_rounds reached 3 on lemma_x.s1",
        "--results-json", json.dumps([
            {"sub_problem_id": "lemma_x.s1", "status": "stuck",
             "fail_reason": "type mismatch in Mathlib API call"},
            {"sub_problem_id": "lemma_x.s2", "status": "stuck",
             "fail_reason": "missing instance"},
        ]),
        # Note: not passing --decision-reason; should fall back to
        # parent's _pending_decision_reason (slice 3.A §8 fixup).
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
    ])
    assert r.returncode == 0, r.stderr

    parent = _by_id(backlog, "lemma_x")
    assert parent["state"] == "INITIALIZED"
    assert parent["stuck_rounds"] == 0
    assert parent["children"] == []
    # Children rows REMOVED
    assert _by_id(backlog, "lemma_x.s1") is None
    assert _by_id(backlog, "lemma_x.s2") is None
    # History entry recorded
    assert len(parent["history_log"]) == 1
    entry = parent["history_log"][0]
    assert entry["iteration"] == 1
    assert entry["decomposition"] == ["lemma_x.s1", "lemma_x.s2"]
    # decision_reason pulled from stash (slice 3.A §8 P0 fix)
    assert entry["decision_reason"] == "first try: split by inductive structure"
    # Stash consumed (popped) from parent
    assert "_pending_decision_reason" not in parent

    # ── Step 4: Read history log → check prompt prefix format ────────
    r = _run([
        "python3", str(READ_HISTORY),
        "--node-id", "lemma_x",
        "--backlog-path", str(backlog),
    ])
    assert r.returncode == 0, r.stderr
    block = r.stdout
    assert "## Previous attempt history (DO NOT repeat failed strategies)" in block
    assert "Iteration 1: decomposed into [lemma_x.s1, lemma_x.s2]" in block
    assert "first try: split by inductive structure" in block
    assert "ACTION: Choose a DIFFERENT decomposition strategy" in block

    # ── Step 5: Second decomposition (DIFFERENT strategy) ────────────
    r = _run([
        "python3", str(DECOMPOSE_NODE),
        "--parent-id", "lemma_x",
        "--sub-problems-json", json.dumps([
            {"id": "lemma_x.t1", "theorem": "x_t1", "blocker": "alt step"},
        ]),
        "--decision-reason", "second try: monolithic (single-step)",
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
    ])
    assert r.returncode == 0, r.stderr

    parent = _by_id(backlog, "lemma_x")
    assert parent["state"] == "INACTIVE_WAIT"
    assert parent["children"] == ["lemma_x.t1"]
    assert parent["_pending_decision_reason"] == "second try: monolithic (single-step)"
    # History from first round PRESERVED
    assert len(parent["history_log"]) == 1
    assert parent["history_log"][0]["decomposition"] == ["lemma_x.s1", "lemma_x.s2"]

    # ── Step 6: Mark t1 as DONE + propagate_done ─────────────────────
    # Process_sorry_result with status=proved would do this; we
    # simulate the state mutation + invoke propagate_done directly.
    with locked_backlog(backlog) as data:
        for it in data["sorry_items"]:
            if it["id"] == "lemma_x.t1":
                it["state"] = "DONE"
                it["done_reason"] = "proved"
                it["status"] = "proved"
        atomic_write_yaml(backlog, data)

    r = _run([
        "python3", str(PROPAGATE_DONE),
        "--node-id", "lemma_x.t1",
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
    ])
    assert r.returncode == 0, r.stderr

    parent = _by_id(backlog, "lemma_x")
    # Cascade fired: parent now DONE/done_by_dependency
    assert parent["state"] == "DONE"
    assert parent["done_reason"] == "done_by_dependency"

    # ── Step 7: Verify the full event chain in events.jsonl ─────────
    events = _events(sandbox)
    event_names = [e.get("name") for e in events if "name" in e]
    # Required milestones in order:
    # decompose × 2, retreat × 1, dag-cycle-done × 1
    assert event_names.count("subtasks-split") == 2
    assert event_names.count("retreat-triggered") == 1
    assert event_names.count("dag-cycle-done") == 1
    # sorry-pool-snapshot fires at decompose time (slice 3.B §8 P0 fix)
    assert event_names.count("sorry-pool-snapshot") == 2

    # Order: subtasks-split → retreat-triggered → subtasks-split → dag-cycle-done
    ordered_critical = [n for n in event_names if n in {
        "subtasks-split", "retreat-triggered", "dag-cycle-done"
    }]
    assert ordered_critical == [
        "subtasks-split",       # first decompose
        "retreat-triggered",    # retreat on stuck × 3
        "subtasks-split",       # second decompose
        "dag-cycle-done",       # cascade DONE to root
    ]


def test_module_present_marker() -> None:
    """Differentiation evidence: this test file exists only on
    merge/newloop-import, not on rollback/sdk-bridge-pre-newloop."""
    assert DECOMPOSE_NODE.exists()
    assert RECORD_RETREAT.exists()
    assert READ_HISTORY.exists()
    assert PROPAGATE_DONE.exists()

"""Slice 03 L2 integration smoke for refine_decomposition.py.

Per `docs/SLICE_03_INFORMAL_AGENT_SPEC.md` §7.2: end-to-end through
the orchestrator-shape (CLI subprocess) for a multi-round refinement
sequence on the same parent. Stubbed SKILL output simulates the
informal-refine subagent.

Round 1: LLM proposes refining (drops 1 child, adds 1 new)
Round 2: LLM signals noAdjustment → coverage_stable=true; loop exits

Asserts the cap arithmetic (2 refinements committed = czy parity
3-total-InformalAgent invocations) and that the multi-round narrative
shape works through subprocess invocations.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
REFINE = SCRIPTS_DIR / "refine_decomposition.py"


def _v2_parent_with_children() -> List[Dict[str, Any]]:
    parent = {
        "id": "p", "file": "Statlean/Foo.lean", "line": 1,
        "theorem": "p_thm", "type": "blocked", "depth": 0,
        "priority": 50, "estimated_lines": 100,
        "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["p.s1", "p.s2", "p.s3"],
        "parent_id": None, "history_log": [],
        "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
    }
    children = []
    for i, cid in enumerate(["p.s1", "p.s2", "p.s3"]):
        children.append({
            "id": cid, "file": "Statlean/Foo.lean", "line": 5 + i,
            "theorem": f"{cid}_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
        })
    return [parent] + children


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    data = {
        "schema_version": 2, "version": "v100",
        "sorry_items": _v2_parent_with_children(),
    }
    p.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    return p


def _run_refine(parent_id: str, json_text: str, backlog: Path,
                sandbox: Path, tmp_path: Path,
                round_n: int) -> subprocess.CompletedProcess:
    json_file = tmp_path / f"sub-{parent_id}-round-{round_n}.json"
    json_file.write_text(json_text)
    return subprocess.run(
        [
            "python3", str(REFINE),
            "--parent-id", parent_id,
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )


def test_l2_two_round_refinement_then_no_adjustment(
    backlog: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """Round 1: refine (drop p.s2, add p.new). Round 2: noAdjustment.
    After round 2, coverage_stable=true, informal_round=1 (since
    round 2 didn't bump). czy parity: 1 initial Step A + 2 refinement
    rounds = 3 total InformalAgent invocations; round 2 was noAdjustment
    so only 1 refinement was committed."""

    # Round 1 — refine
    r1 = _run_refine("p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "split p.s2",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.s3", "description": "s3", "action": "prove", "dependencies": []},
            {"id": "p.new", "description": "new bridge", "action": "prove", "dependencies": []},
        ],
    }), backlog, sandbox, tmp_path, 1)
    assert r1.returncode == 0, r1.stderr

    after_r1 = yaml.safe_load(backlog.read_text())
    by_id_r1 = {it["id"]: it for it in after_r1["sorry_items"]}
    assert by_id_r1["p"]["informal_round"] == 1
    assert by_id_r1["p"]["children"] == ["p.s1", "p.s3", "p.new"]
    assert by_id_r1["p"]["coverage_stable"] is False
    assert "p.s2" not in by_id_r1, "dropped child removed"

    # Round 2 — noAdjustment
    r2 = _run_refine("p", json.dumps({
        "needsDecomposition": True, "noAdjustment": True,
        "decisionReason": "decomposition is fine",
        "subProblems": [],
    }), backlog, sandbox, tmp_path, 2)
    assert r2.returncode == 0, r2.stderr

    after_r2 = yaml.safe_load(backlog.read_text())
    by_id_r2 = {it["id"]: it for it in after_r2["sorry_items"]}
    assert by_id_r2["p"]["coverage_stable"] is True
    assert by_id_r2["p"]["informal_round"] == 1, "noAdjustment didn't bump"
    assert by_id_r2["p"]["children"] == ["p.s1", "p.s3", "p.new"], "children unchanged"

    # Two milestones
    events = sandbox / "events.jsonl"
    milestones = [
        json.loads(line)
        for line in events.read_text().strip().splitlines()
        if json.loads(line).get("kind") == "sandbox_milestone"
    ]
    rounds = [m for m in milestones if m.get("name") == "informal-round"]
    assert len(rounds) == 2
    assert rounds[0]["details"]["verdict"] == "refined"
    assert rounds[1]["details"]["verdict"] == "noAdjustment"


def test_l2_cap_reached_after_two_refinements(
    backlog: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """Two refinements (committed), then a 3rd attempt → cap_reached.
    Matches czy parity: czy `for alignRound = 0; alignRound < 3` runs
    3 InformalAgent invocations; SDK-bridge Step A = 1, then 2
    refinements, then cap. Round 3 is rejected at the script level."""

    # Round 1 — refine (changes children)
    r1 = _run_refine("p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "round 1",
        "subProblems": [
            {"id": "p.s1", "description": "s1", "action": "prove", "dependencies": []},
            {"id": "p.alt1", "description": "alt1", "action": "prove", "dependencies": []},
        ],
    }), backlog, sandbox, tmp_path, 1)
    assert r1.returncode == 0
    assert yaml.safe_load(backlog.read_text())["sorry_items"][0]["informal_round"] == 1

    # Round 2 — refine (different children again)
    r2 = _run_refine("p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "round 2",
        "subProblems": [
            {"id": "p.alt1", "description": "alt1", "action": "prove", "dependencies": []},
            {"id": "p.alt2", "description": "alt2", "action": "prove", "dependencies": []},
        ],
    }), backlog, sandbox, tmp_path, 2)
    assert r2.returncode == 0
    assert yaml.safe_load(backlog.read_text())["sorry_items"][0]["informal_round"] == 2

    # Round 3 — should cap_reached
    r3 = _run_refine("p", json.dumps({
        "needsDecomposition": True, "noAdjustment": False,
        "decisionReason": "round 3 attempted",
        "subProblems": [
            {"id": "p.alt3", "description": "alt3", "action": "prove", "dependencies": []},
        ],
    }), backlog, sandbox, tmp_path, 3)
    assert r3.returncode == 0
    # informal_round NOT bumped past cap
    assert yaml.safe_load(backlog.read_text())["sorry_items"][0]["informal_round"] == 2

    events = sandbox / "events.jsonl"
    milestones = [
        json.loads(line)
        for line in events.read_text().strip().splitlines()
        if json.loads(line).get("kind") == "sandbox_milestone"
    ]
    rounds = [m for m in milestones if m.get("name") == "informal-round"]
    assert len(rounds) == 3
    verdicts = [m["details"]["verdict"] for m in rounds]
    assert verdicts == ["refined", "refined", "cap_reached"]


def test_module_present_marker() -> None:
    assert True

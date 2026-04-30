"""H3 L2 integration test for extract_library_coverage.py.

End-to-end via subprocess.run. Per `docs/H3_LIBRARY_COVERAGE_SPEC.md`
§8.2:

1. Build v2 backlog with one parent (INACTIVE_WAIT) + 2 children (needs_proof)
2. Build stub SKILL output:
   - child.A → cited_by_library with matched_name="MeasureTheory.integral_nonneg"
   - child.B → needs_proof
3. Run extract_library_coverage.py --parent-id ... --subagent-json-file ...
4. Assert:
   - child.A: coverage_state=="cited_by_library",
     library_hit.name=="MeasureTheory.integral_nonneg",
     library_hit.source=="mathlib"
   - child.B: coverage_state=="needs_proof" (unchanged)
   - events.jsonl has 1 library-coverage-extracted milestone with
     cited_by_library_count==1, needs_proof_count==1, verdict=="partial"
   - exit 0
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_library_coverage.py"


# ── Fixture helpers ──────────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _v2_backlog_items() -> List[Dict[str, Any]]:
    parent: Dict[str, Any] = {
        "id": "thm.main",
        "file": "Main.lean", "line": 10,
        "theorem": "main_theorem", "type": "ready", "depth": 0,
        "priority": 50, "estimated_lines": 60,
        "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["sub.A", "sub.B"],
        "parent_id": None, "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    child_a: Dict[str, Any] = {
        "id": "sub.A",
        "file": "SubA.lean", "line": 5,
        "theorem": "integral is nonneg for nonneg integrands",
        "type": "ready", "depth": 1,
        "priority": 50, "estimated_lines": 20,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": "thm.main", "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    child_b: Dict[str, Any] = {
        "id": "sub.B",
        "file": "SubB.lean", "line": 8,
        "theorem": "conditional expectation is additive",
        "type": "ready", "depth": 1,
        "priority": 50, "estimated_lines": 40,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": "thm.main", "history_log": [],
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": [], "assumption_analysis": "",
        "alternative_path": None,
    }
    return [parent, child_a, child_b]


def _stub_skill_output() -> str:
    """Stub SKILL output: sub.A → cited_by_library; sub.B → needs_proof."""
    return json.dumps([
        {
            "sub_problem_id": "sub.A",
            "coverage": "cited_by_library",
            "matched_name": "MeasureTheory.integral_nonneg",
            "matched_source": "mathlib",
            "matched_location": "Mathlib/MeasureTheory/Integral/Bochner.lean:42",
            "matched_kind": "lemma",
            "candidates_queried": ["integral_nonneg", "nonneg_integral"],
            "reasoning": "integral_nonneg states nonnegativity of the Bochner integral for nonneg integrands.",
        },
        {
            "sub_problem_id": "sub.B",
            "coverage": "needs_proof",
            "matched_name": None,
            "matched_source": None,
            "matched_location": None,
            "matched_kind": None,
            "candidates_queried": ["condExp_add", "condExp_const"],
            "reasoning": "No candidate's conclusion entails the full conditional expectation linearity claim.",
        },
    ])


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _make_backlog(_v2_backlog_items(), p)
    return p


# ── L2 integration test ──────────────────────────────────────────────


@pytest.mark.l2
def test_l2_end_to_end_library_coverage(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Full end-to-end: subprocess.run → assert yaml mutations + events.jsonl."""
    # Build stub SKILL output file
    skill_json_file = tmp_path / "_library_coverage_thm.main.json"
    skill_json_file.write_text(_stub_skill_output())

    # Run the script
    result = subprocess.run(
        [
            "python3", str(EXTRACT),
            "--parent-id", "thm.main",
            "--subagent-json-file", str(skill_json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )

    # 4d: exit 0
    assert result.returncode == 0, (
        f"exit {result.returncode}\nstdout: {result.stdout}\nstderr: {result.stderr}"
    )

    # 4a: child sub.A → cited_by_library + library_hit
    final = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in final["sorry_items"]}

    sub_a = by_id["sub.A"]
    assert sub_a["coverage_state"] == "cited_by_library", (
        f"sub.A coverage_state: {sub_a['coverage_state']!r}"
    )
    assert sub_a["library_hit"]["name"] == "MeasureTheory.integral_nonneg"
    assert sub_a["library_hit"]["source"] == "mathlib"

    # 4b: child sub.B → still needs_proof; no library_hit
    sub_b = by_id["sub.B"]
    assert sub_b["coverage_state"] == "needs_proof"
    assert sub_b.get("library_hit") is None

    # 4c: events.jsonl has 1 library-coverage-extracted milestone
    events_file = sandbox / "events.jsonl"
    assert events_file.exists(), "events.jsonl not created"

    lines = [
        line.strip() for line in events_file.read_text().splitlines()
        if line.strip()
    ]
    milestone_events = []
    for line in lines:
        try:
            ev = json.loads(line)
            if ev.get("kind") == "sandbox_milestone" and ev.get("name") == "library-coverage-extracted":
                milestone_events.append(ev)
        except json.JSONDecodeError:
            pass

    assert len(milestone_events) == 1, (
        f"expected 1 library-coverage-extracted milestone, got {len(milestone_events)}"
    )

    details = milestone_events[0].get("details", {})
    assert details.get("cited_by_library_count") == 1, details
    assert details.get("needs_proof_count") == 1, details
    assert details.get("verdict") == "partial", details
    assert details.get("parent_id") == "thm.main", details

    # Validation invariant: cited + needs_proof + skipped == sub_problems_checked
    assert (
        details.get("cited_by_library_count", 0)
        + details.get("needs_proof_count", 0)
        + details.get("skipped_count", 0)
        == details.get("sub_problems_checked", -1)
    ), f"count partition mismatch: {details}"

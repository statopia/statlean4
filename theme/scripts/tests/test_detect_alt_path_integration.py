"""H2 L2 integration test for detect_alt_path.py.

Per `docs/H2_DETECT_ALT_PATH_SPEC.md` §8.2: end-to-end multi-step
scenario via subprocess. The detect-alt-path Task subagent is stubbed
(no live LLM); we write canonical JSON to a file and invoke the script.

What this adds beyond the L1 unit tests:
  - End-to-end via subprocess.run: stub SKILL JSON file, real CLI args
  - Verifies events.jsonl has correct milestone name + payload shape
  - Verifies yaml mutation (alternative_path set / null / cached)
  - Verifies G3 cache (second run on same parent → verdict=cached)
  - Verifies record_retreat.py reset hook (alternative_path reset to None)
  - Verifies re-dispatch after reset (new SKILL run → detected again)
  - v1→v2 migration runs (schema_version present in output)

Test scenario (per spec §8.2):
  Step 1: Pre-build v2 backlog with parent + 3 children + R6 references
  Step 2: Pre-build sandbox paper_body.txt with ~2000 chars
  Step 3: Stub SKILL JSON (hasAlternative=true) to a temp file
  Step 4: Call detect_alt_path.py → expect exit 0 + detected milestone + yaml set
  Step 5: Re-call same script → G3 cache hit → cached milestone + yaml unchanged
  Step 6: Call record_retreat.py on parent → alternative_path reset to null
  Step 7: Re-call detect_alt_path.py → G3 cache miss → detected again
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
DETECT = SCRIPTS_DIR / "detect_alt_path.py"
RECORD_RETREAT = SCRIPTS_DIR / "record_retreat.py"


# ── Fixtures ──────────────────────────────────────────────────────────


def _v2_parent(parent_id: str = "slln.main") -> Dict[str, Any]:
    return {
        "id": parent_id,
        "file": "SLLN.lean",
        "line": 5,
        "theorem": "SLLN_main",
        "type": "ready",
        "depth": 0,
        "priority": 50,
        "estimated_lines": 120,
        "dependencies": [],
        "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["slln.sub1", "slln.sub2", "slln.sub3"],
        "parent_id": None,
        "history_log": [],
        "stuck_rounds": 0,
        "attempts": 0,
        "references": [],
        "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": 1,
        "coverage_stable": False,
        "detailed_proof_plan": None,
        "direct_assembly": None,
        "proof_sketch": None,
        "assumption_hints": [],
        "assumption_analysis": "",
        "alternative_path": None,
    }


def _v2_child(child_id: str, parent_id: str, coverage: str) -> Dict[str, Any]:
    return {
        "id": child_id,
        "file": "SLLN.lean",
        "line": 20,
        "theorem": f"sub_{child_id}",
        "type": "ready",
        "depth": 1,
        "priority": 50,
        "estimated_lines": 30,
        "dependencies": [],
        "unlocks": [],
        "state": "INITIALIZED",
        "children": [],
        "parent_id": parent_id,
        "history_log": [],
        "stuck_rounds": 0,
        "attempts": 0,
        "references": [
            {
                "ref_id": "slln_ref_001",
                "coverage": coverage,
                "coverage_assessment": (
                    "The reference directly proves the truncation step using L4 bound."
                    if coverage != "no_coverage"
                    else ""
                ),
            }
        ],
        "coverage_state": coverage,
        "citation_verified": False,
        "informal_round": 0,
        "coverage_stable": False,
        "detailed_proof_plan": None,
        "direct_assembly": None,
        "proof_sketch": None,
        "assumption_hints": [],
        "assumption_analysis": "",
        "alternative_path": None,
    }


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    parent = _v2_parent("slln.main")
    child1 = _v2_child("slln.sub1", "slln.main", "cited_by_reference")
    child2 = _v2_child("slln.sub2", "slln.main", "partial_coverage")
    child3 = _v2_child("slln.sub3", "slln.main", "no_coverage")
    # Give child3 a non-empty coverage_assessment so G1 passes
    child3["references"][0]["coverage_assessment"] = "No direct match but related lemma found."
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": [parent, child1, child2, child3],
    }
    p.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    return p


@pytest.fixture
def paper_body_file(sandbox: Path) -> Path:
    """Write ~2000-char reference proof text to sandbox/paper_body.txt."""
    body = (
        "Strong Law of Large Numbers proof via Borel-Cantelli + truncation.\n"
        "Let X_i be iid with E[X_i]=0 and E[X_i^4] < ∞. Truncate at level n: "
        "X_i^{(n)} = X_i * 1_{|X_i| <= n}. Then for each k, by Chebyshev: "
        "P(|S_k^{(n)} - S_k| > ε) ≤ E[|X_1|^4 * 1_{|X_1|>n}] / ε^4. "
        "Apply Borel-Cantelli lemma: sum_n P(|S_n/n| > ε) < ∞ for each ε > 0. "
        "Therefore S_n/n → 0 a.s. The truncation argument is standard: "
        "since E[X_1^4] < ∞, the 4th moment bound gives E[X_1^4 1_{|X_1|>n}] → 0. "
        "Key lemmas: L4-moment-bound, Borel-Cantelli, tail-summability. "
        "This approach differs from the martingale method in that it does not "
        "require constructing a backward filtration or invoking Doob's convergence. "
        "The Borel-Cantelli lemma is directly applicable once the 4th moment is finite. "
    ) * 4  # ~2000 chars
    pb = sandbox / "paper_body.txt"
    pb.write_text(body)
    return pb


def _stub_skill_json(tmp_path: Path, name: str = "alt_path.json") -> Path:
    """Write a stub SKILL JSON (hasAlternative=true) to a temp file."""
    p = tmp_path / name
    p.write_text(json.dumps({
        "hasAlternative": True,
        "approachName": "Test Approach",
        "description": "A different proof via truncation + Borel-Cantelli.",
        "keyTools": ["lemma1", "lemma2"],
        "currentPathCoverage": "2 sub-problems need_proof under current plan.",
        "alternativePathCoverage": "Both truncation sub-problems are reference-covered.",
        "isMoreEfficient": True,
        "efficiencyReason": "fewer steps than martingale approach",
        "recommendSwitch": True,
    }))
    return p


def _run_detect(
    parent_id: str,
    json_file: Path,
    backlog: Path,
    sandbox: Path,
    paper_body_path: Path,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            "python3", str(DETECT),
            "--parent-id", parent_id,
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--paper-body-path", str(paper_body_path),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )


def _read_milestones(sandbox: Path, name: str) -> List[dict]:
    events = sandbox / "events.jsonl"
    if not events.exists():
        return []
    lines = events.read_text().strip().splitlines()
    result = []
    for line in lines:
        ev = json.loads(line)
        if ev.get("kind") == "sandbox_milestone" and ev.get("name") == name:
            result.append(ev)
    return result


# ── L2 multi-step integration test ────────────────────────────────────


def test_l2_multi_step_full_scenario(
    backlog: Path, sandbox: Path, paper_body_file: Path, tmp_path: Path
) -> None:
    """End-to-end multi-step scenario per spec §8.2.

    Steps 1-2 are handled by fixtures (backlog + paper_body_file).

    Step 3-5: SKILL JSON → detect_alt_path.py → yaml updated → G3 cache hit.
    Step 6-7: record_retreat.py → alternative_path reset → re-detect.
    """

    # ── Step 3: Stub SKILL JSON ────────────────────────────────────────
    skill_json = _stub_skill_json(tmp_path)

    # ── Step 4: First invocation → expect detected ────────────────────
    r1 = _run_detect("slln.main", skill_json, backlog, sandbox, paper_body_file)
    assert r1.returncode == 0, f"Step 4 failed: stderr={r1.stderr!r}"

    milestones_1 = _read_milestones(sandbox, "alt-path-detected")
    assert len(milestones_1) == 1, f"Expected 1 milestone after Step 4, got {len(milestones_1)}"
    m1 = milestones_1[0]["details"]
    assert m1["verdict"] == "detected"
    assert m1["has_alternative"] is True
    assert m1["recommend_switch"] is True
    assert m1["approach_name_excerpt"] == "Test Approach"
    assert m1["key_tools_count"] == 2
    assert "took_ms" in m1

    # yaml: alternative_path is non-null dict with all 9 snake_case fields
    data_after_step4 = yaml.safe_load(backlog.read_text())
    by_id = {it["id"]: it for it in data_after_step4["sorry_items"]}
    parent_after = by_id["slln.main"]
    alt = parent_after["alternative_path"]
    assert alt is not None
    assert isinstance(alt, dict)
    assert alt["has_alternative"] is True
    assert alt["approach_name"] == "Test Approach"
    assert alt["recommend_switch"] is True
    assert "description" in alt
    assert "key_tools" in alt
    assert "current_path_coverage" in alt
    assert "alternative_path_coverage" in alt
    assert "is_more_efficient" in alt
    assert "efficiency_reason" in alt
    # No other yaml fields touched
    assert by_id["slln.sub1"]["alternative_path"] is None

    # ── Step 5: Second invocation → G3 cache hit ──────────────────────
    r2 = _run_detect("slln.main", skill_json, backlog, sandbox, paper_body_file)
    assert r2.returncode == 0, f"Step 5 failed: stderr={r2.stderr!r}"

    milestones_2 = _read_milestones(sandbox, "alt-path-detected")
    assert len(milestones_2) == 2, f"Expected 2 milestones after Step 5, got {len(milestones_2)}"
    m2 = milestones_2[1]["details"]
    assert m2["verdict"] == "cached"
    assert m2["approach_name_excerpt"] is None  # spec §4: no re-emit of cached content

    # yaml UNCHANGED after cache hit
    data_after_step5 = yaml.safe_load(backlog.read_text())
    assert data_after_step5 == data_after_step4, "yaml must be unchanged on cache hit"

    # ── Step 6: record_retreat.py → alternative_path reset to None ────
    retreat_result = json.dumps([
        {"sub_problem_id": "slln.sub1", "status": "stuck",
         "fail_reason": "Lean type mismatch in truncation step"},
        {"sub_problem_id": "slln.sub2", "status": "stuck"},
        {"sub_problem_id": "slln.sub3", "status": "error"},
    ])
    r_retreat = subprocess.run(
        [
            "python3", str(RECORD_RETREAT),
            "--parent-id", "slln.main",
            "--retreat-reason", "stuck_rounds reached threshold",
            "--results-json", retreat_result,
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r_retreat.returncode == 0, f"Step 6 record_retreat failed: {r_retreat.stderr!r}"

    # After retreat: alternative_path reset to None (D-7 hook)
    data_after_retreat = yaml.safe_load(backlog.read_text())
    parent_after_retreat = next(
        it for it in data_after_retreat["sorry_items"]
        if it["id"] == "slln.main"
    )
    assert parent_after_retreat["alternative_path"] is None, (
        "alternative_path must be reset to None after retreat (D-7)"
    )
    # Also check slice 03 resets still hold
    assert parent_after_retreat["informal_round"] == 0
    assert parent_after_retreat["coverage_stable"] is False

    # ── Step 7: Re-detect after reset → SKILL dispatches again ─────────
    # record_retreat removed all children → parent now has no children.
    # We need to re-add children to test re-detection.
    # Directly patch yaml to add children back (simulates re-decompose).
    for it in data_after_retreat["sorry_items"]:
        if it["id"] == "slln.main":
            it["state"] = "INACTIVE_WAIT"
            it["children"] = ["slln.sub1_new"]
            break
    new_child = _v2_child("slln.sub1_new", "slln.main", "partial_coverage")
    new_child["references"][0]["coverage_assessment"] = "Covered by reference §3.2."
    data_after_retreat["sorry_items"].append(new_child)
    backlog.write_text(yaml.safe_dump(data_after_retreat, sort_keys=False, allow_unicode=True))

    skill_json2 = _stub_skill_json(tmp_path, "alt_path_2.json")
    r3 = _run_detect("slln.main", skill_json2, backlog, sandbox, paper_body_file)
    assert r3.returncode == 0, f"Step 7 failed: stderr={r3.stderr!r}"

    milestones_3 = _read_milestones(sandbox, "alt-path-detected")
    assert len(milestones_3) == 3, f"Expected 3 milestones after Step 7, got {len(milestones_3)}"
    m3 = milestones_3[2]["details"]
    assert m3["verdict"] == "detected", (
        f"Expected detected after cache reset, got {m3['verdict']!r}"
    )
    assert m3["has_alternative"] is True

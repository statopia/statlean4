"""H1 L2 integration smoke for elaborate_plan.py via subprocess.run.

Mirrors `docs/H1_ELABORATE_PLAN_SPEC.md` §7.2.

End-to-end shape:
  1. Pre-build a v2 backlog with parent + 3 children where:
     - parent.coverage_stable=True (alignment loop converged)
     - child A: coverage_state=cited_by_library, citation_verified=True
     - child B: coverage_state=needs_proof
     - child C: coverage_state=partial_coverage with assessment
  2. Stub the SKILL output via a pre-written text file (realistic 800-char
     plan body citing specific lemma names — no real LLM dispatch).
  3. Call elaborate_plan.py --mode assembly via subprocess.
  4. Assert: events.jsonl has 1 plan-elaborated milestone, yaml shows
     parent.detailed_proof_plan==plan_text, children A/B/C unchanged.
  5. Re-run with same SKILL output (testing idempotence).
  6. Assert: milestone verdict=skipped_already_present, plan_length=0,
     yaml unchanged.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
ELAB = SCRIPTS_DIR / "elaborate_plan.py"


REALISTIC_PLAN = (
    "Detailed assembly plan for parent p (test fixture).\n\n"
    "1. Open with `intro h` to introduce the universally-quantified hypothesis.\n"
    "2. Apply child p.s1 (cited_by_library: MeasureTheory.integral_mono_ae) "
    "to discharge the integrability subgoal. Bind h.measurable to the\n"
    "   measurable_of_continuous parameter.\n"
    "3. Use `apply Iff.intro` to split into forward + backward implications.\n"
    "   3a. Forward: cite child p.s2 (needs_proof — handled by prover);\n"
    "       pass h.bound as the boundedness hypothesis.\n"
    "   3b. Backward: cite child p.s3 (partial_coverage — see assessment);\n"
    "       use Real.norm_add_le combined with linarith on the bound.\n"
    "4. Combine via `simp [child_results]` to close the residual goal.\n"
    "5. Close any leftover obligations with `linarith` or `omega`.\n"
)


def _build_v2_backlog_assembly_fixture(path: Path) -> None:
    """Parent p with 3 children: A=cited_by_library+verified,
    B=needs_proof, C=partial_coverage with assessment."""
    items: List[Dict[str, Any]] = [
        {
            "id": "p", "file": "Statlean/Foo.lean", "line": 10,
            "theorem": "p_thm", "type": "blocked", "depth": 0,
            "priority": 50, "estimated_lines": 100,
            "dependencies": [], "unlocks": [],
            "state": "INACTIVE_WAIT",
            "children": ["p.s1", "p.s2", "p.s3"],
            "parent_id": None,
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 1,
            "coverage_stable": True,  # loop converged
            "detailed_proof_plan": None,
            "direct_assembly": "Brief: combine s1 + s2 + s3 via apply chains.",
            "proof_sketch": None,
        },
        {
            "id": "p.s1", "file": "Statlean/Foo.lean", "line": 12,
            "theorem": "s1_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 5,
            "dependencies": [], "unlocks": [],
            "state": "DONE", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [{"id": "ref1", "context": "MeasureTheory.integral_mono_ae"}],
            "coverage_state": "cited_by_library",
            "citation_verified": True,
            "done_reason": "library_verified",
            "informal_round": 0, "coverage_stable": False,
            "detailed_proof_plan": None,
            "direct_assembly": None, "proof_sketch": None,
        },
        {
            "id": "p.s2", "file": "Statlean/Foo.lean", "line": 14,
            "theorem": "s2_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "detailed_proof_plan": None,
            "direct_assembly": None, "proof_sketch": None,
        },
        {
            "id": "p.s3", "file": "Statlean/Foo.lean", "line": 18,
            "theorem": "s3_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [{"id": "ref3", "context": "Real.norm_add_le; gap: bound is < 1, need ≤"}],
            "coverage_state": "partial_coverage",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "detailed_proof_plan": None,
            "direct_assembly": None, "proof_sketch": None,
        },
    ]
    data = {"schema_version": 2, "version": "v100", "sorry_items": items}
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(path, 0o644)


def _by_id(backlog: Path, item_id: str) -> Dict[str, Any]:
    data = yaml.safe_load(backlog.read_text())
    return next(it for it in data["sorry_items"] if it["id"] == item_id)


def _read_events(sandbox: Path) -> List[Dict[str, Any]]:
    events_path = sandbox / "events.jsonl"
    if not events_path.exists():
        return []
    return [json.loads(line) for line in events_path.read_text().splitlines() if line]


def test_l2_assembly_mode_full_round_trip(tmp_path: Path) -> None:
    """End-to-end: stub SKILL output, dispatch script, verify yaml +
    events; then verify idempotent re-run."""
    backlog = tmp_path / "sorry_backlog.yaml"
    _build_v2_backlog_assembly_fixture(backlog)
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    # Snapshot pre-state for child-row immutability check
    pre = yaml.safe_load(backlog.read_text())
    pre_children = [
        it for it in pre["sorry_items"] if it["id"] in ("p.s1", "p.s2", "p.s3")
    ]

    # Stub SKILL output (realistic 800-char plan)
    text_path = tmp_path / "_elaborate_plan_p.txt"
    text_path.write_text(REALISTIC_PLAN, encoding="utf-8")

    # Run #1 — should produce verdict=elaborated
    result = subprocess.run(
        [
            "python3", str(ELAB),
            "--parent-id", "p",
            "--subagent-text-file", str(text_path),
            "--mode", "assembly",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"

    # Milestone shape
    events = _read_events(sandbox)
    plan_events = [
        e for e in events
        if e.get("kind") == "sandbox_milestone" and e.get("name") == "plan-elaborated"
    ]
    assert len(plan_events) == 1
    payload = plan_events[0]["details"]
    assert payload["parent_id"] == "p"
    assert payload["verdict"] == "elaborated"
    assert payload["variant"] == "assembly"
    assert payload["plan_length"] == len(REALISTIC_PLAN)
    assert isinstance(payload["took_ms"], int)
    assert payload["took_ms"] >= 0

    # yaml: parent.detailed_proof_plan == plan
    parent_after = _by_id(backlog, "p")
    assert parent_after["detailed_proof_plan"] == REALISTIC_PLAN

    # Children unchanged on the load-bearing field set. Migration may
    # add additive defaults on read (H7 fields etc.); those are
    # idempotent migrations, not mutations. Compare on the protected
    # column set H1's Layer 1 cares about.
    CHILD_PROTECTED = (
        "id", "file", "line", "theorem", "type", "depth", "priority",
        "estimated_lines", "dependencies", "unlocks", "state", "children",
        "parent_id", "history_log", "stuck_rounds", "attempts",
        "references", "coverage_state", "citation_verified",
        "informal_round", "coverage_stable",
        "detailed_proof_plan", "direct_assembly", "proof_sketch",
    )
    post = yaml.safe_load(backlog.read_text())
    post_children_by_id = {
        it["id"]: it for it in post["sorry_items"]
        if it["id"] in ("p.s1", "p.s2", "p.s3")
    }
    pre_children_by_id = {it["id"]: it for it in pre_children}
    assert set(pre_children_by_id.keys()) == set(post_children_by_id.keys())
    for cid, pre_ch in pre_children_by_id.items():
        post_ch = post_children_by_id[cid]
        for k in CHILD_PROTECTED:
            assert post_ch.get(k) == pre_ch.get(k), (
                f"child {cid} field {k} mutated: {pre_ch.get(k)!r} → "
                f"{post_ch.get(k)!r}"
            )

    # Run #2 — same input → idempotence
    result2 = subprocess.run(
        [
            "python3", str(ELAB),
            "--parent-id", "p",
            "--subagent-text-file", str(text_path),
            "--mode", "assembly",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert result2.returncode == 0, f"stderr: {result2.stderr}"

    events2 = _read_events(sandbox)
    plan_events2 = [
        e for e in events2
        if e.get("kind") == "sandbox_milestone" and e.get("name") == "plan-elaborated"
    ]
    assert len(plan_events2) == 2  # original + idempotent retry
    payload2 = plan_events2[1]["details"]
    assert payload2["verdict"] == "skipped_already_present"
    assert payload2["plan_length"] == 0
    assert payload2["variant"] is None

    # yaml unchanged from run #1
    parent_after2 = _by_id(backlog, "p")
    assert parent_after2["detailed_proof_plan"] == REALISTIC_PLAN

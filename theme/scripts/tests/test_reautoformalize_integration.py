"""H4-reautoformalize L2 integration test.

Per `docs/H4_REAUTOFORMALIZE_SPEC.md` §8.2. End-to-end for the skeleton-
rewrite path (two-phase pipeline):

  Phase A: reautoformalize_node.py (prep)
  Phase B: agent-simulated Lean skeleton write (stub)
  Phase C: commit_reautoformalize.py (commit)

What this adds beyond L1 tests:
  - Both scripts invoked via subprocess (real shell calls)
  - events.jsonl contains TWO reautoformalized milestones (enriching, committed)
  - yaml `theorem` field updated after commit; all other fields byte-identical
  - Full pipeline: prep → agent stub → commit works end-to-end
  - L2 extended: locked-path end-to-end (context file written; commit NOT invoked)

No live LLM calls: agent step is stubbed by writing a fake Lean file.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
REAUTO = SCRIPTS_DIR / "reautoformalize_node.py"
COMMIT = SCRIPTS_DIR / "commit_reautoformalize.py"


# ── Fixture helpers ──────────────────────────────────────────────────


def _v2_backlog_with_stuck_sorry(path: Path) -> None:
    """Build a v2 backlog with one ACTIVE_PROVING sorry with assumption hints."""
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": [
            {
                "id": "int.s1",
                "file": "Lemma2.lean",
                "line": 8,
                "theorem": "Lemma: for all square-integrable martingale M, the Doob decomposition exists.",
                "type": "ready",
                "depth": 1,
                "priority": 50,
                "estimated_lines": 40,
                "dependencies": [],
                "unlocks": [],
                "state": "ACTIVE_PROVING",
                "children": [],
                "parent_id": "parent.main",
                "history_log": [],
                "stuck_rounds": 1,
                "references": [],
                "coverage_state": "needs_proof",
                "attempts": 2,
                "citation_verified": False,
                "informal_round": 1,
                "coverage_stable": False,
                "assumption_hints": [
                    "X is square-integrable",
                    "the filtration is complete",
                ],
                "assumption_analysis": "Without L2-integrability the Doob decomposition theorem cannot apply.",
                "detailed_proof_plan": "Step 1: apply Doob.",
                "direct_assembly": None,
                "proof_sketch": "Apply martingale decomposition.",
                "done_reason": None,
            }
        ],
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _v2_backlog_with_stuck_sorry(p)
    return p


def _milestones(sandbox: Path, name: str) -> List[Dict[str, Any]]:
    events = sandbox / "events.jsonl"
    if not events.exists():
        return []
    return [
        json.loads(l)
        for l in events.read_text().splitlines()
        if json.loads(l).get("kind") == "sandbox_milestone"
        and json.loads(l).get("name") == name
    ]


# ── L2.1 full skeleton-rewrite pipeline ─────────────────────────────


def test_l2_full_skeleton_rewrite_pipeline(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """End-to-end skeleton-rewrite path:
      1. Run reautoformalize_node.py → exit 0 + verdict=enriching + enrich file
      2. Simulate agent writing enriched Lean file (stub)
      3. Run commit_reautoformalize.py → exit 0 + verdict=committed
      4. Assert events.jsonl has 2 reautoformalized milestones
      5. Assert yaml theorem updated + all other fields byte-identical
    """
    pre_data = yaml.safe_load(backlog.read_text())
    pre_row = next(it for it in pre_data["sorry_items"] if it["id"] == "int.s1")
    pre_row_snapshot = dict(pre_row)

    # ── Phase A: prep ────────────────────────────────────────────────
    r1 = subprocess.run(
        [
            "python3", str(REAUTO),
            "--sub-problem-id", "int.s1",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r1.returncode == 0, f"prep script failed: {r1.stderr}"

    ms_enriching = _milestones(sandbox, "reautoformalized")
    assert len(ms_enriching) == 1, (
        f"expected 1 enriching milestone, got {len(ms_enriching)}"
    )
    prep_details = ms_enriching[0]["details"]
    assert prep_details["verdict"] == "enriching"
    assert prep_details["hint_count"] == 2

    enrich_file = Path(prep_details["enrich_file"])
    assert enrich_file.exists(), "enrich file not created"
    enrich_content = enrich_file.read_text(encoding="utf-8")
    assert "X is square-integrable" in enrich_content
    assert "filtration is complete" in enrich_content
    assert "Missing hypotheses" in enrich_content

    # yaml unchanged after prep
    mid_data = yaml.safe_load(backlog.read_text())
    mid_row = next(it for it in mid_data["sorry_items"] if it["id"] == "int.s1")
    assert mid_row["theorem"] == pre_row_snapshot["theorem"], (
        "prep script mutated `theorem` (Layer 1 violation)"
    )

    # ── Phase B: simulate agent Lean skeleton write ──────────────────
    # The agent rewrites Lemma2.lean with enriched skeleton. We stub this
    # by writing a fake Lean file with hypotheses derived from the hints.
    lean_file = sandbox / "Lemma2.lean"
    lean_file.write_text(
        "-- enriched skeleton (agent-written stub)\n"
        "theorem doob_decomp (hX : L2Integrable X) (hF : CompleteFiltration F) : "
        "DoobDecompositionExists M := by\n"
        "  sorry\n",
        encoding="utf-8",
    )

    # ── Phase C: commit ──────────────────────────────────────────────
    r2 = subprocess.run(
        [
            "python3", str(COMMIT),
            "--sub-problem-id", "int.s1",
            "--enriched-theorem-file", str(enrich_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r2.returncode == 0, f"commit script failed: {r2.stderr}"

    # Two reautoformalized milestones: enriching + committed
    all_ms = _milestones(sandbox, "reautoformalized")
    assert len(all_ms) == 2, f"expected 2 milestones, got {len(all_ms)}"
    verdicts = [m["details"]["verdict"] for m in all_ms]
    assert "enriching" in verdicts
    assert "committed" in verdicts

    commit_details = next(m["details"] for m in all_ms if m["details"]["verdict"] == "committed")
    assert commit_details["sub_problem_id"] == "int.s1"
    assert "took_ms" in commit_details

    # Yaml: theorem updated; all other fields byte-identical
    post_data = yaml.safe_load(backlog.read_text())
    post_row = next(it for it in post_data["sorry_items"] if it["id"] == "int.s1")

    assert post_row["theorem"] == enrich_content, (
        "yaml theorem field not updated to enriched text"
    )
    # All other fields must match pre-run snapshot
    for key, val in pre_row_snapshot.items():
        if key == "theorem":
            continue
        assert post_row.get(key) == val, (
            f"Field `{key}` changed: pre={val!r} post={post_row.get(key)!r}"
        )


# ── L2.2 locked path: .integrity.json present → prompt-augment ──────


def test_l2_locked_path_no_commit(
    backlog: Path, sandbox: Path
) -> None:
    """When .integrity.json is present, prep script takes locked_fallback_prompt.
    No commit script needed — agent injects hint context instead.
    yaml unchanged throughout."""
    # Create .integrity.json to simulate locked state
    integrity = {
        "signatures": [
            {"name": "doob_decomp", "sig": "theorem doob_decomp : True := by sorry"}
        ],
        "createdAt": "2026-04-30T00:00:00.000Z",
        "source": "lock_signatures",
    }
    (sandbox / ".integrity.json").write_text(json.dumps(integrity), encoding="utf-8")

    pre_bytes = backlog.read_bytes()

    r = subprocess.run(
        [
            "python3", str(REAUTO),
            "--sub-problem-id", "int.s1",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, f"prep script failed: {r.stderr}"

    ms = _milestones(sandbox, "reautoformalized")
    assert len(ms) == 1
    assert ms[0]["details"]["verdict"] == "locked_fallback_prompt"
    assert ms[0]["details"]["hint_count"] == 2

    # Context file exists
    ctx = sandbox / "_assumption_context_int.s1.txt"
    assert ctx.exists()
    ctx_text = ctx.read_text(encoding="utf-8")
    assert "square-integrable" in ctx_text

    # No enrich file
    for f in sandbox.iterdir():
        assert not f.name.startswith("_enrich_desc_"), f"unexpected enrich file: {f}"

    # yaml unchanged
    assert backlog.read_bytes() == pre_bytes, "yaml was mutated on locked path"


# ── L2.3 no_hints path: H7 hasn't run ───────────────────────────────


def test_l2_no_hints_empty_list(tmp_path: Path, sandbox: Path) -> None:
    """assumption_hints=[] → verdict=no_hints; no temp files; yaml unchanged."""
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": [
            {
                "id": "int.s2",
                "file": "Lemma3.lean",
                "line": 5,
                "theorem": "Some lemma.",
                "type": "ready",
                "depth": 1,
                "priority": 50,
                "estimated_lines": 20,
                "dependencies": [],
                "unlocks": [],
                "state": "ACTIVE_PROVING",
                "children": [],
                "parent_id": "p1",
                "history_log": [],
                "stuck_rounds": 0,
                "references": [],
                "coverage_state": "needs_proof",
                "attempts": 0,
                "citation_verified": False,
                "informal_round": 0,
                "coverage_stable": False,
                "assumption_hints": [],
                "assumption_analysis": "",
                "detailed_proof_plan": "",
                "direct_assembly": None,
                "proof_sketch": "",
                "done_reason": None,
            }
        ],
    }
    backlog = tmp_path / "sorry_backlog.yaml"
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    pre_bytes = backlog.read_bytes()

    r = subprocess.run(
        [
            "python3", str(REAUTO),
            "--sub-problem-id", "int.s2",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, f"script failed: {r.stderr}"

    ms = _milestones(sandbox, "reautoformalized")
    assert len(ms) == 1
    assert ms[0]["details"]["verdict"] == "no_hints"

    # No temp files
    for f in sandbox.iterdir():
        assert not f.name.startswith("_enrich_") and not f.name.startswith("_assumption_context_")

    assert backlog.read_bytes() == pre_bytes

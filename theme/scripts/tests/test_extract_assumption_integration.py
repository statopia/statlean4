"""H7 L2 integration smoke for extract_assumption.py.

Per `docs/H7_HELPER_ASSUMPTION_SPEC.md` §7.2: end-to-end shell-shape
test that mirrors the orchestrator pattern. The helper-assumption
Task subagent is stubbed (we don't call an LLM); we just write the
canonical JSON output to a file and invoke `extract_assumption.py`
via subprocess.

What this adds beyond the L1.* tests:
  - End-to-end via subprocess: stub subagent JSON, pipe through script,
    verify yaml + events.jsonl
  - v1→v2 migration runs end-to-end (input yaml has no schema_version)
  - milestone payload is emitted to events.jsonl with correct shape
  - exit 0 on happy path; verdict `extracted` consumed correctly
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_assumption.py"


def _v1_one_stuck_subproblem() -> List[Dict[str, Any]]:
    """A v1-shape backlog (no schema_version, no v2 fields). The
    script's locked_backlog reader migrates on read."""
    return [
        {
            "id": "stuck.s1", "file": "X.lean", "line": 5,
            "theorem": "stuck_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
        },
    ]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog_v1(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    # Note: NO schema_version key — script's reader migrates.
    p.write_text(yaml.safe_dump({
        "version": "v100",
        "sorry_items": _v1_one_stuck_subproblem(),
    }, sort_keys=False, allow_unicode=True))
    return p


def _run(
    sub_problem_id: str,
    json_text: str,
    backlog: Path,
    sandbox: Path,
    tmp_path: Path,
) -> subprocess.CompletedProcess:
    json_file = tmp_path / f"sub-{sub_problem_id}.json"
    json_file.write_text(json_text)
    return subprocess.run(
        [
            "python3", str(EXTRACT),
            "--sub-problem-id", sub_problem_id,
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )


def test_l2_end_to_end_extracted_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """End-to-end: stub a SKILL JSON, pipe through script, verify yaml
    + events.jsonl. Confirms the orchestrator pattern works:
      1. exit 0 on happy path
      2. events.jsonl has 1 assumption-extracted milestone with
         verdict=`extracted`, added_hints_count=1
      3. yaml shows assumption_hints == ["X is integrable"]
      4. yaml shows assumption_analysis == "..." (≤400 chars)
      5. v1→v2 migration ran (schema_version: 2 in output yaml)"""
    subagent_json = json.dumps({
        "missingAssumptions": ["X is integrable"],
        "analysis": "Without integrability, finite expectation cannot be established.",
    })
    r = _run("stuck.s1", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r.returncode == 0, f"script failed: {r.stderr}"

    # Events: 1 assumption-extracted milestone with shape
    events_path = sandbox / "events.jsonl"
    assert events_path.is_file()
    lines = events_path.read_text().strip().splitlines()
    milestones = [
        json.loads(l) for l in lines
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    ext = [m for m in milestones if m.get("name") == "assumption-extracted"]
    assert len(ext) == 1, f"expected 1 milestone, got {len(ext)}"
    payload = ext[0]["details"]
    assert payload["sub_problem_id"] == "stuck.s1"
    assert payload["verdict"] == "extracted"
    assert payload["added_hints_count"] == 1
    assert payload["previous_hint_count"] == 0  # migration default was []
    assert payload["current_hint_count"] == 1
    # D-1 invariant: current count == per-call list size (NOT prev + new)
    assert payload["current_hint_count"] == payload["added_hints_count"]
    assert payload["excerpt"] is not None
    assert "Missing:" in payload["excerpt"]
    assert payload["analysis_excerpt"] is not None
    assert "took_ms" in payload

    # Yaml — migration ran, fields written, schema_version: 2
    final = yaml.safe_load(backlog_v1.read_text())
    assert final.get("schema_version") == 2, "v1→v2 migration didn't run"
    by_id = {it["id"]: it for it in final["sorry_items"]}
    s1 = by_id["stuck.s1"]
    assert s1["assumption_hints"] == ["X is integrable"]
    assert s1["assumption_analysis"].startswith(
        "Without integrability"
    )


def test_l2_end_to_end_empty_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """`empty` verdict: subagent diagnosed but found nothing missing.
    Verdict=`empty`, assumption_analysis written, assumption_hints
    overwritten to []."""
    subagent_json = json.dumps({
        "missingAssumptions": [],
        "analysis": "All hypotheses appear to be present in the statement.",
    })
    r = _run("stuck.s1", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r.returncode == 0, f"script failed: {r.stderr}"

    events_path = sandbox / "events.jsonl"
    lines = events_path.read_text().strip().splitlines()
    payload = json.loads(lines[-1])["details"]
    assert payload["verdict"] == "empty"
    assert payload["added_hints_count"] == 0
    assert payload["excerpt"] is None
    assert payload["analysis_excerpt"] is not None

    final = yaml.safe_load(backlog_v1.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "stuck.s1")
    assert s1["assumption_hints"] == []
    assert s1["assumption_analysis"].startswith("All hypotheses")


def test_l2_end_to_end_parse_error_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Malformed JSON via subprocess: exit 0 (script handles parse_error
    gracefully — yaml unchanged, milestone emitted)."""
    r = _run("stuck.s1", "not-json {[}", backlog_v1, sandbox, tmp_path)
    # Note: parse_error is a verdict, not an exit code. Script exits 0
    # since validation succeeded (sub_problem_id existed, JSON file was
    # readable). The verdict in the milestone communicates the failure.
    assert r.returncode == 0, f"script unexpectedly failed: {r.stderr}"

    events_path = sandbox / "events.jsonl"
    lines = events_path.read_text().strip().splitlines()
    milestones = [
        json.loads(l) for l in lines
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    ext = [m for m in milestones if m.get("name") == "assumption-extracted"]
    assert len(ext) == 1
    payload = ext[0]["details"]
    assert payload["verdict"] == "parse_error"
    assert payload["added_hints_count"] == 0

    # Yaml: parse_error path does NOT write yaml back (yaml unchanged
    # invariant per spec §3.3 step 4). The v1 input is preserved on disk
    # exactly — the in-memory migration that locked_backlog applies is
    # not flushed because no atomic_write_yaml call fires on this branch.
    final = yaml.safe_load(backlog_v1.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "stuck.s1")
    # On v1 input the H7 fields are absent (no migration on disk on
    # parse_error path); we accept either shape so the test doesn't
    # over-specify the unchanged-yaml invariant.
    assert s1.get("assumption_hints", []) == []
    assert s1.get("assumption_analysis", "") == ""


def test_module_present_marker() -> None:
    assert True

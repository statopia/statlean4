"""H5 L2 integration smoke for extract_web_probe.py.

Per `docs/H5_WEB_PROBE_SPEC.md` §8.2: end-to-end shell-shape test that
mirrors the orchestrator pattern. The helper-web-probe Task subagent is
stubbed (no live LLM); we write canonical JSON output to a file and invoke
extract_web_probe.py via subprocess.

What this adds beyond L1 tests:
  - End-to-end via subprocess: stub subagent JSON, pipe through script,
    verify yaml + events.jsonl
  - v1→v2 migration runs end-to-end (input yaml has no schema_version)
  - web-probe-completed milestone emitted with correct shape
  - exit 0 on happy path; verdict `completed` consumed correctly
  - --clear-context path verifies webprobe_context reset; no extra milestone
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_web_probe.py"


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
    extra_args: list | None = None,
) -> subprocess.CompletedProcess:
    json_file = tmp_path / f"webprobe-{sub_problem_id}.json"
    json_file.write_text(json_text)
    cmd = [
        "python3", str(EXTRACT),
        "--sub-problem-id", sub_problem_id,
        "--subagent-json-file", str(json_file),
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
    ]
    if extra_args:
        cmd.extend(extra_args)
    return subprocess.run(cmd, capture_output=True, text=True)


def _run_clear(
    sub_problem_id: str,
    backlog: Path,
    sandbox: Path,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            "python3", str(EXTRACT),
            "--sub-problem-id", sub_problem_id,
            "--clear-context",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )


def _read_milestones(sandbox: Path, name: str) -> list:
    events_path = sandbox / "events.jsonl"
    if not events_path.is_file():
        return []
    milestones = []
    for line in events_path.read_text().strip().splitlines():
        evt = json.loads(line)
        if evt.get("kind") == "sandbox_milestone" and evt.get("name") == name:
            milestones.append(evt)
    return milestones


# ── L2.1 end-to-end happy path ───────────────────────────────────────


def test_l2_end_to_end_completed_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """End-to-end: stub SKILL JSON, call script, verify yaml + events.jsonl.

    Spec §8.2 assertions:
    1. exit 0 on happy path
    2. events.jsonl has 1 web-probe-completed milestone with verdict=completed,
       hits_count=1, query_used set, findings_excerpt populated, context_length > 0
    3. yaml webprobe_context non-empty; contains "## Web Probe"
    4. v1→v2 migration ran (schema_version: 2 in output yaml)
    """
    subagent_json = json.dumps({
        "sub_problem_id": "stuck.s1",
        "generated_query": "integral_nonneg Lean 4 Mathlib",
        "web_hits": [
            {
                "title": "Mathlib.MeasureTheory.Integral.Bochner",
                "url": "https://github.com/leanprover-community/mathlib4/blob/main/Mathlib/MeasureTheory/Integral/Bochner.lean",
                "snippet": "integral_nonneg says the integral is nonneg when f is nonneg",
            }
        ],
        "web_fetch_content": "\n\n--- https://github.com/leanprover-community/mathlib4/blob/main/Mathlib/MeasureTheory/Integral/Bochner.lean ---\ntheorem integral_nonneg (hf : 0 ≤ f) : 0 ≤ ∫ a, f a ∂μ",
        "findings": "Try exact MeasureTheory.integral_nonneg",
        "suggestion": "Import Mathlib.MeasureTheory.Integral.Bochner",
        "assembled_context": (
            "## Web Probe (stuck recovery for stuck_thm)\n"
            "Query: integral_nonneg Lean 4 Mathlib\n\n"
            "### Findings\nTry exact MeasureTheory.integral_nonneg\n\n"
            "### Suggestion\nImport Mathlib.MeasureTheory.Integral.Bochner\n\n"
            "### Top hits\n"
            "- Mathlib.MeasureTheory.Integral.Bochner\n"
            "  https://github.com/leanprover-community/mathlib4/blob/main/Mathlib/MeasureTheory/Integral/Bochner.lean\n"
        ),
    })
    r = _run("stuck.s1", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r.returncode == 0, f"script failed: stderr={r.stderr}"

    # Milestone
    milestones = _read_milestones(sandbox, "web-probe-completed")
    assert len(milestones) == 1, f"expected 1 milestone, got {len(milestones)}"
    payload = milestones[0]["details"]
    assert payload["sub_problem_id"] == "stuck.s1"
    assert payload["verdict"] == "completed"
    assert payload["hits_count"] == 1
    assert payload["query_used"] == "integral_nonneg Lean 4 Mathlib"
    assert payload["findings_excerpt"] is not None
    assert "integral_nonneg" in payload["findings_excerpt"]
    assert payload["context_length"] > 0
    assert "took_ms" in payload

    # yaml
    final = yaml.safe_load(backlog_v1.read_text())
    assert final.get("schema_version") == 2, "v1→v2 migration didn't run"
    by_id = {it["id"]: it for it in final["sorry_items"]}
    s1 = by_id["stuck.s1"]
    assert "## Web Probe" in s1["webprobe_context"]
    assert s1["webprobe_context"] != ""


# ── L2.2 empty hits ──────────────────────────────────────────────────


def test_l2_end_to_end_empty_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Empty hits → verdict=empty; webprobe_context=""."""
    subagent_json = json.dumps({
        "sub_problem_id": "stuck.s1",
        "generated_query": "obscure query",
        "web_hits": [],
        "web_fetch_content": "",
        "findings": "No relevant web results found.",
        "suggestion": "Try a different approach in the prover; web search returned nothing useful.",
        "assembled_context": "",
    })
    r = _run("stuck.s1", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r.returncode == 0, f"script failed: {r.stderr}"

    milestones = _read_milestones(sandbox, "web-probe-completed")
    assert len(milestones) == 1
    payload = milestones[0]["details"]
    assert payload["verdict"] == "empty"
    assert payload["context_length"] == 0
    assert payload["findings_excerpt"] is None

    final = yaml.safe_load(backlog_v1.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "stuck.s1")
    assert s1.get("webprobe_context", "") == ""


# ── L2.3 parse_error ─────────────────────────────────────────────────


def test_l2_end_to_end_parse_error_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Malformed JSON: exit 2; milestone emitted with verdict=parse_error."""
    r = _run("stuck.s1", "not-json {[broken", backlog_v1, sandbox, tmp_path)
    assert r.returncode == 2, f"expected exit 2, got {r.returncode}: {r.stderr}"

    # Milestone still emitted (script emits before returning 2)
    milestones = _read_milestones(sandbox, "web-probe-completed")
    assert len(milestones) == 1
    payload = milestones[0]["details"]
    assert payload["verdict"] == "parse_error"
    assert payload["context_length"] == 0

    # yaml unchanged (no webprobe_context written — v1 input stays v1 on disk)
    final = yaml.safe_load(backlog_v1.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "stuck.s1")
    assert s1.get("webprobe_context", "") == ""


# ── L2.4 --clear-context ─────────────────────────────────────────────


def test_l2_clear_context_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """After write, --clear-context resets webprobe_context=""; no new milestone."""
    # Step 1: write
    subagent_json = json.dumps({
        "sub_problem_id": "stuck.s1",
        "generated_query": "test query",
        "web_hits": [{"title": "T", "url": "https://github.com/x", "snippet": "S"}],
        "web_fetch_content": "",
        "findings": "Found something.",
        "suggestion": "Try this.",
        "assembled_context": "## Web Probe\n### Findings\nFound something.",
    })
    r1 = _run("stuck.s1", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r1.returncode == 0, f"write failed: {r1.stderr}"

    # Verify something was written
    data_after_write = yaml.safe_load(backlog_v1.read_text())
    s1_after_write = next(it for it in data_after_write["sorry_items"] if it["id"] == "stuck.s1")
    assert s1_after_write["webprobe_context"] != ""

    # Step 2: clear
    r2 = _run_clear("stuck.s1", backlog_v1, sandbox)
    assert r2.returncode == 0, f"clear failed: {r2.stderr}"

    # webprobe_context is now ""
    data_after_clear = yaml.safe_load(backlog_v1.read_text())
    s1_after_clear = next(it for it in data_after_clear["sorry_items"] if it["id"] == "stuck.s1")
    assert s1_after_clear["webprobe_context"] == ""

    # No extra milestone was emitted for the clear
    milestones = _read_milestones(sandbox, "web-probe-completed")
    assert len(milestones) == 1, (
        f"expected 1 milestone (from write only), got {len(milestones)}"
    )


# ── L2.5 missing sub_problem_id ──────────────────────────────────────


def test_l2_missing_sub_problem_id_via_subprocess(
    backlog_v1: Path, sandbox: Path, tmp_path: Path
) -> None:
    """sub_problem_id not in yaml → exit 2."""
    subagent_json = json.dumps({
        "sub_problem_id": "nonexistent",
        "generated_query": "test",
        "web_hits": [],
        "web_fetch_content": "",
        "findings": "f",
        "suggestion": "s",
        "assembled_context": "## Web Probe\n",
    })
    r = _run("nonexistent", subagent_json, backlog_v1, sandbox, tmp_path)
    assert r.returncode == 2, f"expected exit 2, got {r.returncode}"


def test_module_present_marker() -> None:
    assert True

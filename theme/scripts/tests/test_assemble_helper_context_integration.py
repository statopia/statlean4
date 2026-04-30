"""PROVER_INJECT L2 integration test for assemble_helper_context.py.

Per `docs/PROVER_INJECT_SPEC.md` §8.2: end-to-end subprocess test that
mirrors the orchestrator pattern.

What this adds beyond L1 tests:
  - End-to-end via subprocess (real CLI invocation)
  - events.jsonl written by emit_event.py (real file I/O)
  - helper-context-assembled milestone emitted with correct shape
  - yaml byte-identical after script runs (Layer 1 invariant)
  - All three sources present → sections assembled correctly
  - Consume-once clear via extract_web_probe.py --clear-context verified:
    webprobe_context cleared; referenceprobe_findings unchanged
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
ASSEMBLE = SCRIPTS_DIR / "assemble_helper_context.py"
CLEAR_WEBPROBE = SCRIPTS_DIR / "extract_web_probe.py"


def _make_backlog_with_all_sources(
    path: Path,
    sub_id: str,
    webprobe_context: str,
    referenceprobe_findings: List[Dict[str, Any]],
) -> None:
    """Write a v2 sorry_backlog.yaml with all three source fields populated."""
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": [
            {
                "id": sub_id,
                "file": "Lemma.lean",
                "line": 10,
                "theorem": "lemma_stuck",
                "type": "ready",
                "depth": 1,
                "priority": 50,
                "estimated_lines": 20,
                "dependencies": [],
                "unlocks": [],
                "state": "ACTIVE_PROVING",
                "children": [],
                "parent_id": "parent.p1",
                "history_log": [],
                "stuck_rounds": 2,
                "references": [],
                "coverage_state": "needs_proof",
                "attempts": 0,
                "citation_verified": False,
                "informal_round": 0,
                "coverage_stable": False,
                "assumption_hints": [],
                "assumption_analysis": "",
                "webprobe_context": webprobe_context,
                "referenceprobe_findings": referenceprobe_findings,
                "alternative_path": None,
                "library_hit": None,
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
def sub_id() -> str:
    return "stub.s1"


@pytest.fixture
def backlog_all_sources(tmp_path: Path, sub_id: str) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    findings = [
        {
            "assembledContext": (
                "**Matched passage**:\nLemma 2.3 states integral_nonneg "
                "requires f ≥ 0 a.e.\n\n"
                "**Why it might help**:\nThe stuck sorry is trying to prove "
                "non-negativity of an integral.\n\n"
                "**Suggested next step**:\nUse `MeasureTheory.integral_nonneg`."
            ),
            "matchedPassage": "Lemma 2.3 states integral_nonneg requires f ≥ 0 a.e.",
            "analysis": "The stuck sorry is trying to prove non-negativity of an integral.",
            "suggestion": "Use `MeasureTheory.integral_nonneg`.",
            "stuck_rounds": 2,
            "timestamp": 1714518000000,
        }
    ]
    _make_backlog_with_all_sources(
        p,
        sub_id=sub_id,
        webprobe_context=(
            "## Web Probe (stuck recovery)\n\n"
            "Try `integral_nonneg` from Mathlib. "
            "See https://leanprover-community.github.io/mathlib4_docs/..."
        ),
        referenceprobe_findings=findings,
    )
    return p


def _run_assemble(
    sub_id: str,
    backlog: Path,
    sandbox: Path,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            "python3", str(ASSEMBLE),
            "--sub-problem-id", sub_id,
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True,
        text=True,
    )


def test_l2_all_three_sources_integration(
    tmp_path: Path,
    sandbox: Path,
    sub_id: str,
    backlog_all_sources: Path,
) -> None:
    """L2: three-source end-to-end via subprocess — all assertions from spec §8.2."""
    # Pre-create assumption context file
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text(
        "Missing hypothesis 1: f is measurable\n"
        "Missing hypothesis 2: μ is σ-finite\n"
    )

    # Capture yaml bytes before
    yaml_before = backlog_all_sources.read_bytes()

    # Run script
    result = _run_assemble(sub_id, backlog_all_sources, sandbox)

    # Assert exit 0
    assert result.returncode == 0, (
        f"expected exit 0, got {result.returncode}\n"
        f"stdout: {result.stdout}\n"
        f"stderr: {result.stderr}"
    )

    # Assert events.jsonl has helper-context-assembled milestone
    events_path = sandbox / "events.jsonl"
    assert events_path.exists(), "events.jsonl should have been created by emit_event"

    milestone_events = []
    for line in events_path.read_text().splitlines():
        if not line.strip():
            continue
        ev = json.loads(line)
        if ev.get("kind") == "sandbox_milestone" and ev.get("name") == "helper-context-assembled":
            milestone_events.append(ev)

    assert len(milestone_events) >= 1, "helper-context-assembled milestone must be emitted"
    milestone = milestone_events[0]
    details = milestone.get("details", {})

    # Verdict = assembled
    assert details.get("verdict") == "assembled", (
        f"expected verdict=assembled, got {details.get('verdict')}"
    )

    # All three sources present
    sources = details.get("sources", [])
    assert "webprobe" in sources, f"expected webprobe in sources, got {sources}"
    assert "refprobe" in sources, f"expected refprobe in sources, got {sources}"
    assert "assumption" in sources, f"expected assumption in sources, got {sources}"

    # output_len > 0
    output_len = details.get("output_len", 0)
    assert output_len > 0, f"output_len should be > 0, got {output_len}"

    # _helper_context file exists, non-empty
    ctx_output = sandbox / f"_helper_context_{sub_id}.md"
    assert ctx_output.exists(), "_helper_context_*.md must be written"
    content = ctx_output.read_text()
    assert len(content) > 0, "_helper_context_*.md must be non-empty"

    # Contains all three section headers
    assert "### Web Probe (most-recent)" in content, (
        "output must contain ### Web Probe section"
    )
    assert "### Reference Probe (most-recent)" in content, (
        "output must contain ### Reference Probe section"
    )
    assert "### Diagnosed missing hypotheses" in content, (
        "output must contain ### Diagnosed missing hypotheses section"
    )

    # Contains known content from each source
    assert "integral_nonneg" in content, "webprobe content should appear in output"
    assert "Lemma 2.3" in content, "refprobe content should appear in output"
    assert "measurable" in content, "assumption content should appear in output"

    # Total length ≤ 6000 (aggregate cap)
    assert len(content) <= 6000, f"output length {len(content)} exceeds aggregate cap 6000"

    # Layer 1: yaml byte-identical
    yaml_after = backlog_all_sources.read_bytes()
    assert yaml_before == yaml_after, (
        "assemble_helper_context must NOT mutate yaml (Layer 1 invariant)"
    )


def test_l2_consume_once_clear_integration(
    tmp_path: Path,
    sandbox: Path,
    sub_id: str,
    backlog_all_sources: Path,
) -> None:
    """L2: after prover attack, extract_web_probe --clear-context clears webprobe_context
    but leaves referenceprobe_findings unchanged."""
    # First: run assemble (sets up context)
    result = _run_assemble(sub_id, backlog_all_sources, sandbox)
    assert result.returncode == 0

    # Read referenceprobe_findings before clear
    data_before = yaml.safe_load(backlog_all_sources.read_text())
    items_before = data_before["sorry_items"]
    item_before = next(it for it in items_before if it["id"] == sub_id)
    findings_before = list(item_before["referenceprobe_findings"])
    assert len(findings_before) > 0, "test requires non-empty referenceprobe_findings"

    # Call consume-once clear
    clear_result = subprocess.run(
        [
            "python3", str(CLEAR_WEBPROBE),
            "--sub-problem-id", sub_id,
            "--clear-context",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog_all_sources),
        ],
        capture_output=True,
        text=True,
    )
    assert clear_result.returncode == 0, (
        f"clear-context failed: {clear_result.stderr}"
    )

    # Assert webprobe_context is now ""
    data_after = yaml.safe_load(backlog_all_sources.read_text())
    items_after = data_after["sorry_items"]
    item_after = next(it for it in items_after if it["id"] == sub_id)
    assert item_after["webprobe_context"] == "", (
        "webprobe_context should be empty after --clear-context"
    )

    # Assert referenceprobe_findings unchanged (accumulate semantics, D-4)
    findings_after = item_after["referenceprobe_findings"]
    assert findings_after == findings_before, (
        "referenceprobe_findings must NOT be cleared (accumulate semantics per H6 D-2)"
    )

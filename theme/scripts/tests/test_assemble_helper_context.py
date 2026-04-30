"""PROVER_INJECT L1 unit tests for assemble_helper_context.py.

Coverage matrix per `docs/PROVER_INJECT_SPEC.md` §8.1:

  L1.1 webprobe_context non-empty in yaml → output contains ## Web Probe section;
       verdict=`assembled`; sources=["webprobe"]
  L1.2 referenceprobe_findings[-1].assembledContext non-empty → output contains
       ## Reference Probe section; verdict=`assembled`; sources=["refprobe"]
  L1.3 _assumption_context_*.txt present in sandbox → output contains
       ## Assumption hints section; verdict=`assembled`; sources=["assumption"]
  L1.4 all three sources non-empty → output contains all three sections separated
       by ---; output_len > 0 and <= 6000; sources=["webprobe","refprobe","assumption"]
  L1.5 all sources empty/absent → output file exists but empty (0 bytes);
       verdict=`empty`; sources=[]
  L1.6 referenceprobe_findings=[] (empty list) → refprobe section absent;
       if webprobe also empty → verdict=`empty`
  L1.7 webprobe_context non-empty but referenceprobe_findings[-1].assembledContext
       is "" → refprobe section absent; webprobe section present
  L1.8 Layer 1 — yaml byte-identical pre/post (script writes zero yaml)
  L1.9 sub_problem_id missing in yaml → exit 0 (non-blocking); output file empty;
       verdict=`parse_error` milestone emitted

All tests use fixture yaml files and pre-created sandbox temp files.
No live LLM or web calls.
"""
from __future__ import annotations

import copy
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

# Ensure scripts dir on path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from assemble_helper_context import (  # noqa: E402
    assemble,
    AGGREGATE_CAP,
    WEBPROBE_CAP,
    REFPROBE_CAP,
    ASSUMPTION_CAP,
    VERDICT_ASSEMBLED,
    VERDICT_EMPTY,
    VERDICT_PARSE_ERROR,
    _build_webprobe_section,
    _build_refprobe_section,
    _build_assumption_section,
)

SCRIPTS_DIR = Path(__file__).resolve().parent.parent


# ── Fixtures ─────────────────────────────────────────────────────────

def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _base_item(
    sub_id: str = "sub.s1",
    webprobe_context: str = "",
    referenceprobe_findings: Any = None,
) -> Dict[str, Any]:
    """Pre-migrated v2 row for Layer 1 tests."""
    return {
        "id": sub_id,
        "file": "X.lean",
        "line": 5,
        "theorem": "stuck_thm",
        "type": "ready",
        "depth": 1,
        "priority": 50,
        "estimated_lines": 30,
        "dependencies": [],
        "unlocks": [],
        # v2 state-machine fields
        "state": "ACTIVE_PROVING",
        "children": [],
        "parent_id": "parent.one",
        "history_log": [],
        "stuck_rounds": 2,
        # E4 fields
        "references": [],
        "coverage_state": "needs_proof",
        # other v2 fields
        "attempts": 0,
        "citation_verified": False,
        "informal_round": 0,
        "coverage_stable": False,
        # H7 fields
        "assumption_hints": [],
        "assumption_analysis": "",
        # H5 field
        "webprobe_context": webprobe_context,
        # H6 field
        "referenceprobe_findings": referenceprobe_findings if referenceprobe_findings is not None else [],
    }


# ── L1.1 webprobe_context non-empty ──────────────────────────────────

def test_l1_1_webprobe_present(tmp_path: Path) -> None:
    """L1.1: webprobe_context non-empty → assembled, sources=["webprobe"]."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    webprobe_text = "## Web Probe\n\nTry integral_nonneg from Mathlib."
    _make_backlog([_base_item(sub_id, webprobe_context=webprobe_text)], backlog)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["webprobe"]
    assert payload["webprobe_len"] > 0
    assert payload["refprobe_len"] == 0
    assert payload["assumption_len"] == 0
    assert payload["output_len"] > 0

    # Check assembled block content
    block = payload["_assembled_block"]
    assert "### Web Probe (most-recent)" in block
    assert "integral_nonneg" in block
    assert "### Reference Probe" not in block
    assert "### Diagnosed missing" not in block


# ── L1.2 referenceprobe_findings[-1] non-empty ───────────────────────

def test_l1_2_refprobe_present(tmp_path: Path) -> None:
    """L1.2: referenceprobe_findings[-1].assembledContext non-empty → assembled."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    findings = [
        {
            "assembledContext": "**Matched passage**:\nLemma 2.1 requires regularity.",
            "matchedPassage": "Lemma 2.1",
            "analysis": "The passage shows regularity needed.",
            "suggestion": "Add regularity hypothesis.",
            "stuck_rounds": 2,
            "timestamp": 1000,
        }
    ]
    _make_backlog([_base_item(sub_id, referenceprobe_findings=findings)], backlog)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["refprobe"]
    assert payload["refprobe_len"] > 0
    assert payload["webprobe_len"] == 0
    assert payload["assumption_len"] == 0

    block = payload["_assembled_block"]
    assert "### Reference Probe (most-recent)" in block
    assert "Lemma 2.1" in block
    assert "### Web Probe" not in block


# ── L1.3 _assumption_context_*.txt present ───────────────────────────

def test_l1_3_assumption_file_present(tmp_path: Path) -> None:
    """L1.3: _assumption_context_*.txt in sandbox → assembled, sources=["assumption"]."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    _make_backlog([_base_item(sub_id)], backlog)
    # Write assumption context file
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text("Missing: f is continuous\nMissing: μ is σ-finite")

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["assumption"]
    assert payload["assumption_len"] > 0
    assert payload["webprobe_len"] == 0
    assert payload["refprobe_len"] == 0

    block = payload["_assembled_block"]
    assert "### Diagnosed missing hypotheses" in block
    assert "f is continuous" in block


# ── L1.4 all three sources present ───────────────────────────────────

def test_l1_4_all_three_sources(tmp_path: Path) -> None:
    """L1.4: all three sources non-empty → all sections present; output_len <= 6000."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    webprobe_text = "## Web Probe\n\nTry integral_nonneg."
    findings = [
        {
            "assembledContext": "**Matched passage**:\nLemma 3.2 in paper.",
            "matchedPassage": "Lemma 3.2",
            "analysis": "Needs continuity.",
            "suggestion": "Add cont hyp.",
            "stuck_rounds": 1,
            "timestamp": 2000,
        }
    ]
    _make_backlog(
        [_base_item(sub_id, webprobe_context=webprobe_text, referenceprobe_findings=findings)],
        backlog,
    )
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text("Missing: h : ContinuousOn f Set.univ")

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert "webprobe" in payload["sources"]
    assert "refprobe" in payload["sources"]
    assert "assumption" in payload["sources"]
    assert payload["output_len"] > 0
    assert payload["output_len"] <= AGGREGATE_CAP

    block = payload["_assembled_block"]
    assert "### Web Probe (most-recent)" in block
    assert "### Reference Probe (most-recent)" in block
    assert "### Diagnosed missing hypotheses" in block
    # Sections separated by ---
    assert "---" in block


# ── L1.5 all sources absent ───────────────────────────────────────────

def test_l1_5_all_sources_absent(tmp_path: Path) -> None:
    """L1.5: all sources empty → verdict=empty; output_len=0."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    _make_backlog([_base_item(sub_id)], backlog)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_EMPTY
    assert payload["sources"] == []
    assert payload["output_len"] == 0
    assert payload["webprobe_len"] == 0
    assert payload["refprobe_len"] == 0
    assert payload["assumption_len"] == 0
    # No _assembled_block for empty verdict
    assert payload.get("_assembled_block", "") == ""


# ── L1.6 referenceprobe_findings=[] ──────────────────────────────────

def test_l1_6_refprobe_empty_list(tmp_path: Path) -> None:
    """L1.6: referenceprobe_findings=[] AND webprobe empty → verdict=empty."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    _make_backlog([_base_item(sub_id, referenceprobe_findings=[])], backlog)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_EMPTY
    assert payload["sources"] == []


def test_l1_6b_refprobe_empty_list_but_webprobe_present(tmp_path: Path) -> None:
    """L1.6b: referenceprobe_findings=[] but webprobe non-empty → sources=["webprobe"]."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    _make_backlog(
        [_base_item(sub_id, webprobe_context="Some webprobe context.", referenceprobe_findings=[])],
        backlog,
    )

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["webprobe"]
    assert "### Reference Probe" not in payload["_assembled_block"]


# ── L1.7 referenceprobe_findings[-1].assembledContext == "" ──────────

def test_l1_7_refprobe_empty_assembled_context(tmp_path: Path) -> None:
    """L1.7: referenceprobe_findings[-1].assembledContext is "" → refprobe absent."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    webprobe_text = "## Web Probe\n\nTry simp."
    findings = [
        {
            "assembledContext": "",  # empty assembled context
            "matchedPassage": "",
            "analysis": "",
            "suggestion": "",
            "stuck_rounds": 1,
            "timestamp": 3000,
        }
    ]
    _make_backlog(
        [_base_item(sub_id, webprobe_context=webprobe_text, referenceprobe_findings=findings)],
        backlog,
    )

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["webprobe"]
    assert "### Reference Probe" not in payload["_assembled_block"]
    assert "### Web Probe (most-recent)" in payload["_assembled_block"]


# ── L1.8 Layer 1 — yaml byte-identical pre/post ───────────────────────

def test_l1_8_yaml_byte_identical(tmp_path: Path) -> None:
    """L1.8: yaml is NOT mutated by assemble_helper_context (Layer 1 invariant)."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    webprobe_text = "## Web Probe\n\ninteral_nonneg test."
    findings = [
        {
            "assembledContext": "**Matched**:\nSome passage.",
            "matchedPassage": "Some passage.",
            "analysis": "test",
            "suggestion": "Try this.",
            "stuck_rounds": 1,
            "timestamp": 4000,
        }
    ]
    _make_backlog(
        [_base_item(sub_id, webprobe_context=webprobe_text, referenceprobe_findings=findings)],
        backlog,
    )
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text("Missing: h : Continuous g")

    # Capture yaml bytes before
    yaml_before = backlog.read_bytes()

    assemble(backlog, sub_id, sandbox)

    # Yaml must be byte-identical after
    yaml_after = backlog.read_bytes()
    assert yaml_before == yaml_after, "assemble_helper_context must NOT mutate yaml"


# ── L1.9 sub_problem_id missing in yaml ──────────────────────────────

def test_l1_9_sub_problem_id_missing(tmp_path: Path) -> None:
    """L1.9: sub_problem_id missing → parse_error verdict, no raise."""
    sub_id = "sub.missing"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    # Backlog with a DIFFERENT sub_problem_id
    _make_backlog([_base_item("sub.other")], backlog)

    # Should return parse_error, not raise
    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert payload["sources"] == []
    assert payload["output_len"] == 0


# ── Cap enforcement ───────────────────────────────────────────────────

def test_cap_enforcement_aggregate(tmp_path: Path) -> None:
    """Aggregate cap: assembled block > 6000 chars is truncated to 6000."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    # Build sources that together would exceed 6000 chars
    webprobe_text = "W" * 3000
    refprobe_assembled = "R" * 3000
    assumption_text = "A" * 2000

    findings = [
        {
            "assembledContext": refprobe_assembled,
            "matchedPassage": "X",
            "analysis": "Y",
            "suggestion": "Z",
            "stuck_rounds": 1,
            "timestamp": 5000,
        }
    ]
    _make_backlog(
        [_base_item(sub_id, webprobe_context=webprobe_text, referenceprobe_findings=findings)],
        backlog,
    )
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text(assumption_text)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["output_len"] <= AGGREGATE_CAP
    assert len(payload["_assembled_block"]) <= AGGREGATE_CAP


def test_cap_enforcement_webprobe_individual(tmp_path: Path) -> None:
    """Individual webprobe cap: webprobe_context > 3000 chars is truncated."""
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    long_webprobe = "W" * 5000  # exceeds WEBPROBE_CAP=3000
    _make_backlog([_base_item(sub_id, webprobe_context=long_webprobe)], backlog)

    payload = assemble(backlog, sub_id, sandbox)

    assert payload["verdict"] == VERDICT_ASSEMBLED
    # webprobe section includes header + content; content capped at 3000
    block = payload["_assembled_block"]
    # The "W"*3000 content should be present but not 5000 Ws
    assert "W" * WEBPROBE_CAP in block
    assert "W" * (WEBPROBE_CAP + 1) not in block


def test_enriching_path_skips_assumption(tmp_path: Path) -> None:
    """D-2 gate: _enrich_desc_${id}_*.txt present → assumption section skipped."""
    sub_id = "sub.s1"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    # Write both assumption context and enriching sentinel
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text("Missing: some hypothesis")
    # Enriching sentinel
    enrich_sentinel = sandbox / f"_enrich_desc_{sub_id}_20260430T120000.txt"
    enrich_sentinel.write_text("Enriched description text")

    section = _build_assumption_section(sandbox, sub_id)

    # Should be empty because enriching path is active
    assert section == "", (
        "D-2: assumption section should be skipped when enriching sentinel is present"
    )


def test_enriching_path_skips_assumption_at_assemble_level(tmp_path: Path) -> None:
    """D-2 gate at assemble() level: enriching sentinel + webprobe + refprobe
    non-empty → output has webprobe + refprobe sections, NO assumption.

    PROVER_INJECT §8 code review S4.1 fixup: previously D-2 was only tested
    at the `_build_assumption_section()` unit level. This test exercises
    the full assemble() entry point with all three signals present, ensuring
    the gate composes correctly with the multi-source assembly path.
    """
    sub_id = "sub.s1"
    backlog = tmp_path / "sorry_backlog.yaml"
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    webprobe_text = "## Web Probe\n\nTry integral_nonneg."
    findings = [
        {
            "assembledContext": "**Matched passage**:\nLemma 3.2 in paper.",
            "matchedPassage": "Lemma 3.2",
            "analysis": "Needs continuity.",
            "suggestion": "Add cont hyp.",
            "stuck_rounds": 1,
            "timestamp": 2000,
        }
    ]
    _make_backlog(
        [_base_item(sub_id, webprobe_context=webprobe_text, referenceprobe_findings=findings)],
        backlog,
    )

    # Both assumption context AND enriching sentinel present
    ctx_file = sandbox / f"_assumption_context_{sub_id}.txt"
    ctx_file.write_text("Missing: h : ContinuousOn f Set.univ")
    enrich_sentinel = sandbox / f"_enrich_desc_{sub_id}_20260430T120000.txt"
    enrich_sentinel.write_text("Enriched description text")

    payload = assemble(backlog, sub_id, sandbox)

    # Webprobe + refprobe present; assumption SKIPPED via D-2 gate
    assert payload["verdict"] == VERDICT_ASSEMBLED
    assert payload["sources"] == ["webprobe", "refprobe"], (
        f"D-2 gate at assemble() level failed: expected ['webprobe', 'refprobe'], "
        f"got {payload['sources']}"
    )
    assert "assumption" not in payload["sources"], (
        "D-2: assumption MUST NOT appear in sources when enriching sentinel present"
    )

    block = payload["_assembled_block"]
    assert "### Web Probe (most-recent)" in block
    assert "### Reference Probe (most-recent)" in block
    assert "### Diagnosed missing hypotheses" not in block, (
        "D-2: assumption section header MUST NOT be in assembled block"
    )

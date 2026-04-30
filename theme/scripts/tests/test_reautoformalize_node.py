"""H4-reautoformalize L1 unit tests for reautoformalize_node.py and
commit_reautoformalize.py.

Coverage matrix per `docs/H4_REAUTOFORMALIZE_SPEC.md` §8.1:
  L1.1 assumption_hints non-empty + Lean file absent (unlocked):
       verdict=enriching, enrich desc temp file written, milestone emitted
  L1.2 assumption_hints empty → verdict=no_hints; no temp file; yaml unchanged
  L1.3 assumption_hints non-empty + Lean file exists (unlocked, no .integrity.json):
       verdict=enriching; enriched desc includes all hints as bullets; hint_count correct
  L1.4 assumption_hints non-empty + sandbox has .integrity.json (locked):
       verdict=locked_fallback_prompt; hint context written to _assumption_context_*.txt;
       no enriched desc file
  L1.5 sub_problem_id missing in yaml → verdict=parse_error; no temp file
  L1.6 Enriched description clamped at 4000 chars (desc truncated, hints preserved)
  L1.7 commit_reautoformalize.py Layer 1 invariant: only `theorem` field mutated;
       all other named fields byte-identical pre/post
  L1.8 reautoformalize_node.py writes ZERO yaml; yaml byte-identical pre/post

All tests use fixture yamls; no live LLM calls.
"""
from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from reautoformalize_node import (  # noqa: E402
    ENRICHED_DESC_MAX_CHARS,
    INTEGRITY_FILE,
    VERDICT_ENRICHING,
    VERDICT_LOCKED_FALLBACK,
    VERDICT_NO_HINTS,
    VERDICT_PARSE_ERROR,
    _build_enriched_desc,
    _check_locked,
    run_prep,
)
from commit_reautoformalize import (  # noqa: E402
    VERDICT_COMMITTED,
    apply_commit,
)

REAUTO = SCRIPTS_DIR / "reautoformalize_node.py"
COMMIT = SCRIPTS_DIR / "commit_reautoformalize.py"


# ── Shared fixture helpers ────────────────────────────────────────────


def _all_v2_fields() -> Dict[str, Any]:
    """Full v2 sorry_item row — all named fields populated.

    This is the canonical Layer 1 invariant reference: every non-theorem
    field must be byte-identical before/after commit_reautoformalize.py.
    """
    return {
        "id": "sub.t1",
        "file": "Lemma1.lean",
        "line": 10,
        "theorem": "original NL description of the sorry",
        "type": "ready",
        "depth": 2,
        "priority": 60,
        "estimated_lines": 25,
        "dependencies": ["sub.t0"],
        "unlocks": [],
        "state": "ACTIVE_PROVING",
        "children": [],
        "parent_id": "parent.p1",
        "history_log": [],
        "stuck_rounds": 2,
        "references": [],
        "coverage_state": "needs_proof",
        "attempts": 1,
        "citation_verified": False,
        "informal_round": 1,
        "coverage_stable": False,
        "assumption_hints": [
            "X is square-integrable",
            "the filtration is complete",
        ],
        "assumption_analysis": "Without integrability, finite expectation step fails.",
        "detailed_proof_plan": "Step 1: apply measurability lemma.",
        "direct_assembly": None,
        "proof_sketch": "Use Doob's inequality.",
        "done_reason": None,
        # migration-added fields (migrate_item_v1_to_v2 calls setdefault)
        "alternative_path": None,
        "library_hit": None,
        # H5 helper-web-probe field (webprobe_context; default "")
        "webprobe_context": "",
        # H6 helper-reference-probe field (referenceprobe_findings; default [])
        "referenceprobe_findings": [],
    }


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
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
    _make_backlog([_all_v2_fields()], p)
    return p


# ── L1.1 non-empty hints + Lean file absent (unlocked) ───────────────


def test_l1_1_hints_present_unlocked_writes_enrich_file(
    backlog: Path, sandbox: Path
) -> None:
    """Non-empty assumption_hints, no .integrity.json → verdict=enriching,
    enrich desc file written, yaml byte-identical (prep writes zero yaml)."""
    pre_yaml = backlog.read_bytes()

    payload = run_prep(backlog, "sub.t1", sandbox)

    assert payload["verdict"] == VERDICT_ENRICHING, f"got {payload}"
    assert payload["hint_count"] == 2

    # Enrich file exists
    enrich_file = Path(payload["enrich_file"])
    assert enrich_file.exists(), "enriched desc temp file not created"
    content = enrich_file.read_text(encoding="utf-8")
    assert "square-integrable" in content
    assert "filtration is complete" in content
    assert "Missing hypotheses" in content

    # yaml unchanged (L1.8)
    assert backlog.read_bytes() == pre_yaml, "yaml was mutated by prep script"


# ── L1.2 empty hints → no_hints ──────────────────────────────────────


def test_l1_2_empty_hints_no_op(tmp_path: Path, sandbox: Path) -> None:
    """assumption_hints=[] → verdict=no_hints; no temp file; yaml unchanged."""
    row = _all_v2_fields()
    row["assumption_hints"] = []
    row["assumption_analysis"] = ""
    backlog = tmp_path / "sorry_backlog.yaml"
    _make_backlog([row], backlog)
    pre_yaml = backlog.read_bytes()

    payload = run_prep(backlog, "sub.t1", sandbox)

    assert payload["verdict"] == VERDICT_NO_HINTS
    assert payload["hint_count"] == 0

    # No temp file
    for f in sandbox.iterdir():
        assert not f.name.startswith("_enrich_desc_"), f"unexpected file: {f}"
        assert not f.name.startswith("_assumption_context_"), f"unexpected file: {f}"

    assert backlog.read_bytes() == pre_yaml


# ── L1.3 non-empty hints + Lean file exists (unlocked) ───────────────


def test_l1_3_hints_lean_file_present_unlocked(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """assumption_hints present, Lean file exists in sandbox (but no
    .integrity.json) → verdict=enriching; all hints in bullet form."""
    # Write a fake Lean file in the sandbox
    lean_file = sandbox / "Lemma1.lean"
    lean_file.write_text("theorem foo : True := by sorry\n")

    payload = run_prep(backlog, "sub.t1", sandbox)

    assert payload["verdict"] == VERDICT_ENRICHING
    assert payload["hint_count"] == 2

    enrich_file = Path(payload["enrich_file"])
    content = enrich_file.read_text(encoding="utf-8")
    assert "- X is square-integrable" in content
    assert "- the filtration is complete" in content


# ── L1.4 .integrity.json present → locked_fallback_prompt ────────────


def test_l1_4_integrity_json_present_fallback_path(
    backlog: Path, sandbox: Path
) -> None:
    """.integrity.json in sandbox → verdict=locked_fallback_prompt;
    _assumption_context_*.txt written; no _enrich_desc_* file.

    D-2 fixture: create a valid-schema .integrity.json (mirrors
    toolRunner.ts IntegrityManifest shape) to simulate a locked state.
    """
    integrity = {
        "signatures": [
            {"name": "foo", "sig": "theorem foo : True := by sorry"}
        ],
        "createdAt": "2026-04-30T00:00:00.000Z",
        "source": "lock_signatures",
    }
    (sandbox / INTEGRITY_FILE).write_text(
        json.dumps(integrity), encoding="utf-8"
    )

    payload = run_prep(backlog, "sub.t1", sandbox)

    assert payload["verdict"] == VERDICT_LOCKED_FALLBACK
    assert payload["hint_count"] == 2

    # Context file written
    context_file = sandbox / f"_assumption_context_sub.t1.txt"
    assert context_file.exists(), "hint context file not created"
    ctx_text = context_file.read_text(encoding="utf-8")
    assert "square-integrable" in ctx_text
    assert "filtration is complete" in ctx_text
    assert "missing" in ctx_text.lower()

    # No enrich desc file
    for f in sandbox.iterdir():
        assert not f.name.startswith("_enrich_desc_"), f"unexpected enrich file: {f}"


def test_l1_4_check_locked_detects_integrity_file(tmp_path: Path) -> None:
    """_check_locked returns True when .integrity.json exists, False otherwise."""
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    assert _check_locked(sandbox) is False

    (sandbox / INTEGRITY_FILE).write_text("{}", encoding="utf-8")
    assert _check_locked(sandbox) is True


# ── L1.5 sub_problem_id missing → parse_error ────────────────────────


def test_l1_5_missing_sub_problem_id(backlog: Path, sandbox: Path) -> None:
    """sub_problem_id not in yaml → verdict=parse_error; no temp file."""
    payload = run_prep(backlog, "nonexistent.id", sandbox)

    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert "error" in payload

    for f in sandbox.iterdir():
        assert not f.name.startswith("_enrich_desc_"), f"unexpected file: {f}"
        assert not f.name.startswith("_assumption_context_"), f"unexpected file: {f}"


# ── L1.6 enriched description clamped at 4000 chars ──────────────────


def test_l1_6_enriched_desc_clamped_at_4000_chars() -> None:
    """When original theorem + hints exceed 4000 chars, truncate theorem
    from the end (preserve all hints). D-5."""
    # 5 long hints of ~400 chars each
    long_hints = [
        "h" * 390 + f" hypothesis_{i}"
        for i in range(5)
    ]
    long_theorem = "original theorem " + "x" * 2000

    result = _build_enriched_desc(long_theorem, long_hints, "")

    assert len(result) <= ENRICHED_DESC_MAX_CHARS, (
        f"clamped result len {len(result)} exceeds cap {ENRICHED_DESC_MAX_CHARS}"
    )
    # All hints must be present (asymmetric truncation: hints take priority)
    for h in long_hints:
        assert h in result, f"hint truncated: {h[:40]}..."


def test_l1_6_pathological_suffix_overflow_truncates_suffix() -> None:
    """Pathological case: hints+analysis suffix alone exceeds 4000 chars.

    Unreachable under H7's normal output (≤5 hints × ≤400 chars ≈ 2000
    chars suffix max), but defensive: when budget for the original
    theorem goes negative, the suffix itself is truncated to fit
    ENRICHED_DESC_MAX_CHARS, possibly dropping later hints.

    H4-reauto §8 code review S5-3 fixup: explicit coverage for the
    `budget < 0` branch in `_build_enriched_desc`.
    """
    # 6 hints × 700 chars = 4200 chars suffix, exceeds 4000 char cap
    huge_hints = [
        "h" * 690 + f" hypothesis_{i}"
        for i in range(6)
    ]
    short_theorem = "T"

    result = _build_enriched_desc(short_theorem, huge_hints, "")

    # Result must still fit the cap (suffix-truncation engages)
    assert len(result) <= ENRICHED_DESC_MAX_CHARS, (
        f"pathological suffix not truncated: len {len(result)} > "
        f"cap {ENRICHED_DESC_MAX_CHARS}"
    )


def test_l1_6_short_inputs_not_truncated() -> None:
    """Short theorem + 2 hints: result < 4000 chars; all content preserved."""
    result = _build_enriched_desc(
        "Lemma about measurability of martingale X.",
        ["X is square-integrable", "the filtration is complete"],
        "Without integrability the proof stalls.",
    )
    assert len(result) < ENRICHED_DESC_MAX_CHARS
    assert "X is square-integrable" in result
    assert "filtration is complete" in result
    assert "Missing hypotheses" in result
    # Analysis included (Q-3 resolution)
    assert "Analysis" in result
    assert "integrability" in result


# ── L1.7 commit_reautoformalize Layer 1 invariant ────────────────────


def test_l1_7_commit_only_mutates_theorem_field(
    tmp_path: Path, sandbox: Path
) -> None:
    """commit_reautoformalize.apply_commit mutates ONLY `theorem`.
    All 18 other named fields on the targeted row are byte-identical pre/post.
    """
    row = _all_v2_fields()
    backlog = tmp_path / "sorry_backlog.yaml"
    _make_backlog([row], backlog)

    # Snapshot all fields except `theorem`
    pre_data = yaml.safe_load(backlog.read_text())
    pre_row = next(it for it in pre_data["sorry_items"] if it["id"] == "sub.t1")
    pre_row_no_theorem = {k: v for k, v in pre_row.items() if k != "theorem"}

    enriched_theorem = (
        "original NL description of the sorry\n\n"
        "**Missing hypotheses (from diagnostics):**\n"
        "- X is square-integrable\n"
        "- the filtration is complete"
    )
    payload = apply_commit(backlog, "sub.t1", enriched_theorem)

    assert payload["verdict"] == VERDICT_COMMITTED
    assert payload["new_theorem_len"] == len(enriched_theorem)

    # Post-write: only `theorem` changed
    post_data = yaml.safe_load(backlog.read_text())
    post_row = next(it for it in post_data["sorry_items"] if it["id"] == "sub.t1")

    assert post_row["theorem"] == enriched_theorem, "theorem field not updated"

    post_row_no_theorem = {k: v for k, v in post_row.items() if k != "theorem"}
    changed = {
        k for k in pre_row_no_theorem
        if pre_row_no_theorem.get(k) != post_row_no_theorem.get(k)
    }
    assert post_row_no_theorem == pre_row_no_theorem, (
        f"Fields changed beyond `theorem`: {changed}"
    )


# ── L1.8 reautoformalize_node writes ZERO yaml ───────────────────────


def test_l1_8_prep_writes_zero_yaml(backlog: Path, sandbox: Path) -> None:
    """reautoformalize_node.run_prep writes zero yaml.
    yaml byte-identical before and after run. (Mirrors spec §5 L1.1.)"""
    pre_bytes = backlog.read_bytes()
    run_prep(backlog, "sub.t1", sandbox)
    post_bytes = backlog.read_bytes()
    assert pre_bytes == post_bytes, "prep script wrote yaml (invariant violated)"


# ── Bonus: parse_error path on missing backlog ────────────────────────


def test_missing_backlog_returns_parse_error(tmp_path: Path, sandbox: Path) -> None:
    """If backlog file doesn't exist, run_prep returns parse_error."""
    payload = run_prep(
        tmp_path / "nonexistent.yaml", "sub.t1", sandbox
    )
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert "error" in payload


# ── CLI subprocess smoke ─────────────────────────────────────────────


def test_cli_reauto_node_exits_0_on_enriching(
    backlog: Path, sandbox: Path
) -> None:
    """CLI: exits 0 and emits reautoformalized milestone with verdict=enriching."""
    r = subprocess.run(
        [
            "python3", str(REAUTO),
            "--sub-problem-id", "sub.t1",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, f"CLI failed: {r.stderr}"

    events = sandbox / "events.jsonl"
    assert events.exists()
    milestones = [
        json.loads(l)
        for l in events.read_text().splitlines()
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    ms = [m for m in milestones if m.get("name") == "reautoformalized"]
    assert len(ms) == 1
    assert ms[0]["details"]["verdict"] == VERDICT_ENRICHING


def test_cli_commit_exits_0_and_emits_committed(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """CLI: commit script exits 0 and emits verdict=committed."""
    enrich_text = (
        "original NL description of the sorry\n\n"
        "**Missing hypotheses (from diagnostics):**\n"
        "- X is square-integrable"
    )
    enrich_file = tmp_path / "_enrich_desc_sub.t1_1.txt"
    enrich_file.write_text(enrich_text, encoding="utf-8")

    r = subprocess.run(
        [
            "python3", str(COMMIT),
            "--sub-problem-id", "sub.t1",
            "--enriched-theorem-file", str(enrich_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 0, f"CLI failed: {r.stderr}"

    events = sandbox / "events.jsonl"
    milestones = [
        json.loads(l)
        for l in events.read_text().splitlines()
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    ms = [m for m in milestones if m.get("name") == "reautoformalized"]
    assert len(ms) == 1
    assert ms[0]["details"]["verdict"] == VERDICT_COMMITTED

    # Yaml updated
    post = yaml.safe_load(backlog.read_text())
    row = next(it for it in post["sorry_items"] if it["id"] == "sub.t1")
    assert row["theorem"] == enrich_text

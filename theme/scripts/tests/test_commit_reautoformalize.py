"""H4-reautoformalize L1 unit tests for commit_reautoformalize.py.

Per `docs/H4_REAUTOFORMALIZE_SPEC.md` §8.1 — commit-side tests.
Covers:
  L1.7 Layer 1 invariant: ONLY `theorem` field mutated; all other named
       fields byte-identical pre/post write.
  Additional: missing backlog, missing sub_problem_id, enrich-file not found.

The L2 integration test (test_reautoformalize_integration.py) covers the
full two-script pipeline end-to-end.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from commit_reautoformalize import (  # noqa: E402
    VERDICT_COMMITTED,
    VERDICT_PARSE_ERROR,
    apply_commit,
)

COMMIT = SCRIPTS_DIR / "commit_reautoformalize.py"


# ── Fixture helpers ──────────────────────────────────────────────────


def _full_v2_row() -> Dict[str, Any]:
    """All 19 named v2 fields (theorem + 18 others) — canonical Layer 1 ref."""
    return {
        "id": "commit.c1",
        "file": "Lemma4.lean",
        "line": 12,
        "theorem": "original theorem text before enrichment",
        "type": "ready",
        "depth": 1,
        "priority": 70,
        "estimated_lines": 30,
        "dependencies": [],
        "unlocks": ["commit.c2"],
        "state": "ACTIVE_PROVING",
        "children": [],
        "parent_id": "parent.q1",
        "history_log": [{"round": 1, "event": "stuck"}],
        "stuck_rounds": 1,
        "references": [],
        "coverage_state": "needs_proof",
        "attempts": 3,
        "citation_verified": False,
        "informal_round": 2,
        "coverage_stable": False,
        "assumption_hints": ["f is measurable", "the measure is sigma-finite"],
        "assumption_analysis": "Measurability required for integration step.",
        "detailed_proof_plan": "Step 1: apply Fubini.",
        "direct_assembly": None,
        "proof_sketch": "Use dominated convergence.",
        "done_reason": None,
        # migration-added fields (migrate_item_v1_to_v2 setdefault)
        "alternative_path": None,
        "library_hit": None,
        # H5 webprobe (setdefault "")
        "webprobe_context": "",
        # H6 reference probe (setdefault [])
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
    _make_backlog([_full_v2_row()], p)
    return p


# ── L1.7 Layer 1 invariant ───────────────────────────────────────────


def test_l1_7_only_theorem_field_mutated(
    backlog: Path,
) -> None:
    """commit_reautoformalize.apply_commit mutates ONLY `theorem`.
    All 18 other named fields on the targeted row are byte-identical
    pre/post write. All other rows (none here, but generalized test
    checks every non-theorem key).
    """
    pre_data = yaml.safe_load(backlog.read_text())
    pre_row = next(
        it for it in pre_data["sorry_items"] if it["id"] == "commit.c1"
    )
    pre_snapshot = dict(pre_row)

    enriched = (
        "original theorem text before enrichment\n\n"
        "**Missing hypotheses (from diagnostics):**\n"
        "- f is measurable\n"
        "- the measure is sigma-finite"
    )
    payload = apply_commit(backlog, "commit.c1", enriched)

    assert payload["verdict"] == VERDICT_COMMITTED
    assert payload["old_theorem_len"] == len("original theorem text before enrichment")
    assert payload["new_theorem_len"] == len(enriched)

    post_data = yaml.safe_load(backlog.read_text())
    post_row = next(
        it for it in post_data["sorry_items"] if it["id"] == "commit.c1"
    )

    # theorem updated
    assert post_row["theorem"] == enriched

    # Every other field byte-identical
    protected_fields = [k for k in pre_snapshot if k != "theorem"]
    for field in protected_fields:
        assert post_row.get(field) == pre_snapshot[field], (
            f"Field `{field}` changed: pre={pre_snapshot[field]!r} "
            f"post={post_row.get(field)!r}"
        )


def test_l1_7_other_rows_unchanged(tmp_path: Path) -> None:
    """Commit to row A must not touch row B."""
    row_a = _full_v2_row()
    row_b = dict(_full_v2_row())
    row_b["id"] = "commit.c2"
    row_b["theorem"] = "completely different theorem"

    backlog = tmp_path / "sorry_backlog.yaml"
    _make_backlog([row_a, row_b], backlog)
    pre_row_b = dict(yaml.safe_load(backlog.read_text())["sorry_items"][1])

    apply_commit(backlog, "commit.c1", "enriched text")

    post_data = yaml.safe_load(backlog.read_text())
    post_row_b = next(it for it in post_data["sorry_items"] if it["id"] == "commit.c2")
    assert post_row_b == pre_row_b, f"Row B was mutated: {post_row_b}"


# ── Error paths ──────────────────────────────────────────────────────


def test_missing_sub_problem_id_raises_value_error(
    backlog: Path,
) -> None:
    """sub_problem_id not in yaml → raises ValueError."""
    with pytest.raises(ValueError, match="not in sorry_items"):
        apply_commit(backlog, "nonexistent.id", "enriched text")


def test_cli_missing_enrich_file_exits_2(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """CLI: non-existent enriched-theorem-file → exit 2."""
    r = subprocess.run(
        [
            "python3", str(COMMIT),
            "--sub-problem-id", "commit.c1",
            "--enriched-theorem-file", str(tmp_path / "nonexistent.txt"),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 2, f"expected exit 2, got {r.returncode}"


def test_cli_missing_sub_problem_id_exits_2(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """CLI: sub_problem_id missing in yaml → exit 2."""
    enrich_file = tmp_path / "enrich.txt"
    enrich_file.write_text("some text", encoding="utf-8")
    r = subprocess.run(
        [
            "python3", str(COMMIT),
            "--sub-problem-id", "does.not.exist",
            "--enriched-theorem-file", str(enrich_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True,
    )
    assert r.returncode == 2, f"expected exit 2, got {r.returncode}"

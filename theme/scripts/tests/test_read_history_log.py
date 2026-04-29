"""L1 unit tests for read_history_log.py (czy newloop port slice 2).

Coverage:
  - Empty history_log → empty string
  - Single entry → exact format match against czy informalAgent.ts:741-763
  - Multi-entry → entries listed in insertion order (oldest first)
  - Slice lengths: decision_reason 500, description 300, fail_reason 200
  - Proved results filtered out (czy informalAgent.ts:754)
  - ACTION trailer present iff history non-empty
  - Node not in backlog → empty string (graceful, not raise)
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from read_history_log import (  # noqa: E402
    SLICE_DECISION,
    SLICE_DESCRIPTION,
    SLICE_FAIL_REASON,
    format_history_block,
    read_history_for_node,
)


# ── format_history_block ─────────────────────────────────────────────


def test_empty_log_returns_empty() -> None:
    assert format_history_block([]) == ""


def test_single_entry_byte_match() -> None:
    """Output must MATCH czy informalAgent.ts:742-763 exactly."""
    log = [
        {
            "iteration": 1,
            "decomposition": ["a", "b", "c"],
            "decision_reason": "induction on n",
            "decomposition_details": [
                {"id": "a", "description": "base case"},
                {"id": "c", "description": "step case at n+1"},
            ],
            "results": [
                {"sub_problem_id": "a", "status": "proved"},
                {"sub_problem_id": "b", "status": "proved"},
                {"sub_problem_id": "c", "status": "stuck", "fail_reason": "type mismatch"},
            ],
            "retreat_reason": "stuck_rounds reached 3",
        }
    ]
    out = format_history_block(log)
    expected = (
        "## Previous attempt history (DO NOT repeat failed strategies)\n"
        "- Iteration 1: decomposed into [a, b, c]\n"
        "    Reason: induction on n\n"
        "    a: base case\n"
        "    c: step case at n+1\n"
        "  - c: stuck (type mismatch)\n"
        "  Retreat reason: stuck_rounds reached 3\n"
        "ACTION: Choose a DIFFERENT decomposition strategy from previous attempts.\n"
    )
    assert out == expected


def test_multi_entry_chronological_order() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["x"],
            "results": [{"sub_problem_id": "x", "status": "stuck"}],
            "retreat_reason": "first try",
        },
        {
            "iteration": 2,
            "decomposition": ["y"],
            "results": [{"sub_problem_id": "y", "status": "stuck"}],
            "retreat_reason": "second try",
        },
    ]
    out = format_history_block(log)
    # First entry appears before second
    pos1 = out.index("Iteration 1")
    pos2 = out.index("Iteration 2")
    assert pos1 < pos2
    assert "first try" in out
    assert "second try" in out
    # Single trailing ACTION line, not per entry
    assert out.count("ACTION:") == 1


def test_proved_results_filtered_out() -> None:
    """Per czy informalAgent.ts:754, only non-proved results are listed."""
    log = [
        {
            "iteration": 1,
            "decomposition": ["a", "b"],
            "results": [
                {"sub_problem_id": "a", "status": "proved"},
                {"sub_problem_id": "b", "status": "stuck", "fail_reason": "x"},
            ],
        }
    ]
    out = format_history_block(log)
    # The proved one ("a: proved") should NOT appear as a "  - a: proved" line
    assert "  - a: proved" not in out
    # The stuck one should appear
    assert "  - b: stuck" in out


def test_decision_reason_sliced_to_500() -> None:
    long_reason = "x" * 1000
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "results": [{"sub_problem_id": "a", "status": "stuck"}],
            "decision_reason": long_reason,
        }
    ]
    out = format_history_block(log)
    # Find the Reason: line
    reason_line = [ln for ln in out.split("\n") if ln.startswith("    Reason:")][0]
    payload = reason_line[len("    Reason: "):]
    assert len(payload) == SLICE_DECISION
    assert payload == "x" * SLICE_DECISION


def test_description_sliced_to_300() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "decomposition_details": [{"id": "a", "description": "y" * 500}],
            "results": [{"sub_problem_id": "a", "status": "stuck"}],
        }
    ]
    out = format_history_block(log)
    desc_line = [ln for ln in out.split("\n") if ln.startswith("    a:")][0]
    payload = desc_line[len("    a: "):]
    assert len(payload) == SLICE_DESCRIPTION


def test_fail_reason_sliced_to_200() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "results": [
                {"sub_problem_id": "a", "status": "stuck", "fail_reason": "z" * 500},
            ],
        }
    ]
    out = format_history_block(log)
    line = [ln for ln in out.split("\n") if ln.startswith("  - a:")][0]
    # Format: "  - a: stuck (zzz...)"
    paren_open = line.index("(")
    paren_close = line.rindex(")")
    payload = line[paren_open + 1:paren_close]
    assert len(payload) == SLICE_FAIL_REASON


def test_no_decision_reason_skips_reason_line() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "results": [{"sub_problem_id": "a", "status": "stuck"}],
        }
    ]
    out = format_history_block(log)
    assert "Reason:" not in out


def test_no_retreat_reason_skips_retreat_line() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "results": [{"sub_problem_id": "a", "status": "stuck"}],
        }
    ]
    out = format_history_block(log)
    assert "Retreat reason:" not in out


def test_no_decomposition_details_skips_per_child_lines() -> None:
    log = [
        {
            "iteration": 1,
            "decomposition": ["a"],
            "results": [{"sub_problem_id": "a", "status": "stuck"}],
        }
    ]
    out = format_history_block(log)
    # Output should NOT contain a "    a: <description>" line
    desc_lines = [ln for ln in out.split("\n") if ln.startswith("    a:")]
    assert desc_lines == []


def test_action_trailer_only_when_non_empty() -> None:
    assert "ACTION:" not in format_history_block([])
    assert "ACTION:" in format_history_block([
        {"iteration": 1, "decomposition": [], "results": []}
    ])


# ── read_history_for_node ────────────────────────────────────────────


def _write_yaml(path: Path, items: list, schema_v2: bool = True) -> None:
    data = {"sorry_items": items}
    if schema_v2:
        data["schema_version"] = 2
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def test_read_history_node_found_with_history(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    _write_yaml(backlog, [
        {
            "id": "foo",
            "history_log": [
                {
                    "iteration": 1,
                    "decomposition": ["a"],
                    "results": [{"sub_problem_id": "a", "status": "stuck"}],
                    "retreat_reason": "r",
                }
            ],
        }
    ])
    out = read_history_for_node(backlog, "foo")
    assert "Iteration 1" in out
    assert "ACTION:" in out


def test_read_history_node_not_found_returns_empty(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    _write_yaml(backlog, [{"id": "foo", "history_log": []}])
    assert read_history_for_node(backlog, "ghost") == ""


def test_read_history_empty_log_returns_empty(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    _write_yaml(backlog, [{"id": "foo", "history_log": []}])
    assert read_history_for_node(backlog, "foo") == ""


def test_read_history_missing_backlog_returns_empty(tmp_path: Path) -> None:
    assert read_history_for_node(tmp_path / "nope.yaml", "foo") == ""


def test_read_history_handles_v1_yaml(tmp_path: Path) -> None:
    """A v1 yaml (no schema_version, no history_log) should be migrated
    on read; result is empty since no history exists yet."""
    backlog = tmp_path / "b.yaml"
    _write_yaml(backlog, [{"id": "foo", "stuck_rounds": 0}], schema_v2=False)
    assert read_history_for_node(backlog, "foo") == ""


# ── Differentiation evidence ─────────────────────────────────────────


def test_module_present_marker() -> None:
    from read_history_log import format_history_block as _fmt  # noqa: F401
    assert callable(_fmt)

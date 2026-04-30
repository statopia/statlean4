"""H4 L1 unit tests for `_stuck_context.py` — StuckContext assembly.

Coverage matrix per `docs/H4_DISPATCH_HELPER_SPEC.md` §7.1 (companion file):

  L1.A: events.jsonl has 1 subagent-stuck event for sub_problem_id →
        lastError extracted; clamped to 200 chars
  L1.B: events.jsonl has 5+ subagent-stuck events → deadEnds collects
        last 5 unique blockers (de-duped by 80-char prefix)
  L1.C: events.jsonl absent → assemble returns empty StuckContext (all
        fields None)
  L1.D: parent history_log has 2 retreat entries → deadEnds includes
        both retreatReason strings
  L1.E: codeAttempted reads sandbox file at target_line ± 20 lines;
        clamped to 800 chars

Plus a few helpers / corner cases for robustness.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from _stuck_context import (  # noqa: E402
    StuckContext,
    _clamp,
    _dedupe_by_prefix,
    _read_events_jsonl,
    _stuck_events_for,
    assemble_stuck_context,
)


# ── Fixture helpers ──────────────────────────────────────────────────


def _write_events_jsonl(sandbox: Path, events: List[Dict[str, Any]]) -> None:
    path = sandbox / "events.jsonl"
    with path.open("w", encoding="utf-8") as f:
        for ev in events:
            f.write(json.dumps(ev, ensure_ascii=False) + "\n")


def _stuck_event(sorry_id: str, blocker: str, ts: int = 0) -> Dict[str, Any]:
    return {
        "ts": ts,
        "kind": "sandbox_milestone",
        "name": "subagent-stuck",
        "details": {"sorry_id": sorry_id, "blocker": blocker},
    }


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


# ── Pure helpers ─────────────────────────────────────────────────────


def test_clamp_short_string_returned_unchanged() -> None:
    assert _clamp("hello", 200) == "hello"


def test_clamp_long_string_truncated() -> None:
    s = "x" * 300
    assert _clamp(s, 200) == "x" * 200


def test_clamp_none_returns_none() -> None:
    assert _clamp(None, 200) is None


def test_clamp_whitespace_only_returns_none() -> None:
    assert _clamp("   ", 200) is None
    assert _clamp("\n\t\n", 200) is None


def test_clamp_strips_input() -> None:
    assert _clamp("  hello  ", 200) == "hello"


def test_dedupe_by_prefix_basic() -> None:
    items = ["abc def", "abc ghi", "xyz pqr"]
    assert _dedupe_by_prefix(items, 3) == ["abc def", "xyz pqr"]


def test_dedupe_by_prefix_empty() -> None:
    assert _dedupe_by_prefix([], 80) == []


def test_dedupe_by_prefix_preserves_order_keeps_first() -> None:
    items = ["A first", "B middle", "A second"]
    # 1-char prefix collapses A-* together; first wins.
    assert _dedupe_by_prefix(items, 1) == ["A first", "B middle"]


# ── L1.A: lastError extracted from most-recent stuck event ───────────


def test_l1_a_last_error_extracted_from_single_stuck_event(sandbox: Path) -> None:
    """events.jsonl has 1 subagent-stuck event → lastError = blocker
    string (clamped to 200 chars)."""
    _write_events_jsonl(sandbox, [
        _stuck_event("sub.s1", "type mismatch: expected MeasurableSet, got Set"),
    ])
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error == "type mismatch: expected MeasurableSet, got Set"
    assert ctx.dead_ends == ["type mismatch: expected MeasurableSet, got Set"]


def test_l1_a_last_error_clamped_to_200_chars(sandbox: Path) -> None:
    big = "X" * 500
    _write_events_jsonl(sandbox, [_stuck_event("sub.s1", big)])
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error is not None
    assert len(ctx.last_error) == 200


def test_l1_a_most_recent_stuck_wins(sandbox: Path) -> None:
    """Multiple stuck events for same sorry → lastError == LAST one's
    blocker (matches czy `pendingEntry.lastError` semantic)."""
    _write_events_jsonl(sandbox, [
        _stuck_event("sub.s1", "first error", ts=100),
        _stuck_event("sub.s1", "second error", ts=200),
        _stuck_event("sub.s1", "third error (most recent)", ts=300),
    ])
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error == "third error (most recent)"


def test_l1_a_other_sorries_ignored(sandbox: Path) -> None:
    """Stuck events for OTHER sub_problem_ids are ignored — last_error
    must come from the queried id only."""
    _write_events_jsonl(sandbox, [
        _stuck_event("sub.other", "wrong sorry", ts=300),
        _stuck_event("sub.s1", "right sorry", ts=200),
    ])
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error == "right sorry"


# ── L1.B: deadEnds collects last 5 unique, dedup by 80-char prefix ───


def test_l1_b_dead_ends_collects_last_5(sandbox: Path) -> None:
    """events.jsonl has 6 distinct stuck events → deadEnds keeps
    the LAST 5 (czy proofLoop.ts:724 .slice(-5)). All 6 are
    distinct so de-dupe is a no-op."""
    events = [
        _stuck_event("sub.s1", f"error variant {i}", ts=100 + i)
        for i in range(6)
    ]
    _write_events_jsonl(sandbox, events)
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.dead_ends is not None
    assert len(ctx.dead_ends) == 5
    # The last 5 (variants 1..5) are kept; variant 0 is dropped.
    assert ctx.dead_ends == [
        "error variant 1",
        "error variant 2",
        "error variant 3",
        "error variant 4",
        "error variant 5",
    ]


def test_l1_b_dead_ends_dedupes_by_80_char_prefix(sandbox: Path) -> None:
    """Two stuck events whose first 80 chars are identical → only one
    survives dedup."""
    same_prefix = "type mismatch: expected MeasurableSet, got Set when applying continuous_of_lipschitz"
    assert len(same_prefix) >= 80
    _write_events_jsonl(sandbox, [
        _stuck_event("sub.s1", same_prefix + " (occurrence 1)", ts=100),
        _stuck_event("sub.s1", same_prefix + " (occurrence 2)", ts=200),
    ])
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.dead_ends is not None
    assert len(ctx.dead_ends) == 1
    # First occurrence wins (de-dupe is order-preserving on first match).
    assert ctx.dead_ends[0].startswith("type mismatch: expected MeasurableSet")


# ── L1.C: events.jsonl absent → empty StuckContext ───────────────────


def test_l1_c_missing_events_jsonl_returns_empty_context(sandbox: Path) -> None:
    """No events.jsonl in sandbox → all fields None (graceful
    degradation per spec §3.4 R3)."""
    # Don't write events.jsonl
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error is None
    assert ctx.dead_ends is None
    assert ctx.code_attempted is None
    assert ctx.current_goal is None
    # to_dict() drops all None / empty
    assert ctx.to_dict() == {}


def test_l1_c_empty_events_jsonl_returns_empty_context(sandbox: Path) -> None:
    """events.jsonl exists but is empty → all fields None."""
    (sandbox / "events.jsonl").write_text("")
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.to_dict() == {}


def test_l1_c_corrupt_lines_skipped_silently(sandbox: Path) -> None:
    """Corrupt lines in events.jsonl don't abort assembly; the good
    lines still produce valid context."""
    path = sandbox / "events.jsonl"
    with path.open("w") as f:
        f.write("not json at all\n")
        f.write(json.dumps(_stuck_event("sub.s1", "real error")) + "\n")
        f.write("{also not json\n")
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.last_error == "real error"


# ── L1.D: parent history_log feeds deadEnds ──────────────────────────


def test_l1_d_history_log_retreat_reasons_included(sandbox: Path) -> None:
    """parent history_log[*].retreat_reason → deadEnds (last 3 entries
    per spec §3.4 augmentation)."""
    _write_events_jsonl(sandbox, [
        _stuck_event("sub.s1", "stuck blocker A"),
    ])
    history = [
        {"iteration": 0, "retreat_reason": "first restrategize"},
        {"iteration": 1, "retreat_reason": "second restrategize"},
    ]
    ctx = assemble_stuck_context(sandbox, "sub.s1", parent_history_log=history)
    assert ctx.dead_ends is not None
    # Both retreat reasons present, plus the blocker, in the right order.
    assert "first restrategize" in ctx.dead_ends
    assert "second restrategize" in ctx.dead_ends
    assert "stuck blocker A" in ctx.dead_ends


def test_l1_d_history_log_keeps_only_last_3(sandbox: Path) -> None:
    """4 history entries → last 3 retreat_reasons kept."""
    history = [
        {"iteration": i, "retreat_reason": f"retreat {i}"}
        for i in range(4)
    ]
    ctx = assemble_stuck_context(sandbox, "sub.s1", parent_history_log=history)
    assert ctx.dead_ends is not None
    # Last 3 kept (retreat 1, retreat 2, retreat 3); retreat 0 dropped.
    assert "retreat 0" not in ctx.dead_ends
    assert "retreat 1" in ctx.dead_ends
    assert "retreat 2" in ctx.dead_ends
    assert "retreat 3" in ctx.dead_ends


def test_l1_d_history_entries_without_retreat_reason_skipped(
    sandbox: Path
) -> None:
    """Entries with missing/empty retreat_reason are ignored."""
    history = [
        {"iteration": 0},  # no retreat_reason at all
        {"iteration": 1, "retreat_reason": ""},  # empty
        {"iteration": 2, "retreat_reason": "real reason"},
    ]
    ctx = assemble_stuck_context(sandbox, "sub.s1", parent_history_log=history)
    assert ctx.dead_ends is not None
    assert ctx.dead_ends == ["real reason"]


# ── L1.E: codeAttempted reads sandbox file at target_line ± 20 ───────


def test_l1_e_code_attempted_reads_window(sandbox: Path) -> None:
    """A .lean file at target_line is read with ±20 line window."""
    lean_path = sandbox / "Main.lean"
    lines = [f"-- line {i}" for i in range(1, 100)]
    lean_path.write_text("\n".join(lines))

    ctx = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="Main.lean",
        target_line=50,
    )
    assert ctx.code_attempted is not None
    # Window is 20 lines either side around line 50 → lines 30..70
    assert "-- line 50" in ctx.code_attempted
    assert "-- line 30" in ctx.code_attempted
    assert "-- line 70" in ctx.code_attempted
    # Outside window
    assert "-- line 1\n" not in ctx.code_attempted
    assert "-- line 99" not in ctx.code_attempted


def test_l1_e_code_attempted_clamped_to_800(sandbox: Path) -> None:
    """Long lines push snippet over 800 chars → truncated."""
    lean_path = sandbox / "Main.lean"
    # Each line is 100 chars; 41 lines × 100 = 4100 chars >> 800
    long_line = "X" * 99
    lines = [long_line for _ in range(100)]
    lean_path.write_text("\n".join(lines))
    ctx = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="Main.lean",
        target_line=50,
    )
    assert ctx.code_attempted is not None
    assert len(ctx.code_attempted) == 800


def test_l1_e_missing_file_yields_none(sandbox: Path) -> None:
    """file_rel pointing to nonexistent file → code_attempted None."""
    ctx = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="DoesNotExist.lean",
        target_line=10,
    )
    assert ctx.code_attempted is None


def test_l1_e_target_line_zero_yields_none(sandbox: Path) -> None:
    """target_line == 0 (or None) → code_attempted None."""
    lean_path = sandbox / "Main.lean"
    lean_path.write_text("only line\n")
    ctx_zero = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="Main.lean",
        target_line=0,
    )
    ctx_none = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="Main.lean",
        target_line=None,
    )
    assert ctx_zero.code_attempted is None
    assert ctx_none.code_attempted is None


def test_l1_e_path_traversal_refused(sandbox: Path, tmp_path: Path) -> None:
    """file_rel that escapes sandbox → code_attempted None (defense)."""
    outside = tmp_path / "outside.lean"
    outside.write_text("secret\n" * 50)
    ctx = assemble_stuck_context(
        sandbox, "sub.s1",
        file_rel="../outside.lean",
        target_line=5,
    )
    assert ctx.code_attempted is None


# ── current_goal pass-through ────────────────────────────────────────


def test_current_goal_passes_through_clamped(sandbox: Path) -> None:
    """The agent-side LSP probe's currentGoal is clamped to 1500 chars."""
    long_goal = "G " * 1000  # 2000 chars
    ctx = assemble_stuck_context(
        sandbox, "sub.s1",
        current_goal=long_goal,
    )
    assert ctx.current_goal is not None
    assert len(ctx.current_goal) == 1500


def test_current_goal_none_when_unset(sandbox: Path) -> None:
    ctx = assemble_stuck_context(sandbox, "sub.s1")
    assert ctx.current_goal is None


# ── to_dict shape ────────────────────────────────────────────────────


def test_to_dict_drops_none_fields(sandbox: Path) -> None:
    """StuckContext.to_dict() omits None / empty fields so JSON is minimal."""
    ctx = StuckContext(
        last_error="boom",
        dead_ends=None,
        current_goal=None,
        code_attempted=None,
    )
    assert ctx.to_dict() == {"lastError": "boom"}


def test_to_dict_emits_camelcase_keys(sandbox: Path) -> None:
    """Keys must match czy StuckContext (camelCase) for forward-compat
    with H5/H6 placeholders that consume the JSON file."""
    ctx = StuckContext(
        current_goal="goal text",
        last_error="err",
        dead_ends=["a", "b"],
        code_attempted="code",
    )
    d = ctx.to_dict()
    assert set(d.keys()) == {
        "currentGoal", "lastError", "deadEnds", "codeAttempted"
    }


# ── Internal helpers ─────────────────────────────────────────────────


def test_read_events_jsonl_missing_returns_empty(sandbox: Path) -> None:
    assert _read_events_jsonl(sandbox) == []


def test_stuck_events_for_filters_correctly(sandbox: Path) -> None:
    events = [
        {"kind": "sandbox_milestone", "name": "sorry-proved",
         "details": {"sorry_id": "sub.s1"}},  # wrong milestone name
        {"kind": "step", "id": 1, "status": "start"},  # wrong kind
        _stuck_event("sub.s1", "B"),
        _stuck_event("sub.s2", "C"),  # wrong sorry
    ]
    matched = _stuck_events_for(events, "sub.s1")
    assert len(matched) == 1
    assert matched[0]["details"]["blocker"] == "B"

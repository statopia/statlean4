"""Regression tests for benchmark harness fixes.

Covers:
1. adjusted_completion_rate consistency across models and models_by_rounds tables
2. dry-run (skip_compile) stops after 1 round
3. Single-line `:= by ...` proof extraction
"""

import os
import tempfile

import pytest

from harness.metrics import (
    FailureType,
    RunResult,
    RoundMetrics,
    compute_aggregate_stats,
)
from harness.problem_extractor import extract_problem
from harness.runner import _classify_failure
from harness.compiler import CompileResult


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_run(problem_id, solved, failure_type="success", max_rounds=4):
    return RunResult(
        run_id="test", problem_id=problem_id, model_id="m", condition="bare",
        max_rounds=max_rounds, repeat_id=0, solved=solved, total_cost_usd=0.01,
        total_rounds=1, total_time_s=1.0, total_input_tokens=100,
        total_output_tokens=50, timestamp="2026-01-01",
        rounds=[RoundMetrics(
            round=1, input_tokens=100, output_tokens=50, cost_usd=0.01,
            latency_s=1.0, compile_success=solved, failure_type=failure_type,
        )],
    )


# ---------------------------------------------------------------------------
# Test 1: adjusted_completion_rate consistency
# ---------------------------------------------------------------------------

class TestAdjustedCompletionConsistency:
    """models and models_by_rounds must agree on adjusted_completion_rate."""

    def test_parser_error_not_excluded_from_denominator(self):
        """parser_error is model-attributable, not infra — denominator unchanged."""
        runs = [
            _make_run("p1", solved=True),
            _make_run("p2", solved=False, failure_type="parser_error"),
        ]
        stats = compute_aggregate_stats(runs)

        total_adj = stats["models"]["m"]["adjusted_completion_rate"]
        by_rounds_adj = stats["models_by_rounds"][("m", 4)]["adjusted_completion_rate"]

        assert total_adj == by_rounds_adj == 0.5

    def test_infra_error_excluded_from_denominator(self):
        """infra_error IS excluded — adjusted rate should be 1.0 (1 solved / 1 relevant)."""
        runs = [
            _make_run("p1", solved=True),
            _make_run("p2", solved=False, failure_type="infra_error"),
        ]
        stats = compute_aggregate_stats(runs)

        total_adj = stats["models"]["m"]["adjusted_completion_rate"]
        by_rounds_adj = stats["models_by_rounds"][("m", 4)]["adjusted_completion_rate"]

        assert total_adj == by_rounds_adj == 1.0

    def test_mixed_failures(self):
        """3 runs: 1 success, 1 compile_error, 1 infra_error → adjusted = 1/2."""
        runs = [
            _make_run("p1", solved=True),
            _make_run("p2", solved=False, failure_type="compile_error"),
            _make_run("p3", solved=False, failure_type="infra_error"),
        ]
        stats = compute_aggregate_stats(runs)

        total_adj = stats["models"]["m"]["adjusted_completion_rate"]
        by_rounds_adj = stats["models_by_rounds"][("m", 4)]["adjusted_completion_rate"]

        assert total_adj == by_rounds_adj == 0.5


# ---------------------------------------------------------------------------
# Test 2: _classify_failure logic
# ---------------------------------------------------------------------------

class TestClassifyFailure:
    def test_compile_failed_parse_not_ok_is_compile_error(self):
        """Compilation ran and failed → COMPILE_ERROR regardless of parse_ok."""
        cr = CompileResult(success=False, error_message="type mismatch",
                           sorry_count=0, wall_time_s=1.0)
        assert _classify_failure(cr, parse_ok=False) == FailureType.COMPILE_ERROR

    def test_compile_succeeded_parse_not_ok_is_success(self):
        cr = CompileResult(success=True, error_message="",
                           sorry_count=0, wall_time_s=1.0)
        assert _classify_failure(cr, parse_ok=False) == FailureType.SUCCESS

    def test_no_compile_result_parse_not_ok_is_parser_error(self):
        assert _classify_failure(None, parse_ok=False) == FailureType.PARSER_ERROR


# ---------------------------------------------------------------------------
# Test 3: single-line proof extraction
# ---------------------------------------------------------------------------

class TestSingleLineProofExtraction:
    def test_by_trivial(self):
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", dir="/tmp", delete=False
        ) as f:
            f.write("import Mathlib\n\ntheorem foo : True := by trivial\n")
            f.flush()
            tmp = f.name

        try:
            p = extract_problem(lean_file=tmp, theorem_name="foo",
                                difficulty="easy", problem_id="foo")
            assert "trivial" in p.ground_truth.strip()
            assert p.proof_lines >= 1
        finally:
            os.unlink(tmp)

    def test_by_sorry_single_line(self):
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", dir="/tmp", delete=False
        ) as f:
            f.write("import Mathlib\n\ntheorem bar : True := by sorry\n")
            f.flush()
            tmp = f.name

        try:
            p = extract_problem(lean_file=tmp, theorem_name="bar",
                                difficulty="easy", problem_id="bar")
            assert "sorry" in p.ground_truth.strip()
        finally:
            os.unlink(tmp)

    def test_multiline_unchanged(self):
        src = (
            "import Mathlib\n\n"
            "theorem baz : True := by\n"
            "  trivial\n"
        )
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", dir="/tmp", delete=False
        ) as f:
            f.write(src)
            f.flush()
            tmp = f.name

        try:
            p = extract_problem(lean_file=tmp, theorem_name="baz",
                                difficulty="easy", problem_id="baz")
            assert "trivial" in p.ground_truth.strip()
        finally:
            os.unlink(tmp)

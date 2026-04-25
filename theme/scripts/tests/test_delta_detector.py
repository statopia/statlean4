"""Unit tests for theme/scripts/_delta_detector.py.

Covers prompt construction + response parsing — the pure-logic core of
the delta detector. Subprocess-level tests for the CLI wrapper live in
test_detect_delta_cli.py.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from _delta_detector import (  # noqa: E402
    build_prompt,
    parse_response,
    texts_are_trivially_identical,
)


# ── build_prompt ────────────────────────────────────────────────────
class TestBuildPrompt:
    def test_includes_both_texts(self):
        p = build_prompt("BEFORE_BODY", "AFTER_BODY")
        assert "BEFORE_BODY" in p
        assert "AFTER_BODY" in p

    def test_includes_labels(self):
        p = build_prompt("x", "y", "theorems.yaml", "Main.lean")
        assert "theorems.yaml" in p
        assert "Main.lean" in p

    def test_includes_all_change_type_enums(self):
        # Drift-prevention: if emit_event.py adds a new change_type,
        # the prompt should automatically include it.
        p = build_prompt("a", "b")
        for ct in [
            "dim-reduction", "hypothesis-add", "hypothesis-remove",
            "type-weaken", "conclusion-replace", "structure-introduce",
            "scope-restrict", "other",
        ]:
            assert ct in p, f"missing change_type {ct} in prompt"

    def test_includes_severity_enums(self):
        p = build_prompt("a", "b")
        for sev in ["info", "notable", "breaking"]:
            assert sev in p

    def test_truncates_oversized_input(self):
        big = "X" * 30_000
        p = build_prompt(big, "y")
        # Soft cap is 20K chars; truncation marker should appear.
        assert "[truncated" in p
        assert len(p) < 30_000 + 5_000  # ballpark

    def test_default_labels(self):
        p = build_prompt("x", "y")
        assert "before" in p.lower()
        assert "after" in p.lower()


# ── parse_response — happy path ────────────────────────────────────
class TestParseHappy:
    def test_no_change_explicit(self):
        r = parse_response('{"change_detected": false}')
        assert r == {"change_detected": False}

    def test_detected_full(self):
        r = parse_response(
            '{"change_detected": true, "change_type": "hypothesis-add", '
            '"summary": "added continuity", "severity": "notable"}'
        )
        assert r == {
            "change_detected": True,
            "change_type": "hypothesis-add",
            "summary": "added continuity",
            "severity": "notable",
        }

    def test_detected_with_details(self):
        r = parse_response(
            '{"change_detected": true, "change_type": "type-weaken", '
            '"summary": "ℝ → ℕ", "severity": "breaking", '
            '"details": {"old": "ℝ", "new": "ℕ"}}'
        )
        assert r is not None
        assert r["details"] == {"old": "ℝ", "new": "ℕ"}

    def test_summary_trimmed(self):
        r = parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": "  trimmed  ", "severity": "info"}'
        )
        assert r is not None
        assert r["summary"] == "trimmed"


# ── parse_response — surrounding prose / fences ────────────────────
class TestParseTolerant:
    def test_wrapped_in_prose(self):
        raw = (
            "Sure! Here's my analysis:\n\n"
            '{"change_detected": false}\n\n'
            "Let me know if you want a deeper review."
        )
        assert parse_response(raw) == {"change_detected": False}

    def test_inside_code_fence(self):
        raw = (
            "```json\n"
            '{"change_detected": true, "change_type": "other", '
            '"summary": "x", "severity": "notable"}\n'
            "```"
        )
        r = parse_response(raw)
        assert r is not None
        assert r["change_detected"] is True

    def test_first_object_wins_when_multiple(self):
        raw = (
            '{"change_detected": false} '
            '{"change_detected": true, "change_type": "other", '
            '"summary": "z", "severity": "info"}'
        )
        # Picks the first JSON object; subsequent are ignored.
        assert parse_response(raw) == {"change_detected": False}


# ── parse_response — rejection ─────────────────────────────────────
class TestParseReject:
    def test_empty(self):
        assert parse_response("") is None
        assert parse_response("   ") is None

    def test_no_json(self):
        assert parse_response("There is no change.") is None

    def test_malformed_json(self):
        assert parse_response("{not json") is None
        # Note: `{change_detected: false}` (no quotes on key) IS still
        # extractable by our shallow regex but won't parse via json.loads.
        assert parse_response("{change_detected: false}") is None

    def test_array_at_root(self):
        assert parse_response("[]") is None

    def test_change_detected_not_bool(self):
        assert parse_response('{"change_detected": "yes"}') is None
        assert parse_response('{"change_detected": 1}') is None

    def test_detected_missing_change_type(self):
        assert parse_response(
            '{"change_detected": true, "summary": "x", "severity": "info"}'
        ) is None

    def test_detected_invalid_change_type(self):
        assert parse_response(
            '{"change_detected": true, "change_type": "made-up", '
            '"summary": "x", "severity": "info"}'
        ) is None

    def test_detected_invalid_severity(self):
        assert parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": "x", "severity": "catastrophic"}'
        ) is None

    def test_detected_empty_summary(self):
        assert parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": "   ", "severity": "info"}'
        ) is None

    def test_detected_summary_not_string(self):
        assert parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": 42, "severity": "info"}'
        ) is None


# ── parse_response — details edge cases ────────────────────────────
class TestParseDetails:
    def test_details_non_dict_dropped(self):
        # Schema allows details optional; non-object should be dropped
        # silently rather than failing the parse.
        r = parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": "x", "severity": "info", "details": [1,2]}'
        )
        assert r is not None
        assert "details" not in r

    def test_details_omitted_ok(self):
        r = parse_response(
            '{"change_detected": true, "change_type": "other", '
            '"summary": "x", "severity": "info"}'
        )
        assert r is not None
        assert "details" not in r


# ── identity short-circuit ─────────────────────────────────────────
class TestTriviallyIdentical:
    def test_same_text(self):
        assert texts_are_trivially_identical("hello", "hello")

    def test_outer_whitespace_ignored(self):
        assert texts_are_trivially_identical("  x  \n", "x")

    def test_different(self):
        assert not texts_are_trivially_identical("a", "b")

    def test_inner_whitespace_difference_NOT_short_circuited(self):
        # Inner whitespace differences could be cosmetic OR semantic
        # (notation change). Only the LLM should judge, so we don't
        # short-circuit them.
        assert not texts_are_trivially_identical("a b", "a  b")

    def test_empty_both(self):
        assert texts_are_trivially_identical("", "")
        assert texts_are_trivially_identical("   ", "\n")


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))

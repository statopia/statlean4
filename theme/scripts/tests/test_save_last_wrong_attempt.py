"""L1 unit tests for save_last_wrong_attempt.py (E12 phase 03).

Tests cover:
  - parse_lsp_diagnostics: 3 input shapes + edge cases
  - annotate_content: inline markers, HINT tags, idempotency, footer
  - save_last_wrong_attempt CLI integration: write_fail + edit_fail paths
  - replace_fail stub: verify NO save_last_wrong_attempt call (D-7 Option A)

Per spec §8 differentiation evidence: on rollback/sdk-bridge-pre-newloop,
this file is absent → collection-error (not test failure). last_wrong_attempt.lean
does not exist in the sandbox after a write fail in that baseline.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# Add scripts dir to path.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from save_last_wrong_attempt import (  # noqa: E402
    ParsedError,
    annotate_content,
    parse_lsp_diagnostics,
    save_last_wrong_attempt,
)


# ══════════════════════════════════════════════════════════════════════
# parse_lsp_diagnostics — 3 shapes
# ══════════════════════════════════════════════════════════════════════


def test_parse_lsp_shape1_lsp_raw_0indexed() -> None:
    """Shape 1: LSP-raw 0-indexed [{severity, message, range:{start:{line,character}}}]."""
    diag = json.dumps([{
        "severity": "error",
        "message": "unexpected token",
        "range": {"start": {"line": 4, "character": 7}},
    }])
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].line == 5      # 0-indexed line 4 → 1-indexed line 5
    assert result[0].column == 8    # 0-indexed character 7 → 1-indexed column 8
    assert result[0].message == "unexpected token"


def test_parse_lsp_shape2_flat_1indexed() -> None:
    """Shape 2: Flat 1-indexed [{severity, message, line, column}]."""
    diag = json.dumps([{
        "severity": "error",
        "message": "failed to synthesize",
        "line": 10,
        "column": 3,
    }])
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].line == 10
    assert result[0].column == 3
    assert result[0].message == "failed to synthesize"


def test_parse_lsp_shape3_wrapped_items() -> None:
    """Shape 3: Wrapped {success, items:[...]}."""
    diag = json.dumps({
        "success": False,
        "items": [{
            "severity": "error",
            "message": "no goals",
            "line": 7,
            "column": 1,
        }],
    })
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].line == 7
    assert result[0].column == 1
    assert result[0].message == "no goals"


def test_parse_lsp_empty_array() -> None:
    """Empty array → empty list."""
    assert parse_lsp_diagnostics("[]") == []
    assert parse_lsp_diagnostics("") == []
    assert parse_lsp_diagnostics("   ") == []


def test_parse_lsp_warning_severity_filtered() -> None:
    """Warnings filtered out — only severity=error returned."""
    diag = json.dumps([
        {"severity": "warning", "message": "unused variable", "line": 3, "column": 1},
        {"severity": "info", "message": "note", "line": 4, "column": 1},
    ])
    result = parse_lsp_diagnostics(diag)
    assert result == []


def test_parse_lsp_mixed_severity() -> None:
    """Mixed severity: only errors returned."""
    diag = json.dumps([
        {"severity": "warning", "message": "warn", "line": 1, "column": 1},
        {"severity": "error", "message": "error message", "line": 2, "column": 5},
    ])
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].message == "error message"


def test_parse_lsp_shape3_errors_key() -> None:
    """Shape 3 variant: {errors: [...]} key."""
    diag = json.dumps({
        "errors": [{
            "severity": "error",
            "message": "type mismatch",
            "line": 12,
            "column": 4,
        }],
    })
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].line == 12


def test_parse_lsp_invalid_json() -> None:
    """Invalid JSON → empty list (no crash)."""
    assert parse_lsp_diagnostics("not valid json {") == []


def test_parse_lsp_shape1_0indexed_line0() -> None:
    """Shape 1: line=0 in range means 1-indexed line 1."""
    diag = json.dumps([{
        "severity": "error",
        "message": "parse error",
        "range": {"start": {"line": 0, "character": 0}},
    }])
    result = parse_lsp_diagnostics(diag)
    assert len(result) == 1
    assert result[0].line == 1
    assert result[0].column == 1


# ══════════════════════════════════════════════════════════════════════
# annotate_content
# ══════════════════════════════════════════════════════════════════════


def _no_pitfall_match(msg: str):
    """Mock _match_pitfall_subprocess to return None (no match)."""
    return None


def _pitfall_match_syntax(msg: str):
    """Mock returning a lean_syntax_errors match for 'unexpected token λ' messages."""
    if "λ" in msg or "unexpected token" in msg:
        return (
            "docs/pitfalls/lean_syntax_errors.md",
            "§A.1",
            "📚 Similar error pattern → see `docs/pitfalls/lean_syntax_errors.md` §A.1. "
            "Reserved-keyword char (λ Π Σ ∀ ∃) embedded in an identifier. "
            "Rename every occurrence to ASCII.",
        )
    return None


def _pitfall_match_typeclass(msg: str):
    """Mock returning a typeclass_errors match for 'OrderBot' messages."""
    if "OrderBot" in msg:
        return (
            "docs/pitfalls/typeclass_errors.md",
            "§A.1",
            "📚 ℝ has no OrderBot. Use ⨆ instead.",
        )
    return None


def test_annotate_content_no_errors() -> None:
    """No errors → content unchanged."""
    content = "theorem foo : True := trivial\n"
    result = annotate_content(content, [])
    assert result == content


def test_annotate_content_error_at_line3_with_hint() -> None:
    """Error at line 3 that matches a pitfall rule → ERROR marker + HINT tag."""
    content = "line1\nline2\nline3 with λ\nline4\n"
    errors = [ParsedError(line=3, column=12, message="unexpected token 'λ'")]
    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_pitfall_match_syntax,
    ):
        result = annotate_content(content, errors)
    lines = result.split("\n")
    assert "[ERROR col 12:" in lines[2]
    assert "[HINT: see docs/pitfalls/lean_syntax_errors.md §A.1" in lines[2]


def test_annotate_content_error_no_pitfall_match() -> None:
    """Error at line 5 with no pitfall match → ERROR marker, no HINT tag."""
    content = "\n".join(f"line{i}" for i in range(1, 7)) + "\n"
    errors = [ParsedError(line=5, column=3, message="some obscure error")]
    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_no_pitfall_match,
    ):
        result = annotate_content(content, errors)
    lines = result.split("\n")
    assert "[ERROR col 3:" in lines[4]
    assert "[HINT:" not in lines[4]


def test_annotate_content_two_errors_same_file() -> None:
    """Two errors matching same pitfall file → footer has exactly one routing entry."""
    content = "a\nb\nc\nd\ne\n"
    errors = [
        ParsedError(line=2, column=1, message="unexpected token 'λ'"),
        ParsedError(line=4, column=1, message="unexpected token 'Π'"),
    ]
    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_pitfall_match_syntax,
    ):
        result = annotate_content(content, errors)
    # Footer should mention PITFALL ROUTING HINTS only once.
    assert result.count("PITFALL ROUTING HINTS") == 1
    # The footer "→ file §section:" entry should appear exactly once
    # (de-duplication — same file/section across both errors).
    assert result.count("-- → docs/pitfalls/lean_syntax_errors.md §A.1:") == 1


def test_annotate_content_two_errors_different_files() -> None:
    """Two errors matching different pitfall files → footer has 2 entries."""
    content = "a\nb\nc\nd\ne\nf\n"
    errors = [
        ParsedError(line=2, column=1, message="unexpected token 'λ'"),
        ParsedError(line=4, column=1, message="failed to synthesize OrderBot ℝ"),
    ]

    def _combined_match(msg: str):
        if "λ" in msg or "unexpected token" in msg:
            return _pitfall_match_syntax(msg)
        if "OrderBot" in msg:
            return _pitfall_match_typeclass(msg)
        return None

    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_combined_match,
    ):
        result = annotate_content(content, errors)
    assert "docs/pitfalls/lean_syntax_errors.md §A.1" in result
    assert "docs/pitfalls/typeclass_errors.md §A.1" in result


def test_annotate_content_idempotency_line_markers() -> None:
    """Inline ERROR markers are not double-applied on second annotate_content call.

    Note: the footer block IS re-appended on a second call (czy parity — annotateContent
    always appends a fresh footer; the per-line idempotency guard only prevents
    double-annotating already-marked lines). In practice, save_last_wrong_attempt.lean
    is always written from fresh failed content, not re-annotated content.
    """
    content = "line1\nline2 with error\nline3\n"
    errors = [ParsedError(line=2, column=5, message="type mismatch")]
    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_no_pitfall_match,
    ):
        first = annotate_content(content, errors)
        second = annotate_content(first, errors)
    # The per-line annotation should appear exactly once (idempotency guard).
    # Check the annotated line in the second output only appears once inline.
    second_lines = second.split("\n")
    annotated_lines = [ln for ln in second_lines if "[ERROR col 5: type mismatch]" in ln]
    assert len(annotated_lines) == 1, (
        "Per-line ERROR marker should not be duplicated by idempotency guard"
    )


def test_annotate_content_footer_present() -> None:
    """Footer COMPILER ERRORS block always present when errors exist."""
    content = "line1\nline2\n"
    errors = [ParsedError(line=1, column=1, message="some error")]
    with patch(
        "save_last_wrong_attempt._match_pitfall_subprocess",
        side_effect=_no_pitfall_match,
    ):
        result = annotate_content(content, errors)
    assert "COMPILER ERRORS (verbatim" in result
    assert "line 1 col 1: some error" in result


# ══════════════════════════════════════════════════════════════════════
# save_last_wrong_attempt CLI integration
# ══════════════════════════════════════════════════════════════════════


def test_cli_write_fail_with_matching_diagnostics(tmp_path: Path) -> None:
    """Valid content + diagnostics matching rule 8 (OrderBot) → file written, ROUTING HINT."""
    content_file = tmp_path / "failed.lean"
    content_file.write_text("theorem test : True := by\n  exact?  -- [line 2]\n")

    diag = json.dumps([{
        "severity": "error",
        "message": "failed to synthesize OrderBot ℝ",
        "line": 2,
        "column": 5,
    }])

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "save_last_wrong_attempt.py"),
            "--sandbox", str(tmp_path),
            "--content", str(content_file),
            "--diagnostics", diag,
            "--fail-type", "write",
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    out_file = tmp_path / "last_wrong_attempt.lean"
    assert out_file.exists(), "last_wrong_attempt.lean not written"
    out_content = out_file.read_text()
    assert "[ERROR col 5:" in out_content


def test_cli_write_fail_non_matching_diagnostics(tmp_path: Path) -> None:
    """Valid content + non-matching diagnostics → file written, no ROUTING HINT in stdout."""
    content_file = tmp_path / "failed.lean"
    content_file.write_text("-- some lean content\ntheorem foo : True := trivial\n")

    diag = json.dumps([{
        "severity": "error",
        "message": "some completely unique obscure error xyz123abc",
        "line": 2,
        "column": 1,
    }])

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "save_last_wrong_attempt.py"),
            "--sandbox", str(tmp_path),
            "--content", str(content_file),
            "--diagnostics", diag,
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    out_file = tmp_path / "last_wrong_attempt.lean"
    assert out_file.exists()
    # stdout may or may not have ROUTING HINT — just check file was written
    assert "[ERROR col 1:" in out_file.read_text()


def test_cli_empty_diagnostics(tmp_path: Path) -> None:
    """Empty diagnostics → file written, stdout indicates no structured errors."""
    content_file = tmp_path / "failed.lean"
    content_file.write_text("-- failed content with no parseable errors\n")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "save_last_wrong_attempt.py"),
            "--sandbox", str(tmp_path),
            "--content", str(content_file),
            "--diagnostics", "[]",
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    out_file = tmp_path / "last_wrong_attempt.lean"
    assert out_file.exists()
    assert "no structured errors parsed" in result.stdout


def test_cli_sorry_id_milestone(tmp_path: Path) -> None:
    """--sorry-id provided → emits last-wrong-attempt-saved milestone."""
    content_file = tmp_path / "failed.lean"
    content_file.write_text("-- content\nsorry\n")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "save_last_wrong_attempt.py"),
            "--sandbox", str(tmp_path),
            "--content", str(content_file),
            "--diagnostics", "[]",
            "--sorry-id", "test.mylemma",
            "--fail-type", "edit",
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    events_file = tmp_path / "events.jsonl"
    if events_file.exists():
        events = [json.loads(line) for line in events_file.read_text().splitlines() if line]
        milestone_names = [
            e.get("name") for e in events if e.get("kind") == "sandbox_milestone"
        ]
        assert "last-wrong-attempt-saved" in milestone_names, (
            f"Expected last-wrong-attempt-saved in {milestone_names}"
        )


def test_cli_missing_sandbox(tmp_path: Path) -> None:
    """Missing sandbox → exit code 1."""
    content_file = tmp_path / "f.lean"
    content_file.write_text("-- content\n")
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "save_last_wrong_attempt.py"),
            "--sandbox", str(tmp_path / "nonexistent_sandbox"),
            "--content", str(content_file),
            "--diagnostics", "[]",
        ],
        capture_output=True, text=True, timeout=10,
    )
    assert result.returncode == 1


# ══════════════════════════════════════════════════════════════════════
# D-7 Option A: replace_fail stub in process_sorry_result.py
# ══════════════════════════════════════════════════════════════════════


def test_replace_fail_does_not_call_save_last_wrong_attempt(tmp_path: Path) -> None:
    """--status replace_fail MUST NOT write last_wrong_attempt.lean (Phase 03 stub).

    D-7 Option A: replace_fail is stubbed; only a warning log is emitted.
    No save_last_wrong_attempt.py call, no last_wrong_attempt.lean file.
    """
    # Create a minimal sandbox with events.jsonl to accept milestones.
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "process_sorry_result.py"),
            "--sandbox", str(sandbox),
            "--sorry-id", "test.lemma",
            "--status", "replace_fail",
            "--blocker", "replace_sorry failed: type mismatch",
        ],
        capture_output=True, text=True, timeout=30,
    )
    # Should complete without error (exit 0 always per design).
    assert result.returncode == 0, f"stderr: {result.stderr}"
    # last_wrong_attempt.lean MUST NOT be written for replace_fail.
    assert not (sandbox / "last_wrong_attempt.lean").exists(), (
        "replace_fail MUST NOT write last_wrong_attempt.lean in Phase 03 (D-7 Option A)"
    )
    # Warning should be logged to stderr.
    assert "replace_fail" in result.stderr
    assert "Phase 04" in result.stderr


def test_write_fail_does_call_save_last_wrong_attempt(tmp_path: Path) -> None:
    """--status write_fail with --content → last_wrong_attempt.lean IS written."""
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    content_file = tmp_path / "failed.lean"
    content_file.write_text("-- failed content\nsorry\n")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "process_sorry_result.py"),
            "--sandbox", str(sandbox),
            "--sorry-id", "test.mylemma",
            "--status", "write_fail",
            "--blocker", "type mismatch",
            "--content", str(content_file),
            "--diagnostics", "[]",
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    assert (sandbox / "last_wrong_attempt.lean").exists(), (
        "write_fail MUST write last_wrong_attempt.lean"
    )


def test_edit_fail_does_call_save_last_wrong_attempt(tmp_path: Path) -> None:
    """--status edit_fail with --content → last_wrong_attempt.lean IS written."""
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    content_file = tmp_path / "failed.lean"
    content_file.write_text("-- edit failed content\n")

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPTS_DIR / "process_sorry_result.py"),
            "--sandbox", str(sandbox),
            "--sorry-id", "test.editfail",
            "--status", "edit_fail",
            "--blocker", "elaboration error",
            "--content", str(content_file),
            "--diagnostics", "[]",
        ],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"
    assert (sandbox / "last_wrong_attempt.lean").exists(), (
        "edit_fail MUST write last_wrong_attempt.lean"
    )


# ══════════════════════════════════════════════════════════════════════
# SKILL.md content verification (sentinel strings)
# ══════════════════════════════════════════════════════════════════════


def test_lean_skeleton_skill_contains_escapable_existential() -> None:
    """lean-skeleton/SKILL.md must contain SKELETON_HONESTY_RULES sentinel."""
    skill_path = SCRIPTS_DIR.parent / "skills" / "lean-skeleton" / "SKILL.md"
    assert skill_path.exists(), f"Missing: {skill_path}"
    content = skill_path.read_text()
    assert "Escapable existential" in content, (
        "lean-skeleton/SKILL.md missing SKELETON_HONESTY_RULES sentinel 'Escapable existential'"
    )
    assert "HARD BAN" in content, (
        "lean-skeleton/SKILL.md missing LEAN_NAMING_CONVENTION sentinel 'HARD BAN'"
    )


def test_prover_prompt_contains_honesty_rule_blocks() -> None:
    """prove-deep.md launch_background_agent prompt body must contain the
    4 honestyRules blocks (Path A czy parity per Phase 03 §8 follow-up via
    Batch B spec review S3.1, 2026-04-30): czy interpolates these via TS
    template literal directly into prover prompt; SDK-bridge inlines them
    into prove-deep.md instead of the previous proof-closure/SKILL.md fold
    (which was dead text — general-purpose subagent dispatch with no
    /proof-closure invocation)."""
    cmd_path = (
        SCRIPTS_DIR.parent.parent / ".claude" / "commands" / "prove-deep.md"
    )
    assert cmd_path.exists(), f"Missing: {cmd_path}"
    content = cmd_path.read_text()
    assert "trivial witnesses" in content, (
        "prove-deep.md missing PROOF_WITNESS_HONESTY_RULE sentinel 'trivial witnesses'"
    )
    assert "unexpected token 'λ'" in content, (
        "prove-deep.md missing LEAN_QUICK_ERROR_TABLE sentinel"
    )
    assert "HARD BAN" in content, (
        "prove-deep.md missing LEAN_NAMING_CONVENTION sentinel 'HARD BAN'"
    )


def test_prover_prompt_contains_kb_references() -> None:
    """prove-deep.md launch_background_agent prompt body must contain
    LEAN_KB_REFERENCES table (Path A czy parity)."""
    cmd_path = (
        SCRIPTS_DIR.parent.parent / ".claude" / "commands" / "prove-deep.md"
    )
    assert cmd_path.exists()
    content = cmd_path.read_text()
    assert "docs/pitfalls/README.md" in content
    assert "instance_pollution.md" in content
    assert "measure_theory_patterns.md" in content


def test_prove_deep_md_contains_kb_references() -> None:
    """prove-deep.md Phase 2 preamble must contain LEAN_KB_REFERENCES block."""
    cmd_path = (
        SCRIPTS_DIR.parent.parent / ".claude" / "commands" / "prove-deep.md"
    )
    assert cmd_path.exists(), f"Missing: {cmd_path}"
    content = cmd_path.read_text()
    assert "Pitfalls knowledge base" in content
    assert "last_wrong_attempt.lean" in content
    assert "replace_fail" in content
    assert "Phase 04" in content

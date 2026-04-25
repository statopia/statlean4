"""Subprocess-level tests for theme/scripts/detect_delta.py.

Uses --mock-response so the LLM is bypassed; exercises the file-IO,
parse, identity short-circuit, and emit paths end-to-end.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "theme" / "scripts" / "detect_delta.py"


def _run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def _read_events(sandbox: Path) -> list[dict]:
    f = sandbox / "events.jsonl"
    if not f.exists():
        return []
    return [json.loads(l) for l in f.read_text().splitlines() if l]


def _write_pair(tmp_path: Path, before: str, after: str) -> tuple[Path, Path]:
    b = tmp_path / "before.txt"
    a = tmp_path / "after.txt"
    b.write_text(before)
    a.write_text(after)
    return b, a


# ── identity short-circuit ─────────────────────────────────────────
def test_byte_identical_skips_llm(tmp_path: Path):
    b, a = _write_pair(tmp_path, "same", "same")
    r = _run(
        "--before", str(b),
        "--after", str(a),
    )
    assert r.returncode == 0, r.stderr
    assert "no change (byte-identical)" in r.stdout


def test_outer_whitespace_only_short_circuits(tmp_path: Path):
    b, a = _write_pair(tmp_path, "  hello  \n", "hello")
    r = _run("--before", str(b), "--after", str(a))
    assert r.returncode == 0, r.stderr
    assert "byte-identical" in r.stdout


# ── mock LLM: no change ───────────────────────────────────────────
def test_mock_no_change_no_emit(tmp_path: Path):
    b, a = _write_pair(tmp_path, "x", "y")  # different so we don't short-circuit
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", '{"change_detected": false}',
        "--sandbox", str(tmp_path),
    )
    assert r.returncode == 0, r.stderr
    assert r.stdout.strip() == "no change"
    # No event was emitted.
    assert _read_events(tmp_path) == []


# ── mock LLM: detected → emits ────────────────────────────────────
def test_mock_detected_emits(tmp_path: Path):
    b, a = _write_pair(tmp_path, "before", "after")
    response = (
        '{"change_detected": true, "change_type": "hypothesis-add", '
        '"summary": "added continuity", "severity": "notable"}'
    )
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", response,
        "--sandbox", str(tmp_path),
        "--before-rel", "theorems.yaml",
        "--after-rel", "Main.lean",
    )
    assert r.returncode == 0, r.stderr
    assert "delta emitted" in r.stdout
    events = _read_events(tmp_path)
    assert len(events) == 1
    e = events[0]
    assert e["kind"] == "formalization_delta"
    assert e["change_type"] == "hypothesis-add"
    assert e["summary"] == "added continuity"
    assert e["severity"] == "notable"
    assert e["before_path"] == "theorems.yaml"
    assert e["after_path"] == "Main.lean"


def test_mock_detected_with_details(tmp_path: Path):
    b, a = _write_pair(tmp_path, "before", "after")
    response = (
        '{"change_detected": true, "change_type": "type-weaken", '
        '"summary": "ℝ → ℕ", "severity": "breaking", '
        '"details": {"old": "ℝ", "new": "ℕ"}}'
    )
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", response,
        "--sandbox", str(tmp_path),
    )
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    assert e["severity"] == "breaking"
    assert e["details"] == {"old": "ℝ", "new": "ℕ"}


# ── detect-only (no --sandbox) ────────────────────────────────────
def test_detect_only_prints_json(tmp_path: Path):
    b, a = _write_pair(tmp_path, "before", "after")
    response = (
        '{"change_detected": true, "change_type": "other", '
        '"summary": "x", "severity": "notable"}'
    )
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", response,
        # no --sandbox
    )
    assert r.returncode == 0, r.stderr
    parsed = json.loads(r.stdout.strip())
    assert parsed["change_detected"] is True
    assert parsed["change_type"] == "other"


# ── error paths ───────────────────────────────────────────────────
def test_missing_before_fails(tmp_path: Path):
    b = tmp_path / "nope.txt"
    a = tmp_path / "after.txt"
    a.write_text("x")
    r = _run("--before", str(b), "--after", str(a))
    assert r.returncode == 1
    assert "BEFORE not found" in r.stderr


def test_missing_after_fails(tmp_path: Path):
    b = tmp_path / "before.txt"
    a = tmp_path / "nope.txt"
    b.write_text("x")
    r = _run("--before", str(b), "--after", str(a))
    assert r.returncode == 1
    assert "AFTER not found" in r.stderr


def test_unparseable_response_fails(tmp_path: Path):
    b, a = _write_pair(tmp_path, "x", "y")
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", "I cannot determine if there's a change.",
    )
    assert r.returncode == 1
    assert "could not parse" in r.stderr


def test_invalid_enum_in_response_fails(tmp_path: Path):
    b, a = _write_pair(tmp_path, "x", "y")
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response",
        '{"change_detected": true, "change_type": "made-up", '
        '"summary": "x", "severity": "notable"}',
    )
    assert r.returncode == 1
    assert "could not parse" in r.stderr


def test_sandbox_must_be_directory(tmp_path: Path):
    b, a = _write_pair(tmp_path, "x", "y")
    not_a_dir = tmp_path / "not-a-dir"
    not_a_dir.write_text("")
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", '{"change_detected": true, "change_type": "other", '
                           '"summary": "x", "severity": "info"}',
        "--sandbox", str(not_a_dir),
    )
    assert r.returncode == 1
    assert "not a directory" in r.stderr


# ── --quiet flag ──────────────────────────────────────────────────
def test_quiet_suppresses_stdout_on_no_change(tmp_path: Path):
    b, a = _write_pair(tmp_path, "same", "same")
    r = _run("--before", str(b), "--after", str(a), "--quiet")
    assert r.returncode == 0
    assert r.stdout.strip() == ""


def test_quiet_suppresses_stdout_on_emit(tmp_path: Path):
    b, a = _write_pair(tmp_path, "x", "y")
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", '{"change_detected": true, "change_type": "other", '
                           '"summary": "x", "severity": "info"}',
        "--sandbox", str(tmp_path),
        "--quiet",
    )
    assert r.returncode == 0
    assert r.stdout.strip() == ""
    # Event still emitted
    assert len(_read_events(tmp_path)) == 1


# ── --before-rel / --after-rel defaults ───────────────────────────
def test_emitted_paths_default_to_basename_when_rel_omitted(tmp_path: Path):
    b = tmp_path / "theorems.yaml"
    a = tmp_path / "Main.lean"
    b.write_text("a")
    a.write_text("b")
    r = _run(
        "--before", str(b),
        "--after", str(a),
        "--mock-response", '{"change_detected": true, "change_type": "other", '
                           '"summary": "x", "severity": "info"}',
        "--sandbox", str(tmp_path),
    )
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    # Without --before-rel/--after-rel, the emitter doesn't get those
    # arguments, so they're absent from the event.
    assert "before_path" not in e
    assert "after_path" not in e

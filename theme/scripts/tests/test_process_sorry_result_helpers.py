"""L1 unit tests for process_sorry_result.py NEW slice 3.B helpers.

This file covers ONLY the new slice-3.B additions; the broader
process_sorry_result.py end-to-end behavior (extract_sorries refresh,
emit_event chains, validate_decomposition) was historically untested
and is out of scope for this slice.
"""
from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import process_sorry_result as psr  # noqa: E402


# ── _read_stuck_rounds ───────────────────────────────────────────────


def test_read_stuck_rounds_returns_zero_when_backlog_missing(tmp_path: Path) -> None:
    with patch.object(psr, "BACKLOG_PATH", tmp_path / "nonexistent.yaml"):
        assert psr._read_stuck_rounds("foo") == 0


def test_read_stuck_rounds_returns_zero_when_sorry_missing(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    backlog.write_text(yaml.safe_dump({
        "schema_version": 2,
        "sorry_items": [{"id": "other", "stuck_rounds": 5}],
    }))
    with patch.object(psr, "BACKLOG_PATH", backlog):
        assert psr._read_stuck_rounds("foo") == 0


def test_read_stuck_rounds_returns_value_when_present(tmp_path: Path) -> None:
    backlog = tmp_path / "b.yaml"
    backlog.write_text(yaml.safe_dump({
        "schema_version": 2,
        "sorry_items": [{"id": "foo", "stuck_rounds": 2}],
    }))
    with patch.object(psr, "BACKLOG_PATH", backlog):
        assert psr._read_stuck_rounds("foo") == 2


def test_read_stuck_rounds_defaults_zero_when_field_absent(tmp_path: Path) -> None:
    """v1 yaml may have an item without stuck_rounds field; should default 0."""
    backlog = tmp_path / "b.yaml"
    backlog.write_text(yaml.safe_dump({
        "sorry_items": [{"id": "foo", "theorem": "foo_thm"}],
    }))
    with patch.object(psr, "BACKLOG_PATH", backlog):
        assert psr._read_stuck_rounds("foo") == 0


def test_read_stuck_rounds_handles_yaml_parse_error(tmp_path: Path) -> None:
    """Malformed yaml → return 0 silently (caller treats as fresh state)."""
    backlog = tmp_path / "b.yaml"
    backlog.write_text("not: valid: yaml: at: all: : :")
    with patch.object(psr, "BACKLOG_PATH", backlog):
        assert psr._read_stuck_rounds("foo") == 0

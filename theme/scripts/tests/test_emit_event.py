"""Unit tests for theme/scripts/emit_event.py.

Run from statlean repo root:
  pytest theme/scripts/tests/test_emit_event.py -v
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "theme" / "scripts" / "emit_event.py"


def _run(sandbox: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--sandbox", str(sandbox), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def _read_events(sandbox: Path) -> list[dict]:
    events_file = sandbox / "events.jsonl"
    if not events_file.exists():
        return []
    return [json.loads(line) for line in events_file.read_text().splitlines() if line]


def test_step_start_writes_event(tmp_path: Path) -> None:
    r = _run(tmp_path, "step", "--id", "1", "--title", "Foo", "--status", "start")
    assert r.returncode == 0, r.stderr
    events = _read_events(tmp_path)
    assert len(events) == 1
    e = events[0]
    assert e["kind"] == "step"
    assert e["id"] == 1
    assert e["title"] == "Foo"
    assert e["status"] == "start"
    assert isinstance(e["ts"], int) and e["ts"] > 0


def test_step_done_omits_title(tmp_path: Path) -> None:
    r = _run(tmp_path, "step", "--id", "2", "--status", "done")
    assert r.returncode == 0, r.stderr
    events = _read_events(tmp_path)
    assert events[0]["status"] == "done"
    assert "title" not in events[0]


def test_step_start_without_title_fails(tmp_path: Path) -> None:
    r = _run(tmp_path, "step", "--id", "1", "--status", "start")
    assert r.returncode != 0
    assert "requires --title" in r.stderr


def test_artifact_with_explicit_size(tmp_path: Path) -> None:
    r = _run(
        tmp_path,
        "artifact",
        "--kind-tag", "yaml",
        "--path", "theorems.yaml",
        "--size", "1234",
    )
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    assert e["kind"] == "artifact"
    assert e["kind_tag"] == "yaml"
    assert e["path"] == "theorems.yaml"
    assert e["size"] == 1234


def test_artifact_auto_stat_size(tmp_path: Path) -> None:
    f = tmp_path / "paper.tex"
    f.write_text("hello world")  # 11 bytes
    r = _run(tmp_path, "artifact", "--kind-tag", "pdf-extract", "--path", "paper.tex")
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    assert e["size"] == 11


def test_artifact_nonexistent_path_omits_size(tmp_path: Path) -> None:
    r = _run(
        tmp_path,
        "artifact",
        "--kind-tag", "lean-skeleton",
        "--path", "doesnotexist.lean",
    )
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    assert "size" not in e


def test_error_event(tmp_path: Path) -> None:
    r = _run(tmp_path, "error", "--code", "OCR_FAIL", "--msg", "silent exit")
    assert r.returncode == 0, r.stderr
    e = _read_events(tmp_path)[0]
    assert e["kind"] == "error"
    assert e["code"] == "OCR_FAIL"
    assert e["msg"] == "silent exit"


def test_multiple_events_appended_in_order(tmp_path: Path) -> None:
    _run(tmp_path, "step", "--id", "1", "--title", "A", "--status", "start")
    _run(tmp_path, "step", "--id", "1", "--status", "done")
    _run(tmp_path, "step", "--id", "2", "--title", "B", "--status", "start")
    events = _read_events(tmp_path)
    assert [e.get("status") for e in events] == ["start", "done", "start"]
    assert [e.get("id") for e in events] == [1, 1, 2]


def test_nonexistent_sandbox_fails(tmp_path: Path) -> None:
    missing = tmp_path / "nope"
    r = _run(missing, "step", "--id", "1", "--title", "X", "--status", "start")
    assert r.returncode == 2
    assert "does not exist" in r.stderr


def test_sandbox_is_file_fails(tmp_path: Path) -> None:
    f = tmp_path / "notadir"
    f.write_text("")
    r = _run(f, "step", "--id", "1", "--title", "X", "--status", "start")
    assert r.returncode == 2
    assert "not a directory" in r.stderr


def test_jsonl_is_single_line_per_event(tmp_path: Path) -> None:
    """Guard the jsonl invariant: newline-separated single-line JSON only."""
    _run(tmp_path, "step", "--id", "7", "--title", "has\nnewline", "--status", "start")
    lines = (tmp_path / "events.jsonl").read_text().splitlines()
    # Title containing '\n' is escaped to '\\n' in JSON, so still one line.
    assert len(lines) == 1
    parsed = json.loads(lines[0])
    assert parsed["title"] == "has\nnewline"

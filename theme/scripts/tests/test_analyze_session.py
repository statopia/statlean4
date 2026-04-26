"""Unit tests for analyze_session.py.

Run from statlean repo root:
  pytest theme/scripts/tests/test_analyze_session.py -v
"""
from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "theme" / "scripts" / "analyze_session.py"

# Import pure helpers directly.
sys.path.insert(0, str(REPO_ROOT / "theme" / "scripts"))
from analyze_session import (  # noqa: E402
    analyze,
    parse_ts,
    relativise,
    render,
    as_json,
)


# ── Pure helpers ────────────────────────────────────────────────────────

def test_parse_ts_accepts_zulu() -> None:
    dt = parse_ts("2026-04-24T15:49:03.276Z")
    assert dt is not None
    assert dt.tzinfo is not None
    assert dt.year == 2026 and dt.month == 4 and dt.day == 24


def test_parse_ts_handles_none_and_garbage() -> None:
    assert parse_ts(None) is None
    assert parse_ts("") is None
    assert parse_ts("not a timestamp") is None


def test_relativise_inside_root(tmp_path: Path) -> None:
    root = tmp_path / "statlean"
    (root / "theme").mkdir(parents=True)
    f = root / "theme" / "x.py"
    f.write_text("")
    assert relativise(str(f), root) == "theme/x.py"


def test_relativise_outside_root(tmp_path: Path) -> None:
    root = tmp_path / "statlean"
    root.mkdir()
    elsewhere = tmp_path / "other" / "file.txt"
    elsewhere.parent.mkdir()
    elsewhere.write_text("")
    # Outside → returned as-is.
    assert relativise(str(elsewhere), root).endswith("file.txt")


# ── Transcript fixture + analyze() ─────────────────────────────────────

def _write_jsonl(path: Path, events: Iterable[dict]) -> None:
    path.write_text(
        "\n".join(json.dumps(e) for e in events) + "\n",
        encoding="utf-8",
    )


def _tool_use(name: str, inp: dict) -> dict:
    return {
        "type": "assistant",
        "timestamp": "2026-04-24T16:00:00.000Z",
        "message": {"content": [{"type": "tool_use", "name": name, "input": inp}]},
    }


def _assistant_text(text: str, ts: str = "2026-04-24T16:00:10.000Z") -> dict:
    return {
        "type": "assistant",
        "timestamp": ts,
        "message": {"content": [{"type": "text", "text": text}]},
    }


def _user_text(text: str, ts: str = "2026-04-24T15:49:00.000Z") -> dict:
    return {
        "type": "user",
        "timestamp": ts,
        "message": {"content": [{"type": "text", "text": text}]},
    }


def _tool_err(ts: str = "2026-04-24T16:00:01.000Z") -> dict:
    return {
        "type": "user",
        "timestamp": ts,
        "message": {"content": [{"type": "tool_result", "is_error": True, "content": "boom"}]},
    }


def test_analyze_counts_tools_and_categorizes_bash(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    _write_jsonl(j, [
        _user_text("/prove-deep target Cox Lemma S3"),
        _tool_use("Skill", {"skill": "prove-deep", "args": "..."}),
        _tool_use("Read", {"file_path": str(tmp_path / "Main.lean")}),
        _tool_use("Bash", {"command": "lake build Statlean.Foo"}),
        _tool_use("Bash", {"command": "grep -i x theme/mathlib_full_type_index.tsv"}),
        _tool_use("Bash", {"command": "python3 theme/scripts/emit_event.py ... step --id 1 --status done"}),
        _tool_use("Bash", {"command": "python3 theme/scripts/extract_sorries.py --sandbox ..."}),
        _tool_use("Edit", {"file_path": str(tmp_path / "Main.lean")}),
        _tool_err(),
        _assistant_text("done"),
    ])
    s = analyze(j, tmp_path)
    assert s.tool_names["Bash"] == 4
    assert s.tool_names["Read"] == 1
    assert s.tool_names["Edit"] == 1
    assert s.tool_names["Skill"] == 1
    assert s.lake_build_calls == 1
    assert s.emit_event_calls == 1
    assert s.extract_sorries_calls == 1
    assert s.check_snippet_calls == 0
    assert s.tool_result_errors == 1
    # KB grep on mathlib_full_type_index.tsv picked up
    assert s.kb_hits["mathlib_full_type_index.tsv"]["Bash"] == 1
    # proof_knowledge.yaml not touched
    assert s.kb_hits["proof_knowledge.yaml"] == {} or \
        sum(s.kb_hits["proof_knowledge.yaml"].values()) == 0
    # slash text captured
    assert s.slash_text.startswith("/prove-deep")


def test_analyze_timestamp_span(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    _write_jsonl(j, [
        _user_text("hi", ts="2026-04-24T15:00:00.000Z"),
        _assistant_text("bye", ts="2026-04-24T15:05:30.000Z"),
    ])
    s = analyze(j, tmp_path)
    assert s.first_ts is not None and s.last_ts is not None
    assert s.first_ts < s.last_ts
    assert (s.last_ts - s.first_ts).total_seconds() == 330.0


def test_analyze_ignores_malformed_lines(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    j.write_text(
        json.dumps(_assistant_text("ok")) + "\n"
        + "{not valid json\n"
        + json.dumps(_tool_use("Bash", {"command": "ls"})) + "\n",
        encoding="utf-8",
    )
    s = analyze(j, tmp_path)
    # Malformed line skipped, other two kept.
    assert s.tool_names["Bash"] == 1
    assert s.assistant_chars == 2


def test_analyze_text_chars_separation(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    _write_jsonl(j, [
        _user_text("/xyz 1234567"),      # 12 chars
        _assistant_text("hello world"),  # 11 chars
    ])
    s = analyze(j, tmp_path)
    assert s.user_chars == 12
    assert s.assistant_chars == 11


# ── Rendering / JSON emission ──────────────────────────────────────────

def test_render_contains_key_sections(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    _write_jsonl(j, [
        _user_text("/prove-deep target X"),
        _tool_use("Bash", {"command": "lake build"}),
        _tool_use("Edit", {"file_path": str(tmp_path / "Main.lean")}),
    ])
    out = render(analyze(j, tmp_path))
    for marker in ["Session:", "Tool uses:", "Files modified:", "KB access:", "lake build ×1"]:
        assert marker in out, f"missing marker: {marker!r}"


def test_json_mode_is_valid_json(tmp_path: Path) -> None:
    j = tmp_path / "s.jsonl"
    _write_jsonl(j, [_tool_use("Bash", {"command": "lake build"})])
    data = json.loads(as_json(analyze(j, tmp_path)))
    # Round-trip sanity.
    assert data["tool_names"]["Bash"] == 1
    assert data["lake_build_calls"] == 1


# ── CLI integration ────────────────────────────────────────────────────

def _cli(*args: str, transcripts: Path, repo: Path) -> subprocess.CompletedProcess:
    env = {"STATLEAN_ROOT": str(repo), "PATH": subprocess.os.environ.get("PATH", "")}
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--transcript-dir", str(transcripts), *args],
        capture_output=True, text=True, env=env, check=False,
    )


def test_cli_latest_selects_newest_mtime(tmp_path: Path) -> None:
    tdir = tmp_path / "transcripts"
    tdir.mkdir()
    old = tdir / "aaaaaaaa-0000-0000-0000-000000000000.jsonl"
    new = tdir / "bbbbbbbb-0000-0000-0000-000000000000.jsonl"
    _write_jsonl(old, [_assistant_text("old", ts="2026-04-01T00:00:00.000Z")])
    _write_jsonl(new, [_assistant_text("new", ts="2026-04-02T00:00:00.000Z")])
    # Force mtime order.
    import os
    os.utime(old, (100, 100))
    os.utime(new, (200, 200))
    r = _cli("--latest", transcripts=tdir, repo=tmp_path)
    assert r.returncode == 0, r.stderr
    assert "bbbbbbbb" in r.stdout
    assert "aaaaaaaa" not in r.stdout


def test_cli_uuid_missing_fails(tmp_path: Path) -> None:
    tdir = tmp_path / "transcripts"
    tdir.mkdir()
    r = _cli("--uuid", "does-not-exist", transcripts=tdir, repo=tmp_path)
    assert r.returncode != 0
    assert "uuid not found" in r.stderr


def test_cli_no_sessions_fails(tmp_path: Path) -> None:
    tdir = tmp_path / "transcripts"
    tdir.mkdir()
    r = _cli("--latest", transcripts=tdir, repo=tmp_path)
    assert r.returncode != 0
    assert "no sessions" in r.stderr


def test_cli_json_mode(tmp_path: Path) -> None:
    tdir = tmp_path / "transcripts"
    tdir.mkdir()
    f = tdir / "cccccccc-0000-0000-0000-000000000000.jsonl"
    _write_jsonl(f, [_tool_use("Bash", {"command": "lake build"})])
    r = _cli("--uuid", "cccccccc-0000-0000-0000-000000000000", "--json",
             transcripts=tdir, repo=tmp_path)
    assert r.returncode == 0, r.stderr
    data = json.loads(r.stdout)
    assert data["tool_names"]["Bash"] == 1
    assert data["lake_build_calls"] == 1


def test_cli_around_picks_session_bracketing_commit(tmp_path: Path) -> None:
    """End-to-end: init a git repo, make a commit, stub a transcript whose
    time window brackets it, and verify --around selects that transcript."""
    import os, subprocess as sp
    repo = tmp_path / "statlean"
    repo.mkdir()
    sp.run(["git", "init", "-q"], cwd=repo, check=True)
    sp.run(["git", "-c", "user.email=t@t", "-c", "user.name=t",
            "commit", "--allow-empty", "-q", "-m", "commit-1"], cwd=repo, check=True)
    commit = sp.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    commit_ts = int(sp.check_output(["git", "log", "-1", "--format=%ct", commit],
                                    cwd=repo, text=True).strip())
    commit_dt = datetime.fromtimestamp(commit_ts, tz=timezone.utc)
    tdir = tmp_path / "transcripts"
    tdir.mkdir()
    # Session that brackets the commit:
    before = commit_dt.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    after_dt = datetime.fromtimestamp(commit_ts + 60, tz=timezone.utc)
    after = after_dt.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    bracket = tdir / "ddddddd0-0000-0000-0000-000000000000.jsonl"
    _write_jsonl(bracket, [
        _assistant_text("start", ts=before),
        _assistant_text("end", ts=after),
    ])
    # A decoy session well after:
    decoy_after_dt = datetime.fromtimestamp(commit_ts + 3600, tz=timezone.utc)
    decoy_after = decoy_after_dt.replace(microsecond=0).isoformat().replace("+00:00", "Z")
    decoy = tdir / "eeeeeee0-0000-0000-0000-000000000000.jsonl"
    _write_jsonl(decoy, [_assistant_text("decoy", ts=decoy_after)])

    r = _cli("--around", commit, transcripts=tdir, repo=repo)
    assert r.returncode == 0, r.stderr
    assert "ddddddd0" in r.stdout
    assert "eeeeeee0" not in r.stdout

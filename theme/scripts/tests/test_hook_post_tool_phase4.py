"""
Phase 4 (czy port arch fix, 2026-05-01): hook_post_tool.py T1 escalation
for match_pitfall.py + save_last_wrong_attempt.py + auto_tactic_pre_pass.py.

Background — jobmolovhy6getc (2026-05-01) showed prove-deep.md narrative
T3 invocations of these scripts are unreliable: agent ran 100+ Bash
calls without ever invoking match_pitfall, save_last_wrong_attempt, or
auto_tactic. Phase 4 wires deterministic T1 calls into the SDK PostTool
hook so the czy port arsenal actually triggers when the conditions hold.

Tests in this file pin the wiring contract (hook → script call). The
ported scripts themselves are unchanged; only dispatch fabric is new.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

# Add scripts dir to sys.path for direct module import
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import hook_post_tool  # noqa: E402


# ── _parse_lake_errors regex tests ─────────────────────────────────


def test_parse_lake_errors_single_file_single_error():
    text = "/abs/path/Foo.lean:42:8: error: type mismatch"
    out = hook_post_tool._parse_lake_errors(text)
    assert "/abs/path/Foo.lean" in out
    errs = out["/abs/path/Foo.lean"]
    assert len(errs) == 1
    assert errs[0]["severity"] == "error"
    assert errs[0]["line"] == 42
    assert errs[0]["column"] == 8
    assert errs[0]["message"] == "type mismatch"


def test_parse_lake_errors_multiple_errors():
    text = """
/abs/Foo.lean:10:5: error: first error
/abs/Bar.lean:20:3: error: second error
random non-error text
/abs/Foo.lean:30:1: error: third in foo
""".strip()
    out = hook_post_tool._parse_lake_errors(text)
    assert "/abs/Foo.lean" in out
    assert "/abs/Bar.lean" in out
    assert len(out["/abs/Foo.lean"]) == 2
    assert len(out["/abs/Bar.lean"]) == 1


def test_parse_lake_errors_continuation_lines():
    """Multi-line errors (continuation without `error:`) append to last err."""
    text = """\
/abs/Foo.lean:5:3: error: type mismatch
  hX
has type
  X = Y
but is expected to have type
  X ≠ Y
"""
    out = hook_post_tool._parse_lake_errors(text)
    errs = out["/abs/Foo.lean"]
    assert len(errs) == 1
    msg = errs[0]["message"]
    assert "type mismatch" in msg
    assert "X ≠ Y" in msg  # continuation lines folded in


def test_parse_lake_errors_empty():
    assert hook_post_tool._parse_lake_errors("") == {}
    assert hook_post_tool._parse_lake_errors("just warnings, no errors") == {}


def test_parse_lake_errors_filters_non_lean_files():
    """Only .lean files appear in the output (non-lean errors ignored)."""
    text = """
/abs/some.py:5:1: error: this is python
/abs/Foo.lean:10:5: error: this is lean
""".strip()
    out = hook_post_tool._parse_lake_errors(text)
    # Both .lean and .py end up here because regex doesn't filter ext, but
    # the call site (_handle_bash) checks .endswith(".lean") before
    # invoking save_last_wrong_attempt. The regex itself accepts any
    # ext as long as line:col:error format is present — that's
    # intentionally permissive so the regex stays simple. Pin the
    # behavior so tests fail loudly if it changes.
    # NOTE: regex IS .lean-anchored — re-confirm:
    assert "/abs/some.py:5:1: error: this is python" not in str(out)
    assert "/abs/Foo.lean" in out


# ── Phase 4 hook integration tests ──────────────────────────────────


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    """Create a minimal sandbox with events.jsonl for milestone emission."""
    sb = tmp_path / "sandbox"
    sb.mkdir()
    (sb / "events.jsonl").write_text("")
    return sb


def test_call_match_pitfall_invokes_subprocess(sandbox: Path):
    """_call_match_pitfall must call match_pitfall.py as subprocess
    with --error-text and --sandbox."""
    with patch("hook_post_tool.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0)
        hook_post_tool._call_match_pitfall(sandbox, "unexpected token 'λ'")
        assert mock_run.called
        args = mock_run.call_args[0][0]
        assert "match_pitfall.py" in args[1]
        assert "--error-text" in args
        assert "--sandbox" in args
        assert str(sandbox) in args


def test_call_match_pitfall_caps_error_text_at_4000_chars(sandbox: Path):
    """Long stderr must be capped to match match_pitfall's _MAX_ERROR_LEN
    so the hook stays under HOOK_BUDGET_S even on pathological input."""
    huge = "X" * 10000
    with patch("hook_post_tool.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0)
        hook_post_tool._call_match_pitfall(sandbox, huge)
        args = mock_run.call_args[0][0]
        idx = args.index("--error-text")
        passed = args[idx + 1]
        assert len(passed) == 4000


def test_call_match_pitfall_skips_empty_text(sandbox: Path):
    """No work if there's no error text — hook stays cheap on the
    happy path (lake-build-clean)."""
    with patch("hook_post_tool.subprocess.run") as mock_run:
        hook_post_tool._call_match_pitfall(sandbox, "")
        assert not mock_run.called


def test_call_save_last_wrong_attempt_invokes_subprocess(sandbox: Path, tmp_path: Path):
    """_call_save_last_wrong_attempt must call save_last_wrong_attempt.py
    with the file content path and diagnostics JSON."""
    fake_file = tmp_path / "Foo.lean"
    fake_file.write_text("theorem foo : 1 + 1 = 2 := sorry")
    errs = [{"severity": "error", "line": 1, "column": 5, "message": "msg"}]
    with patch("hook_post_tool.subprocess.run") as mock_run:
        mock_run.return_value = MagicMock(returncode=0)
        hook_post_tool._call_save_last_wrong_attempt(sandbox, str(fake_file), errs)
        assert mock_run.called
        args = mock_run.call_args[0][0]
        assert "save_last_wrong_attempt.py" in args[1]
        assert "--content" in args
        assert str(fake_file) in args
        assert "--diagnostics" in args
        # Verify diagnostics is valid JSON containing our error
        idx = args.index("--diagnostics")
        decoded = json.loads(args[idx + 1])
        assert decoded == errs


def test_call_save_last_wrong_attempt_skips_when_file_missing(sandbox: Path):
    """Don't call subprocess if the file path doesn't exist (defensive)."""
    with patch("hook_post_tool.subprocess.run") as mock_run:
        hook_post_tool._call_save_last_wrong_attempt(
            sandbox, "/nonexistent/foo.lean", [{"severity": "error"}],
        )
        assert not mock_run.called


def test_call_save_last_wrong_attempt_skips_empty_errors(sandbox: Path, tmp_path: Path):
    """No errors → no annotated artifact (nothing to save)."""
    fake_file = tmp_path / "Foo.lean"
    fake_file.write_text("ok")
    with patch("hook_post_tool.subprocess.run") as mock_run:
        hook_post_tool._call_save_last_wrong_attempt(sandbox, str(fake_file), [])
        assert not mock_run.called


def test_maybe_spawn_auto_tactic_uses_detached_popen(sandbox: Path):
    """auto_tactic must spawn detached (Popen + start_new_session=True)
    so its long-running cost doesn't block the hook's 8s budget."""
    with patch("hook_post_tool.subprocess.Popen") as mock_popen:
        mock_popen.return_value = MagicMock()
        hook_post_tool._maybe_spawn_auto_tactic(sandbox)
        assert mock_popen.called
        kwargs = mock_popen.call_args.kwargs
        assert kwargs.get("start_new_session") is True


def test_maybe_spawn_auto_tactic_creates_lockfile(sandbox: Path):
    """Lockfile prevents re-entry within AUTO_TACTIC_LOCKOUT_S window."""
    with patch("hook_post_tool.subprocess.Popen"):
        hook_post_tool._maybe_spawn_auto_tactic(sandbox)
    lock = sandbox / ".auto_tactic.lock"
    assert lock.exists()


def test_maybe_spawn_auto_tactic_respects_lockout(sandbox: Path):
    """Second spawn within lockout window is suppressed."""
    lock = sandbox / ".auto_tactic.lock"
    lock.touch()  # simulate fresh prior spawn
    with patch("hook_post_tool.subprocess.Popen") as mock_popen:
        hook_post_tool._maybe_spawn_auto_tactic(sandbox)
        assert not mock_popen.called


def test_maybe_spawn_auto_tactic_allows_after_lockout_expires(sandbox: Path):
    """Stale lockfile (>10 min old) does not suppress."""
    lock = sandbox / ".auto_tactic.lock"
    lock.touch()
    # Backdate the lockfile beyond the lockout
    old = time.time() - hook_post_tool.AUTO_TACTIC_LOCKOUT_S - 10
    import os
    os.utime(lock, (old, old))
    with patch("hook_post_tool.subprocess.Popen") as mock_popen:
        mock_popen.return_value = MagicMock()
        hook_post_tool._maybe_spawn_auto_tactic(sandbox)
        assert mock_popen.called


# ── End-to-end: simulated PostTool payload ──────────────────────────


def test_handle_bash_lake_build_fail_invokes_phase4_chain(sandbox: Path, tmp_path: Path):
    """Full integration: a Bash payload with `lake build` + error stderr
    triggers (a) lake-build-fail emit, (b) match_pitfall call,
    (c) save_last_wrong_attempt call when /Statlean/*.lean appears."""
    # Plant a real .lean file that the regex will pick up
    statlean = tmp_path / "Statlean" / "Foo"
    statlean.mkdir(parents=True)
    failing_file = statlean / "Bar.lean"
    failing_file.write_text("theorem foo : True := sorry")

    payload = {
        "tool_name": "Bash",
        "tool_input": {"command": "lake build Statlean.Foo.Bar"},
        "tool_response": {
            "stdout": f"{failing_file}:1:9: error: type mismatch",
            "stderr": "",
            "interrupted": False,
        },
        "session_id": "abc12345" * 2,
        "agent_type": "main",
    }
    calls = []

    def fake_run(cmd, **kw):
        calls.append(cmd)
        return MagicMock(returncode=0)

    with patch("hook_post_tool.subprocess.run", side_effect=fake_run):
        hook_post_tool._handle_bash(payload, sandbox)

    # Should have called: emit_event (lake-build-fail), match_pitfall, save_last_wrong_attempt
    scripts_called = [
        cmd[1] for cmd in calls
        if isinstance(cmd, list) and len(cmd) >= 2 and cmd[0] in ("python3",)
    ]
    assert any("emit_event.py" in s for s in scripts_called), \
        "lake-build-fail milestone must be emitted"
    assert any("match_pitfall.py" in s for s in scripts_called), \
        "Phase 4 T1: match_pitfall must fire on lake-build-fail"
    assert any("save_last_wrong_attempt.py" in s for s in scripts_called), \
        "Phase 4 T1: save_last_wrong_attempt must fire on lake-build-fail with /Statlean/*.lean"


def test_handle_bash_lake_build_clean_skips_phase4(sandbox: Path):
    """Clean build (no error in stdout/stderr) must NOT fire match_pitfall
    or save_last_wrong_attempt — they're failure-recovery only."""
    payload = {
        "tool_name": "Bash",
        "tool_input": {"command": "lake build Statlean.Foo"},
        "tool_response": {
            "stdout": "Build completed successfully.",
            "stderr": "",
            "interrupted": False,
        },
        "session_id": "abc12345",
        "agent_type": "main",
    }
    calls = []

    def fake_run(cmd, **kw):
        calls.append(cmd)
        return MagicMock(returncode=0)

    with patch("hook_post_tool.subprocess.run", side_effect=fake_run):
        hook_post_tool._handle_bash(payload, sandbox)

    scripts_called = [
        cmd[1] for cmd in calls
        if isinstance(cmd, list) and len(cmd) >= 2
    ]
    assert not any("match_pitfall.py" in s for s in scripts_called), \
        "match_pitfall must not fire on lake-build-clean"
    assert not any("save_last_wrong_attempt.py" in s for s in scripts_called), \
        "save_last_wrong_attempt must not fire on lake-build-clean"


def test_handle_write_or_edit_delta_pos_spawns_auto_tactic(
    sandbox: Path, tmp_path: Path,
):
    """When sorry pool grows (Write/Edit on .lean adds sorries),
    auto_tactic_pre_pass must spawn detached."""
    # Set up the path the hook expects; the .lean file must be inside
    # /Statlean/ for the hook to process it (line 195 filter).
    fake_file = tmp_path / "Statlean" / "Foo.lean"
    fake_file.parent.mkdir(parents=True)
    fake_file.write_text("theorem t : True := sorry")

    payload = {
        "tool_name": "Write",
        "tool_input": {"file_path": str(fake_file)},
        "agent_type": "main",
    }

    # Simulate sorry-count behavior: pre-existing sorry_list.json with 0
    # entries; after Write, extract_sorries returns 1 entry.
    sl_path = sandbox / "sorry_list.json"
    sl_path.write_text("[]")

    with patch("hook_post_tool.subprocess.run") as mock_run, \
         patch("hook_post_tool.subprocess.Popen") as mock_popen:
        # Make extract_sorries write 1-entry list
        def fake_run(cmd, **kw):
            if any("extract_sorries.py" in str(c) for c in cmd):
                # Simulate the script writing to --output
                if "--output" in cmd:
                    out_idx = cmd.index("--output")
                    Path(cmd[out_idx + 1]).write_text('[{"id":"s1"}]')
            return MagicMock(returncode=0)

        mock_run.side_effect = fake_run
        mock_popen.return_value = MagicMock()
        hook_post_tool._handle_write_or_edit(payload, sandbox)

    assert mock_popen.called, "auto_tactic must spawn when delta>0"
    args = mock_popen.call_args[0][0]
    assert any("auto_tactic_pre_pass.py" in str(a) for a in args)


def test_handle_write_or_edit_delta_neg_does_not_spawn_auto_tactic(
    sandbox: Path, tmp_path: Path,
):
    """delta<0 (sorry was just proved) must NOT trigger auto_tactic —
    that's a regression scenario only relevant when new sorries appear."""
    fake_file = tmp_path / "Statlean" / "Foo.lean"
    fake_file.parent.mkdir(parents=True)
    fake_file.write_text("theorem t : True := trivial")

    payload = {
        "tool_name": "Edit",
        "tool_input": {"file_path": str(fake_file)},
        "agent_type": "main",
    }

    sl_path = sandbox / "sorry_list.json"
    sl_path.write_text('[{"id":"s1"}, {"id":"s2"}]')  # 2 sorries before

    with patch("hook_post_tool.subprocess.run") as mock_run, \
         patch("hook_post_tool.subprocess.Popen") as mock_popen:
        def fake_run(cmd, **kw):
            if any("extract_sorries.py" in str(c) for c in cmd):
                if "--output" in cmd:
                    out_idx = cmd.index("--output")
                    Path(cmd[out_idx + 1]).write_text('[{"id":"s1"}]')  # 1 left now
            return MagicMock(returncode=0)

        mock_run.side_effect = fake_run
        mock_popen.return_value = MagicMock()
        hook_post_tool._handle_write_or_edit(payload, sandbox)

    assert not mock_popen.called, \
        "auto_tactic must NOT spawn when delta<0 (sorry-proved path)"

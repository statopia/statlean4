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


# ── delta subcommand ───────────────────────────────────────────────────
class TestDelta:
    def test_minimal_required_args(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "hypothesis-add",
            "--summary", "Added continuity",
        )
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["kind"] == "formalization_delta"
        assert e["change_type"] == "hypothesis-add"
        assert e["summary"] == "Added continuity"
        # severity defaults to 'notable'
        assert e["severity"] == "notable"
        # optional paths/details omitted
        assert "before_path" not in e
        assert "after_path" not in e
        assert "details" not in e

    def test_all_fields(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "type-weaken",
            "--summary", "ℝ → ℕ",
            "--severity", "breaking",
            "--before-path", "theorems.yaml",
            "--after-path", "Main.lean",
            "--details", '{"old":"ℝ","new":"ℕ"}',
        )
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["change_type"] == "type-weaken"
        assert e["severity"] == "breaking"
        assert e["before_path"] == "theorems.yaml"
        assert e["after_path"] == "Main.lean"
        assert e["details"] == {"old": "ℝ", "new": "ℕ"}

    def test_invalid_change_type_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "made-up-kind",
            "--summary", "x",
        )
        assert r.returncode != 0
        assert "invalid choice" in r.stderr.lower()

    def test_invalid_severity_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "other",
            "--summary", "x",
            "--severity", "catastrophic",
        )
        assert r.returncode != 0
        assert "invalid choice" in r.stderr.lower()

    def test_empty_summary_rejected(self, tmp_path: Path) -> None:
        # argparse requires --summary to be present, but an explicit empty
        # string slips through. _cmd_delta guards against it.
        r = _run(
            tmp_path, "delta",
            "--change-type", "other",
            "--summary", "   ",
        )
        assert r.returncode == 2
        assert "non-empty --summary" in r.stderr

    def test_details_invalid_json_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "other",
            "--summary", "x",
            "--details", "{not json",
        )
        assert r.returncode == 2
        assert "not valid JSON" in r.stderr

    def test_details_must_be_object(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "delta",
            "--change-type", "other",
            "--summary", "x",
            "--details", "[1,2,3]",
        )
        assert r.returncode == 2
        assert "must be a JSON object" in r.stderr

    def test_all_change_types_accepted(self, tmp_path: Path) -> None:
        # Edge: every documented change-type value must be settable.
        # Catches enum drift between argparse choices and ui-signals.md.
        for ct in [
            "dim-reduction", "hypothesis-add", "hypothesis-remove",
            "type-weaken", "conclusion-replace", "structure-introduce",
            "scope-restrict", "other",
        ]:
            sandbox = tmp_path / f"sbx-{ct}"
            sandbox.mkdir()
            r = _run(
                sandbox, "delta",
                "--change-type", ct,
                "--summary", "test",
            )
            assert r.returncode == 0, f"{ct}: {r.stderr}"
            assert _read_events(sandbox)[0]["change_type"] == ct


# ── milestone subcommand ───────────────────────────────────────────────
class TestMilestone:
    def test_minimal(self, tmp_path: Path) -> None:
        r = _run(tmp_path, "milestone", "--name", "lake-build-clean")
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["kind"] == "sandbox_milestone"
        assert e["name"] == "lake-build-clean"
        assert "details" not in e
        assert "path" not in e

    def test_with_path_and_details(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "milestone",
            "--name", "sorry-zero",
            "--path", "Main.lean",
            "--details", '{"count_before":3,"count_after":0}',
        )
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["name"] == "sorry-zero"
        assert e["path"] == "Main.lean"
        assert e["details"] == {"count_before": 3, "count_after": 0}

    def test_invalid_name_rejected(self, tmp_path: Path) -> None:
        r = _run(tmp_path, "milestone", "--name", "made-up")
        assert r.returncode != 0
        assert "invalid choice" in r.stderr.lower()

    def test_all_milestone_names_accepted(self, tmp_path: Path) -> None:
        for name in [
            "lake-build-clean", "sorry-zero", "yaml-complete", "pdf-extracted",
            "skeleton-locked", "proof-verified", "promoted", "other",
        ]:
            sandbox = tmp_path / f"sbx-{name}"
            sandbox.mkdir()
            r = _run(sandbox, "milestone", "--name", name)
            assert r.returncode == 0, f"{name}: {r.stderr}"
            assert _read_events(sandbox)[0]["name"] == name

    def test_details_invalid_json_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "milestone",
            "--name", "other",
            "--details", "not-json",
        )
        assert r.returncode == 2
        assert "not valid JSON" in r.stderr

    def test_details_scalar_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "milestone",
            "--name", "other",
            "--details", "42",
        )
        assert r.returncode == 2
        assert "must be a JSON object" in r.stderr


# ── agent-state subcommand ─────────────────────────────────────────────
class TestAgentState:
    def test_minimal(self, tmp_path: Path) -> None:
        r = _run(tmp_path, "agent-state", "--state", "idle")
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["kind"] == "agent_state"
        assert e["state"] == "idle"
        assert "since_ms" not in e
        assert "prompt" not in e

    def test_awaiting_input_with_prompt(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "agent-state",
            "--state", "awaiting-input",
            "--prompt", "Should I weaken the hypothesis?",
        )
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["state"] == "awaiting-input"
        assert e["prompt"] == "Should I weaken the hypothesis?"

    def test_thinking_with_since_ms(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "agent-state",
            "--state", "thinking",
            "--since-ms", "4500",
        )
        assert r.returncode == 0, r.stderr
        e = _read_events(tmp_path)[0]
        assert e["state"] == "thinking"
        assert e["since_ms"] == 4500

    def test_negative_since_ms_rejected(self, tmp_path: Path) -> None:
        r = _run(
            tmp_path, "agent-state",
            "--state", "thinking",
            "--since-ms", "-1",
        )
        assert r.returncode == 2
        assert "since-ms must be >= 0" in r.stderr

    def test_zero_since_ms_accepted(self, tmp_path: Path) -> None:
        # Edge: 0 is the natural "just transitioned" value, must be allowed.
        r = _run(
            tmp_path, "agent-state",
            "--state", "thinking",
            "--since-ms", "0",
        )
        assert r.returncode == 0, r.stderr
        assert _read_events(tmp_path)[0]["since_ms"] == 0

    def test_invalid_state_rejected(self, tmp_path: Path) -> None:
        r = _run(tmp_path, "agent-state", "--state", "panicking")
        assert r.returncode != 0
        assert "invalid choice" in r.stderr.lower()

    def test_all_states_accepted(self, tmp_path: Path) -> None:
        for state in ["thinking", "tool-call", "awaiting-input", "idle", "done"]:
            sandbox = tmp_path / f"sbx-{state}"
            sandbox.mkdir()
            r = _run(sandbox, "agent-state", "--state", state)
            assert r.returncode == 0, f"{state}: {r.stderr}"
            assert _read_events(sandbox)[0]["state"] == state


# ── interleaving + ordering across new kinds ────────────────────────
class TestInterleaving:
    def test_step_artifact_delta_milestone_state_appended_in_order(
        self, tmp_path: Path
    ) -> None:
        # End-to-end: a realistic skill flow emits step + artifact +
        # delta + milestone + agent-state in sequence. All five must
        # land in events.jsonl in emission order.
        _run(tmp_path, "step", "--id", "1", "--title", "P", "--status", "start")
        _run(tmp_path, "artifact", "--kind-tag", "yaml", "--path", "theorems.yaml")
        _run(
            tmp_path, "delta",
            "--change-type", "hypothesis-add",
            "--summary", "added regularity",
        )
        _run(tmp_path, "milestone", "--name", "yaml-complete")
        _run(tmp_path, "agent-state", "--state", "idle")
        kinds = [e["kind"] for e in _read_events(tmp_path)]
        assert kinds == [
            "step",
            "artifact",
            "formalization_delta",
            "sandbox_milestone",
            "agent_state",
        ]

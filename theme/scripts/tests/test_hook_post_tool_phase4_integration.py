"""
Phase 4 INTEGRATION smoke (czy port arch fix, 2026-05-01) — real
subprocess chain hook_post_tool.py → match_pitfall.py → emit_event.py
→ events.jsonl. No mocks: this verifies the production T1 escalation
chain actually produces milestones when stimulated.

Distinct from test_hook_post_tool_phase4.py (unit tests with mocks),
this exercises the full dispatch fabric by feeding fake-but-realistic
SDK PostTool payloads on stdin and asserting events.jsonl gains the
expected milestones.

Pairs with the real-LLM smoke `scripts/smoke-sdk/07-phase4-hooks.ts`
in /home/gavin/website (which verifies the SDK harness loads the hook
correctly when a job runs).
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
HOOK = SCRIPTS_DIR / "hook_post_tool.py"


def _run_hook(payload: dict, sandbox: Path, timeout: int = 30) -> subprocess.CompletedProcess:
    """Pipe payload to hook_post_tool.py with $SANDBOX env set."""
    env = os.environ.copy()
    env["SANDBOX"] = str(sandbox)
    return subprocess.run(
        ["python3", str(HOOK)],
        input=json.dumps(payload),
        capture_output=True,
        text=True,
        timeout=timeout,
        env=env,
    )


def _read_events(sandbox: Path) -> list[dict]:
    p = sandbox / "events.jsonl"
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        try:
            out.append(json.loads(line))
        except Exception:
            continue
    return out


def _milestone_names(events: list[dict]) -> list[str]:
    return [
        e.get("name", "")
        for e in events
        if e.get("kind") == "sandbox_milestone"
    ]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    sb = tmp_path / "phase4_smoke"
    sb.mkdir()
    (sb / "events.jsonl").write_text("")
    return sb


# ── Smoke 1: lake-build-fail with pitfall pattern → pitfall-matched event ──


def test_lake_build_fail_with_lambda_keyword_emits_pitfall_matched(sandbox: Path):
    """Plant a stderr that match_pitfall's 23 czy rules will catch
    (rule A.1: reserved-keyword char in identifier). Verify the
    full hook → match_pitfall → emit_event chain lands a
    `pitfall-matched` milestone with the routing hint as its details.
    """
    payload = {
        "tool_name": "Bash",
        "tool_input": {"command": "lake build Statlean.Test.PitfallSmoke"},
        "tool_response": {
            "stdout": "/abs/Statlean/Test/PitfallSmoke.lean:5:8: error: unexpected token 'λ'",
            "stderr": "",
            "interrupted": False,
        },
        "session_id": "phase4smoke12345",
        "agent_type": "main",
    }
    result = _run_hook(payload, sandbox)
    assert result.returncode == 0, f"hook crashed: {result.stderr}"

    events = _read_events(sandbox)
    names = _milestone_names(events)

    assert "lake-build-fail" in names, (
        "lake-build-fail must be emitted on error stderr — baseline "
        "behavior, predates Phase 4"
    )
    assert "pitfall-matched" in names, (
        "Phase 4 T1: pitfall-matched milestone must fire when "
        "match_pitfall matches a rule. czy port had this as T3 "
        "narrative — Phase 4 makes it deterministic."
    )

    # Verify the pitfall hint is in the milestone details.
    pm = next(e for e in events if e.get("name") == "pitfall-matched")
    details = pm.get("details", {})
    # match_pitfall.py emits hint text; structure is {hint, file, section, ...}.
    # We accept any non-empty hint payload — exact text is czy-sourced
    # and pinned by match_pitfall's own tests.
    assert any(details.get(k) for k in ("hint", "file", "section", "rule_id")), \
        f"pitfall-matched details lacks hint payload: {details}"


def test_lake_build_clean_does_not_emit_pitfall_matched(sandbox: Path):
    """Happy path: clean build → no Phase 4 milestones at all. Confirms
    the hook is failure-recovery, not always-on overhead."""
    payload = {
        "tool_name": "Bash",
        "tool_input": {"command": "lake build Statlean.Test.PitfallSmoke"},
        "tool_response": {
            "stdout": "Build completed successfully.",
            "stderr": "",
            "interrupted": False,
        },
        "session_id": "phase4smoke12346",
        "agent_type": "main",
    }
    result = _run_hook(payload, sandbox)
    assert result.returncode == 0

    names = _milestone_names(_read_events(sandbox))
    assert "lake-build-clean" in names
    assert "pitfall-matched" not in names
    assert "last-wrong-attempt-saved" not in names


# ── Smoke 2: lake-build-fail with /Statlean/*.lean error → save_last_wrong_attempt ──


def test_lake_build_fail_with_statlean_file_writes_last_wrong_attempt(
    sandbox: Path, tmp_path: Path,
):
    """Phase 4 T1 escalation: save_last_wrong_attempt fires when
    /Statlean/*.lean appears in the error. Verifies the annotated
    artifact lands on disk."""
    # Plant a real .lean file the regex will identify
    statlean = tmp_path / "Statlean" / "Test"
    statlean.mkdir(parents=True)
    failing = statlean / "WrongAttempt.lean"
    failing.write_text(
        "theorem t : 1 + 1 = 2 := by\n"
        "  rfl\n"
        "  -- bogus continuation\n"
        "  sorry\n"
    )

    payload = {
        "tool_name": "Bash",
        "tool_input": {"command": "lake build Statlean.Test.WrongAttempt"},
        "tool_response": {
            "stdout": f"{failing}:2:3: error: unsolved goals\n  some context here",
            "stderr": "",
            "interrupted": False,
        },
        "session_id": "phase4smoke12347",
        "agent_type": "main",
    }
    result = _run_hook(payload, sandbox)
    assert result.returncode == 0, f"hook crashed: {result.stderr}"

    # save_last_wrong_attempt must have written the annotated artifact
    annotated = sandbox / "last_wrong_attempt.lean"
    assert annotated.exists(), (
        "Phase 4 T1: save_last_wrong_attempt must write the annotated "
        "artifact when lake-build-fail names a /Statlean/*.lean file"
    )
    body = annotated.read_text()
    # Annotation contract: per-line ERROR markers + footer (per
    # save_last_wrong_attempt.py docstring referencing
    # lastWrongAttempt.ts:143-211 byte-equal).
    assert "ERROR" in body, (
        "annotated content must contain per-line ERROR markers"
    )

    # Also check that a milestone was emitted documenting the save
    names = _milestone_names(_read_events(sandbox))
    assert any("last-wrong-attempt" in n or "wrong-attempt" in n for n in names), (
        f"a `last-wrong-attempt-saved`-family milestone is expected; got {names}"
    )


# ── Smoke 3: Edit on Statlean/*.lean with delta>0 → auto_tactic spawn (lockfile) ──


def test_edit_with_sorry_pool_growth_spawns_auto_tactic(
    sandbox: Path, tmp_path: Path,
):
    """When a Statlean .lean file Edit grows the sorry pool, auto_tactic
    must spawn detached. Verify by lockfile existence (the spawn itself
    is detached so we can't directly observe its stdout, but the
    lockfile is the synchronous side-effect)."""
    fake_file = tmp_path / "Statlean" / "Test" / "PoolGrowth.lean"
    fake_file.parent.mkdir(parents=True)
    fake_file.write_text("theorem a : True := sorry\ntheorem b : True := sorry\n")

    # Pre-existing sorry_list.json with 0 entries — extract_sorries
    # will refresh it from the file (which has 2 sorries) → delta = +2.
    (sandbox / "sorry_list.json").write_text("[]")

    payload = {
        "tool_name": "Edit",
        "tool_input": {"file_path": str(fake_file)},
        "tool_response": {},
        "session_id": "phase4smoke12348",
        "agent_type": "main",
    }
    result = _run_hook(payload, sandbox)
    assert result.returncode == 0

    # Lockfile is the synchronous evidence that auto_tactic was spawned
    lock = sandbox / ".auto_tactic.lock"
    assert lock.exists(), (
        "Phase 4 T1: auto_tactic_pre_pass.py must spawn (detached) "
        "when sorry pool grows; lockfile is the synchronous trace."
    )

    # And the snapshot milestone records the delta>0 condition
    events = _read_events(sandbox)
    sps = [e for e in events if e.get("name") == "sorry-pool-snapshot"]
    assert sps, "sorry-pool-snapshot must be emitted"
    assert sps[-1]["details"].get("delta", 0) > 0

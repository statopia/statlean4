"""M5 L1 + L2 unit tests for auto_tactic_pre_pass.py.

Coverage matrix per `docs/M5_AUTO_TACTIC_SPEC.md` §7 (post §8 review):

  L1.1  rfl closes a tautology
  L1.2  first-pass-wins semantic (asserts czy tactic order verbatim)
  L1.3  all 9 tactics fail → no mutation
  L1.4  complexity-skip heuristic (parametric over 6 keywords)
  L1.5  Layer 1 invariant — locked theorem signature byte-identical
  L1.6  idempotence on already-DONE rows
  L2    end-to-end via subprocess (skipped if STATLEAN_ROOT absent)

The L1 cases use `try_tactic_fn=` injection on `run_pre_pass` so we
don't need a real Lean toolchain. czy parity is asserted *via the
recorded call sequence* (mock records every tactic the ladder
attempted; tests pin order against `QUICK_TACTICS` constant).
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from unittest.mock import patch

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import auto_tactic_pre_pass as ATP  # noqa: E402
from auto_tactic_pre_pass import (  # noqa: E402
    COMPLEX_MATH_PATTERNS,
    QUICK_TACTICS,
    is_complex_file,
    run_pre_pass,
)


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
SCRIPT = SCRIPTS_DIR / "auto_tactic_pre_pass.py"


# ── Mocks (mirrored from test_verify_citation.py for symmetry) ──────


class TacticMock:
    """Configurable mock for `_try_tactic`. Records each invocation
    and returns a canned (passed, output) per call.

    Pattern matched on E11's TacticMock so the two suites stay
    structurally consistent. The M5 mock additionally has to handle
    multiple sorries × 9 tactics each, so we accept either a flat
    list of (passed, output) tuples (consumed in order) OR a callable
    that takes (file_path, sorry_line, tactic, module_path) and
    returns (passed, output).
    """

    def __init__(
        self,
        results: Optional[List[Tuple[bool, str]]] = None,
        verdict_fn=None,
    ) -> None:
        self.results = list(results) if results is not None else None
        self.verdict_fn = verdict_fn
        self.calls: List[Dict[str, Any]] = []

    def __call__(
        self,
        file_path: Path,
        sorry_line: int,
        tactic: str,
        module_path: Optional[str] = None,
    ) -> Tuple[bool, str]:
        self.calls.append({
            "file_path": file_path, "sorry_line": sorry_line,
            "tactic": tactic, "module_path": module_path,
        })
        if self.verdict_fn is not None:
            return self.verdict_fn(tactic, sorry_line)
        if not self.results:
            raise RuntimeError("TacticMock exhausted")
        return self.results.pop(0)


# ── Fixtures ────────────────────────────────────────────────────────


def _v2_backlog_with_sorry(
    sorry_id: str = "p.s1",
    file_rel: str = "Statlean/Foo.lean",
    line: int = 5,
    state: str = "INITIALIZED",
    coverage_state: str = "needs_proof",
    extras: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    item: Dict[str, Any] = {
        "id": sorry_id, "file": file_rel, "line": line,
        "theorem": f"{sorry_id}_thm", "type": "ready",
        "depth": 0, "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": state, "children": [], "parent_id": None,
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": coverage_state,
        "citation_verified": False,
    }
    if extras:
        item.update(extras)
    return item


def _write_backlog(path: Path, items: List[Dict[str, Any]]) -> None:
    data = {"schema_version": 2, "version": "v100", "sorry_items": items}
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _by_id(backlog_path: Path, item_id: str) -> Dict[str, Any]:
    data = yaml.safe_load(backlog_path.read_text())
    return next(it for it in data["sorry_items"] if it["id"] == item_id)


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    # Pre-create a sorry_list.json so process_sorry_result's refresh
    # step doesn't crash (best-effort, but tests get noisy logs
    # without it).
    (s / "sorry_list.json").write_text("[]")
    return s


@pytest.fixture
def statlean_root(tmp_path: Path) -> Path:
    """Stub repo root with `Statlean/` dir. Individual tests write
    Lean files into here as needed."""
    r = tmp_path / "repo"
    (r / "Statlean").mkdir(parents=True)
    return r


def _write_lean_file(
    statlean_root: Path,
    rel_path: str,
    sig_line: str = "theorem t : 1 + 1 = 2 := sorry",
    pre_lines: Optional[List[str]] = None,
    imports: Optional[List[str]] = None,
) -> Path:
    """Write a minimal Lean file with the sorry on a known line.
    Returns absolute path. The sorry line index = len(imports) + 1
    (default + len(pre_lines)).
    """
    file_path = (statlean_root / rel_path).resolve()
    file_path.parent.mkdir(parents=True, exist_ok=True)
    parts: List[str] = []
    for imp in (imports or []):
        parts.append(f"import {imp}\n")
    for ln in (pre_lines or []):
        parts.append(ln if ln.endswith("\n") else ln + "\n")
    parts.append(sig_line if sig_line.endswith("\n") else sig_line + "\n")
    file_path.write_text("".join(parts), encoding="utf-8")
    return file_path


@pytest.fixture
def mock_psr(monkeypatch: pytest.MonkeyPatch) -> List[List[str]]:
    """Capture process_sorry_result invocations without actually
    spawning subprocesses. Returns a list of cmd-arg-lists for
    later inspection.
    """
    captured: List[List[str]] = []

    def _fake_run(cmd, *args, **kwargs):  # type: ignore[no-untyped-def]
        captured.append(list(cmd))

        class _Result:
            returncode = 0

        return _Result()

    monkeypatch.setattr(ATP.subprocess, "run", _fake_run)
    return captured


# ── L1.1 rfl closes a tautology ─────────────────────────────────────


def test_l1_1_rfl_closes_tautology(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """First tactic (`rfl`) PASSes → backlog row should be flipped via
    process_sorry_result; only ONE tactic call should have been made."""
    rel = "Statlean/Foo.lean"
    file_path = _write_lean_file(statlean_root, rel,
                                  sig_line="theorem t : 1 + 1 = 2 := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "p.s1", file_rel=rel, line=1,
    )])

    mock = TacticMock([(True, "lake build clean")])

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["closed"] == 1
    assert summary["attempted"] == 1
    # First-pass-wins: only ONE tactic call (rfl) made
    assert len(mock.calls) == 1
    assert mock.calls[0]["tactic"] == "rfl"
    # Process_sorry_result invoked with --closer auto_tactic
    assert len(mock_psr) == 1
    cmd = mock_psr[0]
    assert "--status" in cmd and cmd[cmd.index("--status") + 1] == "proved"
    assert "--closer" in cmd and cmd[cmd.index("--closer") + 1] == "auto_tactic"
    assert "--sorry-id" in cmd and cmd[cmd.index("--sorry-id") + 1] == "p.s1"


# ── L1.2 first-pass-wins (czy parity on tactic order) ───────────────


def test_l1_2_first_pass_wins_with_czy_tactic_order(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """Tactics 1-7 fail; `simp` (8th) passes; `aesop` (9th) never
    called. Asserts the call sequence equals czy `:1227` truncated
    at PASS index. This is the load-bearing parity test for D-1."""
    rel = "Statlean/Bar.lean"
    _write_lean_file(statlean_root, rel,
                     sig_line="theorem b : True := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "q.s1", file_rel=rel, line=1,
    )])

    # Tactics 1-7 FAIL (rfl..norm_num); tactic 8 (simp) PASSES.
    results = [(False, f"f-{i}") for i in range(7)] + [(True, "ok")]
    mock = TacticMock(results)

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["closed"] == 1
    # Exactly 8 tactic calls (rfl..simp) — aesop never reached
    assert len(mock.calls) == 8

    # czy `proofLoop.ts:1227` order: pin verbatim
    czy_order = ["rfl", "trivial", "decide", "ring",
                 "linarith", "omega", "norm_num", "simp", "aesop"]
    expected_truncated = czy_order[:8]
    actual = [c["tactic"] for c in mock.calls]
    assert actual == expected_truncated, (
        f"czy parity violated: expected first-8 = {expected_truncated}, "
        f"got {actual}"
    )
    # Also verify the constant itself matches czy (defense-in-depth
    # against drift if someone reorders QUICK_TACTICS later).
    assert QUICK_TACTICS == czy_order


# ── L1.3 all 9 tactics fail → no mutation ───────────────────────────


def test_l1_3_all_nine_fail_no_mutation(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """All 9 fail → backlog byte-identical (still INITIALIZED), no
    process_sorry_result invocation, no `sorry-proved` event."""
    rel = "Statlean/Hard.lean"
    file_path = _write_lean_file(statlean_root, rel,
                                  sig_line="theorem h : ∀ x, x = x := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "h.s1", file_rel=rel, line=1,
    )])
    pre_backlog_bytes = backlog.read_bytes()
    pre_lean_bytes = file_path.read_bytes()

    # 9 FAIL results in order
    mock = TacticMock([(False, f"f-{i}") for i in range(9)])

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["closed"] == 0
    assert summary["attempted"] == 1
    # All 9 tactics tried in czy-verbatim order
    assert len(mock.calls) == 9
    assert [c["tactic"] for c in mock.calls] == QUICK_TACTICS
    # No process_sorry_result call
    assert mock_psr == [], (
        f"FAIL must not invoke process_sorry_result; got {mock_psr}"
    )
    # Backlog byte-identical (mock is in-memory; no row mutation)
    assert backlog.read_bytes() == pre_backlog_bytes
    # Lean file: `_try_tactic` is mocked, so no real mutation happens
    # in this test (real `_try_tactic` reverts on fail; that contract
    # is exercised by E11's L1 + the L2 smoke below).
    assert file_path.read_bytes() == pre_lean_bytes


# ── L1.4 complexity-skip heuristic (parametric over 6 keywords) ─────


@pytest.mark.parametrize("keyword", [
    "MeasureTheory",
    "ProbabilityTheory",
    "ENNReal",
    "IsProbabilityMeasure",
    "FiniteMeasure",
    "StochasticProcess",
])
def test_l1_4_complexity_skip(
    keyword: str,
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """A file mentioning any of the six COMPLEX_MATH_PATTERNS keywords
    triggers the complex-file skip — no `_try_tactic` call is made,
    backlog byte-identical, no process_sorry_result invocation."""
    rel = f"Statlean/Complex_{keyword}.lean"
    # Inline mention of the keyword in an import line is the realistic
    # case — czy detects in the same shape via regex on file content.
    file_path = _write_lean_file(
        statlean_root, rel,
        imports=[f"Mathlib.{keyword}.Foo"],
        sig_line="theorem c : 1 + 1 = 2 := sorry",
    )
    # Verify the regex would match (sanity)
    assert is_complex_file(file_path.read_text()), (
        f"sanity: keyword {keyword!r} must match COMPLEX_MATH_PATTERNS"
    )

    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "c.s1", file_rel=rel, line=2,  # line 2 because of import
    )])
    pre_backlog_bytes = backlog.read_bytes()
    pre_lean_bytes = file_path.read_bytes()

    mock = TacticMock([])  # would raise on any call

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["attempted"] == 0, (
        f"complex file must skip without attempting; summary={summary}"
    )
    assert summary["skipped"] >= 1
    assert mock.calls == [], "no tactic calls on complex-file skip"
    assert mock_psr == []
    assert backlog.read_bytes() == pre_backlog_bytes
    assert file_path.read_bytes() == pre_lean_bytes


# ── L1.5 Layer 1 invariant — locked theorem signature ───────────────


def test_l1_5_layer1_invariant_signature_byte_identical(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """After PASS, the theorem signature line is byte-identical to
    pre-call; only the `:= sorry` body got replaced. Uses the REAL
    `_try_tactic` (no mock!) — but stubs `subprocess.run` to make
    `lake build` succeed without actually invoking lake.

    This is the load-bearing Rule 3 Layer 1 test.
    """
    rel = "Statlean/Sig.lean"
    sig_line = "theorem s : 1 + 1 = 2 := sorry"
    file_path = _write_lean_file(statlean_root, rel, sig_line=sig_line)
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "s.s1", file_rel=rel, line=1,
    )])

    # Stub subprocess.run for BOTH `lake build` (called inside
    # `_try_tactic`) and `process_sorry_result.py` invocation
    # (called by run_pre_pass after PASS). Both succeed; we don't
    # need the real side-effects for this test.
    real_run = subprocess.run
    captured: List[List[str]] = []

    def _fake_run(cmd, *args, **kwargs):  # type: ignore[no-untyped-def]
        captured.append(list(cmd))

        class _Result:
            returncode = 0
            stdout = ""
            stderr = ""

        return _Result()

    # Patch in BOTH modules — _lean_tactic_attempt for lake build,
    # auto_tactic_pre_pass for process_sorry_result invocation.
    monkeypatch.setattr(
        "_lean_tactic_attempt.subprocess.run", _fake_run,
    )
    monkeypatch.setattr(ATP.subprocess, "run", _fake_run)

    # Run with REAL _try_tactic — it will mutate the file in place.
    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=None,  # use real _try_tactic
    )
    assert summary["closed"] == 1

    # Read post-call file content
    post = file_path.read_text(encoding="utf-8")
    # Body should now be `:= by rfl` (rfl was first attempted; mocked
    # lake build → returncode 0 → PASSes on first try).
    # Layer 1 invariant: the signature portion (everything before
    # ` := `) must be byte-identical.
    pre_sig_prefix = "theorem s : 1 + 1 = 2"
    assert post.startswith(pre_sig_prefix), (
        f"Layer 1 invariant violated: signature prefix changed.\n"
        f"  pre  = {pre_sig_prefix!r}\n"
        f"  post = {post.splitlines()[0]!r}"
    )
    # Body change: `sorry` should be gone, replaced by `by rfl`
    assert "sorry" not in post.splitlines()[0], (
        f"sorry still present after PASS: {post.splitlines()[0]!r}"
    )
    assert "by rfl" in post.splitlines()[0]


# ── L1.6 idempotence on already-DONE rows ───────────────────────────


def test_l1_6_idempotence_skip_already_done(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """A row with state=DONE is skipped without any tactic call. A
    mixed backlog (one DONE, one INITIALIZED) attacks ONLY the
    INITIALIZED row."""
    rel_done = "Statlean/Done.lean"
    rel_todo = "Statlean/Todo.lean"
    file_done = _write_lean_file(statlean_root, rel_done,
                                  sig_line="theorem d : True := trivial")
    file_todo = _write_lean_file(statlean_root, rel_todo,
                                  sig_line="theorem t : 1 + 1 = 2 := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [
        _v2_backlog_with_sorry("d.s1", file_rel=rel_done, line=1,
                                state="DONE",
                                extras={"done_reason": "proved"}),
        _v2_backlog_with_sorry("t.s1", file_rel=rel_todo, line=1),
    ])

    mock = TacticMock([(True, "ok")])  # rfl PASSes for the TODO row

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    # Only the TODO row attempted; DONE row skipped
    assert summary["attempted"] == 1
    assert summary["closed"] == 1
    assert summary["skipped"] == 1, (
        f"DONE row must be skipped (counted in skipped); summary={summary}"
    )
    # The single tactic call must target the TODO row, not DONE
    assert len(mock.calls) == 1
    assert mock.calls[0]["sorry_line"] == 1
    # process_sorry_result called for t.s1 only
    assert len(mock_psr) == 1
    cmd = mock_psr[0]
    assert cmd[cmd.index("--sorry-id") + 1] == "t.s1"


# ── L1 helper: SDK-bridge +ε (D-2) — coverage_state R7-owned skip ───


def test_skip_when_coverage_state_is_cited_by_library(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """SDK-bridge +ε vs czy (D-2): rows with `coverage_state ∈
    {cited_by_library, cited_by_reference}` are skipped so M5 doesn't
    double-spend with E11 R7."""
    rel = "Statlean/Cited.lean"
    _write_lean_file(statlean_root, rel,
                     sig_line="theorem x : True := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "x.s1", file_rel=rel, line=1,
        coverage_state="cited_by_library",
    )])
    mock = TacticMock([])  # would raise on any call

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["attempted"] == 0
    assert summary["skipped"] == 1
    assert mock.calls == []
    assert mock_psr == []


# ── L1 helper: --max-sorries cap ────────────────────────────────────


def test_max_sorries_cap_hit(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """If max_sorries=2 and there are 5 eligible rows, exactly 2 are
    attempted; cap_hit=True. czy-parity cost-ceiling per spec §8 R1."""
    items = []
    for i in range(5):
        rel = f"Statlean/F{i}.lean"
        _write_lean_file(statlean_root, rel,
                         sig_line=f"theorem t{i} : True := sorry")
        items.append(_v2_backlog_with_sorry(f"f{i}.s1", file_rel=rel, line=1))
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, items)

    # All would PASS on rfl
    mock = TacticMock(verdict_fn=lambda tac, ln: (True, "ok"))

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        max_sorries=2,
        try_tactic_fn=mock,
    )
    assert summary["attempted"] == 2
    assert summary["closed"] == 2
    assert summary["cap_hit"] is True
    # Exactly 2 tactic calls (rfl × 2 sorries)
    assert len(mock.calls) == 2


# ── L1 helper: per-tactic exception falls through ───────────────────


def test_per_tactic_exception_fall_through(
    tmp_path: Path,
    sandbox: Path,
    statlean_root: Path,
    mock_psr: List[List[str]],
) -> None:
    """If `_try_tactic` raises on tactic 1, the ladder continues to
    tactic 2. Same fall-through semantic as E11 library path
    (czy `:143-156`)."""
    rel = "Statlean/Raise.lean"
    _write_lean_file(statlean_root, rel,
                     sig_line="theorem r : 1 + 1 = 2 := sorry")
    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "r.s1", file_rel=rel, line=1,
    )])

    raise_count = [0]

    def verdict(tactic: str, sorry_line: int) -> Tuple[bool, str]:
        if raise_count[0] == 0 and tactic == "rfl":
            raise_count[0] += 1
            raise RuntimeError("simulated tool exception")
        if tactic == "trivial":
            return True, "ok"
        return False, "f"

    mock = TacticMock(verdict_fn=verdict)

    summary = run_pre_pass(
        backlog_path=backlog,
        statlean_root=statlean_root,
        sandbox=sandbox,
        try_tactic_fn=mock,
    )
    assert summary["closed"] == 1
    # At least 2 calls: rfl (raised) → trivial (PASS)
    assert len(mock.calls) >= 2
    assert mock.calls[0]["tactic"] == "rfl"
    assert mock.calls[1]["tactic"] == "trivial"


# ── L2 — end-to-end via subprocess ──────────────────────────────────


@pytest.mark.l2
@pytest.mark.skipif(
    "STATLEAN_ROOT" not in os.environ,
    reason="L2 smoke requires real Lean toolchain via STATLEAN_ROOT env",
)
def test_l2_e2e_via_subprocess(tmp_path: Path) -> None:
    """End-to-end smoke: invoke auto_tactic_pre_pass.py via subprocess
    against a real fixture. Skipped if STATLEAN_ROOT envvar absent.

    Mirrors test_verify_citation_integration's L2 pattern.
    """
    statlean_root = Path(os.environ["STATLEAN_ROOT"]).resolve()
    assert (statlean_root / "Statlean").is_dir(), (
        f"STATLEAN_ROOT must point to repo root containing Statlean/; "
        f"got {statlean_root}"
    )

    # Build a minimal sandbox + backlog. Real fixture: a tautology.
    sandbox = tmp_path / "sandbox"
    sandbox.mkdir()
    (sandbox / "sorry_list.json").write_text("[]")

    rel = "Statlean/Web/_m5_l2/Main.lean"
    file_path = (statlean_root / rel).resolve()
    file_path.parent.mkdir(parents=True, exist_ok=True)
    file_path.write_text(
        "import Mathlib.Init.Set\n\n"
        "theorem m5_l2 : 1 + 1 = 2 := sorry\n",
        encoding="utf-8",
    )

    backlog = tmp_path / "sorry_backlog.yaml"
    _write_backlog(backlog, [_v2_backlog_with_sorry(
        "m5l2.s1", file_rel=rel, line=3,
    )])

    try:
        result = subprocess.run(
            [
                "python3", str(SCRIPT),
                "--sandbox", str(sandbox),
                "--statlean-root", str(statlean_root),
                "--backlog-path", str(backlog),
                "--max-sorries", "1",
            ],
            capture_output=True, text=True, timeout=300,
        )
        assert result.returncode == 0, (
            f"script exit nonzero: {result.returncode}\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )
        # Backlog row should be DONE / proved
        item = _by_id(backlog, "m5l2.s1")
        assert item.get("state") == "DONE"
        assert item.get("done_reason") == "proved"
        # M5 §8 code review S2.5: events.jsonl must contain a
        # `sorry-proved` event with `closer: "auto_tactic"` — the
        # distinguisher that uniquely attributes M5 as the proof origin
        # (vs the prover loop's default `closer: "prover"`).
        events_file = sandbox / "events.jsonl"
        assert events_file.exists(), (
            "events.jsonl was never written; "
            "process_sorry_result.py emit failed"
        )
        sorry_proved_events = []
        for line in events_file.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            evt = json.loads(line)
            if evt.get("name") == "sorry-proved":
                sorry_proved_events.append(evt)
        assert sorry_proved_events, (
            f"no sorry-proved event in {events_file}; "
            f"contents:\n{events_file.read_text()}"
        )
        # Find the event for m5l2.s1 and assert closer attribution
        m5_events = [
            e for e in sorry_proved_events
            if (e.get("details") or {}).get("sorry_id") == "m5l2.s1"
        ]
        assert m5_events, (
            f"no sorry-proved event for sorry_id=m5l2.s1; "
            f"got: {sorry_proved_events}"
        )
        details = m5_events[0].get("details") or {}
        assert details.get("closer") == "auto_tactic", (
            f"expected closer='auto_tactic'; got {details.get('closer')!r} "
            f"in {details}"
        )
    finally:
        # Cleanup the fixture
        try:
            file_path.unlink()
        except FileNotFoundError:
            pass


# ── Sentinel ─────────────────────────────────────────────────────────


def test_module_present_marker() -> None:
    """Sentinel — guards against silent test-collection exclusion."""
    assert True

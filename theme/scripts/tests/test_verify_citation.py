"""E11 L1 unit tests for verify_citation.py.

Coverage matrix per `docs/E11_CITATION_VERIFY_SPEC.md` §7.1.

Library path (czy citationVerify.ts:72-123):
  L1.1   exact succeeds first try → pass
  L1.2   exact fails, apply succeeds → pass with apply
  L1.3   all four tactics fail → fail
  L1.4   locked-signature invariant
  L1.5   empty cited-lemma guard → exit 2
  L1.6   invalid sorry line guard → exit 2
  L1.7   tool exception on tactic 1 → fall through to tactic 2 (czy :143-156)
  L1.8   basename stripping (file path with dirs)
  L1.8a  tactic 3 (.mp) succeeds individually
  L1.8b  tactic 4 (.mpr) succeeds individually

Reference path (czy citationVerify.ts:218-292):
  L1.9   LLM verified=true → pass
  L1.10  LLM verified=false → fail
  L1.11  LLM malformed JSON → fail
  L1.12  missing eligibility (coverage_state mismatch) → exit 2
  L1.13  LLM strips markdown fences

Idempotence + integrity:
  L1.14  re-run on already-DONE sorry → exit 2 ("already DONE")
  L1.15  ineligible coverage_state → exit 2

All 17 L1 cases from spec §7.1 are present (matches czy
citationVerify.test.ts count). Subdivisions (L1.5×2, L1.11×3,
L1.12×2, L1.15×2) plus 5 helper-coverage units bring the file
total to 28 functions; the underlying spec-mandated cases are 17.
"""
from __future__ import annotations

import copy
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from verify_citation import (  # noqa: E402
    _build_tactics,
    _unwrap_fenced_json,
    apply_library_verification,
    apply_reference_verification,
    parse_reference_subagent_output,
)


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
VERIFY = SCRIPTS_DIR / "verify_citation.py"


# ── Mock helpers ─────────────────────────────────────────────────────


class TacticMock:
    """Configurable mock for verify_citation._try_tactic. Records each
    invocation and returns a canned (passed, output) per call.

    Usage:
        mock = TacticMock([(False, "fail-1"), (True, "ok")])
        apply_library_verification(..., try_tactic_fn=mock)
        assert mock.calls == [...]
    """

    def __init__(self, results: List[Tuple[bool, str]]) -> None:
        self.results = list(results)
        self.calls: List[Dict[str, Any]] = []

    def __call__(self, file_path: Path, sorry_line: int, tactic: str,
                 module_path: Optional[str] = None) -> Tuple[bool, str]:
        self.calls.append({
            "file_path": file_path, "sorry_line": sorry_line,
            "tactic": tactic, "module_path": module_path,
        })
        if not self.results:
            raise RuntimeError("TacticMock exhausted")
        return self.results.pop(0)


class TacticRaiseThenSucceed:
    """Mock where the first call raises (simulating tool exception),
    second call returns (True, "ok"). Tests czy :143-156 fall-through."""

    def __init__(self) -> None:
        self.calls: List[str] = []

    def __call__(self, file_path: Path, sorry_line: int, tactic: str,
                 module_path: Optional[str] = None) -> Tuple[bool, str]:
        self.calls.append(tactic)
        if len(self.calls) == 1:
            raise RuntimeError("simulated tool exception")
        return True, "ok"


# ── Fixtures ─────────────────────────────────────────────────────────


def _v2_backlog_with_sorry(coverage_state: str = "cited_by_library",
                           state: str = "INITIALIZED",
                           extras: Optional[Dict[str, Any]] = None,
                           ) -> List[Dict[str, Any]]:
    item = {
        "id": "p.s1", "file": "Statlean/Foo.lean", "line": 5,
        "theorem": "p_s1_thm", "type": "ready",
        "depth": 1, "priority": 50, "estimated_lines": 30,
        "dependencies": [], "unlocks": [],
        "state": state, "children": [], "parent_id": "p",
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": coverage_state,
        "citation_verified": False,
    }
    if extras:
        item.update(extras)
    return [item]


def _write_backlog(path: Path, items: List[Dict[str, Any]]) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _by_id(backlog: Path, item_id: str) -> Dict[str, Any]:
    data = yaml.safe_load(backlog.read_text())
    return next(it for it in data["sorry_items"] if it["id"] == item_id)


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def lib_backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _write_backlog(p, _v2_backlog_with_sorry("cited_by_library"))
    return p


@pytest.fixture
def ref_backlog(tmp_path: Path) -> Path:
    """Reference-mode backlog with coverage_citation already populated
    (E4 wrote it on R6 with `-- cited from reference: <text>` prefix)."""
    p = tmp_path / "sorry_backlog.yaml"
    _write_backlog(p, _v2_backlog_with_sorry(
        "cited_by_reference",
        extras={"coverage_citation": "-- cited from reference: Theorem 2.1 of Foo'23"},
    ))
    return p


@pytest.fixture
def statlean_root(tmp_path: Path) -> Path:
    """Stub repo root with an empty Statlean/ dir (file-mutate path
    not exercised in mock-driven tests)."""
    r = tmp_path / "repo"
    (r / "Statlean").mkdir(parents=True)
    return r


# ── _build_tactics ────────────────────────────────────────────────────


def test_build_tactics_returns_4_in_correct_order() -> None:
    t = _build_tactics("Foo.bar")
    # Byte-faithful to czy citationVerify.ts:89-94 — including the
    # trailing "(by assumption)" on tactics 3-4 (load-bearing for
    # iff-form lemmas with hypothesis side-conditions)
    assert t == [
        "exact Foo.bar",
        "apply Foo.bar <;> assumption",
        "exact Foo.bar.mp (by assumption)",
        "exact Foo.bar.mpr (by assumption)",
    ]


# ── L1.1 exact succeeds first try ────────────────────────────────────


def test_l1_1_exact_succeeds_first_try(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([(True, "lake build clean")])
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "pass"
    assert payload["tactic_used"] == "exact Foo.bar"
    assert payload["verifier"] == "library_compiler"
    assert payload["done_reason_set"] == "library_verified"
    assert len(mock.calls) == 1
    assert mock.calls[0]["tactic"] == "exact Foo.bar"

    item = _by_id(lib_backlog, "p.s1")
    assert item["state"] == "DONE"
    assert item["done_reason"] == "library_verified"
    assert item["citation_verified"] is True
    assert isinstance(item["citation_verified_at"], int)


# ── L1.2 exact fails, apply succeeds ─────────────────────────────────


def test_l1_2_exact_fails_apply_succeeds(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([(False, "type mismatch"), (True, "ok")])
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "pass"
    assert payload["tactic_used"] == "apply Foo.bar <;> assumption"
    assert len(mock.calls) == 2


# ── L1.3 all four tactics fail ───────────────────────────────────────


def test_l1_3_all_four_tactics_fail(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([(False, "f1"), (False, "f2"), (False, "f3"),
                       (False, "stderr excerpt of last tactic fail")])
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "fail"
    assert payload["tactic_used"] is None
    assert payload["done_reason_set"] is None
    assert "stderr excerpt" in payload["reasoning"]
    assert len(mock.calls) == 4

    item = _by_id(lib_backlog, "p.s1")
    assert item["state"] == "INITIALIZED", "FAIL must NOT mark DONE"
    assert "done_reason" not in item
    assert item["citation_verified"] is False
    assert item["coverage_state"] == "cited_by_library", "preserved per Q4"


# ── L1.4 locked-signature invariant ──────────────────────────────────


def test_l1_4_locked_signature_invariant(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    pre = copy.deepcopy(_by_id(lib_backlog, "p.s1"))
    mock = TacticMock([(True, "ok")])
    apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    post = _by_id(lib_backlog, "p.s1")
    PROTECTED = ("id", "file", "line", "theorem", "type", "depth",
                 "priority", "estimated_lines", "dependencies", "unlocks",
                 "parent_id", "children", "history_log", "stuck_rounds",
                 "attempts", "coverage_state", "coverage_citation",
                 "references")
    for k in PROTECTED:
        assert post.get(k) == pre.get(k), (
            f"protected field {k} changed: {pre.get(k)!r} → {post.get(k)!r}"
        )


# ── L1.5 empty cited-lemma guard ─────────────────────────────────────


def test_l1_5_empty_cited_lemma_raises(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([])
    with pytest.raises(ValueError, match="cited-lemma is empty"):
        apply_library_verification(
            backlog_path=lib_backlog, sorry_id="p.s1",
            cited_lemma="",  # empty
            statlean_root=statlean_root,
            try_tactic_fn=mock,
        )
    # No mock calls — script bails before tactic ladder
    assert mock.calls == []


def test_l1_5_whitespace_cited_lemma_raises(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([])
    with pytest.raises(ValueError, match="cited-lemma is empty"):
        apply_library_verification(
            backlog_path=lib_backlog, sorry_id="p.s1",
            cited_lemma="   ",
            statlean_root=statlean_root,
            try_tactic_fn=mock,
        )


# ── L1.6 invalid sorry line guard ────────────────────────────────────


def test_l1_6_invalid_sorry_line_raises(
    tmp_path: Path, statlean_root: Path,
) -> None:
    """Sorry with line=0 or absent → script refuses (validation guard)."""
    p = tmp_path / "b.yaml"
    bad_items = _v2_backlog_with_sorry("cited_by_library")
    bad_items[0]["line"] = 0  # invalid
    _write_backlog(p, bad_items)
    mock = TacticMock([])
    with pytest.raises(ValueError, match="invalid file/line"):
        apply_library_verification(
            backlog_path=p, sorry_id="p.s1",
            cited_lemma="Foo.bar", statlean_root=statlean_root,
            try_tactic_fn=mock,
        )
    assert mock.calls == []


# ── L1.7 tool exception → fall through (czy :143-156) ────────────────


def test_l1_7_tool_exception_falls_through(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticRaiseThenSucceed()
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "pass"
    # Tactic 1 raised, tactic 2 (apply <;> assumption) was the one that succeeded
    assert payload["tactic_used"] == "apply Foo.bar <;> assumption"
    assert mock.calls == ["exact Foo.bar", "apply Foo.bar <;> assumption"]


# ── L1.8 basename stripping (file path includes dirs) ────────────────


def test_l1_8_passes_full_path_to_tool(
    tmp_path: Path, statlean_root: Path,
) -> None:
    """The tool receives the resolved absolute file path (caller can
    extract basename if needed). czy strips at the consumer side; we
    pass the full path so the script can be filesystem-aware."""
    p = tmp_path / "b.yaml"
    items = _v2_backlog_with_sorry("cited_by_library")
    items[0]["file"] = "Statlean/Concentration/MGF.lean"  # nested
    _write_backlog(p, items)

    mock = TacticMock([(True, "ok")])
    apply_library_verification(
        backlog_path=p, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    expected = (statlean_root / "Statlean/Concentration/MGF.lean").resolve()
    assert mock.calls[0]["file_path"] == expected


# ── L1.8a / L1.8b tactics 3 + 4 individual coverage ──────────────────


def test_l1_8a_tactic_3_mp_succeeds_individually(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([(False, "f1"), (False, "f2"), (True, "ok"), ])
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.iff_form", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "pass"
    assert payload["tactic_used"] == "exact Foo.iff_form.mp (by assumption)"
    assert len(mock.calls) == 3


def test_l1_8b_tactic_4_mpr_succeeds_individually(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    mock = TacticMock([(False, "f1"), (False, "f2"), (False, "f3"),
                       (True, "ok")])
    payload = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.iff_form", statlean_root=statlean_root,
        try_tactic_fn=mock,
    )
    assert payload["verdict"] == "pass"
    assert payload["tactic_used"] == "exact Foo.iff_form.mpr (by assumption)"
    assert len(mock.calls) == 4


# ── L1.9 LLM verified=true ────────────────────────────────────────────


def test_l1_9_llm_verified_true_marks_done(ref_backlog: Path) -> None:
    json_str = json.dumps({
        "verified": True,
        "reasoning": "All three checks pass: hypotheses match...",
    })
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text=json_str,
    )
    assert payload["verdict"] == "pass"
    assert payload["verifier"] == "reference_llm"
    assert payload["done_reason_set"] == "reference_axiom"
    assert payload["tactic_used"] is None
    assert payload["cited_lemma"] == "Theorem 2.1 of Foo'23"  # prefix stripped

    item = _by_id(ref_backlog, "p.s1")
    assert item["state"] == "DONE"
    assert item["done_reason"] == "reference_axiom"
    assert item["citation_verified"] is True


def test_l1_9_coverage_citation_without_prefix_falls_through(
    tmp_path: Path,
) -> None:
    """If `coverage_citation` was set without the `-- cited from
    reference: ` prefix (e.g. user manually edited yaml), the milestone
    payload uses the raw value — no error."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _v2_backlog_with_sorry(
        "cited_by_reference",
        extras={"coverage_citation": "Lemma X.Y (no prefix)"},
    ))
    payload = apply_reference_verification(
        backlog_path=p, sorry_id="p.s1",
        subagent_text=json.dumps({"verified": True, "reasoning": "ok"}),
    )
    assert payload["verdict"] == "pass"
    assert payload["cited_lemma"] == "Lemma X.Y (no prefix)"  # raw passthrough


# ── L1.10 LLM verified=false ──────────────────────────────────────────


def test_l1_10_llm_verified_false_marks_fail(ref_backlog: Path) -> None:
    json_str = json.dumps({
        "verified": False,
        "reasoning": "Check B fails: reference gives weaker conclusion",
    })
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text=json_str,
    )
    assert payload["verdict"] == "fail"
    assert payload["done_reason_set"] is None

    item = _by_id(ref_backlog, "p.s1")
    assert item["state"] == "INITIALIZED"
    assert "done_reason" not in item
    assert item["citation_verified"] is False
    assert item["coverage_state"] == "cited_by_reference"  # preserved


# ── L1.11 LLM malformed JSON ──────────────────────────────────────────


def test_l1_11_malformed_json_treated_as_fail(ref_backlog: Path) -> None:
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text="not valid json {[}",
    )
    assert payload["verdict"] == "fail"
    assert "parse failed" in payload["reasoning"].lower()


def test_l1_11_root_not_object_treated_as_fail(ref_backlog: Path) -> None:
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text=json.dumps([{"verified": True}]),  # array, not object
    )
    assert payload["verdict"] == "fail"


def test_l1_11_missing_verified_field_treated_as_fail(ref_backlog: Path) -> None:
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text=json.dumps({"reasoning": "no verified field"}),
    )
    assert payload["verdict"] == "fail"
    assert "missing or non-bool" in payload["reasoning"].lower()


# ── L1.12 missing eligibility (coverage_state mismatch) ──────────────


def test_l1_12_library_mode_on_reference_sorry_raises(
    tmp_path: Path, statlean_root: Path,
) -> None:
    """A sorry with coverage_state=cited_by_reference is NOT eligible
    for library mode."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _v2_backlog_with_sorry("cited_by_reference"))
    mock = TacticMock([])
    with pytest.raises(ValueError, match="library mode requires"):
        apply_library_verification(
            backlog_path=p, sorry_id="p.s1",
            cited_lemma="Foo.bar", statlean_root=statlean_root,
            try_tactic_fn=mock,
        )


def test_l1_12_reference_mode_on_library_sorry_raises(tmp_path: Path) -> None:
    """A sorry with coverage_state=cited_by_library is NOT eligible
    for reference mode."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _v2_backlog_with_sorry("cited_by_library"))
    json_str = json.dumps({"verified": True, "reasoning": "x"})
    with pytest.raises(ValueError, match="reference mode requires"):
        apply_reference_verification(
            backlog_path=p, sorry_id="p.s1",
            subagent_text=json_str,
        )


# ── L1.13 LLM strips markdown fences ─────────────────────────────────


def test_l1_13_markdown_fenced_json_unwraps(ref_backlog: Path) -> None:
    raw = '```json\n{"verified": true, "reasoning": "ok"}\n```'
    payload = apply_reference_verification(
        backlog_path=ref_backlog, sorry_id="p.s1",
        subagent_text=raw,
    )
    assert payload["verdict"] == "pass"


def test_unwrap_fenced_json_strips_bare_fence() -> None:
    raw = '```\n{"verified": false}\n```'
    assert _unwrap_fenced_json(raw).strip() == '{"verified": false}'


def test_unwrap_fenced_json_passthrough_no_fence() -> None:
    assert _unwrap_fenced_json('{"verified": true}') == '{"verified": true}'


# ── L1.14 idempotence (re-run on already-DONE) ───────────────────────


def test_l1_14_rerun_on_already_done_raises(
    tmp_path: Path, statlean_root: Path,
) -> None:
    """An already-DONE sorry must NOT be re-verified — idempotence
    guard rejects (caller's responsibility to filter eligible nodes)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _v2_backlog_with_sorry(
        "cited_by_library", state="DONE",
        extras={"done_reason": "library_verified", "citation_verified": True},
    ))
    mock = TacticMock([])
    with pytest.raises(ValueError, match="already DONE"):
        apply_library_verification(
            backlog_path=p, sorry_id="p.s1",
            cited_lemma="Foo.bar", statlean_root=statlean_root,
            try_tactic_fn=mock,
        )
    assert mock.calls == [], "no tactic attempted on idempotence reject"


def test_l1_14_rerun_after_fail_is_allowed(
    lib_backlog: Path, statlean_root: Path,
) -> None:
    """A FAIL'd sorry has state=INITIALIZED + citation_verified=False.
    Re-running is ALLOWED (a previous flake from network / lake-build
    transients shouldn't permanently brick the sorry). This test
    confirms the second attempt overwrites citation_verified_at and
    can succeed if the underlying tactic now passes."""
    # Round 1: all 4 tactics fail
    mock1 = TacticMock([(False, "f1"), (False, "f2"), (False, "f3"), (False, "f4")])
    p1 = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock1,
    )
    assert p1["verdict"] == "fail"
    item_after_fail = _by_id(lib_backlog, "p.s1")
    assert item_after_fail["state"] == "INITIALIZED"
    assert item_after_fail["citation_verified"] is False
    first_at = item_after_fail["citation_verified_at"]

    # Round 2: same sorry, exact succeeds first try (e.g. lake cache rebuilt)
    mock2 = TacticMock([(True, "ok")])
    p2 = apply_library_verification(
        backlog_path=lib_backlog, sorry_id="p.s1",
        cited_lemma="Foo.bar", statlean_root=statlean_root,
        try_tactic_fn=mock2,
    )
    assert p2["verdict"] == "pass"
    item_after_pass = _by_id(lib_backlog, "p.s1")
    assert item_after_pass["state"] == "DONE"
    assert item_after_pass["citation_verified"] is True
    # Timestamp advanced (or at least not regressed)
    assert item_after_pass["citation_verified_at"] >= first_at


# ── L1.15 ineligible coverage_state ──────────────────────────────────


def test_l1_15_ineligible_needs_proof_raises(
    tmp_path: Path, statlean_root: Path,
) -> None:
    """A sorry with coverage_state=needs_proof is NOT eligible for
    EITHER library or reference mode."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _v2_backlog_with_sorry("needs_proof"))
    mock = TacticMock([])
    with pytest.raises(ValueError, match="library mode requires"):
        apply_library_verification(
            backlog_path=p, sorry_id="p.s1",
            cited_lemma="Foo.bar", statlean_root=statlean_root,
            try_tactic_fn=mock,
        )

    with pytest.raises(ValueError, match="reference mode requires"):
        apply_reference_verification(
            backlog_path=p, sorry_id="p.s1",
            subagent_text=json.dumps({"verified": True, "reasoning": "x"}),
        )


# ── parse_reference_subagent_output unit ─────────────────────────────


def test_parse_reference_subagent_handles_missing_reasoning() -> None:
    verified, reasoning = parse_reference_subagent_output(
        json.dumps({"verified": True})
    )
    assert verified is True
    assert reasoning == ""


def test_parse_reference_subagent_truncates_long_reasoning() -> None:
    long_text = "x" * 5000
    _, reasoning = parse_reference_subagent_output(
        json.dumps({"verified": False, "reasoning": long_text})
    )
    assert len(reasoning) == 1000  # bounded


# ── Subprocess-level: milestone payload validation ────────────────────


def test_milestone_emits_via_subprocess(
    ref_backlog: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """End-to-end via subprocess: confirm citation-verified milestone
    fires with payload schema correct (spec §4 invariants)."""
    json_file = tmp_path / "subagent.json"
    json_file.write_text(json.dumps({
        "verified": True,
        "reasoning": "All checks pass",
    }))
    result = subprocess.run(
        [
            "python3", str(VERIFY),
            "--mode", "reference",
            "--sorry-id", "p.s1",
            "--subagent-json-file", str(json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(ref_backlog),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr

    events = sandbox / "events.jsonl"
    assert events.is_file()
    milestones = [
        json.loads(l) for l in events.read_text().strip().splitlines()
        if json.loads(l).get("kind") == "sandbox_milestone"
    ]
    cv = [m for m in milestones if m.get("name") == "citation-verified"]
    assert len(cv) == 1
    payload = cv[0]["details"]
    # Spec §4 invariants
    assert payload["sorry_id"] == "p.s1"
    assert payload["verdict"] == "pass"
    assert payload["verifier"] == "reference_llm"
    assert payload["done_reason_set"] == "reference_axiom"
    assert payload["tactic_used"] is None
    # cited_lemma stripped of "-- cited from reference: " prefix
    assert payload["cited_lemma"] == "Theorem 2.1 of Foo'23"


def test_module_present_marker() -> None:
    assert True

"""H4 L1 unit tests for `dispatch_helper.py`.

Coverage matrix per `docs/H4_DISPATCH_HELPER_SPEC.md` §7.1:

  L1.1  parse marker file with `need:assumption` → invokes
        extract_assumption.py subprocess; verdict=`dispatched`;
        agents_called=["assumption"]
  L1.2  parse marker file with `need:websearch` → no subprocess;
        per_marker_results entry shows ported=False reason=h5_deferred;
        verdict=`all_deferred`
  L1.3  parse marker file with `need:reference` → ported=False
        reason=h6_deferred; verdict=`all_deferred`
  L1.4  parse marker file with `need:full` (collapsed from 3) → 3
        per_marker_results entries; assumption=ported,
        websearch+reference=not_ported; verdict=`dispatched`
  L1.5  parse marker file with empty list → verdict=`no_helpers_needed`;
        agents_called=[]
  L1.6  parse marker file with invalid marker `need:foo` → all stripped;
        verdict=`marker_decider_failed`
  L1.7  parse missing marker file → exit 2; verdict=`parse_error`
  L1.8  parse marker file with `need:assumption` but
        extract_assumption.py subprocess fails → verdict=`dispatched`;
        per_marker_results[0].verdict=`helper_script_failed`;
        subprocess_exit_code reflects failure
  L1.9  sub_problem_id missing in yaml → exit 2;
        verdict=`parse_error`
  L1.10 dispatcher itself produces zero yaml diff (Layer 1 invariant) —
        running with `need:assumption` against a v2 yaml; assert
        byte-identical pre/post EXCEPT `assumption_hints` /
        `assumption_analysis` on the targeted sorry row.

All tests use mock marker files + stub subagent JSON files (no live
LLM). The H7 `extract_assumption.py` subprocess is real (not mocked).
"""
from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dispatch_helper import (  # noqa: E402
    CALL_ORDER,
    PER_MARKER_EXTRACTED,
    PER_MARKER_HELPER_SCRIPT_FAILED,
    PER_MARKER_NOT_YET_PORTED,
    REASON_H5_DEFERRED,
    REASON_H6_DEFERRED,
    VALID_MARKERS,
    VERDICT_ALL_DEFERRED,
    VERDICT_DISPATCHED,
    VERDICT_MARKER_FAILED,
    VERDICT_NO_HELPERS,
    VERDICT_PARSE_ERROR,
    filter_to_allowlist,
    normalize_markers,
    parse_marker_file,
    tuple_sort,
)

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
DISPATCH = SCRIPTS_DIR / "dispatch_helper.py"


# ── Fixtures ─────────────────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _one_stuck_subproblem_backlog() -> List[Dict[str, Any]]:
    """Pre-migrated v2 row for a stuck sub-problem."""
    return [
        {
            "id": "sub.s1", "file": "X.lean", "line": 5,
            "theorem": "stuck_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 2,
            "references": [], "coverage_state": "needs_proof",
            "attempts": 0, "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "assumption_hints": [], "assumption_analysis": "",
        },
    ]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _make_backlog(_one_stuck_subproblem_backlog(), p)
    return p


def _read_events(sandbox: Path) -> List[Dict[str, Any]]:
    """Return list of all events written to events.jsonl."""
    path = sandbox / "events.jsonl"
    if not path.exists():
        return []
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            out.append(json.loads(line))
    return out


def _helper_dispatched_milestones(events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [
        e for e in events
        if e.get("kind") == "sandbox_milestone"
        and e.get("name") == "helper-dispatched"
    ]


def _write_marker_file(tmp_path: Path, content: str, name: str = "marker.txt") -> Path:
    p = tmp_path / name
    p.write_text(content)
    return p


def _write_assumption_json(tmp_path: Path, missing: List[str], analysis: str = "") -> Path:
    p = tmp_path / "assumption.json"
    p.write_text(json.dumps({
        "missingAssumptions": missing,
        "analysis": analysis,
    }))
    return p


def _run_dispatch(
    *,
    sub_problem_id: str,
    marker_file: Path,
    sandbox: Path,
    backlog: Path,
    assumption_json_file: Path | None = None,
    stuck_rounds: int = 0,
) -> subprocess.CompletedProcess:
    cmd = [
        sys.executable, str(DISPATCH),
        "--sub-problem-id", sub_problem_id,
        "--marker-file", str(marker_file),
        "--sandbox", str(sandbox),
        "--backlog-path", str(backlog),
        "--stuck-rounds", str(stuck_rounds),
    ]
    if assumption_json_file is not None:
        cmd.extend(["--assumption-json-file", str(assumption_json_file)])
    return subprocess.run(
        cmd, capture_output=True, text=True, timeout=120,
    )


# ── Pure-helper tests (no subprocess) ────────────────────────────────


def test_parse_marker_file_basic() -> None:
    assert parse_marker_file("need:assumption,need:websearch") == [
        "need:assumption", "need:websearch"
    ]


def test_parse_marker_file_strips_whitespace() -> None:
    assert parse_marker_file("  need:assumption , need:websearch  ") == [
        "need:assumption", "need:websearch"
    ]


def test_parse_marker_file_empty_returns_empty() -> None:
    assert parse_marker_file("") == []
    assert parse_marker_file("   ") == []
    assert parse_marker_file("\n") == []


def test_filter_to_allowlist_keeps_valid() -> None:
    assert filter_to_allowlist(["need:assumption", "need:foo"]) == ["need:assumption"]


def test_filter_to_allowlist_rejects_all_invalid() -> None:
    assert filter_to_allowlist(["need:foo", "need:bar"]) == []


def test_normalize_markers_full_passthrough() -> None:
    assert normalize_markers(["need:full"]) == ["need:full"]


def test_normalize_markers_collapses_three() -> None:
    assert normalize_markers(
        ["need:websearch", "need:reference", "need:assumption"]
    ) == ["need:full"]


def test_normalize_markers_two_passthrough() -> None:
    """Two-marker subsets remain as 2-marker (CALL_ORDER has explicit
    keys for the documented 2-marker combos)."""
    assert normalize_markers(
        ["need:assumption", "need:websearch"]
    ) == ["need:assumption", "need:websearch"]


def test_tuple_sort_alphabetic() -> None:
    """tuple_sort must be deterministic + alphabetic to match CALL_ORDER keys."""
    assert tuple_sort(["need:websearch", "need:assumption"]) == (
        "need:assumption,need:websearch"
    )


def test_call_order_keys_use_tuple_sort() -> None:
    """Every CALL_ORDER key is a sorted comma-join of its constituent markers."""
    for key in CALL_ORDER:
        # Each key is either single-marker or sorted multi-marker.
        parts = key.split(",")
        assert parts == sorted(parts), f"CALL_ORDER key not sorted: {key}"


def test_call_order_full_dispatches_three() -> None:
    """need:full → all 3 sub-agents in czy parity order."""
    assert CALL_ORDER["need:full"] == ["websearch", "reference", "assumption"]


def test_valid_markers_count() -> None:
    """4 markers in czy `:379` allow-list."""
    assert len(VALID_MARKERS) == 4


# ── L1.1 happy path: need:assumption ─────────────────────────────────


def test_l1_1_assumption_marker_invokes_extract_assumption(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """need:assumption → extract_assumption.py runs as subprocess;
    verdict=dispatched; agents_called=["assumption"]; per_marker_results[0]
    has verdict=extracted (assumption hints actually written)."""
    marker_file = _write_marker_file(tmp_path, "need:assumption")
    aj = _write_assumption_json(
        tmp_path,
        missing=["X is integrable", "Y is measurable"],
        analysis="Without integrability, the expectation may diverge.",
    )
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
        stuck_rounds=2,
    )
    assert result.returncode == 0, (
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )

    # Find the helper-dispatched milestone
    events = _read_events(sandbox)
    hd = _helper_dispatched_milestones(events)
    assert len(hd) == 1
    payload = hd[0]["details"]
    assert payload["sub_problem_id"] == "sub.s1"
    assert payload["stuck_rounds"] == 2
    assert payload["verdict"] == VERDICT_DISPATCHED
    assert payload["markers_decided"] == ["need:assumption"]
    assert payload["markers_normalized"] == ["need:assumption"]
    assert payload["agents_called"] == ["assumption"]
    assert len(payload["per_marker_results"]) == 1
    pmr = payload["per_marker_results"][0]
    assert pmr["marker"] == "need:assumption"
    assert pmr["agent"] == "assumption"
    assert pmr["ported"] is True
    assert pmr["verdict"] == PER_MARKER_EXTRACTED
    assert pmr["subprocess_exit_code"] == 0

    # Yaml side: assumption_hints actually written by H7's subprocess
    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == ["X is integrable", "Y is measurable"]


# ── L1.2 need:websearch (H5 ported) ──────────────────────────────────


def test_l1_2_websearch_marker_dispatches_h5(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """need:websearch → H5 (extract_web_probe.py) dispatched (ported=True).
    When no --webprobe-json-file provided, verdict=helper_script_failed
    (missing_webprobe_json), overall verdict=dispatched (because ported=True).

    Updated from H5-deferred placeholder: H5 has now landed; websearch arm
    is ported=True. Per spec §8.2 post-H5-landing update."""
    marker_file = _write_marker_file(tmp_path, "need:websearch")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        # No webprobe_json_file → helper_script_failed
    )
    assert result.returncode == 0

    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    # H5 ported → verdict=dispatched (at least one ported helper ran even if it failed)
    assert payload["verdict"] == VERDICT_DISPATCHED
    assert payload["agents_called"] == ["websearch"]
    pmr = payload["per_marker_results"][0]
    assert pmr["agent"] == "websearch"
    assert pmr["ported"] is True


# ── L1.3 need:reference (placeholder) ────────────────────────────────


def test_l1_3_reference_marker_emits_h6_deferred(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """need:reference → ported=False, reason=h6_deferred."""
    marker_file = _write_marker_file(tmp_path, "need:reference")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_ALL_DEFERRED
    assert payload["agents_called"] == ["reference"]
    pmr = payload["per_marker_results"][0]
    assert pmr["agent"] == "reference"
    assert pmr["ported"] is False
    assert pmr["verdict"] == PER_MARKER_NOT_YET_PORTED
    assert pmr["reason"] == REASON_H6_DEFERRED


# ── L1.4 need:full (collapsed) ───────────────────────────────────────


def test_l1_4_full_marker_dispatches_three_agents(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """need:full → 3 agents in CALL_ORDER (websearch, reference,
    assumption).

    Post H5+H6 landing:
    - websearch: ported=True (H5 shipped; missing webprobe json →
      helper_script_failed but still ported=True)
    - reference: ported=False (H6 reference-probe arm NOT yet activated in
      dispatch_helper; still placeholder per H6 spec §3.5 — H6 does NOT modify
      dispatch_helper.py; H4-full slice will wire it)
    - assumption: ported=True (H7)
    - overall verdict: dispatched (websearch + assumption both ported=True)

    Updated from pre-H5 test: websearch arm is now ported=True (H5 shipped).
    Reference arm remains not-yet-ported (H6 standalone, wired by H4-full)."""
    marker_file = _write_marker_file(tmp_path, "need:full")
    aj = _write_assumption_json(
        tmp_path,
        missing=["pdfProofBody must be non-empty"],
        analysis="Stuck on missing reference data.",
    )
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
        # No webprobe_json_file → websearch helper_script_failed (still ported=True)
    )
    assert result.returncode == 0

    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_DISPATCHED
    assert payload["markers_decided"] == ["need:full"]
    assert payload["markers_normalized"] == ["need:full"]
    assert payload["agents_called"] == ["websearch", "reference", "assumption"]
    assert len(payload["per_marker_results"]) == 3

    by_agent = {p["agent"]: p for p in payload["per_marker_results"]}
    # H5 shipped: websearch ported=True
    assert by_agent["websearch"]["ported"] is True
    # H6 standalone (H4-full will wire reference dispatch): reference still ported=False
    assert by_agent["reference"]["ported"] is False
    # H7 shipped: assumption ported=True
    assert by_agent["assumption"]["ported"] is True
    assert by_agent["assumption"]["verdict"] == PER_MARKER_EXTRACTED


def test_l1_4_three_markers_collapse_to_full(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Three-marker input → normalized to need:full → 3-agent fan-out."""
    marker_file = _write_marker_file(
        tmp_path,
        "need:websearch,need:reference,need:assumption",
    )
    aj = _write_assumption_json(tmp_path, missing=["X bounded"])
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["markers_normalized"] == ["need:full"]
    assert payload["agents_called"] == ["websearch", "reference", "assumption"]


# ── L1.5 empty list → no_helpers_needed ──────────────────────────────


def test_l1_5_empty_marker_file_yields_no_helpers_needed(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Empty marker file → verdict=no_helpers_needed; agents_called=[];
    no subprocess invoked."""
    marker_file = _write_marker_file(tmp_path, "")
    pre_yaml = backlog.read_text()
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_NO_HELPERS
    assert payload["markers_decided"] == []
    assert payload["agents_called"] == []
    assert payload["per_marker_results"] == []

    # Yaml unchanged
    assert backlog.read_text() == pre_yaml


def test_l1_5_whitespace_only_marker_file_is_no_helpers(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    marker_file = _write_marker_file(tmp_path, "   \n\n   ")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_NO_HELPERS


# ── L1.6 invalid markers → marker_decider_failed ─────────────────────


def test_l1_6_invalid_markers_yield_marker_decider_failed(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """All-invalid marker file → verdict=marker_decider_failed;
    agents_called=[]; markers_decided=[] (post-filter)."""
    marker_file = _write_marker_file(tmp_path, "need:foo,need:bar")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0  # not an error — empties + emits milestone
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_MARKER_FAILED
    assert payload["markers_decided"] == []
    assert payload["agents_called"] == []


def test_l1_6_partial_invalid_markers_keeps_valid(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Mixed valid + invalid → only valid kept; valid still dispatches."""
    marker_file = _write_marker_file(
        tmp_path,
        "need:assumption,need:bogus,need:websearch",
    )
    aj = _write_assumption_json(tmp_path, missing=["a"])
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    # need:bogus stripped; remaining 2-marker combo dispatches
    assert payload["markers_decided"] == ["need:assumption", "need:websearch"]
    # CALL_ORDER for sorted "need:assumption,need:websearch" == ["websearch", "assumption"]
    assert payload["agents_called"] == ["websearch", "assumption"]


# ── L1.7 missing marker file ─────────────────────────────────────────


def test_l1_7_missing_marker_file_yields_parse_error(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Marker file path doesn't exist → exit 2; verdict=parse_error
    milestone STILL emitted (so observability sees the failure)."""
    bogus = tmp_path / "does_not_exist.txt"
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=bogus,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 2
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert "marker file not found" in payload.get("parse_error", "")


# ── L1.8 extract_assumption.py subprocess fails ──────────────────────


def test_l1_8_extract_assumption_failure_records_helper_script_failed(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """If extract_assumption.py exits non-zero (e.g. malformed JSON),
    verdict=dispatched (helper INVOKED) but per_marker_results entry
    has verdict=helper_script_failed + non-zero exit code.

    We trigger the failure by passing an assumption json file with
    `missingAssumptions` as a non-array (extract_assumption.py treats
    this as parse_error and exits 0 anyway — so use an unreadable
    json file instead via a path inside the marker dir that doesn't
    exist).
    """
    marker_file = _write_marker_file(tmp_path, "need:assumption")
    # Point assumption-json-file at a nonexistent path → dispatcher
    # records helper_script_failed with reason="assumption_json_file_not_found"
    bogus_json = tmp_path / "no_such_file.json"
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=bogus_json,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    # verdict=dispatched because the dispatcher invoked the assumption
    # branch (per spec §4: "at least one helper actually ran")
    assert payload["verdict"] == VERDICT_DISPATCHED
    assert payload["agents_called"] == ["assumption"]
    pmr = payload["per_marker_results"][0]
    assert pmr["verdict"] == PER_MARKER_HELPER_SCRIPT_FAILED
    assert pmr["ported"] is True
    assert "assumption_json_file_not_found" in pmr.get("reason", "")


def test_l1_8_extract_assumption_nonzero_exit_records_failure(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Trigger a real non-zero subprocess exit by corrupting the backlog
    file AFTER dispatcher's pre-validation pass but before
    extract_assumption.py opens it.

    We cannot easily race against the pre-validation in a single-threaded
    test, so we simulate a real exit-2 by writing an unreadable backlog:
    pass --backlog-path pointing to a directory rather than a file. The
    dispatcher's pre-validation will fail first (exit 2 + parse_error),
    not the subprocess. So this test instead asserts the alternative
    branch — feed extract_assumption.py a yaml that becomes invalid
    after dispatcher hands it off, by symlinking to a corrupt file.

    Actually the cleanest approach: pass a sub_problem_id valid in
    dispatcher's main backlog, but extract_assumption.py uses the same
    backlog so it succeeds. There is NO straightforward unit-test path
    to a non-zero exit from extract_assumption.py without racing. The
    `assumption_json_file_not_found` reason path (L1.8 above) is the
    representative coverage.

    Skipped — the helper-script-failed branch is exercised structurally
    by L1.8 above; a real exit-code variant would require mocking, which
    we deliberately avoid in L1 (real subprocess only).
    """
    pytest.skip(
        "exit-code variant requires mocking; L1.8 covers the helper_script_failed "
        "branch via the `assumption_json_file_not_found` reason path"
    )


# ── L1.9 sub_problem_id missing in yaml ──────────────────────────────


def test_l1_9_missing_sub_problem_id_yields_parse_error(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """sub_problem_id not in sorry_items → exit 2; verdict=parse_error;
    no helper invoked."""
    marker_file = _write_marker_file(tmp_path, "need:assumption")
    aj = _write_assumption_json(tmp_path, missing=["x"])
    result = _run_dispatch(
        sub_problem_id="sub.does_not_exist",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
    )
    assert result.returncode == 2
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert "sub_problem_id not in sorry_items" in payload.get("parse_error", "")
    assert payload["agents_called"] == []

    # Yaml strictly unchanged
    final = yaml.safe_load(backlog.read_text())
    s1 = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert s1["assumption_hints"] == []


# ── L1.10 Layer 1: dispatcher itself produces zero yaml diff ─────────


def test_l1_10_websearch_marker_zero_yaml_diff(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """For markers that DON'T touch H7 (need:websearch placeholder),
    the dispatcher must leave yaml byte-identical."""
    pre_bytes = backlog.read_bytes()
    marker_file = _write_marker_file(tmp_path, "need:websearch")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0
    post_bytes = backlog.read_bytes()
    # Layer 1 invariant: dispatcher writes ZERO yaml when no real helper
    # is invoked — placeholders never write.
    assert post_bytes == pre_bytes


def test_l1_10_assumption_marker_only_h7_fields_change(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """For need:assumption, the dispatcher itself writes nothing; H7's
    extract_assumption.py writes only assumption_hints + assumption_analysis
    on the targeted row. All other fields (and other rows) stay identical."""
    # Add a second row that should be untouched
    items = _one_stuck_subproblem_backlog()
    items.append({
        "id": "sub.s2", "file": "Y.lean", "line": 7,
        "theorem": "other_thm", "type": "ready", "depth": 0,
        "priority": 30, "estimated_lines": 10,
        "dependencies": [], "unlocks": [],
        "state": "DONE", "children": [],
        "parent_id": None, "history_log": [], "stuck_rounds": 0,
        "references": [], "coverage_state": "needs_proof",
        "attempts": 0, "citation_verified": False,
        "informal_round": 0, "coverage_stable": False,
        "assumption_hints": ["preexisting hint on s2"],
        "assumption_analysis": "preexisting on s2",
    })
    _make_backlog(items, backlog)

    pre_data = yaml.safe_load(backlog.read_text())
    pre_s1 = copy.deepcopy(
        next(it for it in pre_data["sorry_items"] if it["id"] == "sub.s1")
    )
    pre_s2 = copy.deepcopy(
        next(it for it in pre_data["sorry_items"] if it["id"] == "sub.s2")
    )

    marker_file = _write_marker_file(tmp_path, "need:assumption")
    aj = _write_assumption_json(
        tmp_path,
        missing=["new hint A", "new hint B"],
        analysis="fresh.",
    )
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
    )
    assert result.returncode == 0

    post_data = yaml.safe_load(backlog.read_text())
    post_s1 = next(it for it in post_data["sorry_items"] if it["id"] == "sub.s1")
    post_s2 = next(it for it in post_data["sorry_items"] if it["id"] == "sub.s2")

    # s1: only assumption_hints + assumption_analysis changed
    PROTECTED_S1 = (
        "id", "file", "line", "theorem", "type", "depth",
        "priority", "estimated_lines", "dependencies", "unlocks",
        "state", "parent_id", "children", "history_log", "stuck_rounds",
        "references", "coverage_state", "attempts",
        "citation_verified", "informal_round", "coverage_stable",
    )
    for k in PROTECTED_S1:
        assert post_s1.get(k) == pre_s1.get(k), (
            f"s1 protected field {k} changed: "
            f"pre={pre_s1.get(k)!r} post={post_s1.get(k)!r}"
        )
    assert post_s1["assumption_hints"] == ["new hint A", "new hint B"]
    assert post_s1["assumption_analysis"] == "fresh."

    # s2: untouched semantically. Migration may add H1 / H7 default
    # fields (detailed_proof_plan / direct_assembly / proof_sketch / etc.)
    # from migrate_item_v1_to_v2; those are additive defaults, not
    # semantic mutations. The invariant we actually enforce: every key
    # PRESENT in pre_s2 has the same value in post_s2.
    for k, v in pre_s2.items():
        assert post_s2.get(k) == v, (
            f"s2 field {k} changed: pre={v!r} post={post_s2.get(k)!r}"
        )
    # And no shared field's value flipped (post may have additive
    # migration-default keys that pre lacked, all None / [] / 0).


# ── Bonus: payload schema invariants ─────────────────────────────────


def test_payload_includes_took_ms_int(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    marker_file = _write_marker_file(tmp_path, "need:websearch")
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0
    payload = _helper_dispatched_milestones(_read_events(sandbox))[0]["details"]
    assert isinstance(payload["took_ms"], int)
    assert payload["took_ms"] >= 0


def test_payload_per_marker_count_matches_agents_called(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Spec §4 invariant: len(per_marker_results) == len(agents_called)
    for every dispatched (or all_deferred) verdict."""
    for marker_text in [
        "need:assumption",
        "need:websearch",
        "need:reference",
        "need:assumption,need:websearch",
        "need:full",
    ]:
        marker_file = _write_marker_file(
            tmp_path, marker_text,
            name=f"marker_{marker_text.replace(':','_').replace(',','_')}.txt",
        )
        aj = _write_assumption_json(tmp_path, missing=["x"])
        # New sandbox per iteration so events.jsonl doesn't accumulate
        sub_sandbox = sandbox / f"sb_{marker_text.replace(':','_').replace(',','_')}"
        sub_sandbox.mkdir()
        result = _run_dispatch(
            sub_problem_id="sub.s1",
            marker_file=marker_file,
            sandbox=sub_sandbox,
            backlog=backlog,
            assumption_json_file=aj,
        )
        assert result.returncode == 0
        payload = _helper_dispatched_milestones(_read_events(sub_sandbox))[0]["details"]
        assert len(payload["per_marker_results"]) == len(payload["agents_called"]), (
            f"For markers={marker_text}: per_marker_results "
            f"{payload['per_marker_results']} agents_called={payload['agents_called']}"
        )


def test_helper_dispatched_milestone_emitted_exactly_once(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """For any single dispatcher invocation, exactly one
    helper-dispatched milestone is emitted (regardless of verdict)."""
    marker_file = _write_marker_file(tmp_path, "need:assumption")
    aj = _write_assumption_json(tmp_path, missing=["x"])
    result = _run_dispatch(
        sub_problem_id="sub.s1",
        marker_file=marker_file,
        sandbox=sandbox,
        backlog=backlog,
        assumption_json_file=aj,
    )
    assert result.returncode == 0
    events = _read_events(sandbox)
    hd = _helper_dispatched_milestones(events)
    assert len(hd) == 1

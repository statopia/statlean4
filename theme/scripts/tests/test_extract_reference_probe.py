"""H6 L1 unit tests for extract_reference_probe.py.

Coverage matrix per `docs/H6_REFERENCE_PROBE_SPEC.md` §8.1:
  L1.1  happy path: matchedPassage + analysis + suggestion all non-empty →
        referenceprobe_findings[0] matches fields; verdict=probed;
        matched_passage_len > 0; milestone emitted
  L1.2  all fields empty strings → verdict=probed_no_content;
        assembledContext == fallback "Reference probe found no content…";
        findings list has 1 entry
  L1.3  malformed JSON → exit 2; verdict=parse_error; yaml unchanged;
        referenceprobe_findings still []
  L1.4  markdown-fenced JSON (```json … ```) → successfully parsed;
        verdict=probed or probed_no_content; no exit 2
  L1.5  paper_body.txt absent from sandbox → exit 0;
        verdict=skipped_no_reference; referenceprobe_findings NOT written
  L1.6  paper_body.txt present but < 10 chars → same as L1.5
  L1.7  Layer 1 invariant: protected fields byte-identical pre/post;
        only referenceprobe_findings changed
  L1.8  10-entry cap: 10th call appends normally; 11th call pops oldest
        post-11th: len(referenceprobe_findings)==10; oldest entry gone
  L1.9  sub_problem_id missing in yaml → exit 2; clear error;
        no milestone emitted
  L1.10 assembledContext cap at 3000 chars: len==3000 AND [-3:]=="..."
        (implementation must use total[:2997] + "...")

All tests use mock SKILL JSON strings (no live LLM calls). yaml backlog
fixtures are minimal v2 yamls with one sorry_item.
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

from extract_reference_probe import (  # noqa: E402
    apply_extraction,
    build_assembled_context,
    build_finding_summary,
    parse_subagent_output,
    unwrap_fenced_json,
    ASSEMBLED_CONTEXT_MAX,
    MAX_FINDINGS_PER_ITEM,
    PAPER_BODY_MIN_CHARS,
    VERDICT_PARSE_ERROR,
    VERDICT_PROBED,
    VERDICT_PROBED_NO_CONTENT,
    VERDICT_SKIPPED_NO_REFERENCE,
)
from _history_log_types import migrate_item_v1_to_v2  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_reference_probe.py"


# ── Fixtures ──────────────────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _one_stuck_subproblem_backlog() -> List[Dict[str, Any]]:
    """Pre-migrated v2 row representing a stuck sub-problem. All v2 +
    H6 fields populated so Layer 1 invariant tests have something to
    enforce against."""
    return [
        {
            "id": "sub.s1", "file": "X.lean", "line": 5,
            "theorem": "stuck_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 3,
            "references": [], "coverage_state": "needs_proof",
            "attempts": 0, "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "assumption_hints": [], "assumption_analysis": "",
            "alternative_path": None, "library_hit": None,
            "referenceprobe_findings": [],
        },
    ]


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    # Write a non-trivial paper_body.txt so tests default to enabled probe
    (s / "paper_body.txt").write_text(
        "Proof of the main theorem. We use the dominated convergence theorem "
        "to show that the integral converges.",
        encoding="utf-8",
    )
    return s


@pytest.fixture
def backlog(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _make_backlog(_one_stuck_subproblem_backlog(), p)
    return p


def _write_skill_json(tmp_path: Path, payload: dict, name: str = "probe.json") -> Path:
    p = tmp_path / name
    p.write_text(json.dumps(payload))
    return p


def _read_events(sandbox: Path) -> List[Dict[str, Any]]:
    path = sandbox / "events.jsonl"
    if not path.exists():
        return []
    out = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            out.append(json.loads(line))
    return out


def _probe_milestones(events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return [
        e for e in events
        if e.get("kind") == "sandbox_milestone"
        and e.get("name") == "reference-probe-completed"
    ]


def _run_extract(
    *,
    sub_problem_id: str,
    subagent_json_file: Path,
    sandbox: Path,
    backlog: Path,
) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            sys.executable, str(EXTRACT),
            "--sub-problem-id", sub_problem_id,
            "--subagent-json-file", str(subagent_json_file),
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog),
        ],
        capture_output=True, text=True, timeout=60,
    )


# ── Unit: build_assembled_context ─────────────────────────────────────


def test_build_assembled_context_all_empty_returns_fallback() -> None:
    result = build_assembled_context("", "", "")
    assert result == "Reference probe found no content directly relevant to the current stuck point."


def test_build_assembled_context_all_present_joins_sections() -> None:
    result = build_assembled_context("passage text", "analysis text", "suggestion text")
    assert "**Matched passage**:" in result
    assert "**Why it might help**:" in result
    assert "**Suggested next step**:" in result
    assert "passage text" in result
    assert "analysis text" in result
    assert "suggestion text" in result


def test_build_assembled_context_only_matched_passage() -> None:
    result = build_assembled_context("a passage", "", "")
    assert "**Matched passage**:" in result
    assert "**Why it might help**:" not in result


def test_build_assembled_context_only_suggestion() -> None:
    result = build_assembled_context("", "", "try simp")
    assert "**Suggested next step**:" in result
    assert "**Matched passage**:" not in result


def test_build_assembled_context_cap_3000_with_ellipsis() -> None:
    """L1.10: cap at 3000 with total[:2997] + '...' per spec §8.1 + S2.8 fixup."""
    long_passage = "A" * 1000
    long_analysis = "B" * 1000
    long_suggestion = "C" * 1000
    result = build_assembled_context(long_passage, long_analysis, long_suggestion)
    assert len(result) == ASSEMBLED_CONTEXT_MAX, (
        f"Expected len={ASSEMBLED_CONTEXT_MAX}, got {len(result)}"
    )
    assert result[-3:] == "...", (
        f"Expected last 3 chars '...', got {result[-3:]!r}"
    )


# ── Unit: parse_subagent_output ────────────────────────────────────────


def test_parse_valid_json_all_fields() -> None:
    raw = json.dumps({
        "matchedPassage": "Some passage from the paper.",
        "analysis": "This passage proves the key step.",
        "suggestion": "Try `exact this_passage_lemma`",
    })
    fields, err = parse_subagent_output(raw)
    assert err is None
    assert fields is not None
    assert fields["matchedPassage"] == "Some passage from the paper."
    assert fields["analysis"] == "This passage proves the key step."
    assert fields["suggestion"] == "Try `exact this_passage_lemma`"


def test_parse_valid_json_empty_fields() -> None:
    raw = json.dumps({"matchedPassage": "", "analysis": "", "suggestion": ""})
    fields, err = parse_subagent_output(raw)
    assert err is None
    assert fields is not None
    assert fields["matchedPassage"] == ""
    assert fields["analysis"] == ""
    assert fields["suggestion"] == ""


def test_parse_malformed_json_returns_error() -> None:
    _, err = parse_subagent_output("not json {[}")
    assert err is not None
    assert "not valid JSON" in err


def test_parse_empty_input_returns_error() -> None:
    _, err = parse_subagent_output("")
    assert err is not None


def test_parse_array_root_returns_error() -> None:
    """E4 SKILL returns an array — H6 must reject this."""
    _, err = parse_subagent_output("[]")
    assert err is not None
    assert "must be object" in err


def test_parse_markdown_fenced_json() -> None:
    """L1.4: ```json ... ``` fence is stripped and parsed."""
    inner = json.dumps({"matchedPassage": "p", "analysis": "a", "suggestion": "s"})
    fenced = f"```json\n{inner}\n```"
    fields, err = parse_subagent_output(fenced)
    assert err is None
    assert fields is not None
    assert fields["matchedPassage"] == "p"


def test_parse_clamps_fields() -> None:
    """czy `:355-357`: matchedPassage ≤500, analysis ≤300, suggestion ≤500."""
    raw = json.dumps({
        "matchedPassage": "M" * 600,
        "analysis": "A" * 400,
        "suggestion": "S" * 600,
    })
    fields, err = parse_subagent_output(raw)
    assert err is None
    assert fields is not None
    assert len(fields["matchedPassage"]) == 500
    assert len(fields["analysis"]) == 300
    assert len(fields["suggestion"]) == 500


def test_parse_missing_fields_default_to_empty() -> None:
    """Missing fields → "" (not None, not error)."""
    fields, err = parse_subagent_output(json.dumps({}))
    assert err is None
    assert fields is not None
    assert fields["matchedPassage"] == ""
    assert fields["analysis"] == ""
    assert fields["suggestion"] == ""


# ── Unit: build_finding_summary ───────────────────────────────────────


def test_build_finding_summary_uses_analysis_first() -> None:
    summary = build_finding_summary("The proof uses DCT.", "try exact dcT_lemma")
    assert summary == "The proof uses DCT."


def test_build_finding_summary_falls_back_to_suggestion() -> None:
    summary = build_finding_summary("", "try exact dcT_lemma")
    assert summary.startswith("Suggestion: try exact dcT_lemma")


def test_build_finding_summary_fallback_when_both_empty() -> None:
    summary = build_finding_summary("", "")
    assert summary == "Reference probe: matched passage found"


def test_build_finding_summary_caps_at_200() -> None:
    long = "A" * 300
    assert len(build_finding_summary(long, "")) == 200


# ── Unit: unwrap_fenced_json ──────────────────────────────────────────


def test_unwrap_strips_json_fence() -> None:
    raw = "```json\n{\"a\": 1}\n```"
    assert unwrap_fenced_json(raw).strip() == '{"a": 1}'


def test_unwrap_passes_through_plain() -> None:
    assert unwrap_fenced_json('{"a": 1}') == '{"a": 1}'


# ── L1.1 happy path ──────────────────────────────────────────────────


def test_l1_1_happy_path_all_fields_non_empty(
    backlog: Path, sandbox: Path
) -> None:
    """All three fields non-empty → verdict=probed; referenceprobe_findings[0]
    populated; matched_passage_len > 0."""
    payload = apply_extraction(
        backlog_path=backlog,
        sub_problem_id="sub.s1",
        subagent_text=json.dumps({
            "matchedPassage": "By the dominated convergence theorem, the integral converges.",
            "analysis": "This passage directly addresses the convergence step.",
            "suggestion": "Try `exact dominated_convergence_theorem`",
        }),
        sandbox=sandbox,
    )

    assert payload["verdict"] == VERDICT_PROBED
    assert payload["matched_passage_len"] > 0
    assert payload["suggestion_len"] > 0
    assert payload["assembled_context_len"] > 0
    assert payload["findings_total"] == 1

    # Round-trip: yaml reflects the append
    final = yaml.safe_load(backlog.read_text())
    item = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert len(item["referenceprobe_findings"]) == 1
    entry = item["referenceprobe_findings"][0]
    assert "By the dominated convergence theorem" in entry["assembledContext"]
    assert entry["matchedPassage"] is not None
    assert entry["suggestion"] is not None
    assert entry["stuck_rounds"] == 3
    assert "timestamp" in entry


# ── L1.2 all fields empty → probed_no_content ────────────────────────


def test_l1_2_all_empty_fields_yields_probed_no_content(
    backlog: Path, sandbox: Path
) -> None:
    """All fields empty strings → verdict=probed_no_content; assembledContext
    == fallback text; findings list has 1 entry (null-content probe is
    still recorded)."""
    payload = apply_extraction(
        backlog_path=backlog,
        sub_problem_id="sub.s1",
        subagent_text=json.dumps({
            "matchedPassage": "", "analysis": "", "suggestion": "",
        }),
        sandbox=sandbox,
    )

    assert payload["verdict"] == VERDICT_PROBED_NO_CONTENT
    assert payload["matched_passage_len"] == 0
    assert payload["suggestion_len"] == 0
    assert payload["findings_total"] == 1

    final = yaml.safe_load(backlog.read_text())
    item = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert len(item["referenceprobe_findings"]) == 1
    entry = item["referenceprobe_findings"][0]
    assert "no content directly relevant" in entry["assembledContext"]


# ── L1.3 malformed JSON → parse_error ────────────────────────────────


def test_l1_3_malformed_json_exits_2_yaml_unchanged(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Malformed JSON → exit 2; yaml unchanged; referenceprobe_findings still []."""
    pre_data = yaml.safe_load(backlog.read_text())
    json_file = _write_skill_json(tmp_path, {})  # will overwrite with bad content
    json_file.write_text("not json at all {[}")

    result = _run_extract(
        sub_problem_id="sub.s1",
        subagent_json_file=json_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 2

    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data


def test_l1_3_empty_output_exits_2_yaml_unchanged(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """Empty subagent output → exit 2; yaml unchanged."""
    pre_data = yaml.safe_load(backlog.read_text())
    json_file = tmp_path / "empty.json"
    json_file.write_text("")

    result = _run_extract(
        sub_problem_id="sub.s1",
        subagent_json_file=json_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 2
    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data


# ── L1.4 markdown-fenced JSON ────────────────────────────────────────


def test_l1_4_fenced_json_parsed_successfully(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """```json … ``` fence stripped and parsed; verdict=probed; no exit 2."""
    inner = json.dumps({
        "matchedPassage": "By Lemma 3.2...",
        "analysis": "The lemma gives integrability.",
        "suggestion": "apply Lemma32",
    })
    json_file = tmp_path / "probe.json"
    json_file.write_text(f"```json\n{inner}\n```")

    result = _run_extract(
        sub_problem_id="sub.s1",
        subagent_json_file=json_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 0, f"stderr: {result.stderr!r}"

    final = yaml.safe_load(backlog.read_text())
    item = next(it for it in final["sorry_items"] if it["id"] == "sub.s1")
    assert len(item["referenceprobe_findings"]) == 1
    assert "By Lemma 3.2" in item["referenceprobe_findings"][0]["assembledContext"]


# ── L1.5 paper_body.txt absent ────────────────────────────────────────


def test_l1_5_paper_body_absent_yields_skipped(
    backlog: Path, tmp_path: Path
) -> None:
    """paper_body.txt absent → exit 0; verdict=skipped_no_reference;
    referenceprobe_findings NOT written."""
    # Sandbox WITHOUT paper_body.txt
    sandbox_no_paper = tmp_path / "sandbox_no_paper"
    sandbox_no_paper.mkdir()

    json_file = _write_skill_json(tmp_path, {
        "matchedPassage": "p", "analysis": "a", "suggestion": "s",
    })
    pre_data = yaml.safe_load(backlog.read_text())

    result = _run_extract(
        sub_problem_id="sub.s1",
        subagent_json_file=json_file,
        sandbox=sandbox_no_paper,
        backlog=backlog,
    )
    assert result.returncode == 0, f"stderr: {result.stderr!r}"

    # yaml unchanged (not even an empty entry appended)
    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data

    events = _read_events(sandbox_no_paper)
    probes = _probe_milestones(events)
    assert len(probes) == 1
    assert probes[0]["details"]["verdict"] == VERDICT_SKIPPED_NO_REFERENCE
    assert probes[0]["details"]["assembled_context_len"] == 0


# ── L1.6 paper_body.txt < 10 chars ───────────────────────────────────


def test_l1_6_paper_body_too_short_yields_skipped(
    backlog: Path, tmp_path: Path
) -> None:
    """paper_body.txt present but < 10 chars → same as L1.5."""
    sandbox_short = tmp_path / "sandbox_short"
    sandbox_short.mkdir()
    (sandbox_short / "paper_body.txt").write_text("short", encoding="utf-8")

    json_file = _write_skill_json(tmp_path, {
        "matchedPassage": "p", "analysis": "a", "suggestion": "s",
    })
    pre_data = yaml.safe_load(backlog.read_text())

    result = _run_extract(
        sub_problem_id="sub.s1",
        subagent_json_file=json_file,
        sandbox=sandbox_short,
        backlog=backlog,
    )
    assert result.returncode == 0

    post_data = yaml.safe_load(backlog.read_text())
    assert post_data == pre_data

    events = _read_events(sandbox_short)
    probes = _probe_milestones(events)
    assert len(probes) == 1
    assert probes[0]["details"]["verdict"] == VERDICT_SKIPPED_NO_REFERENCE


# ── L1.7 Layer 1 invariant ───────────────────────────────────────────


def test_l1_7_protected_fields_byte_identical_post_write(
    backlog: Path, sandbox: Path
) -> None:
    """Rule 3 Layer 1: extract_reference_probe.py mutates ONLY
    `referenceprobe_findings`. All other fields on the targeted row are
    byte-identical pre/post write."""
    pre_data = yaml.safe_load(backlog.read_text())
    pre_item = copy.deepcopy(
        next(it for it in pre_data["sorry_items"] if it["id"] == "sub.s1")
    )

    apply_extraction(
        backlog_path=backlog,
        sub_problem_id="sub.s1",
        subagent_text=json.dumps({
            "matchedPassage": "Some reference passage.",
            "analysis": "Relevant because of integrability.",
            "suggestion": "try exact some_lemma",
        }),
        sandbox=sandbox,
    )

    post_data = yaml.safe_load(backlog.read_text())
    post_item = next(it for it in post_data["sorry_items"] if it["id"] == "sub.s1")

    PROTECTED = (
        # Slice 1 (signature)
        "id", "file", "line", "theorem", "type",
        "depth", "priority", "estimated_lines",
        # v2 state machine
        "state", "parent_id", "children", "history_log",
        "dependencies", "unlocks", "stuck_rounds",
        # E4 helper-reference
        "references", "coverage_state",
        # A1 restrategize counter
        "attempts",
        # E11 citation-verify
        "citation_verified",
        # Slice 03 InformalAgent
        "informal_round", "coverage_stable",
        # H1 elaborate-plan
        "detailed_proof_plan", "direct_assembly", "proof_sketch",
        # H7 helper-assumption
        "assumption_hints", "assumption_analysis",
        # H2 detect-alt-path
        "alternative_path",
        # H3 library-coverage
        "library_hit",
    )
    for k in PROTECTED:
        if k in pre_item:
            assert post_item.get(k) == pre_item.get(k), (
                f"protected field {k} changed: pre={pre_item.get(k)!r} "
                f"post={post_item.get(k)!r}"
            )

    # Mutated field IS different
    assert len(post_item["referenceprobe_findings"]) == 1
    assert post_item["referenceprobe_findings"] != pre_item.get("referenceprobe_findings", [])


# ── L1.8 10-entry accumulate cap ─────────────────────────────────────


def test_l1_8_10_entry_cap_pops_oldest(
    backlog: Path, sandbox: Path
) -> None:
    """D-2 accumulate semantics: 10th call appends normally;
    11th call pops oldest. Post-11th: len==10; oldest entry gone."""
    subagent_json = json.dumps({
        "matchedPassage": "passage X",
        "analysis": "analysis X",
        "suggestion": "suggestion X",
    })

    # Make 10 calls
    for i in range(MAX_FINDINGS_PER_ITEM):
        p = apply_extraction(
            backlog_path=backlog,
            sub_problem_id="sub.s1",
            subagent_text=json.dumps({
                "matchedPassage": f"passage {i}",
                "analysis": f"analysis {i}",
                "suggestion": f"suggestion {i}",
            }),
            sandbox=sandbox,
        )
        assert p["verdict"] == VERDICT_PROBED

    # Verify 10 entries now
    data = yaml.safe_load(backlog.read_text())
    item = next(it for it in data["sorry_items"] if it["id"] == "sub.s1")
    assert len(item["referenceprobe_findings"]) == MAX_FINDINGS_PER_ITEM
    # The 11th call should pop the oldest (entry 0) and keep newest
    p11 = apply_extraction(
        backlog_path=backlog,
        sub_problem_id="sub.s1",
        subagent_text=json.dumps({
            "matchedPassage": "passage 10 (newest)",
            "analysis": "analysis 10",
            "suggestion": "suggestion 10",
        }),
        sandbox=sandbox,
    )
    assert p11["verdict"] == VERDICT_PROBED
    assert p11["findings_total"] == MAX_FINDINGS_PER_ITEM  # still 10

    data2 = yaml.safe_load(backlog.read_text())
    item2 = next(it for it in data2["sorry_items"] if it["id"] == "sub.s1")
    assert len(item2["referenceprobe_findings"]) == MAX_FINDINGS_PER_ITEM
    # Oldest (passage 0) should be gone
    passages = [e.get("matchedPassage") for e in item2["referenceprobe_findings"]]
    assert "passage 0" not in passages
    # Newest should be present
    assert "passage 10 (newest)" in passages


# ── L1.9 sub_problem_id missing ──────────────────────────────────────


def test_l1_9_sub_problem_id_missing_raises_value_error(backlog: Path) -> None:
    """apply_extraction raises ValueError on missing sub_problem_id."""
    with pytest.raises(ValueError, match="sub_problem_id not in sorry_items"):
        apply_extraction(
            backlog_path=backlog,
            sub_problem_id="ghost.id",
            subagent_text=json.dumps({
                "matchedPassage": "p", "analysis": "a", "suggestion": "s",
            }),
        )


def test_l1_9_sub_problem_id_missing_exits_2_via_subprocess(
    backlog: Path, sandbox: Path, tmp_path: Path
) -> None:
    """sub_problem_id not in yaml → exit 2 via subprocess CLI."""
    json_file = _write_skill_json(tmp_path, {
        "matchedPassage": "p", "analysis": "a", "suggestion": "s",
    })
    result = _run_extract(
        sub_problem_id="ghost.id",
        subagent_json_file=json_file,
        sandbox=sandbox,
        backlog=backlog,
    )
    assert result.returncode == 2
    assert "sub_problem_id not in sorry_items" in result.stderr


# ── L1.10 assembledContext cap ────────────────────────────────────────


def test_l1_10_assembled_context_cap_3000_chars(
    backlog: Path, sandbox: Path
) -> None:
    """assembledContext capped at exactly 3000 chars using total[:2997] + '...'
    (NOT total[:3000]). Per spec §8.1 S2.8 post-fixup.

    Use large enough inputs that the raw joined text is > 3000 chars.
    Each section has headers (~30 chars) + separators (~2 chars). With 3 × 1500
    content chars + ~65 chars overhead = ~4565 > 3000. So 1500-char sections
    produce a total that hits the cap.
    """
    # Build directly via build_assembled_context with unclamped large strings
    # (build_assembled_context itself doesn't clamp inputs — the parser does).
    # 3 × 1500 = 4500 + headers/separators > 3000, so cap fires.
    result = build_assembled_context(
        "M" * 1500,   # matched passage (unclamped by this function)
        "A" * 1500,   # analysis (unclamped by this function)
        "S" * 1500,   # suggestion (unclamped by this function)
    )
    assert len(result) == ASSEMBLED_CONTEXT_MAX, (
        f"Expected len={ASSEMBLED_CONTEXT_MAX}, got {len(result)}"
    )
    assert result[-3:] == "...", (
        f"Expected last 3 chars '...', got {result[-3:]!r}"
    )

    # Also verify via apply_extraction: the clamped path still produces valid assembledContext
    payload = apply_extraction(
        backlog_path=backlog,
        sub_problem_id="sub.s1",
        subagent_text=json.dumps({
            "matchedPassage": "M" * 500,   # at cap
            "analysis": "A" * 300,          # at cap
            "suggestion": "S" * 500,        # at cap
        }),
        sandbox=sandbox,
    )
    assert payload["assembled_context_len"] <= ASSEMBLED_CONTEXT_MAX


# ── Migration test ────────────────────────────────────────────────────


def test_migration_adds_referenceprobe_findings_idempotently() -> None:
    """v1 → v2 with H6's new field. Idempotent: running twice
    leaves the item byte-identical to a single migration."""
    v1_item: Dict[str, Any] = {
        "id": "x", "file": "X.lean", "line": 1, "theorem": "x_thm",
        "type": "ready", "depth": 0, "priority": 50,
        "estimated_lines": 30, "dependencies": [], "unlocks": [],
    }
    migrate_item_v1_to_v2(v1_item)
    assert v1_item.get("referenceprobe_findings") == []

    snap = copy.deepcopy(v1_item)
    migrate_item_v1_to_v2(v1_item)
    assert v1_item == snap


def test_migration_preserves_existing_referenceprobe_findings() -> None:
    """If yaml already has referenceprobe_findings, migration must NOT clobber."""
    existing_finding = {"assembledContext": "existing entry", "stuck_rounds": 2}
    item = {
        "id": "x",
        "state": "INITIALIZED", "children": [], "parent_id": None,
        "history_log": [],
        "referenceprobe_findings": [existing_finding],
    }
    migrate_item_v1_to_v2(item)
    assert item["referenceprobe_findings"] == [existing_finding]


# ── Sentinel ─────────────────────────────────────────────────────────


def test_module_present_marker() -> None:
    """Sentinel test — guards against the test file being silently
    excluded from collection (mirrors slice-1 pattern)."""
    assert True

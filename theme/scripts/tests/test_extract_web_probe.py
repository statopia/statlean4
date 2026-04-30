"""H5 L1 unit tests for extract_web_probe.py.

Coverage matrix per `docs/H5_WEB_PROBE_SPEC.md` §8.1:
  L1.1 happy path: findings + hits + assembled_context → webprobe_context set;
       milestone verdict=`completed`; hits_count=2; findings_excerpt populated
  L1.2 empty web_hits fast-path (D-5) → verdict=`empty`; webprobe_context=""
  L1.3 malformed JSON → exit 2; verdict=`parse_error`; yaml unchanged
  L1.4 assembled_context > 3000 chars → truncated to 3000 in yaml; context_length ≤ 3000
       AND deep-fetch block inside assembled_context truncated to 2000 chars (two truncation
       points per spec §3.2 S2.1 fixup)
  L1.5 overwrite existing webprobe_context with new call (D-7 overwrite-on-call)
  L1.6 --clear-context flag → webprobe_context set to ""; no milestone emitted
  L1.7 Layer 1 invariant — locked fields byte-identical post-write
  L1.8 sub_problem_id missing in yaml → exit 2; yaml unchanged
  L1.9 findings field missing from SKILL JSON → defaults to "(no findings)";
       assembled_context still written if assembled_context field present
  L1.10 generated_query field absent → query_used in milestone defaults to "(unknown)";
        script does not fail

All tests use mock JSON files; no live LLM or web calls.
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

from extract_web_probe import (  # noqa: E402
    apply_web_probe,
    apply_clear_context,
    parse_subagent_output,
    ASSEMBLED_CONTEXT_MAX_CHARS,
    VERDICT_COMPLETED,
    VERDICT_EMPTY,
    VERDICT_PARSE_ERROR,
)
from _history_log_types import migrate_item_v1_to_v2  # noqa: E402

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
EXTRACT = SCRIPTS_DIR / "extract_web_probe.py"


# ── Fixtures ─────────────────────────────────────────────────────────


def _make_backlog(items: List[Dict[str, Any]], path: Path) -> None:
    data = {
        "schema_version": 2,
        "version": "v100",
        "sorry_items": items,
    }
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))


def _one_stuck_subproblem_backlog() -> List[Dict[str, Any]]:
    """Pre-migrated v2 row with all protected fields populated for Layer 1 tests."""
    return [
        {
            "id": "sub.s1", "file": "X.lean", "line": 5,
            "theorem": "stuck_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            # v2 state-machine fields
            "state": "INITIALIZED", "children": [],
            "parent_id": "parent.one", "history_log": [], "stuck_rounds": 3,
            # E4 fields
            "references": [], "coverage_state": "needs_proof",
            # other v2 fields
            "attempts": 0, "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            # H7 fields
            "assumption_hints": ["some existing hint"], "assumption_analysis": "old analysis",
            # H5 field
            "webprobe_context": "",
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


def _valid_skill_json(
    sub_problem_id: str = "sub.s1",
    findings: str = "The lemma integral_nonneg exists in Mathlib.MeasureTheory.",
    suggestion: str = "Try `exact MeasureTheory.integral_nonneg (fun x _ => h x)`.",
    web_hits: int = 2,
    assembled_context: str = "",
    generated_query: str = "integral_nonneg Lean 4 Mathlib",
    web_fetch_content: str = "",
) -> str:
    hits = [
        {"title": f"Hit {i+1}", "url": f"https://github.com/leanprover-community/mathlib4/blob/main/Mathlib/Hit{i+1}.lean", "snippet": f"Snippet {i+1}"}
        for i in range(web_hits)
    ]
    ctx = assembled_context or (
        f"## Web Probe (stuck recovery for stuck_thm)\n"
        f"Query: {generated_query}\n\n"
        f"### Findings\n{findings}\n\n"
        f"### Suggestion\n{suggestion}\n\n"
        f"### Top hits\n" + "\n".join(f"- {h['title']}\n  {h['url']}" for h in hits)
    )
    return json.dumps({
        "sub_problem_id": sub_problem_id,
        "generated_query": generated_query,
        "web_hits": hits,
        "web_fetch_content": web_fetch_content,
        "findings": findings,
        "suggestion": suggestion,
        "assembled_context": ctx,
    })


# ── L1.1 — happy path ────────────────────────────────────────────────


def test_l1_1_happy_path(backlog: Path, sandbox: Path) -> None:
    """Valid SKILL JSON with findings + hits → webprobe_context set;
    verdict=completed; hits_count=2; findings_excerpt populated."""
    skill_json = _valid_skill_json(sub_problem_id="sub.s1", web_hits=2)
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    assert payload["verdict"] == VERDICT_COMPLETED
    assert payload["hits_count"] == 2
    assert payload["context_length"] > 0
    assert payload["findings_excerpt"] is not None
    assert "integral_nonneg" in payload["findings_excerpt"]

    data = yaml.safe_load(backlog.read_text())
    item = next(it for it in data["sorry_items"] if it["id"] == "sub.s1")
    assert "## Web Probe" in item["webprobe_context"]
    assert len(item["webprobe_context"]) == payload["context_length"]


# ── L1.2 — empty web_hits fast-path (D-5) ────────────────────────────


def test_l1_2_empty_hits_fastpath(backlog: Path, sandbox: Path) -> None:
    """web_hits=[] AND web_fetch_content="" → verdict=empty; webprobe_context="" (D-5 +1)."""
    # Pre-populate with some old context to verify overwrite
    data = yaml.safe_load(backlog.read_text())
    for it in data["sorry_items"]:
        if it["id"] == "sub.s1":
            it["webprobe_context"] = "old context"
    backlog.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))

    skill_json = json.dumps({
        "sub_problem_id": "sub.s1",
        "generated_query": "something Lean 4 Mathlib",
        "web_hits": [],
        "web_fetch_content": "",
        "findings": "No relevant web results found.",
        "suggestion": "Try a different approach in the prover; web search returned nothing useful.",
        "assembled_context": "",  # empty assembled_context signals empty
    })
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    # D-5: zero hits + empty fetch → verdict=empty (not completed)
    assert payload["verdict"] == VERDICT_EMPTY
    assert payload["context_length"] == 0
    assert payload["findings_excerpt"] is None

    data = yaml.safe_load(backlog.read_text())
    item = next(it for it in data["sorry_items"] if it["id"] == "sub.s1")
    assert item["webprobe_context"] == ""


# ── L1.3 — malformed JSON → parse_error ──────────────────────────────


def test_l1_3_malformed_json(backlog: Path, sandbox: Path) -> None:
    """Malformed JSON → parse_error; yaml unchanged."""
    original_data = yaml.safe_load(backlog.read_text())

    payload, exit_code = apply_web_probe(backlog, "sub.s1", "not-json {[broken")

    assert exit_code == 2
    assert payload["verdict"] == VERDICT_PARSE_ERROR
    assert payload["context_length"] == 0
    assert payload["findings_excerpt"] is None

    # yaml unchanged
    after_data = yaml.safe_load(backlog.read_text())
    assert after_data == original_data


# ── L1.4 — truncation at 3000 chars (two truncation points) ──────────


def test_l1_4_assembled_context_truncated_to_3000(backlog: Path, sandbox: Path) -> None:
    """assembled_context > 3000 chars → script truncates to ASSEMBLED_CONTEXT_MAX_CHARS.

    Two truncation points per spec §3.2:
    (a) web_fetch_content in SKILL JSON may be up to 4000 bytes (fetch-level cap;
        SKILL Step 2 responsibility)
    (b) deep-fetch block inside assembled_context is truncated to 2000 chars
        (renderer-level cap; SKILL Step 3 responsibility, applied BEFORE
        emitting assembled_context)

    Script-side enforcement: the script clamps the FINAL assembled_context to
    3000 chars overall. It does NOT parse the deep-fetch section out of the
    blob to enforce the 2000-char cap — that is structurally a SKILL-trust
    boundary (per H5 §8 code review S2.1: this is the honest layering).
    """
    long_text = "X" * 5000  # exceeds both 3000 and 4000 caps
    # assembled_context itself is > 3000 chars
    long_assembled = "## Web Probe\n" + long_text
    skill_json = json.dumps({
        "sub_problem_id": "sub.s1",
        "generated_query": "test query",
        "web_hits": [{"title": "T", "url": "https://github.com/x", "snippet": "S"}],
        "web_fetch_content": "X" * 4000,  # (a) fetch-level: up to 4000 bytes
        "findings": "some findings",
        "suggestion": "some suggestion",
        "assembled_context": long_assembled,
    })
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    assert payload["verdict"] == VERDICT_COMPLETED
    # Behavioral assertion: stored length is EXACTLY the cap (not just ≤)
    # when input exceeds the cap. This catches a regression that lets
    # >3000-char content slip through.
    assert payload["context_length"] == ASSEMBLED_CONTEXT_MAX_CHARS == 3000

    data = yaml.safe_load(backlog.read_text())
    item = next(it for it in data["sorry_items"] if it["id"] == "sub.s1")
    assert len(item["webprobe_context"]) == ASSEMBLED_CONTEXT_MAX_CHARS
    assert len(item["webprobe_context"]) == payload["context_length"]


def test_l1_4b_oversized_deep_fetch_block_passes_through_under_overall_cap(
    backlog: Path, sandbox: Path
) -> None:
    """Document SKILL-trust boundary: a non-compliant SKILL emitting a
    deep-fetch block > 2000 chars (violating spec §3.2 (b)) is NOT
    detected by the script — the oversized block flows into
    webprobe_context up to the overall 3000-char script-side cap.

    This test exists to make the trust boundary explicit. If a future
    slice adds script-side parsing of the deep-fetch section to enforce
    the 2000-char cap, this test should be updated accordingly.

    H5 §8 code review S2.1 (2026-04-30) flagged this as a SKILL-compliance
    detection gap; the gap is acknowledged here rather than papered over.
    """
    deep_fetch_oversized = "Y" * 2500  # >2000 char cap; SKILL-non-compliant
    # SKILL would have shipped a context that already exceeds the 2000-char
    # deep-fetch cap. The script stores it up to the 3000-char overall cap.
    bad_assembled = "## Deep fetch:\n" + deep_fetch_oversized + "\n## Suggestion: try X"
    skill_json = json.dumps({
        "sub_problem_id": "sub.s1",
        "generated_query": "test query",
        "web_hits": [{"title": "T", "url": "https://github.com/x", "snippet": "S"}],
        "web_fetch_content": "Y" * 2500,
        "findings": "some findings",
        "suggestion": "some suggestion",
        "assembled_context": bad_assembled,
    })
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    # Script does NOT detect/clamp the >2000 deep-fetch sub-block;
    # only the overall 3000-char cap fires.
    data = yaml.safe_load(backlog.read_text())
    item = next(it for it in data["sorry_items"] if it["id"] == "sub.s1")
    stored = item["webprobe_context"]
    assert len(stored) <= ASSEMBLED_CONTEXT_MAX_CHARS
    # The Y-block (2500 chars) survives because 2500 < 3000 overall cap;
    # this test would FAIL if a future change enforces the 2000-char
    # deep-fetch sub-cap (at which point update the assertion to expect
    # truncation).
    assert "Y" * 2000 in stored  # confirms >2000 chars of Y-content stored


# ── L1.5 — overwrite existing webprobe_context ───────────────────────


def test_l1_5_overwrite_existing_context(backlog: Path, sandbox: Path) -> None:
    """Second call fully replaces first (D-7 overwrite-on-each-call)."""
    # First write
    first_json = _valid_skill_json(sub_problem_id="sub.s1", findings="First probe findings")
    payload1, ec1 = apply_web_probe(backlog, "sub.s1", first_json)
    assert ec1 == 0
    assert "First probe findings" in (
        yaml.safe_load(backlog.read_text())["sorry_items"][0]["webprobe_context"]
    )

    # Second write — different findings
    second_json = _valid_skill_json(sub_problem_id="sub.s1", findings="Second probe findings NEW")
    payload2, ec2 = apply_web_probe(backlog, "sub.s1", second_json)
    assert ec2 == 0

    data = yaml.safe_load(backlog.read_text())
    item = data["sorry_items"][0]
    assert "Second probe findings NEW" in item["webprobe_context"]
    # First call's content is gone (not appended)
    assert "First probe findings" not in item["webprobe_context"]


# ── L1.6 — --clear-context ──────────────────────────────────────────


def test_l1_6_clear_context(backlog: Path, sandbox: Path) -> None:
    """--clear-context sets webprobe_context=""; sub_problem_id validated."""
    # Pre-populate context
    skill_json = _valid_skill_json(sub_problem_id="sub.s1")
    apply_web_probe(backlog, "sub.s1", skill_json)

    data = yaml.safe_load(backlog.read_text())
    assert data["sorry_items"][0]["webprobe_context"] != ""

    # Clear
    success, err = apply_clear_context(backlog, "sub.s1")
    assert success is True
    assert err is None

    data = yaml.safe_load(backlog.read_text())
    assert data["sorry_items"][0]["webprobe_context"] == ""


def test_l1_6_clear_context_missing_id(backlog: Path) -> None:
    """--clear-context with missing sub_problem_id returns error."""
    success, err = apply_clear_context(backlog, "nonexistent.id")
    assert success is False
    assert err is not None
    assert "not in sorry_items" in err


# ── L1.7 — Layer 1 invariant ─────────────────────────────────────────


_PROTECTED_FIELDS = [
    "id", "file", "line", "theorem", "type", "depth", "priority",
    "estimated_lines", "dependencies", "unlocks",
    "state", "children", "parent_id", "history_log", "stuck_rounds",
    "references", "coverage_state", "attempts", "citation_verified",
    "informal_round", "coverage_stable",
    "assumption_hints", "assumption_analysis",
]


def test_l1_7_layer1_invariant_locked_fields_unchanged(backlog: Path, sandbox: Path) -> None:
    """Only webprobe_context mutated; all protected fields byte-identical post-write."""
    data_before = yaml.safe_load(backlog.read_text())
    item_before = copy.deepcopy(
        next(it for it in data_before["sorry_items"] if it["id"] == "sub.s1")
    )

    skill_json = _valid_skill_json(sub_problem_id="sub.s1")
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)
    assert exit_code == 0

    data_after = yaml.safe_load(backlog.read_text())
    item_after = next(it for it in data_after["sorry_items"] if it["id"] == "sub.s1")

    for field in _PROTECTED_FIELDS:
        assert item_after.get(field) == item_before.get(field), (
            f"Layer 1 violated: field {field!r} changed from "
            f"{item_before.get(field)!r} to {item_after.get(field)!r}"
        )

    # webprobe_context must have changed
    assert item_after["webprobe_context"] != item_before["webprobe_context"]


# ── L1.8 — sub_problem_id missing in yaml ────────────────────────────


def test_l1_8_sub_problem_id_missing(backlog: Path, sandbox: Path) -> None:
    """sub_problem_id not in yaml → ValueError raised; caller exits 2."""
    skill_json = _valid_skill_json(sub_problem_id="nonexistent.sub")
    with pytest.raises(ValueError, match="not in sorry_items"):
        apply_web_probe(backlog, "nonexistent.sub", skill_json)

    # yaml unchanged
    data = yaml.safe_load(backlog.read_text())
    assert data["sorry_items"][0]["webprobe_context"] == ""


# ── L1.9 — findings field missing → graceful default ─────────────────


def test_l1_9_findings_field_missing(backlog: Path, sandbox: Path) -> None:
    """findings absent from SKILL JSON → defaults to '(no findings)';
    assembled_context still written if assembled_context field present."""
    skill_json = json.dumps({
        "sub_problem_id": "sub.s1",
        "generated_query": "test query",
        "web_hits": [{"title": "T", "url": "https://github.com/x", "snippet": "S"}],
        "web_fetch_content": "",
        # findings deliberately omitted
        "suggestion": "Try something.",
        "assembled_context": "## Web Probe\n### Suggestion\nTry something.",
    })
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    assert payload["verdict"] == VERDICT_COMPLETED
    assert payload["context_length"] > 0

    # findings_excerpt comes from parsed["findings"] which defaults to "(no findings)"
    # completed verdict requires findings_excerpt non-null
    assert payload["findings_excerpt"] is not None
    # "(no findings)" gets truncated to "(no findings)" (≤200 chars)
    assert "(no findings)" in (payload["findings_excerpt"] or "")

    data = yaml.safe_load(backlog.read_text())
    item = data["sorry_items"][0]
    assert item["webprobe_context"] != ""


# ── L1.10 — generated_query field absent ─────────────────────────────


def test_l1_10_generated_query_absent(backlog: Path, sandbox: Path) -> None:
    """generated_query absent → query_used defaults to '(unknown)'; script succeeds."""
    skill_json = json.dumps({
        "sub_problem_id": "sub.s1",
        # generated_query deliberately omitted
        "web_hits": [{"title": "T", "url": "https://github.com/x", "snippet": "S"}],
        "web_fetch_content": "",
        "findings": "Some findings.",
        "suggestion": "Try something.",
        "assembled_context": "## Web Probe\n### Findings\nSome findings.",
    })
    payload, exit_code = apply_web_probe(backlog, "sub.s1", skill_json)

    assert exit_code == 0
    assert payload["verdict"] == VERDICT_COMPLETED
    assert payload["query_used"] == "(unknown)"


# ── Parse-level unit tests ────────────────────────────────────────────


def test_parse_missing_assembled_context() -> None:
    """assembled_context missing → parse_error."""
    raw = json.dumps({
        "sub_problem_id": "x",
        "generated_query": "test",
        "web_hits": [],
        "findings": "f",
        "suggestion": "s",
        # assembled_context omitted
    })
    parsed, err = parse_subagent_output(raw)
    assert parsed is None
    assert err is not None
    assert "assembled_context" in err


def test_parse_fenced_json_unwraps() -> None:
    """Markdown-fenced JSON is unwrapped before parsing."""
    inner = json.dumps({
        "sub_problem_id": "x",
        "generated_query": "test",
        "web_hits": [],
        "findings": "f",
        "suggestion": "s",
        "assembled_context": "## Web Probe\n",
    })
    fenced = f"```json\n{inner}\n```"
    parsed, err = parse_subagent_output(fenced)
    assert parsed is not None
    assert err is None
    assert parsed["findings"] == "f"


def test_parse_non_object_root() -> None:
    """Array root → parse_error."""
    parsed, err = parse_subagent_output("[1, 2, 3]")
    assert parsed is None
    assert err is not None
    assert "object" in err

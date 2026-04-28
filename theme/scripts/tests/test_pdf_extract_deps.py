"""Unit tests for pdf_extract.py dependency-tracing helpers (--include-deps)
and the explicit-pages-priority guarantee in main().

Pure-function tests for `extract_citations` (regex-only, no PDF needed),
integration tests for `expand_with_dependencies` using a synthetic pymupdf-
built PDF, plus subprocess tests for the `--pages > --theorem > --query`
priority order in main().

Run:
  pytest theme/scripts/tests/test_pdf_extract_deps.py -v
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "theme" / "scripts"))

from pdf_extract import (  # noqa: E402
    expand_with_dependencies,
    extract_citations,
    find_all_declaration_clusters,
    parse_theorem_arg,
    scan_pages_for_equation,
    scan_pages_for_theorem,
    scan_proof_span_for_theorem,
)


# ── extract_citations (pure-function regex tests) ─────────────────


def test_basic_english_by_lemma():
    assert ("Lemma", "2.1") in extract_citations("Proof. By Lemma 2.1, we have...")


def test_english_via_theorem_period_id():
    assert ("Theorem", "1.5") in extract_citations("via Theorem 1.5 the bound holds")


def test_english_using_assumption():
    assert ("Assumption", "3.2") in extract_citations("using Assumption 3.2 (a)")


def test_plural_lemmas_and():
    cs = extract_citations("By Lemmas 2.3 and 2.4 we conclude.")
    assert ("Lemma", "2.3") in cs
    assert ("Lemma", "2.4") in cs


def test_chinese_yi_lemma():
    cs = extract_citations("由引理 2.1 可知，对任意 x ...")
    assert ("Lemma", "2.1") in cs


def test_chinese_genju_theorem_with_pair():
    cs = extract_citations("根据定理 5.1 和 5.2，结论成立")
    assert ("Theorem", "5.1") in cs
    assert ("Theorem", "5.2") in cs


def test_excludes_self_reference():
    """Theorem 5.1's own page often restates 'Theorem 5.1' in the heading.
    Caller passes exclude_id='5.1' to suppress self-reference noise."""
    text = "Theorem 5.1. (Main result). Proof. by Lemma 2.1 ..."
    cs = extract_citations(text, exclude_id="5.1")
    assert ("Theorem", "5.1") not in cs
    assert ("Lemma", "2.1") in cs


def test_equation_citations_with_anchor_word():
    """Equation refs ARE first-class citations when grammatically anchored
    (noun like `model`, verb/prep like `from`/`into`/`substituting`).
    Previously we excluded all bare-paren refs as noise; user-reported
    miss on Shao's Theorem 3.10 `model (3.25)` showed that's wrong —
    the equation defines the *setup* the theorem depends on."""
    # Verb-anchored: math-rewrite phrasing
    cs = extract_citations("substituting (2.6) into (2.7) gives ...")
    assert ("Equation", "2.6") in cs
    assert ("Equation", "2.7") in cs
    # Noun-anchored: most common in stat papers ("model (3.25)").
    cs = extract_citations("Theorem 3.10. Consider model (3.25) with assumption A3.")
    assert ("Equation", "3.25") in cs
    # Prep-anchored
    cs = extract_citations("from (3.25), we have the BLUE.")
    assert ("Equation", "3.25") in cs


def test_no_false_positive_on_bare_paren_no_anchor():
    """`(3.25)` standing alone with no preceding noun/verb is the
    DECLARATION form (display equation right-aligned number), not a
    citation. extract_citations must not match it; scan_pages_for_equation
    handles the declaration side."""
    cs = extract_citations("X = Zβ + ε. (3.25) Definition 3.4. Suppose...")
    assert ("Equation", "3.25") not in cs


def test_no_false_positive_on_enumerator_paren():
    """`(i)`, `(ii)`, `(a)` etc. are list enumerators, not equations. The
    [A-Z]?\\d+ ID form requires a digit, so single letters/Romans don't
    match."""
    cs = extract_citations("(i) implies (ii) by Theorem 5.1.")
    assert all(k != "Equation" for k, i in cs), cs


def test_no_false_positive_on_vague_reference():
    """`the previous lemma`, `Lemma X above` — out of scope. Requires
    structural understanding we don't attempt."""
    cs = extract_citations("by the previous lemma we have ...")
    assert cs == []


def test_dedupe_when_cited_twice():
    cs = extract_citations("By Lemma 2.1 and again by Lemma 2.1 we get ...")
    assert cs.count(("Lemma", "2.1")) == 1


def test_handles_multipart_id_3_4_1():
    cs = extract_citations("By Theorem 3.4.1 the bound is tight.")
    assert ("Theorem", "3.4.1") in cs


def test_invoke_verb():
    cs = extract_citations("invoke Proposition 4.7 to bound the error")
    assert ("Proposition", "4.7") in cs


def test_letter_prefixed_id_assumption_a3():
    """Real-world: Shao's Theorem 3.10 references `assumption A3` (lowercase
    in the body). ID `A3` must parse — it didn't before the `[A-Z]?\\d+` fix
    landed (numeric-only ID regex silently dropped letter-prefixed forms)."""
    cs = extract_citations("Consider model (3.25) with assumption A3.")
    assert ("Assumption", "A3") in cs


def test_letter_prefixed_id_lemma_s5():
    cs = extract_citations("By Lemma S5 the result follows.")
    assert ("Lemma", "S5") in cs


def test_assumption_letter_id_with_subnumber():
    """Composite letter-prefixed IDs like `B.1`, `S2.3` should also parse."""
    cs = extract_citations("under Assumption B.1 the conclusion holds")
    assert ("Assumption", "B.1") in cs


# ── Range citations: (A1)–(A10), Lemmas 2.1–2.5, etc. ───────────────
#
# Real-world stat papers reference ranges of assumptions / lemmas via
# en-dash / em-dash / hyphen. The Cox change-point paper's Theorem 1
# states "Under Assumptions (A1)–(A10), ...". Without range support the
# entire assumption dependency was invisible to the citation extractor.
#
# Design choice (first-principles): for ranges, we extract ENDPOINTS only,
# not the full enumeration. Assumption blocks declare contiguously in the
# paper, so the declaration pages of A1 and A10 cover everything between
# via natural page-set union. Cheaper than enumeration, no edge-case
# explosion on letter sequences (A.1.2–A.1.7 etc.).


def test_range_parenthesized_assumptions_endash():
    """Cox Theorem 1 case: `Under Assumptions (A1)–(A10), ...` — endpoints
    only (A1, A10); declaration pages of A1 and A10 cover A2–A9 via the
    natural assumption-block contiguity in the paper."""
    cs = extract_citations("Under Assumptions (A1)–(A10), there exists a neighborhood")
    assert ("Assumption", "A1") in cs, f"missing endpoint A1; got {cs}"
    assert ("Assumption", "A10") in cs, f"missing endpoint A10; got {cs}"


def test_range_bare_lemmas_endash():
    """Bare-id range without parens: `By Lemmas 2.1–2.5, ...`."""
    cs = extract_citations("By Lemmas 2.1–2.5 we conclude.")
    assert ("Lemma", "2.1") in cs
    assert ("Lemma", "2.5") in cs


def test_range_emdash():
    """Em-dash variant `—` (U+2014) is also used in some typesetting
    conventions. Must be recognised."""
    cs = extract_citations("under Assumptions A1—A10 hold")
    assert ("Assumption", "A1") in cs
    assert ("Assumption", "A10") in cs


def test_range_plain_hyphen():
    """OCR sometimes outputs en-dash as plain ASCII hyphen `-`. Must
    still parse as a range when between two valid ids inside a kind-
    anchored citation."""
    cs = extract_citations("by Lemmas 2.1-2.5, the conclusion holds")
    assert ("Lemma", "2.1") in cs
    assert ("Lemma", "2.5") in cs


def test_range_mixed_with_list():
    """Combined: `Lemmas 2.1, 2.3, and 2.5–2.7` → 4 ids (list two + range
    endpoints two). Endpoint-only convention plus list extraction."""
    cs = extract_citations("Lemmas 2.1, 2.3, and 2.5–2.7 give the bound.")
    cited_ids = {i for _k, i in cs if _k == "Lemma"}
    assert {"2.1", "2.3", "2.5", "2.7"} <= cited_ids, f"got Lemma ids: {cited_ids}"


def test_range_parenthesized_single():
    """Single id parenthesized: `By Assumption (A3), ...`. Already common
    in Cox-style papers — must parse the same as bare `Assumption A3`."""
    cs = extract_citations("By Assumption (A3), the conclusion holds")
    assert ("Assumption", "A3") in cs


def test_range_does_not_match_versioned_suffix():
    """Negative: `Lemma 5-style argument` should NOT extract a range —
    `style` isn't a valid id and the regex must back off to `Lemma 5`
    only."""
    cs = extract_citations("the Lemma 5-style argument applies here")
    cited_ids = {i for _k, i in cs if _k == "Lemma"}
    assert "5" in cited_ids
    # No phantom second id picked up
    assert cited_ids == {"5"}, f"got Lemma ids: {cited_ids}"


def test_range_chinese_assumptions():
    """Chinese range form: `由假设 A1—A10` (most common in CS/stats papers
    translated from English) and `(A1)至(A10)`. At minimum endpoints."""
    cs = extract_citations("由假设 A1—A10 ，结论成立")
    cited_ids = {i for _k, i in cs if _k == "Assumption"}
    assert "A1" in cited_ids and "A10" in cited_ids, f"got: {cited_ids}"


# See `test_cox_theorem_1_pulls_assumption_range_from_statement` further
# below — it lives after the COX_PDF / cox_only definitions because the
# decorator can't be referenced before the marker is bound.


# ── Integration: build a synthetic PDF and round-trip via pymupdf ──


@pytest.fixture()
def synthetic_pdf(tmp_path):
    """6-page PDF with a known citation graph:
      Page 0: Lemma 2.1 declared
      Page 1: Definition 1.1 declared
      Page 2: Theorem 5.1 declared, body cites Lemma 2.1 and Definition 1.1
      Page 3: proof spillover (no new declarations)
      Page 4: filler / unrelated section
      Page 5: Theorem 5.2 declared (different result, unrelated)
    """
    import pymupdf

    pages = [
        "Lemma 2.1 (Continuity). For any continuous function f on a compact set, f attains its maximum.",
        "Definition 1.1 (Regularity). A space X is regular if every point has a neighbourhood basis of closed sets.",
        "Theorem 5.1 (Main result). Suppose X is regular and f is continuous. Then f attains a max on X.\n\nProof. By Lemma 2.1 and Definition 1.1, the result follows.",
        "Continuing the argument from the previous page: the bound is tight when X is connected.",
        "Section 6: Applications. Various examples in different settings...",
        "Theorem 5.2 (Counterexample). A different statement on a different space.",
    ]
    doc = pymupdf.open()
    for text in pages:
        page = doc.new_page()
        page.insert_text((50, 100), text, fontsize=11)
    out = tmp_path / "synthetic.pdf"
    doc.save(str(out))
    doc.close()
    return out


def test_scan_pages_for_theorem_finds_5_1(synthetic_pdf):
    """Sanity check on the existing scanner before we layer deps on top."""
    pages = scan_pages_for_theorem(synthetic_pdf, "5.1")
    # Theorem 5.1 declared on page idx 2; scanner also includes the next page
    # (proof spillover convention). Page 5 declares Theorem 5.2 — must NOT
    # be in the set.
    assert 2 in pages
    assert 5 not in pages


def test_expand_with_deps_pulls_referenced_pages(synthetic_pdf):
    """The headline behavior: extract Theorem 5.1 + dep pages."""
    base = scan_pages_for_theorem(synthetic_pdf, "5.1")
    expanded, citations = expand_with_dependencies(
        synthetic_pdf, base, exclude_id="5.1"
    )
    # Should now also include Lemma 2.1 (page 0) and Definition 1.1 (page 1).
    assert 0 in expanded, f"missing Lemma 2.1 page; got {expanded}, citations={citations}"
    assert 1 in expanded, f"missing Definition 1.1 page; got {expanded}, citations={citations}"
    # Original target pages preserved.
    for p in base:
        assert p in expanded
    # Theorem 5.2 (page 5, unrelated) MUST NOT be pulled in.
    assert 5 not in expanded
    # Citations report should mention both deps.
    cited_ids = {cid for _kind, cid in citations}
    assert "2.1" in cited_ids
    assert "1.1" in cited_ids


def test_expand_no_deps_when_theorem_has_no_citations(synthetic_pdf):
    """Theorem 5.2 has no proof body / citations on its page → expanded == base."""
    base = scan_pages_for_theorem(synthetic_pdf, "5.2")
    expanded, citations = expand_with_dependencies(
        synthetic_pdf, base, exclude_id="5.2"
    )
    assert expanded == base
    assert citations == []


def test_expand_respects_max_total_pages_cap(synthetic_pdf):
    """Synthetic small case — just make sure cap doesn't drop target pages."""
    base = scan_pages_for_theorem(synthetic_pdf, "5.1")
    expanded, _ = expand_with_dependencies(
        synthetic_pdf, base, exclude_id="5.1", max_total_pages=len(base)
    )
    # Cap == base length means no extras can fit; target pages preserved.
    assert set(expanded) == set(base)


# ── main() priority enforcement: --pages wins over --theorem ─────────
#
# Subprocess-based because the priority lives in main()'s argparse + branching
# logic. The user's spec was "页码输入优先，没有的话再用关键字". Before this
# fix, main() ran `if theorem: ... elif pages: ...` so --theorem won when both
# were given — agent compliance was the only safeguard. Now the fix is
# structural (script-side ordering), so even an "agent passes both flags"
# bug can't reach the wrong branch.

SCRIPT = (
    Path(__file__).resolve().parents[3] / "theme" / "scripts" / "pdf_extract.py"
)


def _run_extract(*args: str, cwd: Path) -> subprocess.CompletedProcess[str]:
    """Run pdf_extract.py with given args, capturing stdout/stderr."""
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=30,
    )


def test_main_priority_pages_beats_theorem(synthetic_pdf, tmp_path):
    """Both --pages and --theorem given → --pages wins, --theorem branch never runs."""
    out_dir = tmp_path / "out"
    res = _run_extract(
        "--pdf", str(synthetic_pdf),
        "--output-dir", str(out_dir),
        "--pages", "2",            # Only page 1 (0-indexed → page idx 1, i.e. Definition 1.1)
        "--theorem", "5.1",        # Would otherwise pull pages [2, 3] (Theorem 5.1 + spill)
        "--backend", "pymupdf",    # Force a deterministic backend so the test runs offline
        cwd=tmp_path,
    )
    assert res.returncode == 0, f"stderr: {res.stderr}"
    # The pages branch logged the success line.
    assert "Using specified pages: [2]" in res.stdout, res.stdout
    # The theorem branch did NOT run (would have logged "Theorem 5.1 found on pages: ...").
    assert "Theorem 5.1 found on pages" not in res.stdout, res.stdout


def test_main_priority_invalid_pages_falls_through_to_theorem(synthetic_pdf, tmp_path):
    """--pages parses to nothing → graceful fallback to --theorem branch."""
    out_dir = tmp_path / "out"
    res = _run_extract(
        "--pdf", str(synthetic_pdf),
        "--output-dir", str(out_dir),
        "--pages", "999-1000",     # Out of range for a 6-page synthetic PDF
        "--theorem", "5.1",
        "--backend", "pymupdf",
        cwd=tmp_path,
    )
    assert res.returncode == 0, f"stderr: {res.stderr}"
    # Pages spec parsed to nothing — fallthrough message logged.
    assert "parsed to no valid pages" in res.stdout, res.stdout
    # Theorem branch took over.
    assert "Theorem 5.1 found on pages" in res.stdout, res.stdout


# ── Real-PDF regression: Shao's Mathematical Statistics (607 pages) ──
#
# Pinpoints the precision contract for `scan_pages_for_theorem` and
# `expand_with_dependencies` on a real textbook. Ground truth was
# established 2026-04-28 by running `Theorem N.M[.\(]` declaration-form
# regex across every page and reading the matched contexts (see session
# transcript). Each expected page index is the page where the SUFFIX-N.M.
# theorem is **declared** (not back-referenced).
#
# Skipped if the Shao PDF isn't present — the file is large (8MB) and
# may not be checked in to every clone.

SHAO_PDF = Path(__file__).resolve().parents[3] / "mathematical statistics.pdf"
SHAO_AVAILABLE = SHAO_PDF.exists()
shao_only = pytest.mark.skipif(
    not SHAO_AVAILABLE, reason=f"Shao PDF not present at {SHAO_PDF}"
)


# Ground truth: 0-indexed declaration page for each theorem. (1-indexed
# values commented for readability — Shao prints page numbers 1-indexed.)
SHAO_GROUND_TRUTH = {
    # Each entry: (kind, id) → expected_decl_pages_after_first_cluster_heuristic
    # i.e. first hit + strictly-adjacent hits + 1-page spill.
    ("Theorem", "3.9"):  [204, 205],         # p.205 + spill (p.206)
    ("Theorem", "3.8"):  [203, 204],         # p.204 + spill
    ("Theorem", "3.6"):  [199, 200],         # p.200 + spill (later hits 204, 431 are back-refs)
    ("Theorem", "3.7"):  [201, 202],         # p.202 + spill (later hit 204 is back-ref)
    ("Theorem", "3.10"): [205, 206],         # p.206 + spill (later hits 207, 208, 240 are back-refs / exercises)
    ("Theorem", "3.2"):  [181, 182],         # p.182 + spill (p.183 hit was a line-wrapped back-ref, dropped by boundary anchor)
    ("Theorem", "1.5"):  [42, 43],           # p.43 + spill (later hit 203 is back-ref)
    ("Theorem", "1.1"):  [28, 29],           # p.29 + spill (later hits 68/303/346 are back-refs / exercises)
    ("Theorem", "3.13"): [211, 212],         # p.212 (Watson-Royall) + spill p.213 (Example 3.19 starts there → truncated for citation extraction)
    ("Theorem", "3.14"): [213, 214],         # p.214 + spill p.215 (Theorem 3.15 starts there → truncated). Body cites nothing — Example 3.20 illustration follows but is a separate object.
    ("Theorem", "3.15"): [214, 215],         # p.215-216 (Horvitz-Thompson). Self-contained: proof uses basic probability + self-defined eqs (3.47)/(3.48), no external citations.
    ("Lemma",   "1.5"):  [68, 69],           # p.69 + spill (later hits 79/102 are back-refs)
    # Letter-prefixed assumptions, declared adjacently on Shao p.199-200.
    # Boundary anchor `[.!?:]\s+` rejects mid-paragraph line-wrap hits, so
    # the post-spill page is dropped (was p.201 inclusion via lenient `\n`).
    ("Assumption", "A1"): [198, 199],        # p.199 + spill
    ("Assumption", "A2"): [198, 199],        # p.199 + spill
    ("Assumption", "A3"): [198, 199],        # p.199 + spill
}


@shao_only
@pytest.mark.parametrize("kind,tid,expected", [
    (k, i, exp) for (k, i), exp in SHAO_GROUND_TRUTH.items()
])
def test_shao_scan_first_cluster_only(kind, tid, expected):
    """scan_pages_for_theorem must return ONLY the first declaration cluster.

    Shao's textbook back-references each theorem 5-15 times across chapters.
    The current loose regex returned 16 pages for Thm 3.9 (12% precision);
    the declaration-form + first-cluster heuristic should return exactly the
    declaration page + spill.
    """
    got = scan_pages_for_theorem(SHAO_PDF, tid, kind=kind)
    assert got == expected, (
        f"{kind} {tid}: expected {expected}, got {got}. "
        f"Diff: extra={set(got)-set(expected)}, missing={set(expected)-set(got)}"
    )


@shao_only
def test_shao_scan_kindless_returns_earliest_kind():
    """Kindless query returns the EARLIEST declaration of ANY kind, not
    Theorem-specifically. In Shao, `Example 3.9` is declared on p.186
    before `Theorem 3.9` on p.205 — the function correctly finds the
    earliest. Callers who specifically want Theorem must pass kind="Theorem"
    (or use the parse_theorem_arg helper which extracts kind from
    "Theorem 3.9" string input). main() does the parsing for the CLI flow."""
    got = scan_pages_for_theorem(SHAO_PDF, "3.9")
    assert got == [185, 186], f"got {got}"  # Example 3.9 on p.186 + spill


# ── parse_theorem_arg: kind extraction from --theorem string ────────


def test_parse_theorem_arg_extracts_kind_prefix():
    assert parse_theorem_arg("Theorem 3.9") == ("Theorem", "3.9")
    assert parse_theorem_arg("lemma S5") == ("Lemma", "S5")
    assert parse_theorem_arg("Thm 1.2") == ("Theorem", "1.2")
    assert parse_theorem_arg("Prop. 4.1") == ("Proposition", "4.1")
    assert parse_theorem_arg("Definition 2.3") == ("Definition", "2.3")


def test_parse_theorem_arg_bare_id_returns_none_kind():
    assert parse_theorem_arg("4.1") == (None, "4.1")
    assert parse_theorem_arg("S2") == (None, "S2")


def test_parse_theorem_arg_unrecognized_kind_returns_whole_as_id():
    """Foreign-language / unusual labels return the whole string as id and
    kind=None — fall through to kindless scan."""
    assert parse_theorem_arg("Hauptsatz 2") == (None, "Hauptsatz 2")


@shao_only
def test_shao_main_parses_theorem_arg_kind_prefix(tmp_path):
    """End-to-end: agent passes `--theorem "Theorem 3.9"` (with kind), main()
    parses kind and scans Theorem-only — returns p.205-206 not p.186-187
    (which would be Example 3.9)."""
    out_dir = tmp_path / "out"
    res = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--pdf", str(SHAO_PDF),
         "--output-dir", str(out_dir),
         "--theorem", "Theorem 3.9",
         "--backend", "pymupdf"],
        cwd=str(tmp_path), capture_output=True, text=True, timeout=60,
    )
    assert res.returncode == 0, f"stderr: {res.stderr}"
    # Expect Theorem 3.9 (p.205-206), NOT Example 3.9 (p.186-187).
    assert "Theorem 3.9 found on pages: [205, 206]" in res.stdout, res.stdout


@shao_only
def test_shao_scan_equation_3_25_locates_p198():
    """Regression for user-reported equation miss. `(3.25)` is the linear
    model declaration on Shao p.198 (idx 197), referenced by Theorem 3.6,
    3.7, 3.8, 3.9, 3.10 and Proposition 3.4 as `model (3.25)`."""
    pages = scan_pages_for_equation(SHAO_PDF, "3.25")
    assert pages == [197, 198], f"got {pages}"


@shao_only
def test_shao_expand_thm_3_10_pulls_equation_decl():
    """End-to-end: Theorem 3.10 references `model (3.25)`; expansion must
    include p.198 (idx 197) — the equation declaration page."""
    base = scan_pages_for_theorem(SHAO_PDF, "3.10", kind="Theorem")
    expanded, citations = expand_with_dependencies(
        SHAO_PDF, base, exclude_id="3.10", max_total_pages=30
    )
    cited_ids = {(k, i) for k, i in citations}
    assert ("Equation", "3.25") in cited_ids, f"missed (3.25); got {cited_ids}"
    assert 197 in expanded, (
        f"missing eq (3.25) decl page p.198 (idx 197) in expansion "
        f"{[p+1 for p in expanded]}"
    )


@shao_only
def test_shao_expand_thm_3_10_pulls_assumption_decl():
    """Regression for the missed-assumption bug user reported. Theorem 3.10
    references `assumption A3` (and surrounding body mentions A1, A2). The
    expansion must include the Assumption declaration cluster (p.199-201)
    so the agent has the regularity conditions in context, not just the
    theorem statement."""
    base = scan_pages_for_theorem(SHAO_PDF, "3.10", kind="Theorem")
    expanded, citations = expand_with_dependencies(
        SHAO_PDF, base, exclude_id="3.10", max_total_pages=30
    )
    cited_ids = {(k, i) for k, i in citations}
    assert ("Assumption", "A3") in cited_ids, f"missed A3; got {cited_ids}"
    # At least one page from the Assumption A3 declaration cluster (p.199-201).
    assert any(p in expanded for p in [198, 199, 200]), (
        f"missing Assumption A3 decl pages in expansion {[p+1 for p in expanded]}"
    )


@shao_only
def test_shao_expand_thm_3_9_stays_under_25_pages():
    """End-to-end: Thm 3.9 expansion must be small + must include real
    deps (Thm 3.6, 3.7) and exclude back-refs / next-theorem bleed."""
    base = scan_pages_for_theorem(SHAO_PDF, "3.9", kind="Theorem")
    expanded, citations = expand_with_dependencies(
        SHAO_PDF, base, exclude_id="3.9", max_total_pages=30
    )
    assert len(expanded) <= 25, (
        f"expansion blew up to {len(expanded)} pages (was 50 before refactor). "
        f"Pages: {[p+1 for p in expanded]}"
    )
    # Real deps (Thm 3.6, 3.7) — cited in Thm 3.9's proof body on p.205.
    for dep_kind, dep_id in [("Theorem", "3.6"), ("Theorem", "3.7")]:
        decl_pages = SHAO_GROUND_TRUTH[(dep_kind, dep_id)]
        assert any(p in expanded for p in decl_pages), (
            f"missing {dep_kind} {dep_id} decl pages {decl_pages} in expansion {expanded}"
        )
    # MUST NOT contain known noise pages:
    #  - p.432-433: Chapter 6 exercise restating Thm 3.6 (old loose regex pulled)
    #  - Thm 3.2 decl pages [181,182]: Thm 3.2 is cited only INSIDE Thm 3.10's body
    #    on p.206 spill (truncated by next-decl boundary), not by Thm 3.9 itself.
    assert 431 not in expanded and 432 not in expanded, (
        f"pulled Chapter 6 exercise pages (431/432); expanded = {[p+1 for p in expanded]}"
    )
    assert 181 not in expanded and 182 not in expanded, (
        f"pulled Thm 3.2 decl pages — these are Thm 3.10's deps bleeding from spill. "
        f"expanded = {[p+1 for p in expanded]}"
    )


@shao_only
def test_shao_thm_3_14_zero_citations_after_truncation():
    """Theorem 3.14 is followed by Example 3.20 on p.214, then Theorem 3.15
    on p.215. Truncation at both boundaries leaves only the Thm 3.14
    statement itself, which has no explicit theorem/equation citations.
    User confirmed (2026-04-28): Example 3.20 should NOT be pulled in as a
    Thm 3.14 dep — it's a separate object. Regression guard for over-eager
    truncation relaxation."""
    base = scan_pages_for_theorem(SHAO_PDF, "3.14", kind="Theorem")
    assert base == [213, 214], f"got {base}"
    expanded, citations = expand_with_dependencies(
        SHAO_PDF, base, exclude_id="3.14", max_total_pages=30
    )
    assert citations == [], f"unexpected citations: {citations}"
    assert expanded == [213, 214], f"unexpected expansion: {expanded}"


@shao_only
def test_shao_thm_3_13_dep_is_only_theorem_2_2():
    """User-reported regression: Thm 3.13 (Watson-Royall) cited only
    Theorem 2.2 in its proof body. Old code pulled Theorem 3.14 (next
    theorem on spill page p.214) and Equation 3.43 (inside Example 3.19
    on spill p.213) as false positives — both cured by:
      (a) boundary anchor `[.!?:]\\s+` rejecting line-wrapped back-refs
          → strict cluster shrinks from [211,212,213] to [211] only
      (b) per-page truncation at next-declaration boundary → Example 3.19
          on spill p.213 cuts citation extraction before Eq 3.43.
    """
    base = scan_pages_for_theorem(SHAO_PDF, "3.13", kind="Theorem")
    expanded, citations = expand_with_dependencies(
        SHAO_PDF, base, exclude_id="3.13", max_total_pages=30
    )
    # Real cite is Thm 2.2 only.
    cited_ids = {(k, i) for k, i in citations}
    assert ("Theorem", "2.2") in cited_ids, f"missing Thm 2.2; got {cited_ids}"
    # Must NOT contain Thm 3.14 (next theorem, on spill→spill page p.214 — old
    # cluster heuristic without the new boundary anchor pulled it).
    assert ("Theorem", "3.14") not in cited_ids, f"false positive Thm 3.14; got {cited_ids}"
    # Must NOT contain Eq 3.43 (declared inside Example 3.19 on spill p.213).
    assert ("Equation", "3.43") not in cited_ids, f"false positive Eq 3.43; got {cited_ids}"
    # Total expansion stays tiny.
    assert len(expanded) <= 6, f"expansion = {[p+1 for p in expanded]}"


# ── Real-PDF regression: hd.pdf (no-period assumption form + external refs) ──
#
# hd.pdf declares assumptions as `(A1) X1, ...` — paren + SPACE + capital,
# with NO period after the closing paren. Distinct from Cox's `(A1). For
# any...` form. The tier-1 path C must accept both forms while still
# rejecting equation labels `(S1)\n` (paren on own line, no same-line content).
#
# Skipped when hd.pdf isn't present.

HD_PDF = Path("/home/gavin/website/hd.pdf")
HD_AVAILABLE = HD_PDF.exists()
hd_only = pytest.mark.skipif(not HD_AVAILABLE, reason=f"hd.pdf not present at {HD_PDF}")


@hd_only
def test_hd_assumption_a1_paren_no_period_form():
    """hd.pdf p.8 declares `(A1) X1, . . . , Xn are i.i.d. ...` — paren
    immediately followed by space + capital letter, no period. Path C must
    accept this and return the declaration cluster (not fall through to
    tier-2 wide-net which returned 18 pages of back-refs)."""
    pages = scan_pages_for_theorem(HD_PDF, "A1", kind="Assumption")
    # First-cluster + 1-page spill. Cluster anchors at p.8 (idx 7).
    # Spill follows. Whatever the exact cluster span, it must be ≤ 4 pages
    # (small cluster, not 18-page wide-net).
    assert len(pages) <= 4, (
        f"path C didn't anchor on hd's no-period form — fell to tier-2 wide-net. "
        f"got {len(pages)} pages: {[p+1 for p in pages]}"
    )
    # Must include p.8 (idx 7) — the actual declaration page
    assert 7 in pages, f"missing p.8 declaration; got {[p+1 for p in pages]}"


@hd_only
def test_hd_assumption_b1_paren_no_period_form():
    """Same form as A1, declared on hd.pdf p.9 (idx 8)."""
    pages = scan_pages_for_theorem(HD_PDF, "B1", kind="Assumption")
    assert len(pages) <= 4, (
        f"got {len(pages)} pages: {[p+1 for p in pages]}"
    )
    assert 8 in pages, f"missing p.9 declaration; got {[p+1 for p in pages]}"


@hd_only
def test_hd_assumption_a1_no_wrap_continuation_false_positive():
    """Path C false positive: pymupdf text extraction wraps long sentences
    at column boundaries. On hd.pdf p.8 ends mid-sentence with `Under
    Assumption` (no terminal punct), which wraps to p.9 starting with
    `(A1) guarantees the existence...`. Path C's regex anchor `(?:^|\\n)`
    then matches this wrap-continuation `(A1)` as if it were a fresh
    declaration, polluting the cluster: A1 returns 3 pages [8, 9, 10]
    instead of [8] + 1 spill = [8, 9].

    Same problem on p.26 in Lemma 1's statement `... Under Assumption\\n
    (A1) and q ≪ √n, ...`.

    Fix: path C must reject the wrap-continuation case by checking the
    last content char before the match. Real declarations are preceded
    by sentence-terminating punctuation (`.!?:`) or paragraph break;
    wrap continuations are preceded by an alphanumeric character.
    Cross-page lookback strips the page-number footer before examining
    the previous page's content tail.
    """
    pages = scan_pages_for_theorem(HD_PDF, "A1", kind="Assumption")
    # First-cluster heuristic: only the real declaration on p.8 (idx 7),
    # plus 1-page spill = idx 8 (p.9). Wrap false positives on p.9 (top)
    # and p.26 (mid-statement) must NOT extend the cluster.
    assert pages == [7, 8], (
        f"path C wrap-continuation false positive — A1 should be [8, 9] "
        f"(decl + 1 spill), not {[p+1 for p in pages]}"
    )


@hd_only
def test_hd_assumption_b2_starts_with_math_symbol():
    """hd.pdf p.9 declares `(B2) |σ̂^2 ...` — paren + space + `|` (math
    symbol, not a letter). An earlier path-C trailer `[A-Z]` (which under
    IGNORECASE matches any letter, but never a math symbol) silently
    missed this declaration; tier-1 returned no hits and tier-2 wide-net
    was producing 7 pages of back-refs.

    Fix: trailer is `\\S` (any non-whitespace), so math-symbol-starting
    bodies are accepted while `(S1)\\n` equation labels (newline-only
    trailer) remain correctly rejected."""
    pages = scan_pages_for_theorem(HD_PDF, "B2", kind="Assumption")
    assert pages != [], (
        f"B2 declaration on p.9 missed because body starts with `|`. "
        f"path C must accept any non-whitespace trailer."
    )
    assert 8 in pages, f"missing p.9 declaration; got {[p+1 for p in pages]}"
    assert len(pages) <= 4, f"wide-net regression; got {[p+1 for p in pages]}"


@hd_only
def test_hd_external_theorem_4_returns_empty_with_kind():
    """`Theorem 4 in [18] by taking ǫ = 1/p therein.` — hd.pdf p.18 cites
    external bibliographic ref [18], not an in-paper theorem. The paper
    declares Proposition 4 (p.30), not Theorem 4. With kind=Theorem and
    no tier-1 strict hit, scanner must return [] rather than fall to
    tier-2 wide-net (which returned 37 pages = the entire paper)."""
    pages = scan_pages_for_theorem(HD_PDF, "4", kind="Theorem")
    assert pages == [], (
        f"external citation should fail-empty with kind given; got "
        f"{len(pages)} pages: {[p+1 for p in pages[:10]]}..."
    )


@hd_only
def test_hd_in_paper_proposition_4_with_kind_resolves():
    """Positive: hd.pdf DOES declare Proposition 4 on p.30 (idx 29).
    With kind=Proposition, scanner must find it via tier-1."""
    pages = scan_pages_for_theorem(HD_PDF, "4", kind="Proposition")
    assert 29 in pages, f"expected p.30 (Proposition 4 decl); got {[p+1 for p in pages]}"
    assert len(pages) <= 4


def test_kindless_query_still_uses_tier_2_fallback():
    """Negative regression: when the user calls scan_pages_for_theorem
    WITHOUT specifying kind, tier-2 wide-net must still fire (best-effort
    behavior for kindless queries). Only kind-given queries get the
    fail-empty treatment.

    Synthetic PDF with no theorem-form declaration but containing the
    bare id `7.7` in body text. Kindless tier-1 fails, tier-2 picks it up."""
    import pymupdf
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "kindless.pdf"
        doc = pymupdf.open()
        for txt in [
            "page 0 filler",
            "On this page we mention 7.7 in passing.",
            "page 2 filler",
        ]:
            page = doc.new_page()
            page.insert_text((50, 100), txt, fontsize=11)
        doc.save(str(out))
        doc.close()

        pages = scan_pages_for_theorem(out, "7.7")  # kind=None
        # Tier-2 fallback should fire and find p.1 (idx 1)
        assert 1 in pages, (
            f"tier-2 fallback should fire for kindless queries; got {pages}"
        )


# ── Real-PDF regression: Cox change-point (statement vs proof split) ──
#
# This paper defers proofs to a supplementary appendix far from the lemma
# statement — Lemma S1 is declared on p.14 but its `Proof of Lemma S1.`
# header is on p.47 (33-page gap), terminating at `Proof of Theorem 1.`
# on p.49. The original `scan_pages_for_theorem` heuristic ("first
# declaration cluster + 1 spill page") returns only [13, 14] (0-indexed)
# and structurally misses the proof body — a coverage gap that
# `scan_proof_span_for_theorem` exists to close.
#
# Skipped if the Cox PDF isn't present at the absolute path below. The
# file lives in the website repo (out-of-tree from statlean) so the
# absolute hardcoded path is the simplest portable option; alternative
# would be a symlink, which adds setup friction.

COX_PDF = Path(
    "/home/gavin/website/Functional_linear_Cox_regression_model_with_a_change_point_in_the_covariate.pdf"
)
COX_AVAILABLE = COX_PDF.exists()
cox_only = pytest.mark.skipif(
    not COX_AVAILABLE, reason=f"Cox PDF not present at {COX_PDF}"
)


@cox_only
def test_cox_lemma_s1_proof_span_far_from_declaration():
    """Cox paper has `Proof of Lemma S1.` on p.47 (idx 46), 33 pages after
    the declaration on p.14. The proof body spans p.47-49 (idx 46-48),
    terminated by `Proof of Theorem 1.` on p.49.

    Ground truth (verified 2026-04-28 by inspecting raw page text):
      idx 46 (p.47): proof header at offset 4632 — last ~1KB of page
      idx 48 (p.49): `Proof of Theorem 1.` at offset 863 — terminator
      idx 47 (p.48): pure proof body (LaTeX gibberish, no headers)

    Expected: [46, 47, 48]. The terminator page (idx 48) is INCLUDED
    because the previous proof's last sentences are on the same page —
    excluding it would drop the actual end of Lemma S1's proof.
    """
    pages = scan_proof_span_for_theorem(COX_PDF, "Lemma", "S1")
    assert pages == [46, 47, 48], (
        f"got {[p+1 for p in pages]} (expected p.47-49)"
    )


@cox_only
def test_cox_lemma_s1_proof_span_returns_empty_for_unknown_id():
    """`scan_proof_span_for_theorem` returning [] is a legitimate signal,
    not an error — many lemmas are stated without an in-paper proof
    (cited from another work). Caller composes statement + (maybe-empty)
    proof span as needed."""
    pages = scan_proof_span_for_theorem(COX_PDF, "Lemma", "S99")
    assert pages == []


@cox_only
def test_cox_lemma_s1_full_extraction_unions_decl_and_proof():
    """End-to-end: caller composes declaration cluster + proof span to
    get the complete `(statement, proof)` page set. Expected result:
    p.14 (decl) + p.15 (decl spill) + p.47-49 (proof span)."""
    decl = scan_pages_for_theorem(COX_PDF, "S1", kind="Lemma")
    proof = scan_proof_span_for_theorem(COX_PDF, "Lemma", "S1")
    full = sorted(set(decl) | set(proof))
    # Statement cluster
    assert 13 in full, f"missing p.14 (declaration); got {[p+1 for p in full]}"
    # Proof span
    assert 46 in full, f"missing p.47 (proof start); got {[p+1 for p in full]}"
    assert 48 in full, f"missing p.49 (proof end); got {[p+1 for p in full]}"
    # Must NOT pull in the second non-adjacent re-declaration on p.33
    # (Zhou et al. supplementary version). first-cluster heuristic on
    # `scan_pages_for_theorem` already excludes it; this guard ensures
    # `scan_proof_span_for_theorem` doesn't accidentally re-include it.
    assert 32 not in full, (
        f"unexpected p.33 (Zhou et al. re-declaration) in full set: {[p+1 for p in full]}"
    )


def test_proof_span_qed_terminator_synthetic():
    """Sanity check on terminator detection: when no `Proof of` header
    follows but a QED mark closes the proof, span should end at the QED
    page. Uses ``QED`` (plain ASCII) rather than ``∎`` because pymupdf's
    default font silently substitutes U+220E with U+00B7 (middle dot) on
    `insert_text`, which would mask the test from catching real regressions.
    Real PDFs render ``∎`` correctly; the regex covers both forms."""
    import pymupdf
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "qed.pdf"
        doc = pymupdf.open()
        for txt in [
            "Filler page 0.",
            "Lemma 1.1 (Test). For all x, P(x).",
            "Proof of Lemma 1.1. By induction on x. Base case: trivial.",
            "Inductive step: assume P(k). Then P(k+1) follows. QED",
            "Section 2: Applications. Various examples...",
        ]:
            page = doc.new_page()
            page.insert_text((50, 100), txt, fontsize=11)
        doc.save(str(out))
        doc.close()

        pages = scan_proof_span_for_theorem(out, "Lemma", "1.1")
        # Proof starts on idx 2, QED on idx 3 → span = [2, 3]
        assert pages == [2, 3], f"got {pages}"


@cox_only
def test_cox_lemma_s1_deps_truncate_at_next_proof_of():
    """Regression for `Proof of` boundary leak: when proof span page p.49
    contains both end-of-Lemma-S1-proof and start-of-`Proof of Theorem 1.`
    header, citation extraction must NOT pull `Theorem 1` from the next
    proof's header. `_truncate_at_next_declaration` must recognise
    ``Proof of <Kind> <id>`` as a boundary, not just ``<Kind> <id>.``.

    Real cites by Lemma S1's proof body are S2/S4/S5/S6 (other lemmas).
    Theorem 1 is the next proof, not a cite — false positive if leaked.
    """
    decl = scan_pages_for_theorem(COX_PDF, "S1", kind="Lemma")
    proof = scan_proof_span_for_theorem(COX_PDF, "Lemma", "S1")
    base = sorted(set(decl) | set(proof))
    expanded, citations = expand_with_dependencies(
        COX_PDF, base, exclude_id="S1", max_total_pages=30
    )
    cited_ids = {(k, i) for k, i in citations}
    # Real cites that should be present
    assert ("Lemma", "S5") in cited_ids, f"missing real cite Lemma S5; got {citations}"
    # False positive that must be suppressed by `Proof of` boundary truncation
    assert ("Theorem", "1") not in cited_ids, (
        f"false positive Theorem 1 (bled from `Proof of Theorem 1.` header on p.49); "
        f"got {citations}"
    )


@cox_only
def test_cox_assumption_bare_paren_declaration_form():
    """Cox declares its assumptions as `(A1). For any i = 1, ...` — bare
    paren, no `Assumption` kind word. The current `scan_pages_for_theorem`
    tier-1 strict regex requires `<kind> <id>.` form, so it falls through
    to tier-2 wide-net which returns 22 pages of back-refs (wrong).

    Fix: tier-1 must recognise bare-paren-with-period-trailing form for
    `Assumption|Condition|Hypothesis` kind. The period-plus-capital-letter
    trailer (`)\\.\\s+[A-Z]`) discriminates this from the equation label
    form `(S1)\\n` which has no period (handled by scan_pages_for_equation).
    """
    pages = scan_pages_for_theorem(COX_PDF, "A1", kind="Assumption")
    # Cox declares A1-A9 on p.13, A10 on p.14. Tier-1 first-cluster + spill
    # should return [12, 13] (idx) = p.13 + spill p.14, NOT 22 back-ref pages.
    assert pages == [12, 13], f"got {[p+1 for p in pages]}"


@cox_only
def test_cox_assumption_bare_paren_does_not_match_equation_label():
    """Negative regression: `(S1)` standing alone on its own line on
    Cox p.38 is the EQUATION label, not an assumption declaration. The
    bare-paren-with-period rule must require the trailing `\\.\\s+[A-Z]`
    sentence-start, which equation labels don't have."""
    # `S1` is a Lemma elsewhere; treat it as a hypothetical Assumption query
    # to probe that the equation label form is NOT matched.
    pages = scan_pages_for_theorem(COX_PDF, "S1", kind="Assumption")
    # No `(S1). For any...` declaration exists in Cox; should be empty
    # under tier-1 strict. Tier-2 wide-net would return many pages — that's
    # the failure mode we're guarding against. Empty (or tier-2 pure-id
    # fallback only on small PDFs) means the strict arm correctly
    # rejected the equation label as a declaration.
    # Accept empty OR tier-2 fallback that doesn't claim p.38 specifically
    # as an Assumption declaration page. p.38 must NOT be in any
    # tier-1 strict cluster.
    # Simpler check: result must NOT be exactly [37, 38] (the equation
    # label location pattern that strict-with-no-period would produce).
    assert pages != [37, 38], (
        f"bare-paren rule wrongly matched equation label (S1) on p.38: got {pages}"
    )


@cox_only
def test_cox_theorem_1_pulls_assumption_range_from_statement():
    """End-to-end Cox Theorem 1 case: statement on p.15-16 says `Under
    Assumptions (A1)–(A10), ...`. The dep expansion must surface A1 and
    A10 as Assumption citations and pull their declaration pages.

    The Cox paper declares (A1)–(A10) contiguously around p.7-8 (per
    inspection); endpoint-only extraction lands those pages naturally.
    """
    decl = scan_pages_for_theorem(COX_PDF, "1", kind="Theorem")
    proof = scan_proof_span_for_theorem(COX_PDF, "Theorem", "1")
    base = sorted(set(decl) | set(proof))
    expanded, citations = expand_with_dependencies(
        COX_PDF, base, exclude_id="1", max_total_pages=30
    )
    cited_ids = {(k, i) for k, i in citations}
    assert ("Assumption", "A1") in cited_ids, (
        f"missed A1 endpoint of `Assumptions (A1)–(A10)` from Theorem 1 statement; "
        f"got {citations}"
    )
    assert ("Assumption", "A10") in cited_ids, (
        f"missed A10 endpoint; got {citations}"
    )


@cox_only
def test_cox_lemma_s1_has_two_declaration_clusters():
    """Cox `Lemma S1` is declared TWICE: p.14 in the main paper, p.33 in
    the supplementary as a re-statement citing Zhou et al. (2023). They
    state different things — the supplementary version uses (A8)–(A10)
    only — so a user investigating the paper might want to see both.

    `scan_pages_for_theorem` returns the first cluster (canonical paper-
    intent declaration). `find_all_declaration_clusters` exposes both so
    the CLI can warn the user about the alternative.
    """
    clusters = find_all_declaration_clusters(COX_PDF, "S1", kind="Lemma")
    assert len(clusters) == 2, (
        f"expected 2 clusters (p.14 + p.33), got {len(clusters)}: {clusters}"
    )
    # First cluster anchors at p.14 (idx 13)
    assert 13 in clusters[0], f"expected p.14 in first cluster; got {clusters[0]}"
    # Second cluster anchors at p.33 (idx 32)
    assert 32 in clusters[1], f"expected p.33 in second cluster; got {clusters[1]}"


@cox_only
def test_cox_theorem_1_has_single_cluster():
    """Cox Theorem 1 is declared exactly once on p.16 — single cluster."""
    clusters = find_all_declaration_clusters(COX_PDF, "1", kind="Theorem")
    assert len(clusters) == 1, f"expected 1 cluster; got {clusters}"


def test_find_all_clusters_returns_empty_when_no_strict_hit():
    """When the strict tier-1 regex finds no declaration anywhere, the
    function returns [] — distinct from "1 cluster of 0 pages" (which is
    not a thing). Caller distinguishes via len(result) == 0."""
    import pymupdf
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "no_thm.pdf"
        doc = pymupdf.open()
        for txt in ["Just some text.", "More filler.", "Nothing relevant."]:
            page = doc.new_page()
            page.insert_text((50, 100), txt, fontsize=11)
        doc.save(str(out))
        doc.close()

        clusters = find_all_declaration_clusters(out, "999", kind="Theorem")
        assert clusters == []


@cox_only
def test_main_warns_on_multi_cluster_lemma_s1(tmp_path, capsys):
    """End-to-end: `python3 pdf_extract.py --theorem "Lemma S1" ...` must
    surface an informational note that 2 declaration clusters exist.
    The note is a stdout `[pdf-extract] note: ...` line so the agent's
    tool_result captures it without scraping stderr separately.
    """
    out_dir = tmp_path / "out"
    res = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--pdf", str(COX_PDF),
         "--output-dir", str(out_dir),
         "--theorem", "Lemma S1",
         "--backend", "pymupdf"],
        cwd=str(tmp_path), capture_output=True, text=True, timeout=60,
    )
    assert res.returncode == 0, f"stderr: {res.stderr}"
    # The note should mention that S1 has 2 clusters and list both pages.
    assert "note:" in res.stdout.lower(), (
        f"missing multi-cluster note in stdout; got:\n{res.stdout}"
    )
    assert "2 non-adjacent" in res.stdout or "2 cluster" in res.stdout.lower(), (
        f"note didn't mention cluster count; got:\n{res.stdout}"
    )
    # And the page numbers should appear (1-indexed: 14 and 33)
    assert "14" in res.stdout and "33" in res.stdout, (
        f"note didn't mention p.14 or p.33; got:\n{res.stdout}"
    )


@cox_only
def test_main_no_warning_on_single_cluster_theorem_1(tmp_path):
    """Negative regression: Theorem 1 is declared exactly once. No
    multi-cluster note should appear (otherwise it'd be noise on the
    common path)."""
    out_dir = tmp_path / "out"
    res = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--pdf", str(COX_PDF),
         "--output-dir", str(out_dir),
         "--theorem", "Theorem 1",
         "--backend", "pymupdf"],
        cwd=str(tmp_path), capture_output=True, text=True, timeout=60,
    )
    assert res.returncode == 0, f"stderr: {res.stderr}"
    # No multi-cluster note. The "Theorem 1 found on pages: ..." line is
    # fine; only `note: ... clusters` would indicate the warning fired.
    assert "non-adjacent declaration clusters" not in res.stdout, (
        f"unexpected multi-cluster note for single-cluster theorem; got:\n{res.stdout}"
    )


def test_proof_span_caps_at_max_span_pages():
    """Pathological case: no terminator within max_span_pages → cap to
    `start_page + max_span_pages`. Default 4 pages — proofs rarely
    exceed this without a terminator surfacing."""
    import pymupdf
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "long.pdf"
        doc = pymupdf.open()
        # 8 pages, proof starts on page 0, no QED, no next 'Proof of'
        for i in range(8):
            page = doc.new_page()
            txt = (
                "Proof of Lemma 1.1. By construction..."
                if i == 0
                else f"Continuing the argument from page {i-1}..."
            )
            page.insert_text((50, 100), txt, fontsize=11)
        doc.save(str(out))
        doc.close()

        pages = scan_proof_span_for_theorem(out, "Lemma", "1.1", max_span_pages=4)
        # Span = start (idx 0) + 4 next pages = [0, 1, 2, 3, 4]
        assert pages == [0, 1, 2, 3, 4], f"got {pages}"

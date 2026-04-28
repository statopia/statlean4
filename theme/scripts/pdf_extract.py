#!/usr/bin/env python3
"""Extract theorems from PDF → structured LaTeX.

Backends:
    pymupdf    — fast, local, no API cost (default for all modes)
    claude-api — most accurate, uses Claude API (requires ANTHROPIC_API_KEY, costs credits)
    openai-api — uses OpenAI API (requires OPENAI_API_KEY, costs credits)
    mineru     — MinerU OCR + VLM (requires local GPU or heavy CPU)

pymupdf extracts raw text; Claude Code can post-process in-session to restore LaTeX.

Usage:
    # Full PDF extraction (pymupdf, fast, zero cost)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir>

    # Extract only specific pages
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --pages 5-8

    # Extract a specific theorem (auto-finds the page)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --theorem "4.1"

    # Search by keyword (finds pages containing the keyword, sends only those)
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir> --query "consistency of MLE"
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Optional, Tuple


# ── Common statistics notation defaults ──
DEFAULT_NOTATION = {
    "symbols": {
        r"\mathbb{E}": "expectation",
        r"\operatorname{E}": "expectation",
        r"\operatorname{Var}": "variance",
        r"\mathbb{V}": "variance",
        r"\operatorname{Cov}": "covariance",
        r"\mathbb{P}": "probability",
        r"\operatorname{P}": "probability",
        r"\mathcal{N}": "normal distribution",
        r"\sim": "distributed as",
        r"\perp": "independent",
        r"\mid": "conditional",
        r"\mathbb{R}": "real numbers",
        r"\mathbb{Z}": "integers",
        r"\mathbb{N}": "natural numbers",
        r"\nabla": "gradient",
        r"\partial": "partial derivative",
        r"\int": "integral",
        r"\sum": "summation",
        r"\prod": "product",
        r"\sup": "supremum",
        r"\inf": "infimum",
        r"\lim": "limit",
        r"\log": "logarithm",
        r"\exp": "exponential",
        r"\|": "norm delimiter",
        r"\lfloor": "floor",
        r"\lceil": "ceiling",
    }
}


# ── Theorem-like block detection ──
THEOREM_KEYWORDS = [
    "theorem", "lemma", "corollary", "proposition",
    "definition", "remark", "example", "conjecture",
]
PROOF_KEYWORDS = ["proof", "proof sketch", "proof outline"]

THEOREM_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(THEOREM_KEYWORDS) + r")"
    r"\s*(\d+(?:\.\d+)*)?\s*"
    r"(?:\(([^)]*)\))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)

PROOF_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(PROOF_KEYWORDS) + r")"
    r"\s*(?:of\s+(?:theorem|lemma|corollary|proposition)\s*(\d+(?:\.\d+)*))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)


# ═══════════════════════════════════════════════════════════
# Page scanning: find relevant pages (fast, local)
# ═══════════════════════════════════════════════════════════

def scan_pages_for_keyword(pdf_path: Path, keyword: str) -> List[int]:
    """Scan PDF text to find pages containing the keyword. Returns 0-indexed page numbers."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    matching_pages = []
    keyword_lower = keyword.lower()
    for i in range(len(doc)):
        text = doc[i].get_text().lower()
        if keyword_lower in text:
            matching_pages.append(i)
    doc.close()
    return matching_pages


def _strict_scan_hits(doc, theorem_id: str, kind: Optional[str]) -> List[int]:
    """Internal: page indices matching tier-1 STRICT declaration patterns.

    No clustering, no spill, no tier-2 fallback. Used by both
    `scan_pages_for_theorem` (which then takes [first_cluster] + spill) and
    `find_all_declaration_clusters` (which clusters and returns all). The
    three regex arms (A: strict-leading, B: loose-leading + strict trailing,
    C: bare-paren-with-period for assumption-like kinds) match the same
    declaration shapes documented in `scan_pages_for_theorem`'s docstring.

    `doc` is an already-opened pymupdf document; caller manages the
    open/close lifecycle.
    """
    all_keywords = THEOREM_KEYWORDS + ["example", "remark", "conjecture"]
    kind_alt_loose = "|".join(
        all_keywords + ["thm", "lem", "cor", "prop", "def", "ex", "rem"]
    )
    kind_alt = re.escape(kind) if kind else kind_alt_loose

    escaped = re.escape(theorem_id)
    end_anchor = r"(?!\d|\.\d)"

    strict_re = re.compile(
        rf"(?:^|[\.\!?:]\s+)\b(?:{kind_alt})\s+{escaped}{end_anchor}\s*[\.\(:]",
        re.IGNORECASE,
    )
    loose_decl_re = re.compile(
        rf"\n\s*\b(?:{kind_alt})\s+{escaped}{end_anchor}\s*"
        rf"(?:\([^\)]{{4,}}\)|\.\s+[A-Z]|:\s+[A-Z])",
        re.IGNORECASE,
    )
    # Path C: bare-paren declaration form `(<id>) <body>` for
    # Assumption / Condition / Hypothesis kinds. Two-stage detection:
    #
    #  Stage 1 (regex): line-anchored paren + same-line content.
    #    `(?:^|\n)\s*\(<id>\)[ \t]*[\.:]?[ \t]+\S`
    #    `[ \t]+\S` forbids the `(S1)\n` equation-label form (newline
    #    immediately after paren = no same-line content).
    #
    #  Stage 2 (line-walk): wrap-continuation rejection. pymupdf wraps
    #    long sentences at column boundaries, so a body sentence like
    #    "...Under Assumption\n(A1) guarantees..." surfaces with `(A1)`
    #    at line start — stage 1's regex would falsely accept it. We
    #    inspect the last meaningful char before the match: real
    #    declarations are preceded by sentence-terminating punctuation
    #    (`.!?:`) or paragraph break (empty); wrap continuations are
    #    preceded by alphanumeric content. Cross-page lookback is
    #    required because the wrap may span the page boundary (hd p.8
    #    ends with "Assumption", p.9 starts with "(A1) guarantees").
    #
    # Real-paper body variants observed:
    #   - Cox `(A1). For any X1...` — period + space + body
    #   - hd  `(A1) X1, ...`        — space + body (no period)
    #   - hd  `(A2) max1≤i≤n ...`   — space + lowercase
    #   - hd  `(B2) |σ̂^2 ...`       — space + math symbol
    bare_paren_active = (
        kind is not None and kind.lower() in ("assumption", "condition", "hypothesis")
    )
    bare_paren_re: Optional[re.Pattern[str]] = None
    if bare_paren_active:
        bare_paren_re = re.compile(
            rf"(?:^|\n)\s*\(\s*{escaped}{end_anchor}\s*\)[ \t]*[\.:]?[ \t]+\S",
            re.IGNORECASE,
        )

    hits: List[int] = []
    prev_page_text: Optional[str] = None
    for i in range(len(doc)):
        text = doc[i].get_text()
        page_hit = (
            strict_re.search(text) is not None
            or loose_decl_re.search(text) is not None
        )
        if not page_hit and bare_paren_active and bare_paren_re is not None:
            page_hit = _has_bare_paren_decl(text, bare_paren_re, prev_page_text)
        if page_hit:
            hits.append(i)
        prev_page_text = text
    return hits


def _last_content_char(text: str) -> Optional[str]:
    """Last meaningful non-whitespace char of `text`, skipping a trailing
    page-number footer (a final line containing only digits). Used by
    path C to inspect the previous page's content tail when a match
    falls at the top of the current page (no in-page predecessor).

    Returns None when text has no content at all (entirely whitespace
    or only a page-number footer).
    """
    lines = text.rstrip().split("\n")
    while lines and lines[-1].strip().isdigit():
        lines.pop()
    while lines and not lines[-1].strip():
        lines.pop()
    if not lines:
        return None
    last = lines[-1].rstrip()
    return last[-1] if last else None


def _has_bare_paren_decl(
    text: str,
    pattern: re.Pattern[str],
    prev_page_text: Optional[str],
) -> bool:
    """Path C wrap-continuation rejection: does at least one `pattern`
    match in `text` correspond to a real declaration, not a wrap
    continuation of an earlier sentence?

    A match qualifies as a real declaration when the last meaningful
    character before it is sentence-terminating punctuation (`.!?:`)
    or there is no preceding content (paragraph break / doc start).
    A match disqualifies (treated as wrap continuation) when the
    preceding content's last char is alphanumeric — that means an
    earlier sentence wrapped onto this paren-leading line.

    `prev_page_text` provides cross-page lookback for matches at the
    top of the page (where in-page predecessor is empty).
    """
    for m in pattern.finditer(text):
        before = text[: m.start()]
        # Walk back to last non-whitespace char in this page.
        idx = len(before) - 1
        while idx >= 0 and before[idx].isspace():
            idx -= 1
        if idx >= 0:
            trail: Optional[str] = before[idx]
        elif prev_page_text is not None:
            trail = _last_content_char(prev_page_text)
        else:
            trail = None  # truly at doc start

        if trail is None or trail in ".!?:":
            return True
        # else: alpha/digit/other — wrap continuation, try next match
    return False


def _cluster_strict_hits(strict_hits: List[int]) -> List[List[int]]:
    """Group strictly-adjacent (gap ≤ 1) page indices into clusters.

    Each declaration of a theorem typically spans 1-2 pages (statement
    page + spill); a 1-page gap between hits is normal. A gap > 1 means
    we've hit a different declaration of the same id elsewhere — a
    re-declaration in another chapter (rare but real, e.g. Cox change-
    point's `Lemma S1` is declared on p.14 in main paper AND on p.33 as
    a re-statement citing Zhou et al. in the supplementary).
    """
    if not strict_hits:
        return []
    clusters: List[List[int]] = [[strict_hits[0]]]
    for p in strict_hits[1:]:
        if p - clusters[-1][-1] <= 1:
            clusters[-1].append(p)
        else:
            clusters.append([p])
    return clusters


def find_all_declaration_clusters(
    pdf_path: Path,
    theorem_id: str,
    kind: Optional[str] = None,
) -> List[List[int]]:
    """All tier-1 strict declaration clusters of `(kind, theorem_id)`.

    Public companion to `scan_pages_for_theorem` for callers (notably the
    CLI's main()) that need to know whether a query has more than one
    declaration cluster and where they live. `scan_pages_for_theorem`
    returns only the FIRST cluster (the canonical paper-intent declaration);
    this returns ALL clusters so the caller can warn the user / agent
    about possible re-declarations they may want to inspect with an
    explicit `--pages <range>` follow-up.

    Each cluster is a list of consecutive 0-indexed pages. Returns ``[]``
    when no strict-declaration hit is found anywhere (caller may then
    fall back to interpreting an empty result as "not declared in this
    paper" or proceed to tier-2 / external-reference handling).
    """
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    try:
        return _cluster_strict_hits(_strict_scan_hits(doc, theorem_id, kind))
    finally:
        doc.close()


def scan_pages_for_theorem(
    pdf_path: Path,
    theorem_id: str,
    *,
    kind: Optional[str] = None,
) -> List[int]:
    r"""Find the page(s) where a specific theorem is **declared**.

    Two-tier strategy, from first principles about how math PDFs render
    declarations vs references:

      Tier 1 — declaration form: ``<Kind> <id>[.(:]``
        Real declarations end in a heading marker (period for sentence-form
        ``Theorem 3.9.``, paren for named-form ``Theorem 3.9 (Name)``, colon
        for block-form). Real references typically end with ``,`` / no punct
        (``by Theorem 3.9, we have...``). When tier 1 hits, returns ONLY the
        first contiguous cluster of strictly-adjacent hits, plus 1 page of
        proof spill. Theorems are declared once; later isolated hits with
        the same id are back-refs from other chapters.

      Tier 2 — loose fallback: ``<Kind>.?\s*<id>`` plus bare-id ``\b<id>\b``
        Used only when tier 1 finds nothing AND ``kind`` is None (kindless
        best-effort). When kind is given, tier-1's three arms (A/B/C) cover
        every reasonable declaration form on real papers; if they still fail,
        the citation is overwhelmingly likely external (e.g.
        ``Theorem 4 in [18]`` referencing a bibliographic ref) and tier-2
        wide-net would return dozens of pages of garbage. So kind-given
        tier-1 miss returns ``[]`` — caller distinguishes "not in this paper"
        from "found here". Tier-2 is preserved for kindless queries because
        the user/agent there asked for a best-effort scan.

    ``kind`` (e.g. ``"Theorem"``, ``"Lemma"``) restricts both tiers to that
    specific theorem kind. Without it, all theorem-like keywords are tried
    in a single alternation — kindless query then returns the EARLIEST
    declaration of any kind (in Shao that's Example 3.9 on p.186, not
    Theorem 3.9 on p.205). Pass kind when you have it (citations include
    it; main() parses it from the ``--theorem`` arg).

    The end-anchor ``(?!\d|\.\d)`` rejects sub-numbered ids: when looking
    for ``3.1``, the regex won't match ``3.1.2`` or ``3.15``.
    """
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    try:
        strict_hits = _strict_scan_hits(doc, theorem_id, kind)

        if strict_hits:
            clusters = _cluster_strict_hits(strict_hits)
            cluster = clusters[0]
            result = list(cluster)
            # 1-page proof spill after the last page of the cluster.
            if cluster[-1] + 1 < len(doc):
                result.append(cluster[-1] + 1)
            return sorted(set(result))

        # Kind-given strict miss: caller specified an exact target, tier-1
        # covers all reasonable declaration shapes, and we still found
        # nothing — the citation is almost certainly external. Fail-empty
        # so the caller knows "not here" rather than receiving 30+ pages
        # of bare-id back-references via tier-2 wide-net.
        if kind:
            return []

        all_keywords = THEOREM_KEYWORDS + ["example", "remark", "conjecture"]
        kind_alt_loose = "|".join(
            all_keywords + ["thm", "lem", "cor", "prop", "def", "ex", "rem"]
        )
        kind_alt = re.escape(kind) if kind else kind_alt_loose
        escaped = re.escape(theorem_id)
        end_anchor = r"(?!\d|\.\d)"

        # Tier 2: loose fallback when strict found nothing.
        # Original wide-net behavior preserved — this is the OCR-failed-heading
        # / unusual-format escape hatch. On big PDFs without a tier-1 hit, the
        # user is already in trouble: main() will then fail closed for >15-page
        # PDFs (see SystemExit in main()), so the noise here is bounded.
        loose_re = re.compile(
            rf"(?:{kind_alt})\.?\s*{escaped}{end_anchor}",
            re.IGNORECASE,
        )
        bare_re = re.compile(rf"\b{escaped}{end_anchor}", re.IGNORECASE)
        matching: List[int] = []
        for i in range(len(doc)):
            text = doc[i].get_text()
            if loose_re.search(text) or bare_re.search(text):
                matching.append(i)
                if i + 1 < len(doc):
                    matching.append(i + 1)
        return sorted(set(matching))
    finally:
        doc.close()


_KIND_ARG_CANON = {
    "theorem": "Theorem", "thm": "Theorem",
    "lemma": "Lemma", "lem": "Lemma",
    "proposition": "Proposition", "prop": "Proposition",
    "corollary": "Corollary", "cor": "Corollary",
    "definition": "Definition", "def": "Definition",
    "assumption": "Assumption",
    "example": "Example", "ex": "Example",
    "remark": "Remark", "rem": "Remark",
    "conjecture": "Conjecture",
}


def parse_theorem_arg(arg: str) -> Tuple[Optional[str], str]:
    """Parse `--theorem <arg>` into (kind, id).

    Accepts:
      "Theorem 3.9"   → ("Theorem", "3.9")
      "lemma S5"      → ("Lemma", "S5")
      "Thm 1.2"       → ("Theorem", "1.2")
      "Prop. 4.1"     → ("Proposition", "4.1")
      "4.1"           → (None, "4.1")          ← bare id, kindless
      "Hauptsatz 2"   → (None, "Hauptsatz 2")  ← unrecognized, treat whole as id

    Rationale: `scan_pages_for_theorem(pdf, id, kind=<X>)` restricts the scan
    to that specific kind, so `Example 3.9` won't shadow `Theorem 3.9` (this
    matters in textbooks where the same numeric id is used across kinds —
    Shao has Example 3.9 on p.186 AND Theorem 3.9 on p.205).
    """
    pattern = "|".join(_KIND_ARG_CANON.keys())
    m = re.match(rf"^\s*({pattern})\s*\.?\s*(\S+)\s*$", arg, re.IGNORECASE)
    if m:
        return _KIND_ARG_CANON[m.group(1).lower()], m.group(2)
    return None, arg.strip()


def scan_proof_span_for_theorem(
    pdf_path: Path,
    kind: Optional[str],
    theorem_id: str,
    *,
    max_span_pages: int = 4,
) -> List[int]:
    r"""Find the page range of a ``Proof of <kind> <id>.`` block.

    Distinct from ``scan_pages_for_theorem`` (which locates the *declaration*).
    Statistical papers commonly defer proofs to a supplementary appendix far
    from the lemma statement — Cox change-point paper has Lemma S1 declared
    on p.14 but proved on p.47-49. The "first declaration cluster + 1 spill"
    heuristic in scan_pages_for_theorem misses that proof entirely. This
    function returns the proof-body span as a separate concept.

    Anchor: ``(?:^|\n)\s*Proof\s+of\s+<kind>\s+<id>(?:\(...\))?\s*[.:]`` —
    sentence-start leading + declarative trailing, optional parenthesised
    name between id and terminator (``Proof of Theorem 5.1 (Continuity).``).

    Span end signals (any of):
      - Next ``Proof of`` header on a downstream page
      - ``∎`` / ``□`` / ``QED`` / ``Q.E.D.`` mark on any subsequent page
      - ``max_span_pages`` cap (default 4 — proofs rarely exceed without a
        terminator surfacing; cap guards against runaway on malformed PDFs)

    The terminator page is INCLUDED in the result. Rationale: when the next
    ``Proof of`` header starts mid-page, the previous proof's last sentences
    sit on the same page (Cox p.49 = end of Lemma S1 proof + start of
    Proof of Theorem 1). Excluding it would drop those sentences.

    Returns ``[]`` when no anchor is found. This is a legitimate signal —
    the paper may state the lemma without proof (cited from another work);
    callers must not treat empty as error.

    ``kind=None`` falls back to scanning all theorem-like keywords. Pass an
    explicit kind whenever known to avoid pathological cross-kind matches
    (``Proof of Example 3.9`` shouldn't match a query for ``Theorem 3.9``).
    """
    import pymupdf

    escaped_id = re.escape(theorem_id)
    end_anchor = r"(?!\d|\.\d)"  # rejects 3.1.2 / 3.15 when looking for 3.1
    if kind:
        kind_alt = re.escape(kind)
    else:
        all_kw = THEOREM_KEYWORDS + ["example", "remark", "conjecture"]
        kind_alt = "|".join(
            all_kw + ["thm", "lem", "cor", "prop", "def", "ex", "rem"]
        )

    # Anchor: declarative leading + optional named-theorem parens + closer.
    # `(?:\([^)]*\))?` permits "Proof of Theorem 5.1 (Continuity)." form.
    proof_start_re = re.compile(
        rf"(?:^|\n)\s*Proof\s+of\s+(?:{kind_alt})\s+{escaped_id}{end_anchor}"
        rf"\s*(?:\([^)]*\))?\s*[\.:]",
        re.IGNORECASE,
    )
    # Terminator: any subsequent "Proof of <something> <id>" header — kind
    # is unconstrained because *any* next proof ends the current span.
    # `\S+` for id captures "S1" / "1.5" / "3.4.1" / "A3" uniformly.
    next_proof_re = re.compile(
        r"(?:^|\n)\s*Proof\s+of\s+\w+\s+\S+\s*(?:\([^)]*\))?\s*[\.:]",
        re.IGNORECASE,
    )
    qed_re = re.compile(r"[∎□]|\bQED\b|\bQ\.E\.D\.")

    doc = pymupdf.open(str(pdf_path))
    try:
        # 1. Locate the start page + character offset of THIS proof.
        start_page = -1
        start_offset = -1
        for i in range(len(doc)):
            text = doc[i].get_text()
            m = proof_start_re.search(text)
            if m:
                start_page = i
                start_offset = m.end()
                break
        if start_page < 0:
            return []

        # 2. In-page terminator: same page contains the proof end (rare for
        # appendix-style papers but possible for short proofs). Slice to the
        # text AFTER this proof's start anchor so we don't self-terminate.
        first_text = doc[start_page].get_text()
        post_start = first_text[start_offset:]
        if next_proof_re.search(post_start) or qed_re.search(post_start):
            return [start_page]

        # 3. Walk forward up to max_span_pages, accumulating pages until a
        # terminator surfaces or the cap is hit. Terminator page included
        # (see docstring rationale).
        result = [start_page]
        for i in range(
            start_page + 1, min(start_page + max_span_pages + 1, len(doc))
        ):
            text = doc[i].get_text()
            result.append(i)
            if next_proof_re.search(text) or qed_re.search(text):
                break
        return result
    finally:
        doc.close()


def parse_page_range(page_spec: str, total_pages: int) -> List[int]:
    """Parse page range like '1-5,8,10-12' into 0-indexed page list."""
    pages = set()
    for part in page_spec.split(","):
        part = part.strip()
        if "-" in part:
            start, end = part.split("-", 1)
            start = max(1, int(start))
            end = min(total_pages, int(end))
            pages.update(range(start - 1, end))  # convert to 0-indexed
        else:
            p = int(part)
            if 1 <= p <= total_pages:
                pages.add(p - 1)
    return sorted(pages)


# ── Citation extraction (for --include-deps) ──────────────────────
#
# Anchors restricted to explicit math-citation phrases. We deliberately
# skip bare equation refs `(2.6)` because those collide with theorem ids
# and produce too many false positives. Likewise skip vague references
# like "the previous lemma" / "above" — they require structural parsing
# we don't have.

_DEP_KIND_EN = (
    r"Lemma|Theorem|Proposition|Corollary|Definition|Assumption|Hypothesis|Conjecture"
)
_DEP_KIND_ZH = r"引理|定理|命题|推论|定义|假设|猜想"
_DEP_VERB_EN = r"by|via|from|using|applying|per|invoke|invokes|invoking|see"
_DEP_VERB_ZH = r"由|根据|应用|利用|参见"
# ID forms covered (from inspecting real papers):
#   - chapter.theorem:   3.9, 3.4.1
#   - appendix style:    A3, A.1, B.1, S5, S2.3 (S = supplementary; common
#                        in stat papers; `A.1` and `B.1` use a dot between
#                        letter and number)
#   - assumption refs:   A1, A2, A3 (Shao Theorem 3.8/3.9/3.10 reference these)
# Optional `[A-Z]\.?` prefix then digits, then 0-3 `.digit` segments. Won't
# match Roman numerals (IV.2 — rare) or sub-letter suffixes (3.9a — the
# bare-digit core matches and trailing letter is lost).
_DEP_ID = r"(?:[A-Z]\.?)?\d+(?:\.\d+){0,3}"

# Same id, optionally wrapped in ASCII parens. Used inside kind-anchored
# citation captures where `Assumption (A3)` and `Assumption A3` should
# parse identically. Kept distinct from `_DEP_ID` because the bare-paren
# form must NOT be matched outside a kind anchor — `(2.6)` standing alone
# is the equation declaration form, handled by `scan_pages_for_equation`.
_DEP_ID_PARENS = rf"\(?{_DEP_ID}\)?"

# Range / list separators between ids inside one citation:
#   - `,` `and` `&` `or` — list form (existing behavior)
#   - `–` (U+2013 EN DASH) — typographically correct for ranges, what real
#     papers print (Cox change-point: `Assumptions (A1)–(A10)`)
#   - `—` (U+2014 EM DASH) — alternative typesetting convention
#   - `-` (ASCII hyphen) — what OCR sometimes emits when the en/em dash is
#     mis-recognized; accepted because the kind anchor already bounds the
#     match to citation context (no risk of matching unrelated `2-3`).
# Range expansion convention: take ENDPOINTS only. Assumption / lemma
# blocks declare contiguously in real papers, so the declaration pages of
# A1 and A10 cover A2–A9 via the natural page-set union — cheaper and
# avoids letter-sequence enumeration edge cases (A.1.2–A.1.7 etc.).
# Order matters: regex alternation matches left-to-right, first-success.
# `,\s*and` must be tried BEFORE bare `,` so `2.1, 2.3, and 2.5` parses as
# four-id list (Oxford comma) rather than truncating at `2.3` because the
# bare `,` matched but `and 2.5` doesn't begin with a valid id.
_RANGE_OR_LIST_SEP_EN = r"(?:,\s*and|,|and|&|or|–|—|-)"
_RANGE_OR_LIST_SEP_ZH = r"(?:,|，|和|与|及|至|到|–|—|-)"

# English: `by Lemma 2.1`, `via Theorems 1.5 and 1.6`, `using Assumption A.1`,
# bare `Definition 1.1` (when conjoined like "...Lemma 2.1 and Definition 1.1").
# Verb anchor optional: dropping it lets the second clause of a conjoined
# citation match (the leading verb only attaches to the first noun phrase).
# False-positive risk is bounded by `exclude_id` for self-references and by
# the scan_pages_for_theorem step that requires the cited id to exist as a
# theorem-like declaration *somewhere* in the PDF.
# Capturing groups: (1) kind, (2) ids-blob — we then extract every \d+(\.\d+)*
# from the blob to handle both `Lemmas 2.3 and 2.4` (list) and
# `Lemmas 2.3–2.5` (range, endpoints only via _ID_PICK_RE iteration).
_CITATION_EN_RE = re.compile(
    rf"\b(?:(?:{_DEP_VERB_EN})\s+)?(?P<kind>{_DEP_KIND_EN})s?\b\s*"
    rf"(?P<ids>{_DEP_ID_PARENS}(?:\s*{_RANGE_OR_LIST_SEP_EN}\s*{_DEP_ID_PARENS})*)",
    re.IGNORECASE,
)
# Chinese: `由引理 2.1`, `根据定理 5.1 和 5.2`. No leading verb required when the
# pair appears as a noun phrase (e.g. "由引理2.1可知"). Ids may be CJK-attached.
_CITATION_ZH_RE = re.compile(
    rf"(?:{_DEP_VERB_ZH})?\s*(?P<kind>{_DEP_KIND_ZH})\s*(?P<ids>{_DEP_ID_PARENS}(?:\s*{_RANGE_OR_LIST_SEP_ZH}\s*{_DEP_ID_PARENS})*)",
)
_ID_PICK_RE = re.compile(_DEP_ID)

# ── Equation citations (added 2026-04-28 after Shao p.198 miss) ─────
#
# Math papers reference numbered equations as `model (3.25)` / `from (3.25)`
# / `by (3.25)`. Bare `(3.25)` standing alone is the declaration form, not
# a citation — captured by `scan_pages_for_equation` instead. Citation
# anchors restricted to a closed set of math-context nouns + math-context
# verbs/preps, so generic "(2.6) into (2.7)" with no preceding word doesn't
# trigger noise.

_EQ_NOUN = (
    r"model|equation|equations|formula|formulas|system|expression"
    r"|identity|relation|relations|condition|conditions"
    r"|inequality|inequalities|Eq|Eqs"
)
_EQ_VERB = (
    r"from|by|see|via|using|applying|substituting|replacing"
    r"|satisfies|satisfying|gives|implies|holds|applies|follows"
    r"|in|into|of|to"
)
_CITATION_EQ_RE = re.compile(
    rf"\b(?:{_EQ_NOUN}|{_EQ_VERB})\s+\(\s*({_DEP_ID})\s*\)",
    re.IGNORECASE,
)

# Map prose kind word back to the canonical English form scan_pages_for_theorem
# already understands. The downstream scan only uses the id (case-insensitive
# regex over the full alt list) so this is mostly cosmetic — but it keeps the
# returned tuples readable when a caller logs them.
_KIND_CANON = {
    "lemma": "Lemma", "lemmas": "Lemma", "引理": "Lemma",
    "theorem": "Theorem", "theorems": "Theorem", "定理": "Theorem",
    "proposition": "Proposition", "propositions": "Proposition", "命题": "Proposition",
    "corollary": "Corollary", "corollaries": "Corollary", "推论": "Corollary",
    "definition": "Definition", "definitions": "Definition", "定义": "Definition",
    "assumption": "Assumption", "assumptions": "Assumption", "假设": "Assumption",
    "hypothesis": "Assumption", "hypotheses": "Assumption",
    "conjecture": "Conjecture", "conjectures": "Conjecture", "猜想": "Conjecture",
}


def extract_citations(text: str, exclude_id: Optional[str] = None) -> List[Tuple[str, str]]:
    """Find inline citations like 'by Lemma 2.1' or '由定理 5.3 和 5.4'.

    Returns a list of (kind, id) tuples in document order, deduplicated.
    `exclude_id` (e.g. the target theorem's own id) is filtered out so a
    theorem's own restated id doesn't trigger a self-reference dep.

    Patterns matched:
      - English: `(by|via|from|using|applying|per|invoke|see) (Lemma|Theorem|...)s? <id>[, and <id>]*`
      - Chinese: `[由|根据|...]?(引理|定理|...) <id>[, 和 <id>]*`
      - Plurals: `Lemmas 2.3 and 2.4` → two entries
    Patterns NOT matched (deliberate): bare `(2.6)` equation refs, "the previous
    lemma", "Lemma X above" — too noisy / require structural understanding.
    """
    seen: set[Tuple[str, str]] = set()
    out: List[Tuple[str, str]] = []
    for rx in (_CITATION_EN_RE, _CITATION_ZH_RE):
        for m in rx.finditer(text):
            kind_raw = m.group("kind").lower()
            kind = _KIND_CANON.get(kind_raw, kind_raw.capitalize())
            for id_match in _ID_PICK_RE.finditer(m.group("ids")):
                cid = id_match.group(0)
                if exclude_id and cid == exclude_id:
                    continue
                key = (kind, cid)
                if key in seen:
                    continue
                seen.add(key)
                out.append(key)
    # Equation refs — separate regex because the format is `<noun> (<id>)`
    # not `<verb> <kind> <id>` (no kind word, just parens).
    for m in _CITATION_EQ_RE.finditer(text):
        cid = m.group(1)
        if exclude_id and cid == exclude_id:
            continue
        key = ("Equation", cid)
        if key in seen:
            continue
        seen.add(key)
        out.append(key)
    return out


def _truncate_at_next_declaration(text: str, target_id: str) -> str:
    """Cut ``text`` at the position of the first non-target declaration.

    Spill pages (the page after a target theorem's last declaration line)
    often contain the start of the *next* theorem-like block — Example,
    Theorem, Lemma, Corollary etc. extract_citations would then pull in
    that next block's body as if it were a citation by the target. The
    fix: when scanning a page text for citations, truncate at the first
    declaration of any kind+id where ``id != target_id``.

    Implementation note: uses the same boundary-anchored declaration
    pattern as scan_pages_for_theorem tier 1, so what counts as a
    declaration here matches what counts there. The target's own
    declaration is skipped (id == target_id); only OTHER theorems'
    declarations cut the text.
    """
    all_kw = THEOREM_KEYWORDS + ["example", "remark", "conjecture"]
    kind_alt = "|".join(all_kw + ["thm", "lem", "cor", "prop", "def", "ex", "rem"])
    end_anchor = r"(?!\d|\.\d)"
    # Three alternation arms — each represents a different way a non-target
    # declarative block can start on a spill page. Captured id is in
    # group(1)/(2)/(3) depending on which arm fired.
    #   Arm A: strict-leading (`. ` / line-start) + lax trailing — covers the
    #     usual `Theorem 5.1.` / `Lemma 2.3 (...)` shapes.
    #   Arm B: loose-leading (`\n`) + strict declarative trailing — covers
    #     section-heading-followed-by-decl where heading lacks terminal punct.
    #   Arm C: `Proof of <kind> <id>` boundaries — added 2026-04-28 after Cox
    #     Lemma S1 case where p.49 contained end-of-S1-proof + start-of-
    #     `Proof of Theorem 1.` header. Without arm C the `Theorem 1` slipped
    #     into citation extraction as a false positive dep.
    decl_re = re.compile(
        rf"(?:^|[\.\!?:]\s+)\b(?:{kind_alt})\s+({_DEP_ID}){end_anchor}\s*[\.\(:]"
        rf"|"
        rf"\n\s*\b(?:{kind_alt})\s+({_DEP_ID}){end_anchor}\s*"
        rf"(?:\([^\)]{{4,}}\)|\.\s+[A-Z]|:\s+[A-Z])"
        rf"|"
        rf"(?:^|\n)\s*Proof\s+of\s+(?:{kind_alt})\s+({_DEP_ID}){end_anchor}"
        rf"\s*(?:\([^\)]*\))?\s*[\.:]",
        re.IGNORECASE,
    )
    for m in decl_re.finditer(text):
        cited_id = m.group(1) or m.group(2) or m.group(3)
        if cited_id and cited_id != target_id:
            return text[: m.start()]
    return text


def scan_pages_for_equation(pdf_path: Path, eq_id: str) -> List[int]:
    """Find the page where equation ``(eq_id)`` is **declared**.

    Equation declaration form: ``(<id>)`` standing alone on its own line —
    that's the LaTeX `\\label{eq:foo}` rendered as a right-aligned number
    after a display equation. Citations like ``model (3.25)`` always have
    grammatical context (noun/verb before the parens) and never appear
    bare; the bare-paren-on-own-line form is therefore a reliable
    declaration signal.

    Returns the declaration page + 1-page spill. Equations don't have the
    cross-reference proliferation problem theorems have (the declaration
    only renders once with the right-aligned number); first-cluster
    heuristic isn't needed.

    Returns ``[]`` if no declaration found (the equation might have been
    inline-numbered or the paper uses a different convention).
    """
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    try:
        escaped = re.escape(eq_id)
        # `(?:^|\n)` start-of-line, optional whitespace, `(<id>)`, optional
        # whitespace, end-of-line. `re.MULTILINE` lets `^/$` match line
        # boundaries too — belt-and-braces for both pymupdf flavors.
        decl_re = re.compile(
            rf"(?:^|\n)\s*\({escaped}\)\s*(?:\n|$)",
            re.MULTILINE,
        )
        for i in range(len(doc)):
            if decl_re.search(doc[i].get_text()):
                return [i, i + 1] if i + 1 < len(doc) else [i]
        return []
    finally:
        doc.close()


def expand_with_dependencies(
    pdf_path: Path,
    target_pages: List[int],
    *,
    exclude_id: Optional[str] = None,
    max_total_pages: int = 30,
) -> Tuple[List[int], List[Tuple[str, str]]]:
    """Augment target_pages with pages where dependencies (cited Lemma /
    Theorem / Definition / Assumption / ...) are *declared*.

    Reuses scan_pages_for_theorem to locate the dep declaration page. Depth is
    fixed to 1 by design — recursive expansion explodes page count on densely-
    cited papers. Bumps to depth=2 should be opt-in via a future flag once we
    have evidence it pays off in real runs.

    Caps total pages at `max_total_pages` so a pathological paper can't blow
    out the OCR budget. Returns (expanded_pages, found_citations) so the caller
    can log the dep-trace decision.
    """
    import pymupdf

    if not target_pages:
        return list(target_pages), []

    doc = pymupdf.open(str(pdf_path))
    try:
        # Per-page truncation at first non-target declaration. Prevents the
        # spill page from bleeding next-theorem content into citation
        # extraction (Shao Thm 3.13 case: spill p.213 contains Example 3.19
        # whose body was getting pulled as if it were a Thm 3.13 dep).
        target_id_for_truncate = exclude_id or ""
        per_page_text = []
        for i in target_pages:
            if i >= len(doc):
                continue
            page_text = doc[i].get_text()
            if target_id_for_truncate:
                page_text = _truncate_at_next_declaration(
                    page_text, target_id_for_truncate
                )
            per_page_text.append(page_text)
        target_text = "\n".join(per_page_text)
    finally:
        doc.close()

    citations = extract_citations(target_text, exclude_id=exclude_id)
    if not citations:
        return list(target_pages), []

    extra: set[int] = set()
    for cited_kind, cid in citations:
        # Dispatch on kind. Equations get a dedicated scanner (paren-on-own-line
        # is the declaration signal); theorems/lemmas/etc go through
        # scan_pages_for_theorem with kind passed so `Theorem 3.6` won't pull
        # in `Lemma 3.6` declarations and vice versa.
        if cited_kind == "Equation":
            pages = scan_pages_for_equation(pdf_path, cid)
        else:
            pages = scan_pages_for_theorem(pdf_path, cid, kind=cited_kind)
        for p in pages:
            if p not in target_pages:
                extra.add(p)

    merged = sorted(set(target_pages) | extra)
    if len(merged) > max_total_pages:
        # Keep target pages intact; truncate extras to fit budget.
        keep_extras = max_total_pages - len(target_pages)
        if keep_extras <= 0:
            return list(target_pages), citations
        sorted_extras = sorted(extra)[:keep_extras]
        merged = sorted(set(target_pages) | set(sorted_extras))
    return merged, citations


# ═══════════════════════════════════════════════════════════
# Backend: pymupdf (fast, local, no model)
# ═══════════════════════════════════════════════════════════

def run_pymupdf(pdf_path: Path, raw_output_dir: Path, pages: Optional[List[int]] = None) -> Path:
    """Extract PDF to markdown using pymupdf4llm."""
    try:
        import pymupdf4llm
    except ImportError:
        raise SystemExit("[pdf-extract] pymupdf4llm not found. Install: pip install pymupdf4llm")

    raw_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"[pdf-extract] Running pymupdf4llm on {pdf_path.name}")

    if pages is not None:
        md_text = pymupdf4llm.to_markdown(str(pdf_path), pages=pages)
        print(f"[pdf-extract] Extracted pages {[p+1 for p in pages]}")
    else:
        md_text = pymupdf4llm.to_markdown(str(pdf_path))

    md_file = raw_output_dir / f"{pdf_path.stem}.md"
    md_file.write_text(md_text, encoding="utf-8")
    print(f"[pdf-extract] pymupdf4llm output: {md_file} ({len(md_text)} chars)")
    return md_file


# ═══════════════════════════════════════════════════════════
# Backend: claude (most accurate, uses Claude API)
# ═══════════════════════════════════════════════════════════

def pdf_to_page_images(pdf_path: Path, pages: Optional[List[int]] = None) -> List[Tuple[int, bytes]]:
    """Convert PDF pages to PNG images. Returns list of (page_num, png_bytes)."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    images = []
    page_indices = pages if pages is not None else range(len(doc))
    for page_num in page_indices:
        page = doc[page_num]
        mat = pymupdf.Matrix(2, 2)  # 2x resolution for better quality
        pix = page.get_pixmap(matrix=mat)
        images.append((page_num, pix.tobytes("png")))
    doc.close()
    return images


def _extract_page_text(pdf_path: Path, pages: Optional[List[int]] = None) -> Dict[int, str]:
    """Extract raw text per page using pymupdf."""
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    result = {}
    indices = pages if pages is not None else range(len(doc))
    for i in indices:
        result[i] = doc[i].get_text()
    doc.close()
    return result


def run_claude_extract(pdf_path: Path, raw_output_dir: Path,
                       pages: Optional[List[int]] = None,
                       theorem_id: Optional[str] = None,
                       query: Optional[str] = None) -> Path:
    """Use Claude to extract theorems from PDF.

    Strategy:
    - If ANTHROPIC_API_KEY is set: send page images via SDK (most accurate)
    - Otherwise: extract text via pymupdf, send to Claude CLI for LaTeX restoration
    """
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    use_images = bool(os.environ.get("ANTHROPIC_API_KEY"))

    if use_images:
        print(f"[pdf-extract] Using Anthropic SDK with page images (most accurate)")
    else:
        print(f"[pdf-extract] Using Claude CLI with extracted text (no API key for images)")
        print(f"[pdf-extract] Tip: set ANTHROPIC_API_KEY for image-based extraction")

    # Build focus instruction
    if theorem_id:
        focus = f"Focus on Theorem/Lemma/Definition {theorem_id}. Extract its FULL statement and proof."
    elif query:
        focus = f"Focus on content related to: {query}. Extract all relevant theorems, definitions, and proofs."
    else:
        focus = "Extract ALL theorems, lemmas, definitions, propositions, corollaries, and their proofs."

    instructions = f"""{focus}

For each theorem-like block found, output in this EXACT format:

## [Type] [Number] [Optional Name]
[Full statement with LaTeX: $...$ for inline, $$...$$ for display math]

### Proof
[Proof content if present]

Rules:
- Use standard LaTeX: \\mathbb{{E}}, \\operatorname{{Var}}, \\mathcal{{N}}, etc.
- Preserve ALL mathematical details — every subscript, superscript, condition
- Skip headers/footers, page numbers, author info
- If a formula is unclear, add: %% OCR_UNCERTAIN: [what's unclear]"""

    all_md_parts: List[str] = []

    if use_images:
        # Image-based extraction via SDK
        page_images = pdf_to_page_images(pdf_path, pages)
        print(f"[pdf-extract] {len(page_images)} pages to process as images")

        batch_size = 10
        for batch_start in range(0, len(page_images), batch_size):
            batch = page_images[batch_start:batch_start + batch_size]
            page_nums = [p + 1 for p, _ in batch]
            page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
            print(f"[pdf-extract] Sending pages {page_range_str} to Claude...")

            content_parts = []
            for _, img_bytes in batch:
                b64 = base64.b64encode(img_bytes).decode("ascii")
                content_parts.append({
                    "type": "image",
                    "source": {"type": "base64", "media_type": "image/png", "data": b64}
                })
            content_parts.append({"type": "text", "text": instructions + f"\n\nPages shown: {page_range_str}"})

            md_part = _call_claude_api(content_parts)
            all_md_parts.append(md_part)
    else:
        # Text-based extraction via CLI
        page_texts = _extract_page_text(pdf_path, pages)
        print(f"[pdf-extract] {len(page_texts)} pages extracted as text")

        # Process in batches of 10 pages
        page_items = sorted(page_texts.items())
        batch_size = 10
        for batch_start in range(0, len(page_items), batch_size):
            batch = page_items[batch_start:batch_start + batch_size]
            page_nums = [p + 1 for p, _ in batch]
            page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
            print(f"[pdf-extract] Sending pages {page_range_str} to Claude CLI...")

            # Build text content with page markers
            text_content = ""
            for page_num, text in batch:
                text_content += f"\n===== PAGE {page_num + 1} =====\n{text}\n"

            prompt = f"""Below is text extracted from a mathematics/statistics PDF (pages {page_range_str}).
The math formulas have been converted to Unicode and lost their LaTeX formatting.

YOUR TASK: Restore the mathematical content to proper LaTeX and identify theorem-like blocks.

{instructions}

--- PDF TEXT (pages {page_range_str}) ---
{text_content}
--- END PDF TEXT ---"""

            content_parts = [{"type": "text", "text": prompt}]
            md_part = _call_claude_api(content_parts)
            all_md_parts.append(md_part)

    full_md = "\n\n".join(all_md_parts)
    suffix = f"_thm{theorem_id}" if theorem_id else ("_query" if query else "")
    md_file = raw_output_dir / f"{pdf_path.stem}{suffix}_claude.md"
    md_file.write_text(full_md, encoding="utf-8")
    print(f"[pdf-extract] Claude extraction: {md_file} ({len(full_md)} chars)")
    return md_file


def _call_claude_api(content_parts: list) -> str:
    """Call Claude API with image+text content. Tries SDK first, then CLI."""
    # Method 1: Anthropic Python SDK (needs ANTHROPIC_API_KEY)
    try:
        import anthropic
        if os.environ.get("ANTHROPIC_API_KEY"):
            client = anthropic.Anthropic()
            response = client.messages.create(
                model="claude-sonnet-4-20250514",
                max_tokens=8192,
                messages=[{"role": "user", "content": content_parts}],
            )
            return response.content[0].text
    except ImportError:
        pass
    except Exception as e:
        print(f"[pdf-extract] SDK error: {e}", file=sys.stderr)

    # Method 2: Claude CLI (unset CLAUDECODE to allow nesting)
    # Extract text prompt from content_parts
    text_prompt = ""
    for part in content_parts:
        if isinstance(part, dict) and part.get("type") == "text":
            text_prompt = part["text"]
            break

    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    result = subprocess.run(
        ["claude", "-p", "--output-format", "text"],
        input=text_prompt,
        capture_output=True, text=True, timeout=300,
        env=env,
    )
    if result.returncode != 0:
        print(f"[pdf-extract] Claude CLI error: {result.stderr[:500]}", file=sys.stderr)
        return f"% Claude extraction failed\n% Error: {result.stderr[:200]}"
    return result.stdout


# ═══════════════════════════════════════════════════════════
# Backend: openai-api (uses OpenAI API for extraction)
# ═══════════════════════════════════════════════════════════

def _call_openai_api(content_parts: list) -> str:
    """Call OpenAI API with text content. Tries SDK first, then Codex CLI."""
    # Extract text prompt from content_parts
    text_prompt = ""
    for part in content_parts:
        if isinstance(part, dict) and part.get("type") == "text":
            text_prompt = part["text"]
            break

    # Method 1: OpenAI Python SDK (needs OPENAI_API_KEY)
    try:
        import openai
        if os.environ.get("OPENAI_API_KEY"):
            client = openai.OpenAI()
            response = client.chat.completions.create(
                model="gpt-4o",
                max_tokens=8192,
                messages=[{"role": "user", "content": text_prompt}],
            )
            return response.choices[0].message.content
    except ImportError:
        pass
    except Exception as e:
        print(f"[pdf-extract] OpenAI SDK error: {e}", file=sys.stderr)

    # Method 2: Codex CLI
    try:
        result = subprocess.run(
            ["codex", "exec", "--full-auto", text_prompt],
            capture_output=True, text=True, timeout=300,
        )
        if result.returncode != 0:
            print(f"[pdf-extract] Codex CLI error: {result.stderr[:500]}", file=sys.stderr)
            return f"% OpenAI extraction failed\n% Error: {result.stderr[:200]}"
        return result.stdout
    except FileNotFoundError:
        print("[pdf-extract] ERROR: neither openai SDK nor codex CLI available", file=sys.stderr)
        return "% OpenAI extraction failed — no SDK or CLI available"
    except Exception as e:
        print(f"[pdf-extract] Codex CLI error: {e}", file=sys.stderr)
        return f"% OpenAI extraction failed\n% Error: {e}"


def run_openai_extract(pdf_path: Path, raw_output_dir: Path,
                       pages: Optional[List[int]] = None,
                       theorem_id: Optional[str] = None,
                       query: Optional[str] = None) -> Path:
    """Use OpenAI to extract theorems from PDF (text-based only)."""
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"[pdf-extract] Using OpenAI backend for extraction")

    # Build focus instruction
    if theorem_id:
        focus = f"Focus on Theorem/Lemma/Definition {theorem_id}. Extract its FULL statement and proof."
    elif query:
        focus = f"Focus on content related to: {query}. Extract all relevant theorems, definitions, and proofs."
    else:
        focus = "Extract ALL theorems, lemmas, definitions, propositions, corollaries, and their proofs."

    instructions = f"""{focus}

For each theorem-like block found, output in this EXACT format:

## [Type] [Number] [Optional Name]
[Full statement with LaTeX: $...$ for inline, $$...$$ for display math]

### Proof
[Proof content if present]

Rules:
- Use standard LaTeX: \\mathbb{{E}}, \\operatorname{{Var}}, \\mathcal{{N}}, etc.
- Preserve ALL mathematical details — every subscript, superscript, condition
- Skip headers/footers, page numbers, author info
- If a formula is unclear, add: %% OCR_UNCERTAIN: [what's unclear]"""

    # Text-based extraction via pymupdf + OpenAI
    page_texts = _extract_page_text(pdf_path, pages)
    print(f"[pdf-extract] {len(page_texts)} pages extracted as text")

    all_md_parts: List[str] = []
    page_items = sorted(page_texts.items())
    batch_size = 10
    for batch_start in range(0, len(page_items), batch_size):
        batch = page_items[batch_start:batch_start + batch_size]
        page_nums = [p + 1 for p, _ in batch]
        page_range_str = f"{page_nums[0]}-{page_nums[-1]}" if len(page_nums) > 1 else str(page_nums[0])
        print(f"[pdf-extract] Sending pages {page_range_str} to OpenAI...")

        text_content = ""
        for page_num, text in batch:
            text_content += f"\n===== PAGE {page_num + 1} =====\n{text}\n"

        prompt = f"""Below is text extracted from a mathematics/statistics PDF (pages {page_range_str}).
The math formulas have been converted to Unicode and lost their LaTeX formatting.

YOUR TASK: Restore the mathematical content to proper LaTeX and identify theorem-like blocks.

{instructions}

--- PDF TEXT (pages {page_range_str}) ---
{text_content}
--- END PDF TEXT ---"""

        content_parts = [{"type": "text", "text": prompt}]
        md_part = _call_openai_api(content_parts)
        all_md_parts.append(md_part)

    full_md = "\n\n".join(all_md_parts)
    suffix = f"_thm{theorem_id}" if theorem_id else ("_query" if query else "")
    md_file = raw_output_dir / f"{pdf_path.stem}{suffix}_openai.md"
    md_file.write_text(full_md, encoding="utf-8")
    print(f"[pdf-extract] OpenAI extraction: {md_file} ({len(full_md)} chars)")
    return md_file


# ═══════════════════════════════════════════════════════════
# Backend: mineru (heavy, needs GPU or lots of CPU/RAM)
# ═══════════════════════════════════════════════════════════

def check_mineru() -> bool:
    return shutil.which("mineru") is not None


def _has_gpu() -> bool:
    """Detect whether a real NVIDIA GPU is available.

    torch.cuda.is_available() is NOT reliable here — on CPU-only boxes
    where torch was installed as the CUDA build (e.g. via `pip install
    torch==X.Y.Z+cu124`), it returns True even with no actual device,
    then `torchvision::nms` dispatches to a CUDA backend that has no
    kernel and raises NotImplementedError inside MinerU hybrid, which
    silently swallows it → exit 0 with empty output. See
    docs/CLI_WEB_CONFORMANCE.md §12 (CPU-only VPS silent-fail case).

    Two cheap, authoritative probes:
      1. /dev/nvidia0 exists (kernel driver loaded)
      2. nvidia-smi on PATH (userspace tooling installed)
    Both true → real GPU. Either false → treat as CPU-only.
    """
    return Path("/dev/nvidia0").exists() and shutil.which("nvidia-smi") is not None


def _mineru_attempt(
    cmd: List[str],
    raw_output_dir: Path,
    label: str,
    env: Optional[Dict[str, str]] = None,
    timeout: Optional[float] = None,
) -> Optional[Path]:
    """Run one MinerU invocation and return the path to its main `.md`
    output, or None if MinerU exited 0 but produced no usable markdown
    (silent failure — empirically observed on long docs, e.g. 83-page PDFs
    with -b hybrid-auto-engine; see docs/CLI_WEB_CONFORMANCE.md §12).

    `env` lets the caller override subprocess env (used to set
    `CUDA_VISIBLE_DEVICES=""` when hybrid runs on a CPU-only host with a
    CUDA-build torch so torchvision's nms stays on the CPU backend).

    `timeout` caps wall time for the attempt. Exceeded → log + return
    None so the caller can fall back to the next backend instead of
    hanging forever on a VLM inference that will never complete in a
    user-acceptable window.
    """
    print(f"[pdf-extract] Running ({label}): {' '.join(cmd)}")
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, env=env, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        print(
            f"[pdf-extract] MinerU ({label}) timed out after {timeout}s — "
            f"treating as attempt failure (caller will fall back).",
            file=sys.stderr,
        )
        return None
    if result.returncode != 0:
        print(f"[pdf-extract] MinerU ({label}) stderr:\n{result.stderr[-2000:]}", file=sys.stderr)
        return None
    md_files = [p for p in raw_output_dir.rglob("*.md") if p.stat().st_size >= 100]
    if not md_files:
        print(
            f"[pdf-extract] MinerU ({label}) exit 0 but produced no non-empty "
            f"markdown under {raw_output_dir} — silent failure, treating as "
            f"attempt failure.",
            file=sys.stderr,
        )
        return None
    md_file = max(md_files, key=lambda p: p.stat().st_size)
    print(f"[pdf-extract] MinerU ({label}) output: {md_file} ({md_file.stat().st_size} bytes)")
    return md_file


def _page_range_flags(target_pages: Optional[List[int]]) -> List[str]:
    """Convert an (optionally non-contiguous) list of 0-indexed page
    numbers into MinerU `-s <start> -e <end>` flags.

    MinerU CLI only supports a single contiguous range. For
    non-contiguous requests like `[32, 40, 50]` we pass the superset
    `-s 32 -e 50` — still a massive speedup vs processing the whole
    PDF, and the downstream structure extractor filters blocks by
    heading match anyway.
    """
    if not target_pages:
        return []
    lo = min(target_pages)
    hi = max(target_pages)
    flags = ["-s", str(lo), "-e", str(hi)]
    if set(target_pages) != set(range(lo, hi + 1)):
        print(
            f"[pdf-extract] target_pages {sorted(target_pages)} is non-contiguous; "
            f"passing MinerU the superset [{lo},{hi}] ({hi - lo + 1} pages).",
            file=sys.stderr,
        )
    return flags


# CPU-hybrid budget. Empirically hybrid-auto-engine VLM inference on a
# 10-core CPU-only WSL box took ~74 s/page (MinerU 2.7 / 1.2B VLM model).
# We'll try hybrid when pages <= HYBRID_MAX_PAGES_CPU and cap wall time at
# HYBRID_TIMEOUT_CPU — if exceeded, fall back to pipeline which is ~3× faster
# on CPU at the cost of noisier LaTeX (`V a r`, `\operatorname*{s u p}`).
# On GPU hosts we skip both caps: hybrid is fast enough to run on the whole PDF.
HYBRID_MAX_PAGES_CPU = 3
HYBRID_TIMEOUT_CPU = 360  # seconds


def run_mineru(
    pdf_path: Path,
    raw_output_dir: Path,
    target_pages: Optional[List[int]] = None,
) -> Path:
    """Extract markdown from a PDF via MinerU with a retry cascade.

    Attempt order:
      1. `-b hybrid-auto-engine` — MinerU's VLM-based backend. Cleanest
         LaTeX output per docs/CLI_WEB_CONFORMANCE.md §12. On GPU hosts:
         always tried. On CPU hosts: tried only when target_pages is set
         and small (≤ HYBRID_MAX_PAGES_CPU), with CUDA_VISIBLE_DEVICES=""
         so torchvision::nms stays on the CPU backend (else
         NotImplementedError → silent fail), and a hard wall-clock
         timeout so the agent isn't blocked for 40+ min on 46 pages.
      2. `-b pipeline -d cpu` fallback — slower per-page but reliably
         completes on CPU at any page count. Takes over when attempt 1
         was skipped, silent-failed, timed out, or errored.

    When `target_pages` is supplied the same range is passed via MinerU's
    `-s`/`-e` flags to both attempts — prevents the 83-pages-when-user-
    asked-for-3 silent slowdown that made `jobmobv6mso5nfl` take minutes.

    Raises SystemExit if both attempts fail (or pipeline fails when
    hybrid was skipped) so the caller (agent) sees the failure and can
    surface it via `request_user_decision` rather than proceeding with
    empty input and hallucinating (Rule 3).
    """
    raw_output_dir.mkdir(parents=True, exist_ok=True)
    page_flags = _page_range_flags(target_pages)

    gpu = _has_gpu()
    page_count = len(target_pages) if target_pages else None

    # Decide whether to attempt hybrid. On CPU-only hosts a 46-page VLM
    # inference is ≈ 57 minutes — not user-acceptable, so we only try
    # hybrid for small page ranges where the quality gain is worth the
    # few minutes of wall time.
    if gpu:
        attempt_hybrid = True
        hybrid_env: Optional[Dict[str, str]] = None
        hybrid_timeout: Optional[float] = None
        reason = "GPU detected"
    elif page_count is not None and page_count <= HYBRID_MAX_PAGES_CPU:
        attempt_hybrid = True
        hybrid_env = os.environ.copy()
        # setdefault so a user who already set CUDA_VISIBLE_DEVICES keeps control.
        hybrid_env.setdefault("CUDA_VISIBLE_DEVICES", "")
        hybrid_timeout = HYBRID_TIMEOUT_CPU
        reason = f"CPU-only, pages={page_count} ≤ {HYBRID_MAX_PAGES_CPU}"
    else:
        attempt_hybrid = False
        hybrid_env = None
        hybrid_timeout = None
        reason = (
            f"CPU-only, pages={page_count or 'all'} > {HYBRID_MAX_PAGES_CPU} "
            f"(VLM on CPU is ~74s/page; skipping to avoid long wall time)"
        )

    if attempt_hybrid:
        print(f"[pdf-extract] hybrid gate: attempting ({reason})")
        hybrid_cmd = [
            "mineru", "-p", str(pdf_path), "-o", str(raw_output_dir),
            "-m", "auto", "-b", "hybrid-auto-engine",
            *page_flags,
        ]
        md_file = _mineru_attempt(
            hybrid_cmd, raw_output_dir, "hybrid-auto-engine",
            env=hybrid_env, timeout=hybrid_timeout,
        )
        if md_file is not None:
            return md_file
        print(
            "[pdf-extract] Attempt 1 (hybrid-auto-engine) failed; "
            "retrying with `-b pipeline -d cpu`.",
            file=sys.stderr,
        )
    else:
        print(f"[pdf-extract] hybrid gate: skipped ({reason})")

    # Pipeline backend — runs on CPU, ~25 s/page, noisier LaTeX but reliable.
    pipeline_cmd = [
        "mineru", "-p", str(pdf_path), "-o", str(raw_output_dir),
        "-m", "auto", "-b", "pipeline", "-d", "cpu",
        *page_flags,
    ]
    md_file = _mineru_attempt(pipeline_cmd, raw_output_dir, "pipeline -d cpu")
    if md_file is not None:
        return md_file

    raise SystemExit(
        "[pdf-extract] MinerU failed on "
        + ("BOTH hybrid-auto-engine and pipeline backends" if attempt_hybrid else "pipeline backend (hybrid skipped)")
        + " (exit 0 with empty output, non-zero exit, or timeout). "
        "Do NOT hallucinate content — ask the user to paste the relevant "
        "theorem text (via request_user_decision in pipeline.md Step 1) "
        "or to provide a smaller page range."
    )


# ═══════════════════════════════════════════════════════════
# Common: theorem extraction and LaTeX generation
# ═══════════════════════════════════════════════════════════

def extract_theorem_blocks(md_text: str) -> List[Dict[str, str]]:
    """Parse markdown to extract theorem-like blocks with their proofs."""
    blocks: List[Dict[str, str]] = []
    lines = md_text.split("\n")
    current_block: Optional[Dict[str, str]] = None
    current_proof_for: Optional[str] = None
    buffer: List[str] = []

    def flush():
        nonlocal current_block, buffer, current_proof_for
        if current_block is not None:
            content = "\n".join(buffer).strip()
            if current_proof_for is not None:
                for b in reversed(blocks):
                    if b.get("number") == current_proof_for or current_proof_for is None:
                        b["proof_hint"] = content
                        break
                else:
                    if blocks:
                        blocks[-1]["proof_hint"] = content
            else:
                current_block["statement"] = content
                blocks.append(current_block)
            current_block = None
            current_proof_for = None
            buffer = []

    for line in lines:
        thm_match = THEOREM_HEADING_RE.search(line)
        if thm_match:
            flush()
            kind = thm_match.group(1).lower()
            number = thm_match.group(2) or ""
            name = thm_match.group(3) or ""
            current_block = {
                "kind": kind, "number": number, "name": name,
                "statement": "", "proof_hint": "",
            }
            rest = line[thm_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        proof_match = PROOF_HEADING_RE.search(line)
        if proof_match:
            flush()
            current_block = {"kind": "proof", "number": "", "name": "", "statement": "", "proof_hint": ""}
            current_proof_for = proof_match.group(2) or None
            rest = line[proof_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        if current_block is not None:
            buffer.append(line)

    flush()
    return blocks


def blocks_to_latex(blocks: List[Dict[str, str]], pdf_name: str, backend: str) -> str:
    parts: List[str] = []
    parts.append(f"% Auto-extracted from: {pdf_name}")
    parts.append(f"% Backend: {backend}")
    parts.append(r"% Review formulas marked with % OCR_UNCERTAIN before proceeding.")
    parts.append("")
    parts.append(r"\documentclass{article}")
    parts.append(r"\usepackage{amsmath,amssymb,amsthm}")
    parts.append(r"\newtheorem{theorem}{Theorem}")
    parts.append(r"\newtheorem{lemma}[theorem]{Lemma}")
    parts.append(r"\newtheorem{corollary}[theorem]{Corollary}")
    parts.append(r"\newtheorem{proposition}[theorem]{Proposition}")
    parts.append(r"\newtheorem{definition}[theorem]{Definition}")
    parts.append(r"\begin{document}")
    parts.append("")

    for block in blocks:
        kind = block["kind"]
        if kind == "proof":
            continue
        env = kind if kind in ("theorem", "lemma", "corollary", "proposition", "definition") else "theorem"
        number_comment = f"  % Original number: {block['number']}" if block["number"] else ""
        name_opt = f"[{block['name']}]" if block["name"] else ""
        parts.append(f"\\begin{{{env}}}{name_opt}{number_comment}")
        statement = block["statement"]
        statement = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", statement, flags=re.DOTALL)
        parts.append(statement)
        parts.append(f"\\end{{{env}}}")
        parts.append("")
        if block.get("proof_hint"):
            parts.append(r"\begin{proof}")
            proof = block["proof_hint"]
            proof = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", proof, flags=re.DOTALL)
            parts.append(proof)
            parts.append(r"\end{proof}")
            parts.append("")

    parts.append(r"\end{document}")
    return "\n".join(parts)


def check_latex_balance(tex: str) -> List[str]:
    warnings: List[str] = []
    depth = 0
    for i, c in enumerate(tex):
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        if depth < 0:
            line_num = tex[:i].count("\n") + 1
            warnings.append(f"Line {line_num}: extra closing brace")
            depth = 0
    if depth > 0:
        warnings.append(f"Unbalanced: {depth} unclosed braces at end of file")
    ocr_artifacts = [
        (r"\\mathbb\{[A-Z]\}[A-Z]", "possible merged mathbb"),
        (r"[^\\]_\{[^}]{20,}", "very long subscript (possible OCR merge)"),
        (r"\\[a-z]+\{$", "backslash command at end of line"),
    ]
    for pattern, msg in ocr_artifacts:
        for m in re.finditer(pattern, tex):
            line_num = tex[:m.start()].count("\n") + 1
            warnings.append(f"Line {line_num}: {msg}")
    return warnings


def generate_notation_yaml(tex: str) -> str:
    detected: Dict[str, str] = {}
    for sym, desc in DEFAULT_NOTATION["symbols"].items():
        pattern = re.escape(sym)
        if re.search(pattern, tex):
            detected[sym] = desc
    lines = ["# Auto-generated notation mapping", "# Review and edit as needed", "", "symbols:"]
    for sym, desc in sorted(detected.items()):
        lines.append(f'  "{sym}": "{desc}"')
    if not detected:
        lines.append("  # No standard symbols detected — add mappings manually")
    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Extract theorems from PDF → structured LaTeX",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  # Full PDF (fast local, zero API cost)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/

  # Only Theorem 4.1 (auto-finds page)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --theorem 4.1

  # Pages 5-8 only
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --pages 5-8

  # Search by keyword
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --query "Poincaré inequality"

  # Use Claude API for highest accuracy (costs API credits)
  python3 pdf_extract.py --pdf paper.pdf --output-dir out/ --backend claude-api
""")
    ap.add_argument("--pdf", required=True, help="Path to input PDF")
    ap.add_argument("--output-dir", required=True, help="Output directory")
    ap.add_argument("--backend", choices=["pymupdf", "claude-api", "openai-api", "mineru"], default=None,
                    help="Extraction backend (default: pymupdf, zero API cost). claude-api requires ANTHROPIC_API_KEY. openai-api requires OPENAI_API_KEY.")
    ap.add_argument("--pages", type=str, default=None,
                    help="Page range to extract, e.g. '1-5,8,10-12' (1-indexed)")
    ap.add_argument("--theorem", type=str, default=None,
                    help="Extract a specific theorem by ID, e.g. '4.1'. Auto-finds the page.")
    ap.add_argument("--query", type=str, default=None,
                    help="Extract theorems matching a keyword/phrase. Auto-finds relevant pages.")
    ap.add_argument("--skip-ocr", action="store_true",
                    help="Skip extraction, use existing markdown in output-dir/raw/")
    ap.add_argument("--include-deps", action="store_true",
                    help="After resolving target pages (--theorem / --pages), scan them for "
                         "inline citations (`by Lemma X.Y`, `由定理 X.Y`, ...) and also include the "
                         "pages where those dependencies are declared. Useful when the target "
                         "theorem cites lemmas / definitions / assumptions that live on earlier "
                         "pages but the agent needs them in context. Depth fixed at 1.")
    ap.add_argument("--deps-max-pages", type=int, default=30,
                    help="Cap on total pages after dep expansion. Truncates extras (target pages "
                         "always preserved). Default 30 — guards against pathological papers.")
    ap.add_argument("--no-proof-span", action="store_true",
                    help="With --theorem, by default also scan for `Proof of <Kind> <id>.` and "
                         "union those pages into the target (e.g. Cox-style papers defer proofs "
                         "to a supplementary appendix far from the lemma statement). Pass this "
                         "flag to skip the proof-span lookup — useful for skeleton-only queries "
                         "where you want the statement only.")
    args = ap.parse_args()

    pdf_path = Path(args.pdf).resolve()
    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    raw_dir = output_dir / "raw"

    # Determine which pages to process
    import pymupdf
    doc = pymupdf.open(str(pdf_path))
    total_pages = len(doc)
    doc.close()
    print(f"[pdf-extract] PDF: {pdf_path.name} ({total_pages} pages)")

    target_pages: Optional[List[int]] = None
    # Track the parsed theorem id (kind-stripped) for downstream consumers
    # (--include-deps `exclude_id`, log labels). None when the user didn't
    # supply --theorem or --pages took priority.
    parsed_kind: Optional[str] = None
    parsed_id: Optional[str] = None

    # Priority: explicit --pages > --theorem > --query.
    # Reason: when the user supplies an exact page range they know where the
    # target is — heuristic scanning would only ever degrade that. The agent
    # is allowed to pass both --pages and --theorem (e.g. user typed both
    # into the UI); we structurally enforce "pages wins" so behavior doesn't
    # depend on the agent's discipline. Falls through to scan when --pages
    # is absent or parses to zero indices.
    if args.pages:
        target_pages = parse_page_range(args.pages, total_pages)
        if target_pages:
            print(f"[pdf-extract] Using specified pages: {[p+1 for p in target_pages]}")
        else:
            # Spec parsed to nothing (typo / out-of-range). Fall through so
            # the user isn't punished for an unparseable spec when they also
            # gave a usable --theorem / --query.
            print(f"[pdf-extract] --pages {args.pages!r} parsed to no valid pages; falling through.")
            target_pages = None

    if target_pages is None and args.theorem:
        # Parse `--theorem` arg: extract kind hint if user typed
        # "Theorem 3.9" (vs bare "3.9"). Kind disambiguates same-id
        # collisions across declaration types (e.g. Shao has both
        # Example 3.9 and Theorem 3.9).
        parsed_kind, parsed_id = parse_theorem_arg(args.theorem)
        decl_pages = scan_pages_for_theorem(pdf_path, parsed_id, kind=parsed_kind)
        kind_label = parsed_kind if parsed_kind else "Theorem"
        if decl_pages:
            print(
                f"[pdf-extract] {kind_label} {parsed_id} found on pages: "
                f"{[p+1 for p in decl_pages]}"
            )
        # Multi-cluster note: when the same id is declared in two non-
        # adjacent locations (Cox `Lemma S1` on p.14 + p.33 supplementary
        # re-declaration), surface a stdout note so the agent / user knows
        # the alternative exists and can re-run with `--pages <range>` to
        # see it. We only return the first cluster (canonical paper-intent
        # declaration); the note is informational, not behavior-changing.
        all_clusters = find_all_declaration_clusters(
            pdf_path, parsed_id, kind=parsed_kind
        )
        if len(all_clusters) > 1:
            cluster_starts = [c[0] + 1 for c in all_clusters]
            print(
                f"[pdf-extract] note: {kind_label} {parsed_id} has "
                f"{len(all_clusters)} non-adjacent declaration clusters at "
                f"pages {cluster_starts}. Returning first cluster only; "
                f"re-run with --pages <range> to see the alternatives."
            )
        # Proof-span union: many stat papers defer proofs to a supplementary
        # appendix far from the lemma statement (Cox change-point: Lemma S1
        # declared p.14, proved p.47-49). The declaration-cluster heuristic
        # alone misses the proof body. Default-on union with explicit kind
        # so cross-kind matches don't false-positive (e.g. `Proof of
        # Example 3.9` shouldn't match a `--theorem "Theorem 3.9"` query).
        # Opt-out via --no-proof-span for skeleton-only queries.
        proof_pages: List[int] = []
        if not args.no_proof_span and parsed_kind:
            proof_pages = scan_proof_span_for_theorem(
                pdf_path, parsed_kind, parsed_id
            )
            if proof_pages:
                print(
                    f"[pdf-extract] Proof of {kind_label} {parsed_id} found on "
                    f"pages: {[p+1 for p in proof_pages]}"
                )
        target_pages = sorted(set(decl_pages) | set(proof_pages))
        if not target_pages:
            target_pages = []

    if target_pages is None and args.query:
        target_pages = scan_pages_for_keyword(pdf_path, args.query)
        if target_pages:
            print(f"[pdf-extract] Query matches pages: {[p+1 for p in target_pages]}")

    # If a targeted search returned 0 hits on a large PDF, DO NOT silently
    # fall back to full-PDF OCR — that's a multi-minute footgun. Instead
    # fail closed so the agent either (a) retries with an explicit
    # --pages range, or (b) surfaces to the user via request_user_decision
    # (see pipeline.md Step 1). Empirical threshold: 15 pages — below
    # that, full-PDF OCR is still ~3 min and acceptable.
    LARGE_PDF_THRESHOLD = 15
    if target_pages is not None and len(target_pages) == 0:
        if total_pages > LARGE_PDF_THRESHOLD:
            raise SystemExit(
                f"[pdf-extract] --{'theorem' if args.theorem else 'query'} "
                f"{args.theorem or args.query!r} found no matching pages in "
                f"this {total_pages}-page PDF. Full-PDF OCR would take "
                f"~{total_pages * 15}s (= {total_pages * 15 // 60} min) of "
                f"CPU — refusing to run it silently. Either supply "
                f"--pages <range> explicitly, or ask the user to paste "
                f"the target statement (via request_user_decision). "
                f"Note: the fuzzy scan tries case-insensitive matching "
                f"for bare identifiers AND keyword+identifier pairs; if "
                f"it still missed, the PDF is likely OCR-scanned with "
                f"broken text extraction."
            )
        # Small PDFs: fall back to all pages (the old behavior — cheap).
        print("[pdf-extract] No matching pages found and PDF is short; falling back to all pages.")
        target_pages = None

    # Dep expansion: pull in pages where cited Lemmas / Definitions / Assumptions
    # are declared. Only meaningful when target_pages is a strict subset (full-PDF
    # extraction already includes everything).
    if args.include_deps and target_pages:
        before = list(target_pages)
        # Use the parsed bare id ("S1") for self-reference exclusion, NOT
        # the raw `args.theorem` ("Lemma S1") — extract_citations compares
        # `cid == exclude_id` against bare ids only, so the kind-prefixed
        # form would never match and the target's own id would slip through
        # as a self-citation. Falls back to args.theorem for backward
        # compatibility when --pages was used without --theorem.
        exclude_id = parsed_id if parsed_id else args.theorem
        target_pages, citations = expand_with_dependencies(
            pdf_path, before,
            exclude_id=exclude_id,
            max_total_pages=args.deps_max_pages,
        )
        added = sorted(set(target_pages) - set(before))
        if citations:
            print(f"[pdf-extract] --include-deps: found {len(citations)} citations "
                  f"({', '.join(f'{k} {i}' for k, i in citations[:8])}"
                  f"{'...' if len(citations) > 8 else ''})")
        if added:
            print(f"[pdf-extract] --include-deps: added {len(added)} dep pages: {[p+1 for p in added]}")
        else:
            print("[pdf-extract] --include-deps: no extra pages added (citations resolved within target).")

    # Determine backend.
    #
    # Default policy:
    #   - mineru if installed (local VLM OCR — preserves LaTeX formulas,
    #     handles dense math), because math-heavy papers produce broken
    #     tokens under pymupdf's raw-character-stream extraction.
    #   - else pymupdf (zero-dep text extraction for clean, text-only PDFs).
    #
    # Override with --backend {pymupdf,mineru,claude-api,openai-api}. The
    # claude-api / openai-api paths are only picked when the user explicitly
    # asks, since they spend real tokens.
    is_targeted = target_pages is not None and len(target_pages) < total_pages
    if args.backend:
        backend = args.backend
    else:
        backend = "mineru" if check_mineru() else "pymupdf"
    print(f"[pdf-extract] Using backend: {backend}"
          f"{' (auto: mineru detected)' if not args.backend and backend == 'mineru' else ''}"
          f"{' (auto: mineru not installed, falling back)' if not args.backend and backend == 'pymupdf' else ''}")

    if is_targeted:
        est_tokens = len(target_pages or []) * 1500  # ~1.5K tokens per page image
        print(f"[pdf-extract] Targeted extraction: {len(target_pages or [])} pages, ~{est_tokens} input tokens")
    else:
        print(f"[pdf-extract] Full extraction: {total_pages} pages")

    # Step 1: Extract markdown from PDF
    if args.skip_ocr:
        md_files = list(raw_dir.rglob("*.md"))
        if not md_files:
            raise SystemExit(f"[pdf-extract] --skip-ocr but no .md files in {raw_dir}")
        md_file = max(md_files, key=lambda p: p.stat().st_size)
        print(f"[pdf-extract] Using existing output: {md_file}")
    elif backend == "pymupdf":
        md_file = run_pymupdf(pdf_path, raw_dir, pages=target_pages)
    elif backend == "claude-api":
        md_file = run_claude_extract(
            pdf_path, raw_dir,
            pages=target_pages,
            theorem_id=args.theorem,
            query=args.query,
        )
    elif backend == "openai-api":
        md_file = run_openai_extract(
            pdf_path, raw_dir,
            pages=target_pages,
            theorem_id=args.theorem,
            query=args.query,
        )
    elif backend == "mineru":
        if not check_mineru():
            print("[pdf-extract] ERROR: mineru not found. Install:", file=sys.stderr)
            print("  pip install 'mineru[full]' torch torchvision", file=sys.stderr)
            raise SystemExit(1)
        md_file = run_mineru(pdf_path, raw_dir, target_pages=target_pages)
    else:
        raise SystemExit(f"[pdf-extract] Unknown backend: {backend}")

    md_text = md_file.read_text(encoding="utf-8")

    # Step 2: Extract theorem blocks
    blocks = extract_theorem_blocks(md_text)
    print(f"[pdf-extract] Extracted {len(blocks)} theorem-like blocks")

    if not blocks:
        print("[pdf-extract] WARNING: no structured theorem blocks found.")
        print(f"[pdf-extract] Raw content saved at: {md_file}")
        (output_dir / "paper.tex").write_text(
            f"% No structured theorems extracted from {pdf_path.name}\n"
            f"% Backend: {backend}\n"
            f"% Raw content: {md_file}\n"
            r"\documentclass{article}" + "\n"
            r"\begin{document}" + "\n"
            "% See raw content file for extracted text\n"
            r"\end{document}" + "\n",
            encoding="utf-8",
        )
        (output_dir / "raw_content.md").write_text(md_text, encoding="utf-8")
        _write_summary(output_dir, pdf_path, [], [], md_file, backend)
        return

    # Step 3: Convert to structured LaTeX
    tex = blocks_to_latex(blocks, pdf_path.name, backend)

    # Step 4: Quality checks
    warnings = check_latex_balance(tex)
    if warnings:
        print(f"[pdf-extract] {len(warnings)} LaTeX warnings:")
        for w in warnings[:10]:
            print(f"  - {w}")
        warning_lines = "\n".join(f"% WARNING: {w}" for w in warnings)
        tex = tex.replace(r"\begin{document}",
                          f"% === Quality Warnings ===\n{warning_lines}\n\n\\begin{{document}}")

    # Step 5: Write outputs
    tex_path = output_dir / "paper.tex"
    tex_path.write_text(tex, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {tex_path}")

    notation_yaml = generate_notation_yaml(tex)
    notation_path = output_dir / "notation.yaml"
    notation_path.write_text(notation_yaml, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {notation_path}")

    _write_summary(output_dir, pdf_path, blocks, warnings, md_file, backend)


def _write_summary(output_dir: Path, pdf_path: Path, blocks: list, warnings: list,
                   md_file: Path, backend: str) -> None:
    summary = {
        "pdf": str(pdf_path),
        "backend": backend,
        "blocks_extracted": len(blocks),
        "block_kinds": {k: sum(1 for b in blocks if b["kind"] == k)
                        for k in set(b["kind"] for b in blocks)} if blocks else {},
        "latex_warnings": len(warnings),
        "output_tex": str(output_dir / "paper.tex"),
        "notation_yaml": str(output_dir / "notation.yaml"),
        "raw_output": str(md_file),
    }
    summary_path = output_dir / "extract_summary.json"
    summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[pdf-extract] Summary: {json.dumps(summary, ensure_ascii=False)}")


if __name__ == "__main__":
    main()

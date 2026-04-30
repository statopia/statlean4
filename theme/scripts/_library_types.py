"""Python dataclass mirrors of czy's library-coverage types.

Source of truth: `czy:helperSearchSubAgent.ts:48-64`
(`MatchedLemma`, `LibraryCoverageResult`).

Field-naming convention: TS source uses camelCase; yaml + Python use
snake_case. The mapping is mechanical:

    TS                    ↔  yaml / Python
    --------------------- ↔  ----------------------
    name                  ↔  name
    source                ↔  source
    location              ↔  location (optional)
    kind                  ↔  kind (optional)

H3 slice (per `docs/H3_LIBRARY_COVERAGE_SPEC.md` §4) adds one additive
field per sorry_item child:

    library_hit: MatchedLemma | absent

Written only when coverage_state == "cited_by_library". Absent when
coverage == "needs_proof". D-4 deliberate +1 deviation: czy stores
this in-memory only; SDK-bridge persists for cross-process E11 hand-off.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional


# ── MatchedLemma (czy helperSearchSubAgent.ts:48-54) ──────────────────


@dataclass
class MatchedLemma:
    """One Mathlib/StatLean lemma that matched a sub-problem.

    `name` — the exact lemma name (e.g. "MeasureTheory.integral_nonneg").
    `source` — origin index: "mathlib" | "statlean" | "extern".
    `location` — optional file:line in the index
                 (e.g. "Mathlib/MeasureTheory/Integral/Bochner.lean:42").
    `kind` — lemma kind from the index (e.g. "lemma", "theorem", "def").
    """

    name: str
    source: str  # "mathlib" | "statlean" | "extern"
    location: Optional[str] = None
    kind: Optional[str] = None

    def to_yaml(self) -> Dict[str, Any]:
        """Serialize to yaml-ready dict. Drop None-valued optional fields
        (yaml-clean pattern — matches slice 1 / E4 convention)."""
        d: Dict[str, Any] = {"name": self.name, "source": self.source}
        if self.location is not None:
            d["location"] = self.location
        if self.kind is not None:
            d["kind"] = self.kind
        return d

    @classmethod
    def from_yaml(cls, d: Dict[str, Any]) -> "MatchedLemma":
        return cls(
            name=str(d["name"]),
            source=str(d.get("source", "mathlib")),
            location=d.get("location"),
            kind=d.get("kind"),
        )

    @classmethod
    def from_skill_json(cls, entry: Dict[str, Any]) -> "MatchedLemma":
        """Construct from a SKILL stdout JSON entry that has
        matched_name / matched_source / matched_location / matched_kind
        fields (H3 SKILL output schema per spec §3.2)."""
        return cls(
            name=str(entry["matched_name"]),
            source=str(entry.get("matched_source") or "mathlib"),
            location=entry.get("matched_location") or None,
            kind=entry.get("matched_kind") or None,
        )


# ── LibraryCoverageResult (czy helperSearchSubAgent.ts:56-64) ─────────


@dataclass
class LibraryCoverageResult:
    """Per-sub-problem result from checkLibraryCoverage.

    `sub_problem_id` — child sorry_item id.
    `coverage` — "cited_by_library" or "needs_proof".
    `matched_lemma` — populated when coverage=="cited_by_library".
    `candidates_queried` — token list sent to search_lemmas (telemetry).
    `reasoning` — judge LLM one-sentence reasoning (telemetry).
    """

    sub_problem_id: str
    coverage: str  # "cited_by_library" | "needs_proof"
    matched_lemma: Optional[MatchedLemma] = None
    candidates_queried: Optional[list] = None
    reasoning: Optional[str] = None

    @classmethod
    def from_skill_json(cls, entry: Dict[str, Any]) -> "LibraryCoverageResult":
        """Construct from one element of the SKILL stdout JSON array
        (spec §3.2 output schema)."""
        coverage = str(entry.get("coverage", "needs_proof"))
        matched: Optional[MatchedLemma] = None
        if coverage == "cited_by_library" and entry.get("matched_name"):
            matched = MatchedLemma.from_skill_json(entry)
        return cls(
            sub_problem_id=str(entry["sub_problem_id"]),
            coverage=coverage,
            matched_lemma=matched,
            candidates_queried=entry.get("candidates_queried"),
            reasoning=entry.get("reasoning"),
        )

"""Python dataclass mirrors of czy's `AssumptionDiagnoseResult` and the
helper-assumption schema fields.

Source of truth: `clean/czy-newloop:src/lib/orchestrator/helperSubAgents.ts:115-119`
(`AssumptionDiagnoseResult`).

Field-naming convention: TS source uses camelCase; yaml + Python use
snake_case. The mapping is mechanical:

    TS                       ↔  yaml / Python
    ------------------------ ↔  ------------------------------
    missingAssumptionNLs     ↔  assumption_hints
    findingSummary           ↔  (milestone payload `excerpt`; not persisted on row)
    analysis                 ↔  assumption_analysis

H7 slice (per `docs/H7_HELPER_ASSUMPTION_SPEC.md` §5) extends the
slice 1 v2 schema with two additive fields per sorry_item:

    assumption_hints: list[str]    (default [])
    assumption_analysis: str       (default "")

Schema version stays 2 — additive within v2, not a v3 bump. The
migration patch lives in `_history_log_types.py:migrate_item_v1_to_v2`.

**D-1 semantic (per spec §10): OVERWRITE-ON-EACH-CALL, NOT FIFO-accumulate.**
czy's `AssumptionSubAgent.diagnose` (`helperAssumptionSubAgent.ts:74-132`)
returns `missingAssumptionNLs: list[str]` per call — czy emits a per-call
list and never persists across calls in any global structure. The dormant
`AssumptionVersion` rich chain (`helperSubAgents.ts:185-204`) was intended
but never wired in czy itself (per `docs/CZY_PORT_AUDIT.md` row L4 "types
exist but not actually populated even in czy"). Cross-round chain semantic
in czy emerges through description-enrichment + re-autoformalize cycle
(H4's territory), NOT yaml accumulation.

**Forward-compat note.** The field name `assumption_hints` is preserved at
the schema-evolution level: a future slice can lift the flat `list[str]`
into the richer `AssumptionVersion` chain (label / basedOn / status /
derivedBy / retractionReason) without schema migration. H7 deliberately
does NOT introduce accumulation czy doesn't have.

Per-entry char cap is 400 (czy `:114-118` `.trim().slice(0, 400)`); analysis
char cap is 400 (czy `:120` `.trim().slice(0, 400)`). Mirrors are enforced
in `extract_assumption.py`.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List


# ── Char caps mirroring czy ────────────────────────────────────────────
#
# czy `helperAssumptionSubAgent.ts:114-120` clips each assumption NL to
# 400 chars and the analysis text to 400 chars. We mirror byte-faithfully
# so a downstream consumer that reads either source sees the same shape.

ASSUMPTION_HINT_MAX_CHARS = 400
ASSUMPTION_ANALYSIS_MAX_CHARS = 400


# ── Per-call diagnose result (czy AssumptionDiagnoseResult) ────────────


@dataclass
class AssumptionDiagnoseResult:
    """Mirrors czy's `AssumptionDiagnoseResult`
    (`helperSubAgents.ts:115-119`).

    `missing_assumption_nls` — each entry is a self-contained NL
    statement of one missing hypothesis (≤400 chars, czy `:114-118`).
    Used to overwrite `sorry_item.assumption_hints` per D-1.

    `analysis` — short NL explanation (≤400 chars, czy `:120`) of why
    the proof is likely stuck and what adding these assumptions would
    fix. Used to overwrite `sorry_item.assumption_analysis` per D-7.

    `finding_summary` — czy `:122, :160-165` builds this for tier2-
    findings aggregation. Dormant in czy itself; SDK-bridge equivalent
    is the `assumption-extracted` milestone payload's `excerpt` field
    (spec §4). Not persisted on the sorry row.
    """

    missing_assumption_nls: List[str] = field(default_factory=list)
    analysis: str = ""
    finding_summary: str = ""

    def to_yaml(self) -> Dict[str, Any]:
        """Serialize to a yaml-ready dict. Inverse of `from_yaml`.

        Note: yaml-clean — drops `finding_summary` since it's not
        persisted on the sorry row (it's a milestone-only field per
        §4). The two persisted fields go through dedicated row-level
        writes in `extract_assumption.py`, not via this serializer.
        """
        d = asdict(self)
        d.pop("finding_summary", None)
        return d

    @classmethod
    def from_yaml(cls, d: Dict[str, Any]) -> "AssumptionDiagnoseResult":
        return cls(
            missing_assumption_nls=list(d.get("missing_assumption_nls", [])),
            analysis=str(d.get("analysis", "")),
            finding_summary="",
        )

    @classmethod
    def empty(cls) -> "AssumptionDiagnoseResult":
        """Mirrors czy's `emptyResult()` `:180-182`. Returned on parse
        failure or empty LLM response. Caller treats as "no missing
        assumptions found" — no yaml mutation in extract_assumption.py
        beyond optional analysis-text persistence."""
        return cls()


# ── Helpers ────────────────────────────────────────────────────────────


def trim_hint(s: str) -> str:
    """czy parity: `.trim().slice(0, 400)` (`:114-118`).

    Used per-entry on each missingAssumption NL string. Empty / whitespace-
    only strings are filtered upstream (czy `:115`); this function just
    trims and truncates. Returns the cleaned string.
    """
    return s.strip()[:ASSUMPTION_HINT_MAX_CHARS]


def trim_analysis(s: str) -> str:
    """czy parity: `.trim().slice(0, 400)` (`:120`)."""
    return s.strip()[:ASSUMPTION_ANALYSIS_MAX_CHARS]


def build_finding_summary(nls: List[str], analysis: str) -> str:
    """czy `:160-165` `buildFindingSummary` byte-faithful port.

      - If no missing assumptions → return analysis truncated to 300.
      - Otherwise, build "Missing: <nl1[:80]>; <nl2[:80]>" (first 2),
        with "(+N more)" suffix if more than 2, then truncate to 300.

    Used as the `excerpt` field in the `assumption-extracted` milestone
    payload (spec §4) so observability can surface a one-line summary
    without dragging the full hint list.
    """
    if not nls:
        return analysis[:300]
    prefix = "Missing: " + "; ".join(nl[:80] for nl in nls[:2])
    suffix = f" (+{len(nls) - 2} more)" if len(nls) > 2 else ""
    return f"{prefix}{suffix}"[:300]

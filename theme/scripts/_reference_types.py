"""Python dataclass mirrors of czy's reference-coverage types.

Source of truth: `clean/czy-newloop:src/lib/orchestrator/helperSubAgents.ts:53-58, 176-183`
(`ReferenceSubAgentResult`, `ReferenceAnalysis`).

Field-naming convention: TS source uses camelCase; yaml + Python use
snake_case. The mapping is mechanical:

    TS                       ↔  yaml / Python
    ------------------------ ↔  ------------------------------
    subProblemId             ↔  sub_problem_id
    coverage                 ↔  coverage_state  (yaml top-level field; per-entry preserves "coverage")
    matchingStatement        ↔  matching_statement
    replacementStatement     ↔  replacement_statement
    sorryMapping[id]         ↔  coverage_citation  (per-sorry yaml string)

E4 slice (per `docs/E4_REFERENCE_SUBAGENT_SPEC.md` §5) extends the
slice 1 v2 schema with three additive fields per sorry_item:

    references: list[ReferenceEntry]    (default [])
    coverage_state: str                  (default "needs_proof")
    coverage_citation: str | absent      (only present when set)

Schema version stays 2 — additive within v2, not a v3 bump. The
migration patch lives in `_history_log_types.py:migrate_item_v1_to_v2`
(see spec §5 for the exact 3-line edit).

Reserve `references_*` namespace for any follow-on additions (e.g.
`references_probe_results` for the deferred `referenceProbe` slice).
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any, Dict, List, Optional


# ── Coverage states ────────────────────────────────────────────────────
#
# `cited_by_library` is written by the existing R1-R5 Mathlib search
# ladder (slice already in place). The other three are written by
# helper-reference (this slice). `needs_proof` is the migration default
# for any sorry that hasn't been touched by either path yet.

COVERAGE_STATES = (
    "cited_by_library",     # R1-R5: Mathlib already has this; bypass helper-reference
    "cited_by_reference",   # this slice: paper's reference fully covers the sub-problem
    "partial_coverage",     # this slice: reference is relevant but mismatched
    "no_coverage",          # this slice: reference doesn't help (per-entry detail)
    "needs_proof",          # default — no coverage signal yet, prover should attack
)

DEFAULT_COVERAGE_STATE = "needs_proof"


# ── Per-sub-problem result (czy ReferenceSubAgentResult) ──────────────


@dataclass
class ReferenceEntry:
    """One row in `sorry_item.references[]`. Mirrors czy's
    `ReferenceSubAgentResult` (`helperSubAgents.ts:53-58`).

    `assessment` is the LLM's NL 5-part judgment (claim / theorem /
    hypothesis-match / conclusion-match / final-judgment) — load-bearing
    for downstream re-prompting; preserved verbatim.

    `matching_statement` is non-null only when `coverage ==
    cited_by_reference` AND the LLM provided one (czy `:446-448`
    short-circuit). Per-entry `coverage` here is per-sub-problem; the
    aggregate `coverage_state` on the sorry_item itself reflects whether
    the most-covered entry won.

    `replacement_statement` is the InformalAgent hand-off field. czy
    sets it on `cited_by_reference`. The SDK-bridge consumer (slice 03)
    reads this to remove already-covered sub-problems from the next
    decomposition round."""

    sub_problem_id: str
    coverage: str  # one of COVERAGE_STATES (per-entry; usually not "cited_by_library")
    assessment: str
    matching_statement: Optional[str] = None
    replacement_statement: Optional[str] = None

    def to_yaml(self) -> Dict[str, Any]:
        d = asdict(self)
        # Yaml-clean: drop None-valued optional fields rather than
        # round-tripping them as `field: null` (matches slice 1 pattern).
        return {k: v for k, v in d.items() if v is not None}

    @classmethod
    def from_yaml(cls, d: Dict[str, Any]) -> "ReferenceEntry":
        return cls(
            sub_problem_id=str(d["sub_problem_id"]),
            coverage=str(d.get("coverage", "no_coverage")),
            assessment=str(d.get("assessment", "")),
            matching_statement=d.get("matching_statement"),
            replacement_statement=d.get("replacement_statement"),
        )


# ── Validation / coalesce helpers ──────────────────────────────────────


def coalesce_coverage(raw: Any) -> str:
    """Map any LLM-returned coverage string → one of the three valid
    helper-reference outputs. Mirrors czy `:443-445`: unknown values
    default to `no_coverage` (defensive — LLMs sometimes reply
    'no_match' or 'partial' or 'covered').

    `cited_by_library` is NOT a valid output here — that path runs
    BEFORE helper-reference (R1-R5 Mathlib search). If it somehow
    leaks in, treat as `no_coverage` so the sorry stays attackable.

    Deliberate deviation from czy: this implementation lowercases the
    input before the membership check, so `"CITED_BY_REFERENCE"` and
    `"Cited_By_Reference"` both normalize. czy `:443-445` is
    case-sensitive (`validCoverages.includes(s)`). The looser policy
    is intentional — LLMs occasionally upcase or title-case enum
    strings, and treating those as `no_coverage` would silently lose
    valid signal. If byte-faithful czy parity is ever required, drop
    the `.lower()` call.
    """
    if not isinstance(raw, str):
        return "no_coverage"
    s = raw.strip().lower()
    if s == "cited_by_reference":
        return "cited_by_reference"
    if s == "partial_coverage":
        return "partial_coverage"
    return "no_coverage"


def aggregate_coverage_state(entries: List[ReferenceEntry]) -> str:
    """Pick the sorry_item's top-level `coverage_state` from per-entry
    results. Precedence: any entry with `cited_by_reference` →
    `cited_by_reference`; else any with `partial_coverage` →
    `partial_coverage`; else `needs_proof`.

    Rationale: czy's `helperAgent.ts:321-352` builds
    `HelperCoverageResult[]` per-sub-problem; the SDK-bridge port
    aggregates at the parent level because the sorry_item IS the parent
    in the tree-state machine — sub-problems are children rows. The
    parent's `coverage_state` reflects "the strongest signal we got
    across all my sub-problems."

    Note this is the aggregation rule for what gets WRITTEN into the
    sorry_item.coverage_state field. Per-entry coverage in
    `references[]` preserves the granular signal for downstream consumers.
    """
    if not entries:
        return DEFAULT_COVERAGE_STATE
    if any(e.coverage == "cited_by_reference" for e in entries):
        return "cited_by_reference"
    if any(e.coverage == "partial_coverage" for e in entries):
        return "partial_coverage"
    return DEFAULT_COVERAGE_STATE


# ── Citation string (czy sorryMapping value) ───────────────────────────


def make_coverage_citation(matching_statement: str) -> str:
    """Format the per-sorry citation string. czy
    `helperReferenceSubAgent.ts:208-211` writes
    `\"-- cited from reference: <matching_statement>\"` into
    `sorryMapping[id]`. We mirror byte-for-byte so any follow-on
    consumer that splits on `\": \"` works against either source.
    """
    return f"-- cited from reference: {matching_statement}"

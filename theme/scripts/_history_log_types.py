"""Python dataclass mirrors of czy's `HistoryLogEntry` and node-state types.

Source of truth: `clean/czy-newloop:src/lib/orchestrator/proofState.ts:121-139`
(`HistoryLogEntry`) + `:28` (node states).

Field-naming convention: TS source uses camelCase; yaml + Python use
snake_case. The mapping is mechanical:

    TS                    ↔  yaml / Python
    --------------------- ↔  -----------------------
    iteration             ↔  iteration
    decomposition         ↔  decomposition
    decisionReason        ↔  decision_reason
    decompositionDetails  ↔  decomposition_details (each: {id, description})
    results               ↔  results (each: {sub_problem_id, status,
                              fail_reason})
    usedReferences        ↔  used_references
    usedAssumptions       ↔  used_assumptions
    retreatReason         ↔  retreat_reason

This module also carries the **v1 → v2 sorry_backlog.yaml schema migration**.

  v1: pre-czy-port. Flat sorry_items[] with `dependencies` (cross-sorry
      DAG), `stuck_rounds`, no decomposition/state-machine fields.
  v2: czy decomposition tree. Each sorry_item gains `state` (4 states),
      `children`, `parent_id`, `history_log`. Existing fields untouched.

Detection: missing `schema_version` key → v1 (current statlean state).
Migration is idempotent — calling on a v2 input is a no-op.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional

# ── State machine (czy proofState.ts:28) ───────────────────────────────

# Literal type for static checkers; the runtime accepts any of these strings.
NODE_STATES = ("INITIALIZED", "INACTIVE_WAIT", "ACTIVE_PROVING", "DONE")
RESULT_STATUSES = ("proved", "stuck", "error", "cancelled")

DEFAULT_STATE = "INITIALIZED"
SCHEMA_VERSION_V2 = 2


# ── HistoryLogEntry shape (czy proofState.ts:121-139) ──────────────────


@dataclass
class DecompositionDetail:
    id: str
    description: str


@dataclass
class TaskResult:
    sub_problem_id: str
    status: str  # one of RESULT_STATUSES
    fail_reason: Optional[str] = None


@dataclass
class HistoryLogEntry:
    iteration: int
    decomposition: List[str]
    results: List[TaskResult]
    decision_reason: Optional[str] = None
    decomposition_details: List[DecompositionDetail] = field(default_factory=list)
    used_references: List[str] = field(default_factory=list)
    used_assumptions: List[str] = field(default_factory=list)
    retreat_reason: Optional[str] = None

    def to_yaml(self) -> Dict[str, Any]:
        """Serialize to a yaml-ready dict. Inverse of `from_yaml`."""
        return asdict(self)

    @classmethod
    def from_yaml(cls, d: Dict[str, Any]) -> "HistoryLogEntry":
        return cls(
            iteration=int(d["iteration"]),
            decomposition=list(d.get("decomposition", [])),
            results=[
                TaskResult(
                    sub_problem_id=r["sub_problem_id"],
                    status=r["status"],
                    fail_reason=r.get("fail_reason"),
                )
                for r in d.get("results", [])
            ],
            decision_reason=d.get("decision_reason"),
            decomposition_details=[
                DecompositionDetail(id=dd["id"], description=dd["description"])
                for dd in d.get("decomposition_details", [])
            ],
            used_references=list(d.get("used_references", [])),
            used_assumptions=list(d.get("used_assumptions", [])),
            retreat_reason=d.get("retreat_reason"),
        )


# ── v1 → v2 migration helpers ──────────────────────────────────────────


def detect_schema_version(yaml_data: Dict[str, Any]) -> int:
    """Return 2 iff the yaml top-level has `schema_version: 2`, else 1.

    Current statlean v1 yaml has no `schema_version` key (it has a separate
    `version: v200` stamp which we treat as opaque metadata, not schema
    versioning). Missing key → v1.
    """
    return 2 if yaml_data.get("schema_version") == SCHEMA_VERSION_V2 else 1


def migrate_item_v1_to_v2(item: Dict[str, Any]) -> Dict[str, Any]:
    """Apply v2-shape defaults to a single sorry_item.

    Idempotent: if the item already has the v2 fields, untouched fields are
    preserved. If only some fields exist (partial migration), the missing
    ones get defaults.

    E4 (helper-reference port, per `docs/E4_REFERENCE_SUBAGENT_SPEC.md`
    §5) adds three additive fields. Schema version stays 2 — additive
    within v2, not a v3 bump. `coverage_citation` stays absent until
    written (readers tolerate the missing key; that's the "yaml-clean"
    pattern from slice 1).
    """
    if "state" not in item:
        item["state"] = DEFAULT_STATE
    if "children" not in item:
        item["children"] = []
    if "parent_id" not in item:
        item["parent_id"] = None
    if "history_log" not in item:
        item["history_log"] = []
    # E4 helper-reference fields
    if "references" not in item:
        item["references"] = []
    if "coverage_state" not in item:
        item["coverage_state"] = "needs_proof"
    # `coverage_citation` is intentionally NOT defaulted — absent ≠ ""
    # A1 restrategize counter (per docs/A1_RESTRATEGIZE_SPEC.md §5).
    # Bumped only by restrategize_node.py (NOT per prover-result, unlike
    # czy proofLoop.ts:436-437 — see §2.3 D-1 deviation).
    if "attempts" not in item:
        item["attempts"] = 0
    # E11 citation-verify fields (per docs/E11_CITATION_VERIFY_SPEC.md §5).
    # Set by verify_citation.py at Phase 0 R7. citation_verified gets a
    # default (False) so readers can compare bool; done_reason and
    # citation_verified_at are absent until written (E4 coverage_citation
    # precedent — readers tolerate missing key).
    if "citation_verified" not in item:
        item["citation_verified"] = False
    # done_reason absent until written (D11)
    # citation_verified_at absent until written
    # Slice 03 InformalAgent / refinementRound fields (per
    # docs/SLICE_03_INFORMAL_AGENT_SPEC.md §5).
    # informal_round counts refinements committed (czy-parity cap = 2;
    # 1 initial decompose + 2 refinements = 3 total InformalAgent calls
    # per czy `for alignRound = 0; alignRound < 3`). Bumped by
    # refine_decomposition.py on `refined` verdict; reset to 0 by
    # record_retreat.py and restrategize_node.py (D-8).
    if "informal_round" not in item:
        item["informal_round"] = 0
    # coverage_stable signals "alignment loop converged" — set true on
    # noAdjustment OR converged_pre_dispatch verdict; reset to false on
    # retreat / restrategize (D-11).
    if "coverage_stable" not in item:
        item["coverage_stable"] = False
    return item


def migrate_yaml_v1_to_v2(yaml_data: Dict[str, Any]) -> Dict[str, Any]:
    """Apply v2 schema defaults to a v1-shaped yaml dict.

    Mutates yaml_data in place AND returns it (for chaining). Adds
    `schema_version: 2` at the top level if missing; defaults state /
    children / parent_id / history_log on every sorry_item that lacks
    them. Pre-existing values are preserved.

    Idempotent: a v2 yaml passes through unchanged (modulo dict key order,
    which `yaml.safe_dump(sort_keys=False)` will preserve).

    Defensive against `sorry_items: None` (which yaml.safe_load can produce
    when the key exists with empty value); treated as empty list.
    """
    # Single stderr breadcrumb when the live yaml is first promoted v1 → v2.
    # Slice 2 telemetry can use this to confirm the migration ran.
    was_v1 = detect_schema_version(yaml_data) == 1
    if yaml_data.get("schema_version") != SCHEMA_VERSION_V2:
        yaml_data["schema_version"] = SCHEMA_VERSION_V2
    if was_v1:
        item_count = len(yaml_data.get("sorry_items") or [])
        print(
            f"[migrate] sorry_backlog.yaml v1→v2 ({item_count} items)",
            file=sys.stderr,
        )
    # `sorry_items: None` (empty key in yaml) → iterate empty list, not crash.
    for item in (yaml_data.get("sorry_items") or []):
        migrate_item_v1_to_v2(item)
    return yaml_data

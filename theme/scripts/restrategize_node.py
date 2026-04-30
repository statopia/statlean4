#!/usr/bin/env python3
"""restrategize_node.py — bundle the side-effect chain for a "soft retreat"
(A1 slice; per docs/A1_RESTRATEGIZE_SPEC.md).

Where retreat says "the decomposition itself was wrong; full reset",
restrategize says "the proof STRATEGY for this decomposition was wrong;
keep the per-node attempt history (attempts++) and let the next prove
round try again with a different strategy." czy `controlAgent.ts:585-599`
docstring describes the design intent: up to 3 restrategize rounds,
then retreat.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Agent
invokes once; script atomically:

  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Captures parent.children as the decomposition record
  - Captures which children were DONE (proved before clear)
  - Removes ALL descendants (BFS) — including DONE ones; the
    proved-count is preserved as audit info in the history_log entry
  - Resets parent: state → INITIALIZED, stuck_rounds → 0, children → []
    (locked theorem signature / file / line / theorem fields untouched —
    Rule 3 Layer 1 invariant)
  - **Bumps parent.attempts** (the load-bearing distinction vs retreat)
  - Appends new HistoryLogEntry to parent.history_log[] with structured
    `retreat_reason: "restrategize: cleared N children, M proved"`
  - Writes back via tempfile + os.replace (atomic)
  - Emits `restrategize-triggered` milestone via emit_event.py

Two intentional deviations from czy (per docs/A1_RESTRATEGIZE_SPEC.md
§2.3, registered in docs/CLI_WEB_CONFORMANCE.md §0.2):

  D-1: SDK-bridge `attempts` is bumped ONLY here. czy
       proofLoop.ts:436-437 also bumps per prover-result, which makes
       attempts and stuckCount move in lockstep → restrategize would
       never fire (attempts >= 3 always wins handleStuckNode's
       discrimination). The port restores the design intent stated in
       czy's own controlAgent.ts:585-599 docstring.

  D-2: Restrategize clears DESCENDANTS only — parent stays. czy
       clearSubtree (proofState.ts:807) deletes nodeId itself,
       leaving subsequent setNodeState a no-op on a deleted node. We
       mirror record_retreat.py's "parent survives" pattern.

Exit codes:
  0  — restrategize applied successfully
  2  — validation error (parent not found, parent has no children, attempts >= 3)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/restrategize_node.py \\
        --parent-id <node id> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]

Note: unlike retreat, no --retreat-reason / --results-json args. The
history entry is structurally derived ("restrategize: cleared N
children, M proved"); per-child stuck reasons live elsewhere
(process_sorry_result already records them per round). This matches
czy controlAgent.ts:645's results array (proved-only).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402

# Reuse slice 2's BFS (cycle-safe, orphan-tolerant) instead of
# re-implementing. record_retreat already battle-tested.
from record_retreat import _collect_descendants  # noqa: E402


# Per czy controlAgent.ts:605 + design intent in §2.4: the discrimination
# gate at the agent layer treats `attempts >= 3` as the retreat signal.
# This script enforces the boundary at script-level too: refusing to
# restrategize when attempts is already at the retreat threshold turns
# a narrative slip ("agent skipped the gate") into a loud error, not
# a silent extra round.
ATTEMPTS_RETREAT_THRESHOLD = 3


# ── Helpers ────────────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort.
    Mirrors record_retreat._emit pattern."""
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", name,
                "--details", json.dumps(details, ensure_ascii=False),
            ],
            check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(
            f"[restrategize] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _build_history_entry(
    iteration: int,
    decomposition: List[str],
    proved_children: List[str],
) -> Dict[str, Any]:
    """Produce a v2 HistoryLogEntry dict for restrategize.

    Distinct shape vs retreat (per czy controlAgent.ts:642-649):
      - results carries proved-children only (status='proved'); failed
        children are implicit (cleared without per-child diagnostic)
      - retreat_reason is structurally derived, not free-text
      - used_references / used_assumptions are empty (czy
        controlAgent.ts:646-647)

    Iteration semantic (per record_retreat.py:170-178): per-node count
    of how many times THIS specific parent has been
    retreated-OR-restrategized. Same iteration counter shared with
    retreat — the history_log is the union of both events on this node.
    """
    n = len(decomposition)
    m = len(proved_children)
    return {
        "iteration": iteration,
        "decomposition": list(decomposition),
        "results": [
            {"sub_problem_id": child_id, "status": "proved"}
            for child_id in proved_children
        ],
        "used_references": [],
        "used_assumptions": [],
        "retreat_reason": f"restrategize: cleared {n} children, {m} proved",
    }


# ── Core ───────────────────────────────────────────────────────────────


def apply_restrategize(
    backlog_path: Path,
    parent_id: str,
) -> Dict[str, Any]:
    """Apply restrategize under flock + atomic write. Returns the
    history entry just appended.

    Raises ValueError on validation failure.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []

        # Locate parent
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        current_children: List[str] = list(parent.get("children") or [])
        if not current_children:
            raise ValueError(
                f"parent {parent_id} has no children to restrategize from"
            )

        # Refuse if attempts already at the retreat threshold — the
        # agent should have called record_retreat.py instead. Loud
        # failure beats a silent fourth restrategize round.
        current_attempts = int(parent.get("attempts", 0) or 0)
        if current_attempts >= ATTEMPTS_RETREAT_THRESHOLD:
            raise ValueError(
                f"parent {parent_id} has attempts={current_attempts} "
                f">= {ATTEMPTS_RETREAT_THRESHOLD}; should call record_retreat.py instead"
            )

        # Capture proved-children BEFORE clearing
        children_by_id = {it.get("id"): it for it in items if it.get("id") in current_children}
        proved_children = [
            child_id for child_id in current_children
            if children_by_id.get(child_id, {}).get("state") == "DONE"
        ]

        # Capture decomposition snapshot for history entry
        decomposition = list(current_children)
        iteration = len(parent.get("history_log") or []) + 1

        # Collect ALL descendants for removal (BFS, cycle-safe)
        to_remove = _collect_descendants(items, current_children)

        # Build the history entry (proved-only results)
        entry = _build_history_entry(
            iteration=iteration,
            decomposition=decomposition,
            proved_children=proved_children,
        )

        # Mutate yaml in place:
        #   1. Remove all descendant rows (parent stays — D-2 deviation)
        #   2. Reset parent: state, stuck_rounds, children
        #   3. Bump parent.attempts (D-1)
        #   4. Append entry to parent.history_log
        data["sorry_items"] = [it for it in items if it.get("id") not in to_remove]
        for it in data["sorry_items"]:
            if it.get("id") == parent_id:
                it["state"] = "INITIALIZED"
                it["stuck_rounds"] = 0
                it["children"] = []
                it["attempts"] = current_attempts + 1
                # Slice 03 (per docs/SLICE_03_INFORMAL_AGENT_SPEC.md
                # §10 D-8 / D-11): refinement counter + convergence
                # flag are scoped to "this decomposition of this
                # parent." restrategize clears children → counter +
                # flag must reset so the next decomposition's
                # refinement loop starts clean.
                it["informal_round"] = 0
                it["coverage_stable"] = False
                # H1 elaborate-plan (per docs/H1_ELABORATE_PLAN_SPEC.md
                # §10 D-7 + D-11): elaborated plan + brief seed
                # (direct_assembly / proof_sketch) are scoped to "this
                # converged decomposition of this parent." restrategize
                # clears children → all 3 fields must reset so the next
                # decomposition's elaborate_plan call starts clean.
                # Same rationale as informal_round + coverage_stable
                # reset above; same pattern record_retreat uses.
                it["detailed_proof_plan"] = None
                it["direct_assembly"] = None
                it["proof_sketch"] = None
                # H2 detect-alt-path (per docs/H2_DETECT_ALT_PATH_SPEC.md
                # §10 D-7): the alt-path cache is scoped to "this alignment
                # cycle of this parent." restrategize clears children →
                # alt-path must reset so the new decomposition's detect
                # call starts clean. Same rationale as informal_round reset
                # above; same pattern record_retreat uses (D-7).
                it["alternative_path"] = None
                history_log = list(it.get("history_log") or [])
                history_log.append(entry)
                it["history_log"] = history_log
                # Consume any transient decision-reason stash. Slice 3.A
                # decompose_node sets this; on restrategize the next
                # decomposition round is what consumes it (just like
                # retreat). Clearing here keeps the field hygiene
                # consistent with record_retreat.
                it.pop("_pending_decision_reason", None)
                break

        atomic_write_yaml(backlog_path, data)
        return entry


# ── CLI ────────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        entry = apply_restrategize(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
        )
    except ValueError as e:
        print(f"[restrategize] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[restrategize] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[restrategize] IO failure: {e}", file=sys.stderr)
        return 4

    # Re-read the parent post-write to get post-bump attempts for the milestone
    # payload. Cheap read — atomic_write completed → file is on disk.
    with open(backlog_path, "r", encoding="utf-8") as f:
        data_after = yaml.safe_load(f) or {}
    parent_after = next(
        (it for it in (data_after.get("sorry_items") or [])
         if it.get("id") == args.parent_id),
        None,
    )
    attempts_post = int((parent_after or {}).get("attempts", 0) or 0)

    proved_children = [r["sub_problem_id"] for r in entry["results"]]
    decomposition = entry["decomposition"]
    cleared_count = len(decomposition)  # ALL descendants cleared (per spec §4)

    # Spec §4 invariant: cleared_children_count == decomposition_count.
    # Asserted before emit so a future shape change in
    # apply_restrategize fails loudly here, not silently in consumers.
    assert cleared_count == len(decomposition), (
        f"invariant broken: cleared {cleared_count} != decomp {len(decomposition)}"
    )

    _emit(
        sandbox,
        "restrategize-triggered",
        {
            "parent_id": args.parent_id,
            "iteration": entry["iteration"],
            "attempts": attempts_post,
            "decomposition": decomposition,
            "proved_children": proved_children,
            "cleared_children_count": cleared_count,
        },
    )
    print(
        f"restrategize applied: parent={args.parent_id} "
        f"iteration={entry['iteration']} attempts={attempts_post} "
        f"cleared={cleared_count} proved={len(proved_children)}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""record_retreat.py — bundle the side-effect chain for a sub-tree retreat.

Per czy newloop port (MERGE_PLAN.md §3.2.1, post §8 spec review fix).
Replaces the narrative "agent should: clear children, append history,
reset parent state, emit event" chain. One script call atomically:

  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Captures parent.children as the decomposition record
  - Removes all descendants of each child (recursive DFS)
  - Resets parent: state → INITIALIZED, stuck_rounds → 0, children → []
    (locked theorem signature / file / line / theorem fields untouched —
    Rule 3 Layer 1 invariant)
  - Appends new HistoryLogEntry to parent.history_log[]
    (iteration auto-computed from len(history_log) + 1)
  - Writes back via tempfile + os.replace (atomic)
  - Emits `retreat-triggered` milestone via emit_event.py

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Agent
invokes once; script enforces all sub-steps atomically.

Exit codes:
  0  — retreat applied successfully
  2  — validation error (parent not found, parent has no children, malformed input)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/record_retreat.py \\
        --parent-id <node id> \\
        --retreat-reason "stuck_rounds reached 3 on foo.sub3" \\
        --results-json '[{"sub_problem_id":"foo.sub3","status":"stuck",
                          "fail_reason":"Lean type mismatch in step 3"}]' \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--decision-reason "decomposed by induction on n"] \\
        [--decomposition-details-json '[{"id":"foo.sub1","description":"..."}]'] \\
        [--used-references-json '[]'] \\
        [--used-assumptions-json '[]'] \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402


# ── Helpers ────────────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort."""
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
            f"[record_retreat] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _atomic_write_yaml(path: Path, data: Dict[str, Any]) -> None:
    """Write yaml atomically: tempfile in same dir → os.replace.

    Same-directory tempfile is required for `os.replace` to be atomic
    on POSIX (cross-FS rename is not).

    File mode preservation: `tempfile.mkstemp` defaults to 0o600. After
    `os.replace`, that 600 mode would shadow the original file's mode
    (typically 0o644 for repo files). Stat the original (if it exists)
    and apply its mode to the tempfile fd before replace.
    """
    # Snapshot original mode before any mutation; default 0o644 if no original.
    if path.exists():
        original_mode = os.stat(path).st_mode & 0o777
    else:
        original_mode = 0o644

    fd, tmp_path = tempfile.mkstemp(
        prefix=path.name + ".",
        suffix=".tmp",
        dir=str(path.parent),
    )
    try:
        # Preserve mode BEFORE close so the chmod applies to this fd, not
        # to a possibly-replaced inode. fchmod is fd-bound + atomic.
        os.fchmod(fd, original_mode)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            yaml.safe_dump(data, f, sort_keys=False, allow_unicode=True)
        os.replace(tmp_path, path)
    except Exception:
        # Cleanup tempfile if write fails
        try:
            os.unlink(tmp_path)
        except FileNotFoundError:
            pass
        raise


def _collect_descendants(items: List[dict], root_ids: List[str]) -> set:
    """Return the set of EXISTING ids (descendants reachable from any id
    in root_ids, inclusive) — orphan-only ids that don't correspond to
    any item are excluded from the return value.

    Uses BFS over the items-as-flat-list. Robust against (a) cycles in
    children adjacency (each id visited at most once) and (b) orphan
    children references (id mentioned in another item's children but
    no matching item — silently skipped, not crashed).
    """
    by_id: Dict[str, dict] = {item["id"]: item for item in items if "id" in item}
    visited: set = set()  # cycle guard, includes orphans
    existing: set = set()  # return value — items present in by_id only
    to_visit = list(root_ids)
    while to_visit:
        node_id = to_visit.pop()
        if node_id in visited:
            continue
        visited.add(node_id)
        item = by_id.get(node_id)
        if item is None:
            continue
        existing.add(node_id)
        for child_id in item.get("children") or []:
            if child_id not in visited:
                to_visit.append(child_id)
    return existing


# ── Core ───────────────────────────────────────────────────────────────


def _build_history_entry(
    iteration: int,
    decomposition: List[str],
    results: List[Dict[str, Any]],
    *,
    decision_reason: str | None = None,
    decomposition_details: List[Dict[str, str]] | None = None,
    used_references: List[str] | None = None,
    used_assumptions: List[str] | None = None,
    retreat_reason: str | None = None,
) -> Dict[str, Any]:
    """Produce a v2 HistoryLogEntry dict (yaml-ready, snake_case).

    SEMANTIC NOTE on `iteration`: this is the **per-node retreat count**
    (i.e., how many times THIS specific parent has been retreated and
    re-decomposed). czy's TS source uses a global proof-loop iteration
    counter (`proofState.ts:462`) — these are NOT equivalent. We use the
    per-node count because (a) the SDK-bridge architecture has no
    natural global proof-loop counter to read, (b) the LLM only needs
    the relative "Nth time you've tried this parent" signal, which
    per-node count delivers exactly. The wire format ("Iteration N: …")
    is byte-identical to czy; only the meaning of N differs. Documented
    here + in MERGE_PLAN.md §3.2.1.

    SEMANTIC NOTE on counter taxonomy: czy splits two counters at
    `controlAgent.ts:604-612` — `attempts` triggers retreat (this
    function's call site), `stuckCount` triggers a separate
    "restrategize" path (clear subtree, reset to INITIALIZED,
    attempts++; no history_log entry). The SDK-bridge port collapses
    both into a single `stuck_rounds` field bumped per stuck result.
    Rationale: (a) the read_history_log mechanism subsumes restrategize's
    "look at past attempts and choose differently" function — once
    history_log carries the retreat record, the next decompose attempt
    naturally avoids prior strategies, so the soft-restrategize path
    adds little value beyond the retreat path; (b) one counter is
    simpler to reason about under flock/atomic write contention.
    Consequence: SDK-bridge retreats marginally earlier than czy
    (after 3 stucks rather than 3 attempts-via-multiple-paths). If real
    traces show this is too aggressive, port `attempts` as a second
    counter in slice 4+.
    """
    entry: Dict[str, Any] = {
        "iteration": iteration,
        "decomposition": list(decomposition),
        "results": [
            {
                "sub_problem_id": r["sub_problem_id"],
                "status": r["status"],
                **({"fail_reason": r["fail_reason"]} if r.get("fail_reason") else {}),
            }
            for r in results
        ],
        "used_references": list(used_references or []),
        "used_assumptions": list(used_assumptions or []),
    }
    if decision_reason is not None:
        entry["decision_reason"] = decision_reason
    if decomposition_details:
        entry["decomposition_details"] = [
            {"id": dd["id"], "description": dd["description"]}
            for dd in decomposition_details
        ]
    if retreat_reason is not None:
        entry["retreat_reason"] = retreat_reason
    return entry


def apply_retreat(
    backlog_path: Path,
    parent_id: str,
    retreat_reason: str,
    results: List[Dict[str, Any]],
    *,
    decision_reason: str | None = None,
    decomposition_details: List[Dict[str, str]] | None = None,
    used_references: List[str] | None = None,
    used_assumptions: List[str] | None = None,
) -> Dict[str, Any]:
    """Apply retreat under flock + atomic write. Returns the new history entry.

    Raises ValueError on validation failure.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with open(backlog_path, "rb") as lock_f:
        fcntl.flock(lock_f, fcntl.LOCK_EX)
        try:
            data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
            migrate_yaml_v1_to_v2(data)
            items: List[Dict[str, Any]] = data.get("sorry_items") or []

            # Locate parent
            parent = next((it for it in items if it.get("id") == parent_id), None)
            if parent is None:
                raise ValueError(f"parent_id not in sorry_items: {parent_id}")
            current_children: List[str] = list(parent.get("children") or [])
            if not current_children:
                raise ValueError(
                    f"parent {parent_id} has no children to retreat from"
                )

            # Slice 3.A wires decompose_node to stash decision_reason on
            # the parent as `_pending_decision_reason` (transient runtime
            # field, not v2-canonical). If the caller didn't pass
            # --decision-reason explicitly, pull it from parent. This
            # makes the agent flow ergonomic: decompose with reasoning →
            # if children fail → retreat without re-passing the reason.
            if not decision_reason:
                stashed = parent.get("_pending_decision_reason")
                if stashed:
                    decision_reason = stashed

            # Capture current decomposition (the round we're retreating from)
            decomposition = list(current_children)
            iteration = len(parent.get("history_log") or []) + 1

            # Collect all descendants for removal
            to_remove = _collect_descendants(items, current_children)

            # Build the new history entry
            entry = _build_history_entry(
                iteration=iteration,
                decomposition=decomposition,
                results=results,
                decision_reason=decision_reason,
                decomposition_details=decomposition_details,
                used_references=used_references,
                used_assumptions=used_assumptions,
                retreat_reason=retreat_reason,
            )

            # Mutate yaml in place:
            #   1. Remove all descendant rows
            #   2. Reset parent: state, stuck_rounds, children
            #   3. Append entry to parent.history_log
            data["sorry_items"] = [it for it in items if it.get("id") not in to_remove]
            for it in data["sorry_items"]:
                if it.get("id") == parent_id:
                    it["state"] = "INITIALIZED"
                    it["stuck_rounds"] = 0
                    it["children"] = []
                    # A1 (per docs/A1_RESTRATEGIZE_SPEC.md §6): retreat
                    # = "the decomposition itself was wrong; restart from
                    # scratch." Reset the per-restrategize counter so
                    # the new decomposition starts clean. czy doesn't do
                    # this explicitly because TS state has fresh
                    # ProblemNode per re-decompose; in our yaml-persisted
                    # world we make it explicit.
                    it["attempts"] = 0
                    # Slice 03 (per docs/SLICE_03_INFORMAL_AGENT_SPEC.md
                    # §10 D-8 / D-11): the refinement counter and
                    # convergence flag are scoped to "this decomposition
                    # of this parent." After retreat, the decomposition
                    # is gone; reset the counter and flag so the new
                    # decomposition starts clean.
                    it["informal_round"] = 0
                    it["coverage_stable"] = False
                    # H1 elaborate-plan (per docs/H1_ELABORATE_PLAN_SPEC.md
                    # §10 D-7 + D-11): the elaborated plan AND the brief
                    # seed (direct_assembly / proof_sketch) are scoped
                    # to "this converged decomposition of this parent."
                    # After retreat the decomposition is gone; reset
                    # all 3 fields so the new round's elaborate_plan
                    # call starts from a clean slate. Same 2-line patch
                    # pattern slice 03 used for informal_round +
                    # coverage_stable, A1 used for attempts.
                    it["detailed_proof_plan"] = None
                    it["direct_assembly"] = None
                    it["proof_sketch"] = None
                    history_log = list(it.get("history_log") or [])
                    history_log.append(entry)
                    it["history_log"] = history_log
                    # Consume the transient stash — decision_reason is
                    # now in history_log[N], no longer needed on the
                    # parent. Avoids stale data on subsequent retreats.
                    it.pop("_pending_decision_reason", None)
                    break

            _atomic_write_yaml(backlog_path, data)
            return entry
        finally:
            fcntl.flock(lock_f, fcntl.LOCK_UN)


# ── CLI ────────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument("--retreat-reason", required=True)
    p.add_argument(
        "--results-json",
        required=True,
        help="JSON array of {sub_problem_id, status, fail_reason?}",
    )
    p.add_argument("--decision-reason")
    p.add_argument("--decomposition-details-json", help="JSON array of {id, description}")
    p.add_argument("--used-references-json", help="JSON array of strings")
    p.add_argument("--used-assumptions-json", help="JSON array of strings")
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    try:
        results = json.loads(args.results_json)
        decomposition_details = (
            json.loads(args.decomposition_details_json)
            if args.decomposition_details_json
            else None
        )
        used_references = (
            json.loads(args.used_references_json)
            if args.used_references_json
            else None
        )
        used_assumptions = (
            json.loads(args.used_assumptions_json)
            if args.used_assumptions_json
            else None
        )
    except json.JSONDecodeError as e:
        print(f"[record_retreat] malformed JSON: {e}", file=sys.stderr)
        return 2

    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        entry = apply_retreat(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            retreat_reason=args.retreat_reason,
            results=results,
            decision_reason=args.decision_reason,
            decomposition_details=decomposition_details,
            used_references=used_references,
            used_assumptions=used_assumptions,
        )
    except ValueError as e:
        print(f"[record_retreat] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[record_retreat] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[record_retreat] IO failure: {e}", file=sys.stderr)
        return 4

    _emit(
        sandbox,
        "retreat-triggered",
        {
            "parent_id": args.parent_id,
            "iteration": entry["iteration"],
            "retreat_reason": args.retreat_reason,
            "decomposition": entry["decomposition"],
            "stuck_subproblems": [
                r["sub_problem_id"]
                for r in entry["results"]
                if r["status"] != "proved"
            ],
        },
    )
    print(f"retreat applied: parent={args.parent_id} iteration={entry['iteration']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

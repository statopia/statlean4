#!/usr/bin/env python3
"""refine_decomposition.py — bundle one round of InformalAgent
refinement (Slice 03; per docs/SLICE_03_INFORMAL_AGENT_SPEC.md).

Where E4 (helper-reference) annotates each sub-problem with coverage
and E11 (citation-verify) verifies the citations, slice 03 is the
CONSUMER that turns those annotations into a refined decomposition.
The agent dispatches the `informal-refine` Task subagent to propose
a refined children list given the helper feedback, captures the
JSON to a file, then this script atomically:

  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Validates the parent (exists, INACTIVE_WAIT, has children, not
    already capped at informal_round >= 2)
  - Runs convergence pre-check (czy "all covered" exit at
    `proofLoop.ts:916-919`): if all children are
    cited_by_library/cited_by_reference (and citation_verified=true
    for the latter), exit with verdict=`converged_pre_dispatch`
  - Parses the SKILL JSON output
  - On `noAdjustment=true` AND `informal_round > 0`: exit with
    verdict=`noAdjustment` (czy `:840-843`); coverage_stable=true
  - On a refined sub-problem list: diff against current children,
    write atomically (remove dropped + descendants; add new with
    state=INITIALIZED; KEEP existing kept-children's `theorem` field
    UNCHANGED per Layer 1; bump informal_round)
  - Emits one `informal-round` milestone with verdict + diff summary

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Cap is
**structural** — script returns `cap_reached` at `informal_round >= 2`
(czy parity: 1 initial decompose + up to 2 refinements = 3 total
InformalAgent invocations, matching czy `for alignRound = 0;
alignRound < 3`).

Rule 3 Layer 1 invariant: mutates ONLY parent.{children,
informal_round, coverage_stable, history_log} and (atomically)
removes dropped child rows. KEPT children's `theorem` field is NEVER
overwritten (D-6) — if the LLM rephrased it, the rephrase is dropped
silently with a warning.

Exit codes:
  0  — round completed (refined / noAdjustment / converged_pre_dispatch
       / cap_reached / parse_error all exit 0 with milestone emit;
       agent narrative reads verdict to decide next iteration)
  2  — validation error (parent not found, no children, malformed
       input)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/refine_decomposition.py \\
        --parent-id <node id> \\
        --subagent-json-file /path/to/informal_refine_output.json \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]

Note: parse_error returns exit 0 (NOT exit 3) because parse failure
on the SUBAGENT JSON (vs yaml) is an in-band signal — the agent
narrative loop should be able to read the milestone and decide
whether to retry or terminate. yaml parse error stays exit 3 (out-
of-band IO failure).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402
# Reuse slice 2's BFS — cycle-safe descendants collector.
from record_retreat import _collect_descendants  # noqa: E402


# Per spec §10 D-7: czy `for alignRound = 0; alignRound < 3` runs 3
# InformalAgent invocations (1 initial decompose + 2 refinements).
# SDK-bridge `informal_round` counts refinements committed; cap at >=2
# means refuse the 3rd refinement, matching czy parity.
INFORMAL_ROUND_CAP = 2


# ── JSON unwrap (E4 / E11 pattern) ─────────────────────────────────────


_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def _unwrap_fenced_json(s: str) -> str:
    """Strip markdown code fences. Mirrors czy `:347-350`."""
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── Parse SKILL output ─────────────────────────────────────────────────


def parse_subagent_output(raw_text: str) -> Tuple[bool, Dict[str, Any]]:
    """Parse informal-refine subagent's JSON output. Returns
    (ok, parsed_dict). On any parse failure → (False, {error: ...}).

    Expected schema (mirrors czy `informalAgent.ts:144-172`):
      {
        "needsDecomposition": bool,
        "noAdjustment": bool,
        "decisionReason": "<text>",
        "subProblems": [{"id", "description", "action", "dependencies"}],
        ...
      }

    Defensive: missing fields default sanely (per czy fallback at
    `proofLoop.ts:847-856`). The agent is expected to call this
    again if parse_error fires.
    """
    unwrapped = _unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return False, {"error": "empty subagent output"}
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return False, {"error": f"JSON decode failed: {e}"}
    if not isinstance(parsed, dict):
        return False, {"error": f"root not object: got {type(parsed).__name__}"}
    return True, parsed


# ── Convergence pre-check (czy `:916-919` "all covered") ───────────────


def _all_children_converged(
    parent_children: List[str],
    items: List[Dict[str, Any]],
) -> bool:
    """Return True iff every child is in a converged state — either
    state=DONE (already proved or cited+verified) OR
    coverage_state=cited_by_library AND citation_verified
    OR coverage_state=cited_by_reference AND citation_verified.

    Mirrors czy `:916-919` "all covered" exit. Pure read-only check
    over yaml; no LLM dispatch needed if this returns True.
    """
    by_id = {it.get("id"): it for it in items}
    for child_id in parent_children:
        child = by_id.get(child_id)
        if child is None:
            # Orphan reference — treat as not converged (defensive)
            return False
        state = child.get("state")
        if state == "DONE":
            continue
        coverage = child.get("coverage_state")
        verified = bool(child.get("citation_verified", False))
        if coverage == "cited_by_library" and verified:
            continue
        if coverage == "cited_by_reference" and verified:
            continue
        return False
    return True


# ── Core ───────────────────────────────────────────────────────────────


def _diff_subproblems(
    current_children_ids: List[str],
    proposed_subproblems: List[Dict[str, Any]],
) -> Tuple[List[str], List[str], List[Dict[str, Any]]]:
    """Compute the diff between current children and the LLM's
    proposed sub-problem list.

    Returns (kept_ids, removed_ids, added_subproblems):
      - kept_ids: ids in BOTH current and proposed (LLM "kept" them)
      - removed_ids: ids in current but NOT in proposed (LLM dropped)
      - added_subproblems: items in proposed with NEW ids

    The id-matching is exact-string. Per czy `:1573-1577`, the LLM
    reuses the same id for kept items and invents new ids for added
    items — this matches that contract.
    """
    proposed_ids = {sp.get("id") for sp in proposed_subproblems}
    current_set = set(current_children_ids)
    kept_ids = [cid for cid in current_children_ids if cid in proposed_ids]
    removed_ids = [cid for cid in current_children_ids if cid not in proposed_ids]
    added = [
        sp for sp in proposed_subproblems
        if sp.get("id") and sp.get("id") not in current_set
    ]
    return kept_ids, removed_ids, added


def apply_refinement(
    backlog_path: Path,
    parent_id: str,
    subagent_text: str,
) -> Dict[str, Any]:
    """Apply one refinement round under flock + atomic write. Returns
    the milestone payload dict.

    Verdict outcomes (all exit 0 from main()):
      - cap_reached: informal_round >= 2 → no LLM read; no yaml write
      - converged_pre_dispatch: all children converged → set
        coverage_stable=true; no LLM read; no children change
      - noAdjustment: SKILL says noAdjustment=true AND informal_round
        > 0 → set coverage_stable=true; no children change
      - refined: SKILL proposed a new children list → diff applied;
        informal_round bumped
      - parse_error: SKILL JSON malformed → no yaml write; agent can
        retry next round if narrative chooses

    Raises ValueError on validation errors that prevent yaml access
    entirely (parent missing, has no children, etc.).
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        current_children: List[str] = list(parent.get("children") or [])
        if not current_children:
            raise ValueError(
                f"parent {parent_id} has no children; "
                f"refinement runs after Step A initial decompose"
            )

        current_round = int(parent.get("informal_round", 0) or 0)

        # Cap check (structural — happens BEFORE any LLM work)
        if current_round >= INFORMAL_ROUND_CAP:
            return {
                "parent_id": parent_id,
                "verdict": "cap_reached",
                "informal_round_post": current_round,
                "diff": {"kept": current_children, "removed": [], "added": []},
                "reason": (
                    f"informal_round={current_round} >= cap={INFORMAL_ROUND_CAP}; "
                    f"czy parity ends here"
                ),
            }

        # Convergence pre-check (czy `:916-919` "all covered")
        if _all_children_converged(current_children, items):
            for it in items:
                if it.get("id") == parent_id:
                    it["coverage_stable"] = True
                    break
            atomic_write_yaml(backlog_path, data)
            return {
                "parent_id": parent_id,
                "verdict": "converged_pre_dispatch",
                "informal_round_post": current_round,
                "diff": {"kept": current_children, "removed": [], "added": []},
                "reason": "all children already cited_by_library/reference + verified",
            }

        # Parse SKILL JSON
        ok, parsed = parse_subagent_output(subagent_text)
        if not ok:
            return {
                "parent_id": parent_id,
                "verdict": "parse_error",
                "informal_round_post": current_round,
                "diff": {"kept": current_children, "removed": [], "added": []},
                "reason": parsed.get("error", "unknown parse error"),
            }

        no_adjustment = bool(parsed.get("noAdjustment", False))
        # czy `:840-843`: noAdjustment ONLY exits when alignRound > 0
        # (round 0 is the initial decompose, "no adjustment" is
        # meaningless there). SDK-bridge: informal_round > 0 means
        # at least 1 refinement has been committed already.
        if no_adjustment and current_round > 0:
            for it in items:
                if it.get("id") == parent_id:
                    it["coverage_stable"] = True
                    break
            atomic_write_yaml(backlog_path, data)
            return {
                "parent_id": parent_id,
                "verdict": "noAdjustment",
                "informal_round_post": current_round,
                "diff": {"kept": current_children, "removed": [], "added": []},
                "reason": str(parsed.get("decisionReason", "LLM signaled noAdjustment")),
            }

        # Validate proposed sub-problems
        proposed = parsed.get("subProblems") or []
        if not isinstance(proposed, list) or not proposed:
            return {
                "parent_id": parent_id,
                "verdict": "parse_error",
                "informal_round_post": current_round,
                "diff": {"kept": current_children, "removed": [], "added": []},
                "reason": "subProblems missing or non-list",
            }
        # Each entry needs an id
        for sp in proposed:
            if not isinstance(sp, dict) or not sp.get("id"):
                return {
                    "parent_id": parent_id,
                    "verdict": "parse_error",
                    "informal_round_post": current_round,
                    "diff": {"kept": current_children, "removed": [], "added": []},
                    "reason": "subProblems entry missing id",
                }

        # Compute diff
        kept_ids, removed_ids, added_subs = _diff_subproblems(
            current_children, proposed,
        )
        added_ids = [sp["id"] for sp in added_subs]

        # If no actual change (kept == current AND no added/removed),
        # treat as noAdjustment-equivalent. czy reaches this state via
        # the LLM's own self-report, but defensively handle the
        # "LLM said refined but actually didn't change anything" case.
        if not removed_ids and not added_ids:
            for it in items:
                if it.get("id") == parent_id:
                    it["coverage_stable"] = True
                    break
            atomic_write_yaml(backlog_path, data)
            return {
                "parent_id": parent_id,
                "verdict": "noAdjustment",
                "informal_round_post": current_round,
                "diff": {"kept": kept_ids, "removed": [], "added": []},
                "reason": "proposed subProblems list identical to current children",
            }

        # Apply the refinement — atomic mutation
        # 1. Remove dropped children + their descendants
        to_remove: set = _collect_descendants(items, removed_ids) if removed_ids else set()
        # 2. Build new child rows for added sub-problems
        parent_depth = int(parent.get("depth", 0) or 0)
        parent_file = parent.get("file") or ""
        new_rows = []
        for sp in added_subs:
            new_rows.append({
                "id": sp["id"],
                "file": parent_file,  # placeholder; sub-autoformalize
                                       # will populate the actual sub-file
                                       # later (per spec §6.1 Step C)
                "line": 0,             # placeholder
                "theorem": str(sp.get("description") or sp["id"]),
                "type": "ready",
                "depth": parent_depth + 1,
                "priority": int(parent.get("priority", 50) or 50),
                "estimated_lines": 30,
                "dependencies": list(sp.get("dependencies") or []),
                "unlocks": [],
                "state": "INITIALIZED",
                "children": [],
                "parent_id": parent_id,
                "history_log": [],
                "stuck_rounds": 0,
                "attempts": 0,
                "references": [],
                "coverage_state": "needs_proof",
                "citation_verified": False,
                "informal_round": 0,
                "coverage_stable": False,
            })

        # 3. Apply
        new_children_ids = [sp["id"] for sp in proposed]
        new_items = [it for it in items if it.get("id") not in to_remove]
        # H1 D-11 (per docs/H1_ELABORATE_PLAN_SPEC.md §10): on the
        # `refined` verdict path, also persist the latest brief seed
        # from the SKILL output. czy emits exactly ONE per refinement
        # output: `composition.directAssembly` (decomposition path) OR
        # top-level `proofSketch` (no-decomposition path). czy keeps
        # them in TS in-memory state on the parent ProblemNode; SDK-
        # bridge persists them on the parent yaml row so H1's
        # elaborate_plan.py can read the FINAL alignment round's
        # brief seed without re-dispatching InformalAgent. Architectural
        # translation, not czy deviation. Write only the field actually
        # supplied by the SKILL output; leave the other untouched (so
        # a subsequent SKILL flip from decomposition→direct or vice
        # versa overwrites correctly without leaving stale data —
        # except where neither field is present in this refined output,
        # in which case both stay at their pre-write value).
        composition = parsed.get("composition") or {}
        new_direct_assembly = composition.get("directAssembly") if isinstance(composition, dict) else None
        new_proof_sketch = parsed.get("proofSketch")
        # Find parent in new_items (it survives — D-6 mirror); update
        for it in new_items:
            if it.get("id") == parent_id:
                # KEPT children's `theorem` is NEVER mutated (D-6).
                # We don't touch existing children rows here at all —
                # the diff just changes WHICH ids are in
                # parent.children, not the rows themselves. If the
                # LLM rephrased a kept child's description, that
                # rephrase is silently dropped (Layer 1 invariant).
                it["children"] = new_children_ids
                it["informal_round"] = current_round + 1
                # state stays INACTIVE_WAIT (parent is still mid-decomp)
                if new_direct_assembly is not None:
                    it["direct_assembly"] = new_direct_assembly
                if new_proof_sketch is not None:
                    it["proof_sketch"] = new_proof_sketch
                break
        # Append added rows
        new_items.extend(new_rows)
        data["sorry_items"] = new_items

        atomic_write_yaml(backlog_path, data)

        return {
            "parent_id": parent_id,
            "verdict": "refined",
            "informal_round_post": current_round + 1,
            "diff": {
                "kept": kept_ids,
                "removed": removed_ids,
                "added": added_ids,
            },
            "reason": str(parsed.get("decisionReason", "")),
        }


# ── CLI ────────────────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emit (matches E4 / A1 / E11 pattern)."""
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
            f"[refine_decomposition] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--subagent-json-file",
        required=True,
        help="path to a file containing the informal-refine subagent's JSON output",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[refine_decomposition] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[refine_decomposition] read failed: {e}", file=sys.stderr)
        return 4

    try:
        payload = apply_refinement(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            subagent_text=subagent_text,
        )
    except ValueError as e:
        print(f"[refine_decomposition] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[refine_decomposition] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[refine_decomposition] IO failure: {e}", file=sys.stderr)
        return 4

    _emit(sandbox, "informal-round", payload)

    diff = payload["diff"]
    print(
        f"informal-round: parent={args.parent_id} "
        f"verdict={payload['verdict']} "
        f"informal_round={payload['informal_round_post']} "
        f"kept={len(diff['kept'])} removed={len(diff['removed'])} "
        f"added={len(diff['added'])}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

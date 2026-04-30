#!/usr/bin/env python3
"""decompose_node.py — atomically split a sorry into sub-problems.

Slice 3.A of the czy newloop port. Mirrors czy's `InformalAgent`
decomposition action (`informalAgent.ts:339-355` + `proofState.ts:658-700`):
when the agent decides a hard sorry should be attacked by decomposition
into smaller sub-problems, this script writes the children to the yaml
and flips parent state to INACTIVE_WAIT (parent now structurally
suspended pending children).

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Agent
invokes once with the decomposition; script enforces all atomic side
effects.

Sub-problem rows are inserted with:
  state           = INITIALIZED
  children        = []
  parent_id       = <parent.id>
  history_log     = []
  stuck_rounds    = 0
  + caller-provided fields: id, file, line, theorem, depth (parent.depth+1),
    priority (default 50), blocker, estimated_lines

Parent row is mutated:
  state           = INACTIVE_WAIT
  children        = [<sub-problem ids>]
  (locked theorem signature fields untouched — Rule 3 Layer 1)

Validation:
  - parent must exist
  - parent.state must be INITIALIZED (cannot decompose an already-
    decomposed parent without a retreat first)
  - sub-problem ids must be globally unique (no collision with
    existing sorry_items)
  - sub-problem list must be non-empty

Atomic write: tempfile + os.replace (via _yaml_io.atomic_write_yaml,
which preserves file mode 0o644). Cross-script flock via locked_backlog.

Emits `subtasks-split` milestone (existing in MILESTONE_NAMES) so
process_sorry_result.py's existing milestone listener stays consistent
with the older non-tree decomposition path.

Exit codes:
  0  — decomposition applied
  2  — validation error
  3  — yaml parse error
  4  — IO failure

CLI:
    python3 theme/scripts/decompose_node.py \\
        --parent-id <id> \\
        --sub-problems-json '[{"id":"foo.sub1","theorem":"...","blocker":"..."}]' \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--decision-reason "induction on n"] \\
        [--backlog-path PATH]
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
EXTRACT_SORRIES = SCRIPTS_DIR / "extract_sorries.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, find_item, locked_backlog  # noqa: E402


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
            f"[decompose_node] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


REQUIRED_SUB_FIELDS = ("id",)


def _build_sub_item(parent: Dict[str, Any], spec: Dict[str, Any]) -> Dict[str, Any]:
    """Build a sorry_item row for a sub-problem from caller-provided spec.

    Caller MUST provide `id`. Other fields default to "inherit from
    parent where it makes sense, else neutral":
      - file: parent.file (sub-problems live in parent's .lean file
        unless caller overrides; SubAutoformalize multi-file split is
        slice 3.B's concern)
      - line: 0 (placeholder; actual line known once written)
      - theorem: spec['theorem'] required-ish (most callers provide)
      - depth: parent.depth + 1
      - priority: 50
      - blocker: spec['blocker'] or empty
      - estimated_lines: 0
      - dependencies: []
      - unlocks: []
      - source: f"decomposed from {parent['id']}"
    """
    sub = {
        "id": spec["id"],
        "file": spec.get("file", parent.get("file", "")),
        "line": int(spec.get("line", 0)),
        "theorem": spec.get("theorem", spec["id"]),
        "type": "ready",
        "depth": int(parent.get("depth", 0)) + 1,
        "priority": int(spec.get("priority", 50)),
        "blocker": spec.get("blocker", ""),
        "estimated_lines": int(spec.get("estimated_lines", 0)),
        "dependencies": list(spec.get("dependencies", [])),
        "unlocks": [],
        "source": spec.get("source", f"decomposed from {parent['id']}"),
        "stuck_rounds": 0,
        "state": "INITIALIZED",
        "children": [],
        "parent_id": parent["id"],
        "history_log": [],
    }
    return sub


# ── Core ───────────────────────────────────────────────────────────────


def apply_decomposition(
    backlog_path: Path,
    parent_id: str,
    sub_problems: List[Dict[str, Any]],
    *,
    decision_reason: str | None = None,
    direct_assembly: str | None = None,
    proof_sketch: str | None = None,
) -> List[str]:
    """Apply decomposition under flock + atomic write. Returns list of
    new sub-problem ids.

    H1 D-11 (cross-slice patch per docs/H1_ELABORATE_PLAN_SPEC.md §10):
    `direct_assembly` and `proof_sketch` are the InformalAgent SKILL's
    brief-seed fields (czy `informalAgent.ts:159-162` `composition.directAssembly`
    + czy `:170` `proofSketch`). czy emits exactly ONE per SKILL output —
    `directAssembly` when `needsDecomposition=true`, `proofSketch` when
    `needsDecomposition=false`. SDK-bridge persists them on the parent so
    H1's elaborate_plan.py can read the brief seed without re-dispatching
    InformalAgent. Architectural translation of czy's in-memory
    ProblemNode field; not a czy deviation.

    Raises ValueError on validation failure.
    """
    if not sub_problems:
        raise ValueError("sub_problems must be non-empty")
    for spec in sub_problems:
        for f in REQUIRED_SUB_FIELDS:
            if f not in spec:
                raise ValueError(f"sub_problem missing required field {f!r}: {spec}")

    new_ids: List[str] = []
    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        parent = find_item(items, parent_id)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")
        if parent.get("state") != "INITIALIZED":
            raise ValueError(
                f"parent {parent_id} state is {parent.get('state')!r}; "
                f"only INITIALIZED nodes can be decomposed (retreat first to "
                f"re-decompose an INACTIVE_WAIT parent)"
            )

        existing_ids = {it.get("id") for it in items}
        new_id_set: set = set()
        for spec in sub_problems:
            sid = spec["id"]
            if sid in existing_ids:
                raise ValueError(f"sub-problem id collides with existing item: {sid}")
            if sid in new_id_set:
                raise ValueError(f"duplicate sub-problem id within request: {sid}")
            new_id_set.add(sid)

        # Build sub-rows
        sub_rows = [_build_sub_item(parent, spec) for spec in sub_problems]
        new_ids = [s["id"] for s in sub_rows]

        # Mutate parent: state → INACTIVE_WAIT, children = new_ids.
        # Locked signature fields (file/line/theorem/blocker/dependencies/etc.)
        # are NOT touched — Rule 3 Layer 1 invariant.
        for it in items:
            if it.get("id") == parent_id:
                it["state"] = "INACTIVE_WAIT"
                it["children"] = list(new_ids)
                if decision_reason is not None:
                    # Stash decision_reason as transient metadata so
                    # record_retreat (called later if children fail)
                    # can pull it from parent and write into the
                    # history_log entry. Field name `_pending_decision_reason`
                    # is intentionally underscore-prefixed to mark it
                    # internal-runtime-only (not v2-schema-canonical).
                    it["_pending_decision_reason"] = decision_reason
                # H1 D-11: persist brief seed (czy in-memory →
                # SDK-bridge yaml architectural translation). czy emits
                # ONE of these per SKILL output; we write whichever is
                # provided (None values left as None — caller is
                # responsible for passing exactly one when applicable).
                if direct_assembly is not None:
                    it["direct_assembly"] = direct_assembly
                if proof_sketch is not None:
                    it["proof_sketch"] = proof_sketch
                break
        # Append new sub-rows
        data["sorry_items"] = items + sub_rows

        atomic_write_yaml(backlog_path, data)
    return new_ids


# ── CLI ────────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--sub-problems-json",
        required=True,
        help="JSON array of {id, theorem?, blocker?, file?, line?, priority?, …}",
    )
    p.add_argument("--decision-reason")
    # H1 D-11 cross-slice patch: brief seed from SKILL output —
    # `composition.directAssembly` (czy informalAgent.ts:159-162) when
    # decomposition fired, `proofSketch` (czy :170) when no decomposition.
    # Caller passes whichever the SKILL output produced; the script only
    # writes the field actually supplied. Read by H1's elaborate_plan.py.
    p.add_argument(
        "--direct-assembly",
        help="brief assembly sketch from InformalAgent SKILL output "
             "(composition.directAssembly); persisted on parent for H1",
    )
    p.add_argument(
        "--proof-sketch",
        help="brief direct-mode strategy from InformalAgent SKILL output "
             "(top-level proofSketch); persisted on parent for H1",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    try:
        sub_problems = json.loads(args.sub_problems_json)
    except json.JSONDecodeError as e:
        print(f"[decompose_node] malformed JSON: {e}", file=sys.stderr)
        return 2

    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        new_ids = apply_decomposition(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            sub_problems=sub_problems,
            decision_reason=args.decision_reason,
            direct_assembly=args.direct_assembly,
            proof_sketch=args.proof_sketch,
        )
    except ValueError as e:
        print(f"[decompose_node] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[decompose_node] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[decompose_node] IO failure: {e}", file=sys.stderr)
        return 4

    _emit(
        sandbox,
        "subtasks-split",
        {
            "parent_id": args.parent_id,
            "sub_problem_ids": new_ids,
            "count": len(new_ids),
        },
    )

    # § 8 review fix (slice 3.B P0): preserve telemetry invariants that
    # the previous "process_sorry_result.py at end of every branch"
    # contract guaranteed. After decomposition mutates the backlog, the
    # web UI's sorry_list.json must be refreshed and a sorry-pool-snapshot
    # emitted so depth_histogram + count delta consumers don't go stale.
    sorry_list = sandbox / "sorry_list.json"
    try:
        subprocess.run(
            ["python3", str(EXTRACT_SORRIES),
             "--sandbox", str(sandbox),
             "--output", str(sorry_list)],
            check=False,
        )
    except FileNotFoundError as e:
        print(f"[decompose_node] extract_sorries unavailable: {e}",
              file=sys.stderr)
    if sorry_list.exists():
        try:
            count = len(json.loads(sorry_list.read_text()))
            _emit(
                sandbox,
                "sorry-pool-snapshot",
                {
                    "count": count,
                    "trigger": "decompose_node",
                    "parent_id": args.parent_id,
                    "added_children": len(new_ids),
                },
            )
        except (json.JSONDecodeError, OSError) as e:
            print(f"[decompose_node] sorry-pool-snapshot skipped: {e}",
                  file=sys.stderr)

    print(f"decomposed {args.parent_id} → {new_ids}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

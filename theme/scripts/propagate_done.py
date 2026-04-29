#!/usr/bin/env python3
"""propagate_done.py — cascade DONE state up the decomposition tree.

Slice 3.A of the czy newloop port. Mirrors czy's `propagateDone`
(`proofState.ts:780-797`): when a child is marked DONE, walk up the
parent chain and mark each ancestor DONE iff ALL its children are DONE.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Called
by process_sorry_result.py (or directly by the agent narrative) after
a leaf is marked proved.

Algorithm:
  1. Read backlog under flock; migrate v1→v2.
  2. Verify the input node is in fact DONE; if not, no-op (defensive).
  3. Walk parent_id chain upward:
       - For each ancestor `p`:
         - If every id in p.children has state == "DONE", set
           p.state = "DONE" and continue walking up.
         - Otherwise stop (a sibling is still in flight).
  4. Atomic-write back. Emit `dag-cycle-done` ONLY if a root node
     (parent_id is None) is the highest one we marked DONE — that
     signals the whole proof-tree is complete.

Idempotent: running twice is a no-op (the second run finds ancestors
already DONE).

Locked theorem signature fields untouched (Rule 3 Layer 1).

Exit codes:
  0  — propagation applied (or no-op)
  2  — validation error
  3  — yaml parse error
  4  — IO failure

CLI:
    python3 theme/scripts/propagate_done.py \\
        --node-id <leaf id> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, find_item, locked_backlog  # noqa: E402


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
            f"[propagate_done] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


# ── Core ───────────────────────────────────────────────────────────────


def apply_propagation(
    backlog_path: Path,
    node_id: str,
) -> List[str]:
    """Walk up parent chain, marking ancestors DONE when their children
    are all DONE. Returns the list of node ids that this call newly
    transitioned to DONE (excluding the input node).

    Empty list if the input node isn't DONE, isn't in the backlog, has
    no parent, or the parent isn't ready to propagate.
    """
    transitioned: List[str] = []
    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        by_id: Dict[str, Dict[str, Any]] = {
            it["id"]: it for it in items if "id" in it
        }
        node = by_id.get(node_id)
        if node is None or node.get("state") != "DONE":
            return []

        cursor: Optional[str] = node.get("parent_id")
        while cursor is not None:
            parent = by_id.get(cursor)
            if parent is None:
                # Orphan parent_id — stop, no propagation possible.
                break
            children_ids = parent.get("children") or []
            if not children_ids:
                # Defensive: a parent referenced as parent_id but with
                # no children list. Don't auto-mark DONE because we
                # can't confirm the contract; require explicit action.
                break
            if all(
                (by_id.get(cid) or {}).get("state") == "DONE"
                for cid in children_ids
            ):
                parent["state"] = "DONE"
                transitioned.append(parent["id"])
                cursor = parent.get("parent_id")
            else:
                break

        if transitioned:
            atomic_write_yaml(backlog_path, data)
    return transitioned


# ── CLI ────────────────────────────────────────────────────────────────


def _is_root_done(backlog_path: Path, last_done_id: str) -> bool:
    """Quick re-read to check whether the last propagated node was a
    root (parent_id == None). Used to gate the dag-cycle-done emit."""
    try:
        data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError:
        return False
    items = data.get("sorry_items") or []
    item = find_item(items, last_done_id)
    return bool(item and item.get("parent_id") is None)


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--node-id", required=True)
    p.add_argument("--sandbox", required=True)
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        transitioned = apply_propagation(
            backlog_path=backlog_path,
            node_id=args.node_id,
        )
    except ValueError as e:
        print(f"[propagate_done] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[propagate_done] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[propagate_done] IO failure: {e}", file=sys.stderr)
        return 4

    if transitioned:
        # If the topmost transitioned node is a root, the whole proof tree
        # rooted there is now DONE — emit the dag-cycle-done milestone.
        last = transitioned[-1]
        if _is_root_done(backlog_path, last):
            _emit(
                sandbox,
                "dag-cycle-done",
                {
                    "root_id": last,
                    "ancestors_promoted": transitioned,
                },
            )
        print(f"propagated DONE up: {transitioned}")
    else:
        print(f"no propagation: {args.node_id} either not DONE or no eligible ancestor")
    return 0


if __name__ == "__main__":
    sys.exit(main())

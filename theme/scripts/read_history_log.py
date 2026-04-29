#!/usr/bin/env python3
"""read_history_log.py — format a sorry_item's history_log as a prompt block.

Per czy newloop port (MERGE_PLAN.md §3.2.1). Output format BYTE-MATCHES
czy `informalAgent.ts:741-763`:

    ## Previous attempt history (DO NOT repeat failed strategies)
    - Iteration N: decomposed into [sub1, sub2, sub3]
        Reason: <decision_reason, slice 0-500>
        sub1: <description, slice 0-300>
        sub2: <description, slice 0-300>
      - sub3: stuck (Lean type mismatch in step 3)   ← only non-proved listed
      Retreat reason: <retreat_reason>
    ACTION: Choose a DIFFERENT decomposition strategy from previous attempts.

The trailing blank line + ACTION line are emitted iff history_log is
non-empty. Empty history_log → empty output. Slicing matches czy exactly:
500 chars on decision_reason, 300 on each child description, 200 on
fail_reason.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 read-only formatter; deterministic
given identical yaml input. Agent calls once when re-entering a parent
node post-retreat; output prepended to decompose subagent prompt.

CLI:
    python3 theme/scripts/read_history_log.py \\
        --node-id <sorry_item id> \\
        [--backlog-path PATH] \\
        [--output PATH]   # default: stdout

Exit 0 always (empty output for non-existent node or empty history is
a valid result, not an error).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any, Dict, List

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402


# czy informalAgent.ts:746,750,755 slice lengths.
SLICE_DECISION = 500
SLICE_DESCRIPTION = 300
SLICE_FAIL_REASON = 200


def format_history_block(history_log: List[Dict[str, Any]]) -> str:
    """Format a list of HistoryLogEntry dicts as czy's prompt block.

    Empty list → empty string. Multi-entry → entries listed in
    insertion order (oldest iteration first).
    """
    if not history_log:
        return ""
    lines: List[str] = ["## Previous attempt history (DO NOT repeat failed strategies)"]
    for entry in history_log:
        iteration = entry.get("iteration", "?")
        decomposition = entry.get("decomposition") or []
        lines.append(
            f"- Iteration {iteration}: decomposed into [{', '.join(decomposition)}]"
        )
        decision_reason = entry.get("decision_reason")
        if decision_reason:
            lines.append(f"    Reason: {decision_reason[:SLICE_DECISION]}")
        details = entry.get("decomposition_details") or []
        for d in details:
            d_id = d.get("id", "?")
            d_desc = (d.get("description") or "")[:SLICE_DESCRIPTION]
            lines.append(f"    {d_id}: {d_desc}")
        # czy informalAgent.ts:754: only non-proved results listed.
        for r in entry.get("results") or []:
            status = r.get("status")
            if status == "proved":
                continue
            sub_id = r.get("sub_problem_id", "?")
            fail = r.get("fail_reason")
            if fail:
                lines.append(
                    f"  - {sub_id}: {status} ({fail[:SLICE_FAIL_REASON]})"
                )
            else:
                lines.append(f"  - {sub_id}: {status}")
        retreat_reason = entry.get("retreat_reason")
        if retreat_reason:
            lines.append(f"  Retreat reason: {retreat_reason}")
    lines.append("ACTION: Choose a DIFFERENT decomposition strategy from previous attempts.")
    lines.append("")  # trailing blank line, czy informalAgent.ts:763
    return "\n".join(lines)


def read_history_for_node(backlog_path: Path, node_id: str) -> str:
    """Load yaml, migrate, look up node, return its formatted history block.

    Returns empty string if backlog missing, node missing, or history empty.
    """
    if not backlog_path.exists():
        return ""
    data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
    migrate_yaml_v1_to_v2(data)
    items = data.get("sorry_items") or []
    item = next((it for it in items if it.get("id") == node_id), None)
    if item is None:
        return ""
    return format_history_block(item.get("history_log") or [])


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--node-id", required=True)
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    p.add_argument("--output", help="default: stdout")
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    block = read_history_for_node(backlog_path, args.node_id)
    if args.output:
        Path(args.output).write_text(block, encoding="utf-8")
    else:
        sys.stdout.write(block)
    return 0


if __name__ == "__main__":
    sys.exit(main())

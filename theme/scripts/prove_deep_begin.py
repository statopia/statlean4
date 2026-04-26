#!/usr/bin/env python3
"""prove_deep_begin.py — emit DAG cycle entry milestone with ready_queue dump.

Called by /prove-deep at Phase 0 entry. Replaces the narrative
"emit dispatch-batch-start" instruction in prove-deep.md (which agents
were treating as documentation rather than a real call).

Side effects:
  - Reads theme/input/sorry_backlog.yaml to compute ready queue
  - Emits sandbox_milestone "dispatch-batch-start" via emit_event.py with
    details = {target, mode, ready: [...], time_budget_min}
  - Prints human-readable summary to stdout for the agent's context

Per CLAUDE.md Rule 9 Q3 (determinism gate): bundles all Phase 0 entry
side-effects into one named call so individual steps can't be silently
skipped. Registered in `website/docs/CLI_WEB_CONFORMANCE.md` §0.2.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"


def _emit_milestone(sandbox: Path, name: str, details: dict) -> None:
    subprocess.run(
        [
            "python3", str(EMIT_EVENT),
            "--sandbox", str(sandbox),
            "milestone",
            "--name", name,
            "--details", json.dumps(details),
        ],
        check=True,
    )


def _compute_ready_queue(backlog_path: Path, target: str, mode: str) -> list[dict]:
    """Filter backlog to ready items per target/mode.

    'specific' → only the named sorry id
    'next'     → highest-priority ready item (lowest priority number)
    'all-leaves' → every ready item
    """
    if not backlog_path.exists():
        return []
    data = yaml.safe_load(backlog_path.read_text()) or {}
    items = data.get("sorry_items") or []

    def is_ready(item: dict) -> bool:
        if item.get("status") in {"proved", "trusted"}:
            return False
        if item.get("type") == "blocked" and item.get("blocker"):
            # Truly blocked items stay out unless the blocker has been
            # resolved upstream — sync_sorry_backlog.py owns that logic.
            return False
        return True

    ready = [i for i in items if is_ready(i)]
    if mode == "specific":
        ready = [i for i in ready if i.get("id") == target]
    elif mode == "next":
        ready.sort(key=lambda x: x.get("priority", 999))
        ready = ready[:1]
    # mode == "all-leaves" → keep all ready
    ready.sort(key=lambda x: x.get("priority", 999))
    return ready


def main() -> None:
    ap = argparse.ArgumentParser(description="prove-deep DAG cycle entry")
    ap.add_argument("--sandbox", required=True, help="Per-job sandbox dir")
    ap.add_argument("--target", required=True,
                    help="Sorry ID, 'next', or 'all-leaves'")
    ap.add_argument("--mode", required=True,
                    choices=["specific", "next", "all-leaves"])
    ap.add_argument("--time-budget-min", type=int, default=30,
                    help="Soft deadline in minutes (default 30)")
    ap.add_argument("--backlog", default=str(BACKLOG_DEFAULT),
                    help="Path to sorry_backlog.yaml")
    args = ap.parse_args()

    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists():
        print(f"[prove_deep_begin] sandbox does not exist: {sandbox}",
              file=sys.stderr)
        sys.exit(2)

    ready = _compute_ready_queue(Path(args.backlog), args.target, args.mode)

    details = {
        "target": args.target,
        "mode": args.mode,
        "time_budget_min": args.time_budget_min,
        "ready": [
            {
                "id": r.get("id"),
                "theorem": r.get("theorem"),
                "priority": r.get("priority"),
                "estimated_lines": r.get("estimated_lines"),
            }
            for r in ready
        ],
        "ready_count": len(ready),
    }
    _emit_milestone(sandbox, "dispatch-batch-start", details)

    print(f"[prove_deep_begin] DAG cycle started")
    print(f"  target: {args.target}  mode: {args.mode}  "
          f"budget: {args.time_budget_min}m")
    print(f"  ready: {len(ready)} item(s)")
    for r in ready[:10]:
        print(f"    - {r.get('id')}  priority={r.get('priority')}  "
              f"est={r.get('estimated_lines')} lines")
    if len(ready) > 10:
        print(f"    ... and {len(ready) - 10} more")


if __name__ == "__main__":
    main()

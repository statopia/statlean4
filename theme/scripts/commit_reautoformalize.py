#!/usr/bin/env python3
"""commit_reautoformalize.py — H4-reautoformalize commit script (T2 bundling).

Per `docs/H4_REAUTOFORMALIZE_SPEC.md §3.4`. After the agent has rewritten
the Lean skeleton using the enriched description produced by
`reautoformalize_node.py`, this script commits the enriched NL description
back to sorry_backlog.yaml by updating the `theorem` field of the targeted
sorry row.

This is the COMMIT half of the two-script pipeline:
  1. reautoformalize_node.py — prep (writes enriched desc temp file)
  2. agent narrative (T3) — rewrites Lean skeleton
  3. commit_reautoformalize.py (this) — commits enriched `theorem` to yaml

Layer 1 invariant (L1.2): mutates ONLY `theorem` on the targeted sorry row.
All other fields (file, line, state, parent_id, children, history_log,
stuck_rounds, attempts, coverage_state, references, assumption_hints,
assumption_analysis, detailed_proof_plan, direct_assembly, proof_sketch,
citation_verified, done_reason, informal_round, coverage_stable) are
byte-identical pre/post write. Test L1.7 enforces this.

Verdicts emitted via `reautoformalized` milestone:
  - `committed`    — yaml theorem field updated (exit 0)
  - `parse_error`  — sub_problem_id missing or validation failure (exit 2)

Exit codes:
  0 — committed successfully
  2 — validation error (sub_problem_id missing, backlog/enrich-file unreadable)

CLI:
    python3 theme/scripts/commit_reautoformalize.py \\
        --sub-problem-id <id> \\
        --enriched-theorem-file $SANDBOX/_enrich_desc_${id}_${ts}.txt \\
        --sandbox /path/to/sandbox \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

VERDICT_COMMITTED = "committed"
VERDICT_PARSE_ERROR = "parse_error"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


def apply_commit(
    backlog_path: Path,
    sub_problem_id: str,
    enriched_theorem: str,
) -> Dict[str, Any]:
    """Commit enriched theorem text to sorry_backlog.yaml under flock.

    Mutates ONLY the `theorem` field on the targeted sorry row.
    All other fields on this row and all other rows are byte-identical
    pre/post write (Layer 1 invariant L1.2).

    Returns milestone payload dict.
    Raises ValueError if sub_problem_id missing.
    """
    started_ms = int(time.time() * 1000)

    with locked_backlog(backlog_path) as data:
        items = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            raise ValueError(
                f"sub_problem_id not in sorry_items: {sub_problem_id}"
            )

        old_theorem = item.get("theorem", "")

        # Layer 1 invariant: ONLY mutate `theorem` field.
        # D-7 (deliberate +1 deviation per spec §11): the enriched
        # theorem persists across retreats. czy's `AssumptionVersion`
        # chain (helperSubAgents.ts:185-222) is dormant — czy never
        # populates it — so survival across retreats is +1, not parity.
        # This is intentional: H7 hints are research investment we
        # don't want a retreat to discard.
        item["theorem"] = enriched_theorem

        atomic_write_yaml(backlog_path, data)

    elapsed = int(time.time() * 1000) - started_ms
    return {
        "sub_problem_id": sub_problem_id,
        "verdict": VERDICT_COMMITTED,
        "old_theorem_len": len(old_theorem),
        "new_theorem_len": len(enriched_theorem),
        "took_ms": elapsed,
    }


def _emit(sandbox: Path, name: str, details: Dict[str, Any]) -> None:
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
            f"[commit_reautoformalize] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--sub-problem-id", required=True)
    p.add_argument(
        "--enriched-theorem-file",
        required=True,
        help="Path to file written by reautoformalize_node.py (_enrich_desc_*.txt).",
    )
    p.add_argument("--sandbox", required=True)
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()

    sandbox = Path(args.sandbox).resolve()
    backlog_path = Path(args.backlog_path).resolve()
    enrich_file = Path(args.enriched_theorem_file).resolve()

    if not enrich_file.is_file():
        payload: Dict[str, Any] = {
            "sub_problem_id": args.sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "error": f"enriched-theorem-file not found: {enrich_file}",
            "took_ms": 0,
        }
        _emit(sandbox, "reautoformalized", payload)
        print(
            f"[commit_reautoformalize] enriched-theorem-file not found: {enrich_file}",
            file=sys.stderr,
        )
        return 2

    try:
        enriched_theorem = enrich_file.read_text(encoding="utf-8")
    except OSError as e:
        payload = {
            "sub_problem_id": args.sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "error": f"read enriched-theorem-file failed: {e}",
            "took_ms": 0,
        }
        _emit(sandbox, "reautoformalized", payload)
        print(f"[commit_reautoformalize] read failed: {e}", file=sys.stderr)
        return 2

    try:
        payload = apply_commit(
            backlog_path=backlog_path,
            sub_problem_id=args.sub_problem_id,
            enriched_theorem=enriched_theorem,
        )
    except ValueError as e:
        payload = {
            "sub_problem_id": args.sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "error": str(e)[:200],
            "took_ms": 0,
        }
        _emit(sandbox, "reautoformalized", payload)
        print(f"[commit_reautoformalize] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[commit_reautoformalize] yaml parse failed: {e}", file=sys.stderr)
        return 2
    except OSError as e:
        print(f"[commit_reautoformalize] IO failure: {e}", file=sys.stderr)
        return 2

    _emit(sandbox, "reautoformalized", payload)

    print(
        f"[commit_reautoformalize] sub={args.sub_problem_id} "
        f"verdict={payload['verdict']} "
        f"old_len={payload['old_theorem_len']} "
        f"new_len={payload['new_theorem_len']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

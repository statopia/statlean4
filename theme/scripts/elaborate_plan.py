#!/usr/bin/env python3
"""elaborate_plan.py — bundle the side-effect chain for one
elaboration call (H1 slice; per docs/H1_ELABORATE_PLAN_SPEC.md).

Where slice 03 (`refine_decomposition.py`) converges the decomposition
under helper-reference feedback, H1 fires the SECOND LLM call: a
single-shot "expand the brief seed into a step-by-step detailed plan"
invocation. czy `informalAgent.ts:477-513` `elaboratePlan` runs ONCE
per parent immediately after the alignment loop exits
(`proofLoop.ts:929-940`); the elaborated plan is then sent to the
prover as primary guidance.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Agent
narrative dispatches the `elaborate-plan` Task subagent (capturing
its plain-text plan output to a file), then invokes this script with
`--subagent-text-file`. Script atomically:

  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Validates eligibility:
      * parent exists
      * alignment loop has EXITED (czy parity per
        `proofLoop.ts:929-940` — fires unconditionally after the
        `for alignRound = 0; alignRound < 3` loop terminates,
        regardless of how it exited). In yaml terms: either
        `parent.coverage_stable == True` (slice 03's noAdjustment +
        converged_pre_dispatch verdicts both set this flag) OR
        `parent.informal_round >= 2` (slice 03's cap_reached verdict
        leaves coverage_stable=False but informal_round at the cap;
        the loop has terminated regardless). H1 fires on either,
        matching czy's unconditional post-loop firing. §8 spec review
        S2.3 fix.
      * mode arg consistent with parent.children non-empty
        (assembly mode iff children, direct mode iff no children)
  - Idempotence: skip if `parent.detailed_proof_plan` is already
    non-null AND non-empty; emit a milestone with verdict
    `skipped_already_present` so re-runs don't re-burn LLM cost
  - Reads SKILL stdout text from --subagent-text-file
  - Empty / whitespace-only plan → verdict `skipped_empty_plan`,
    yaml.detailed_proof_plan stays None (czy `:511 catch → null`
    semantic; prover falls back to brief seed)
  - Non-empty plan → write `parent.detailed_proof_plan = plan_text`
    atomically (flock + tempfile + os.replace + mode preservation)
  - Emit one `plan-elaborated` milestone with verdict + variant +
    plan_length + parent_id

Rule 3 Layer 1 invariant (per `record_retreat.py:11-13` precedent):
mutates ONLY `detailed_proof_plan` on the targeted parent row.
Locked theorem signature / file / line / theorem / parent_id /
children / state / coverage_state / coverage_stable / informal_round
/ history_log / references / direct_assembly / proof_sketch all stay
untouched. (The brief seed fields direct_assembly + proof_sketch are
WRITTEN by the patched slice 03 scripts — `decompose_node.py` and
`refine_decomposition.py`; H1 is a READ-ONLY consumer of those.)

Exit codes:
  0  — elaboration applied (one of: elaborated / skipped_already_present
       / skipped_empty_plan; all three emit a milestone)
  2  — validation error (parent not found, mode mismatch, alignment
       loop has not converged)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/elaborate_plan.py \\
        --parent-id <node id> \\
        --subagent-text-file /path/to/elaborate_plan_stdout.txt \\
        --mode <direct|assembly> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]

Models on `verify_citation.py` (E11) for the narrative-pipe pattern
(agent dispatches SKILL → captures stdout → hands file path to script);
on `refine_decomposition.py` (slice 03) for single-field write +
milestone-emit + flock + atomic-write structure.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# Per spec §3.3 step 2: alignment-loop-exited gate. Either signal is
# valid evidence that slice 03's `for alignRound = 0; alignRound < 3`
# has terminated. cap_reached leaves coverage_stable=False but
# informal_round at the cap; noAdjustment / converged_pre_dispatch set
# coverage_stable=True. czy fires elaboration unconditionally after
# the loop exits regardless of how — both signals are "loop exited".
INFORMAL_ROUND_CAP = 2

# Mode arg values (spec §3.2). Single SKILL with two modes selected by
# this arg; agent narrative determines from parent.children non-empty.
MODES = ("direct", "assembly")


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emit (matches E4 / A1 / E11 / slice 03 pattern)."""
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
            f"[elaborate_plan] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _is_loop_exited(parent: Dict[str, Any]) -> bool:
    """czy parity per proofLoop.ts:929-940: elaboration fires
    UNCONDITIONALLY after slice 03's alignment for-loop terminates.

    SDK-bridge signals the same exit via TWO yaml flags (different
    verdicts set different flags in slice 03):
      - noAdjustment / converged_pre_dispatch → coverage_stable=True
      - cap_reached                          → informal_round >= 2

    Either flag → loop has exited → eligible for H1.

    §8 spec review S2.3 (2026-04-30): the original draft only gated on
    coverage_stable=True, which would silently lose the cap_reached
    branch (an unconverged-but-loop-exited parent would never get an
    elaborated plan). Fix: both signals.
    """
    if bool(parent.get("coverage_stable", False)):
        return True
    if int(parent.get("informal_round", 0) or 0) >= INFORMAL_ROUND_CAP:
        return True
    return False


def apply_elaboration(
    backlog_path: Path,
    parent_id: str,
    mode: str,
    plan_text: str,
) -> Dict[str, Any]:
    """Apply elaboration under flock + atomic write. Returns the
    milestone payload dict.

    Verdict outcomes (all exit 0 from main()):
      - elaborated: plan_text non-empty + all preconditions met →
        write detailed_proof_plan; payload carries plan_length + variant
      - skipped_already_present: parent.detailed_proof_plan was already
        set (idempotent re-run); no yaml write; plan_length=0
      - skipped_empty_plan: plan_text was empty / whitespace-only after
        strip; yaml.detailed_proof_plan stays None; matches czy's
        `:511 catch → null` fallback semantic (prover falls back to
        brief seed)

    Raises ValueError on validation errors that prevent yaml access
    entirely (parent missing, mode mismatch, alignment loop hasn't
    converged).
    """
    if mode not in MODES:
        raise ValueError(f"--mode must be one of {MODES}; got {mode!r}")
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        # Mode consistency check (spec §3.2 R6 mitigation; test L1.11).
        # parent.children non-empty → assembly mode; empty → direct mode.
        children: List[str] = list(parent.get("children") or [])
        if mode == "assembly" and not children:
            raise ValueError(
                f"--mode assembly but parent {parent_id} has no children; "
                f"agent narrative determines mode from parent.children"
            )
        if mode == "direct" and children:
            raise ValueError(
                f"--mode direct but parent {parent_id} has {len(children)} "
                f"children; agent narrative determines mode from parent.children"
            )

        # Convergence gate (spec §3.3 step 2; §8 S2.3 fix).
        if not _is_loop_exited(parent):
            raise ValueError(
                f"parent {parent_id} alignment loop has not converged: "
                f"coverage_stable={parent.get('coverage_stable', False)}, "
                f"informal_round={parent.get('informal_round', 0)} "
                f"(need coverage_stable=True OR informal_round >= "
                f"{INFORMAL_ROUND_CAP})"
            )

        # Idempotence pre-check (spec §3.3 step 3; D-9 verdict
        # discrimination). If the plan is already populated and
        # non-empty, skip the LLM read entirely. Re-runs are common
        # because the agent narrative may re-enter Phase 1 Step C-pre
        # for the same parent across cycles; this protects cost.
        existing = parent.get("detailed_proof_plan")
        if existing is not None and isinstance(existing, str) and existing.strip():
            return {
                "parent_id": parent_id,
                "verdict": "skipped_already_present",
                "variant": None,
                "plan_length": 0,
            }

        # Read SKILL plan text. Empty / whitespace-only → skipped_empty_plan
        # (matches czy `:511 catch → null` fallback semantic; prover falls
        # back to direct_assembly / proof_sketch via Phase 2 narrative).
        plan_stripped = plan_text.strip() if plan_text else ""
        if not plan_stripped:
            return {
                "parent_id": parent_id,
                "verdict": "skipped_empty_plan",
                "variant": None,
                "plan_length": 0,
            }

        # Atomic write: only `detailed_proof_plan` mutates (Layer 1).
        for it in items:
            if it.get("id") == parent_id:
                # Store the plan VERBATIM (czy `:336` semantic — LLM
                # output stored as-is; we strip only for the empty
                # check, the stored text retains original whitespace
                # so re-rendering the prover prompt is byte-faithful
                # to czy's behavior).
                it["detailed_proof_plan"] = plan_text
                break
        atomic_write_yaml(backlog_path, data)

        variant = "assembly" if mode == "assembly" else "direct"
        return {
            "parent_id": parent_id,
            "verdict": "elaborated",
            "variant": variant,
            "plan_length": len(plan_text),
        }


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--subagent-text-file",
        required=True,
        help="path to a file containing the elaborate-plan SKILL's "
             "plain-text stdout output (the elaborated plan body)",
    )
    p.add_argument(
        "--mode",
        required=True,
        choices=MODES,
        help="direct = parent has no children (uses ELABORATION_DIRECT_PROMPT); "
             "assembly = parent has children (uses ELABORATION_ASSEMBLY_PROMPT)",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    text_path = Path(args.subagent_text_file).resolve()
    if not text_path.is_file():
        print(
            f"[elaborate_plan] subagent text file not found: {text_path}",
            file=sys.stderr,
        )
        return 2

    try:
        plan_text = text_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[elaborate_plan] read failed: {e}", file=sys.stderr)
        return 4

    started_ms = int(time.time() * 1000)
    try:
        payload = apply_elaboration(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            mode=args.mode,
            plan_text=plan_text,
        )
    except ValueError as e:
        print(f"[elaborate_plan] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[elaborate_plan] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[elaborate_plan] IO failure: {e}", file=sys.stderr)
        return 4

    payload["took_ms"] = int(time.time() * 1000) - started_ms

    # Validation invariants asserted before emit (spec §4):
    #   verdict == "elaborated"          ↔ plan_length > 0 AND variant != None
    #   verdict == "skipped_*"           ↔ plan_length == 0 AND variant is None
    verdict = payload["verdict"]
    if verdict == "elaborated":
        assert payload["plan_length"] > 0, (
            f"elaborated must have plan_length>0; got {payload['plan_length']}"
        )
        assert payload["variant"] in ("direct", "assembly"), (
            f"elaborated must have variant ∈ {{direct, assembly}}; "
            f"got {payload['variant']!r}"
        )
    elif verdict in ("skipped_already_present", "skipped_empty_plan"):
        assert payload["plan_length"] == 0, (
            f"{verdict} must have plan_length==0; got {payload['plan_length']}"
        )
        assert payload["variant"] is None, (
            f"{verdict} must have variant=None; got {payload['variant']!r}"
        )
    else:
        # Defensive — should be unreachable per apply_elaboration contract
        print(
            f"[elaborate_plan] unexpected verdict: {verdict!r}",
            file=sys.stderr,
        )
        return 2

    _emit(sandbox, "plan-elaborated", payload)

    print(
        f"plan-elaborated: parent={args.parent_id} "
        f"verdict={payload['verdict']} variant={payload['variant']} "
        f"plan_length={payload['plan_length']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

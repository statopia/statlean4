#!/usr/bin/env python3
"""emit_event.py — append a UI-signal event to <sandbox>/events.jsonl.

Used by statlean skills to communicate structured progress/artifact/error
events to the web UI (roadmap A1+A2). See theme/conventions/ui-signals.md
§2 for the schema.

Invocation from Bash inside a skill:

    python3 theme/scripts/emit_event.py step \\
        --sandbox "$SANDBOX" --id 1 --title "PDF Extract" --status start

    python3 theme/scripts/emit_event.py step \\
        --sandbox "$SANDBOX" --id 1 --status done

    python3 theme/scripts/emit_event.py artifact \\
        --sandbox "$SANDBOX" --kind-tag pdf-extract \\
        --path extracted/paper.tex

    python3 theme/scripts/emit_event.py error \\
        --sandbox "$SANDBOX" --code OCR_FAIL --msg "MinerU ..."

    python3 theme/scripts/emit_event.py delta \\
        --sandbox "$SANDBOX" --change-type hypothesis-add \\
        --summary "Added regularity assumption (continuity of f) to make Lemma 2.1 typecheck" \\
        --severity notable --before-path theorems.yaml --after-path Main.lean

    python3 theme/scripts/emit_event.py milestone \\
        --sandbox "$SANDBOX" --name lake-build-clean

    python3 theme/scripts/emit_event.py agent-state \\
        --sandbox "$SANDBOX" --state awaiting-input \\
        --prompt "Should I weaken the hypothesis to make this typecheck?"

Design notes:
  - Append-only writes with O_APPEND. POSIX guarantees atomicity of a
    single write(2) under a buffer flush; we write one line per call
    with a trailing newline. Concurrent emits from parallel sub-agents
    therefore interleave safely without explicit locking.
  - The sandbox directory must exist. The skill creates it (that's what
    `proveCli.ts` does at job start); this script does NOT mkdir to
    avoid masking path-typo bugs.
  - Timestamp is milliseconds since epoch so downstream consumers don't
    need to parse ISO strings.
  - Non-zero exit status ONLY if the script itself fails (bad arguments,
    unwritable sandbox). A silent-but-malformed emission is worse than a
    loud failure because the UI would render stale data.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

# `_artifact_classify` lives next to this script. Import it via the
# script-relative path so callers don't need PYTHONPATH wiring.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _artifact_classify import classify_artifact_path  # noqa: E402


# ── Enum tables — single source of truth for arg validation ───────────
#
# Mirrored on the TS consumer side (`src/lib/types.ts` event union, when
# Step 3 lands the LifecyclePanel reducer). Keeping them as module-level
# tuples means argparse's `choices=` reflects the canonical taxonomy and
# any future enum addition lives in one place.

DELTA_CHANGE_TYPES = (
    "dim-reduction",        # weakened a quantifier domain (e.g. ℝ → ℕ, ℝ^n → ℝ^1)
    "hypothesis-add",       # tacked on a regularity / structure assumption
    "hypothesis-remove",    # dropped a hypothesis the agent thought was redundant
    "type-weaken",          # changed a type to a less general one
    "conclusion-replace",   # replaced the conclusion (e.g. with `True ∧ ...`)
    "structure-introduce",  # introduced a `structure ... { holds : True }` shim
    "scope-restrict",       # narrowed the universally-quantified scope
    "other",                # caller writes their own summary; UI surfaces as-is
)

DELTA_SEVERITIES = (
    "info",      # additive / cosmetic, no semantic change
    "notable",   # semantic change worth surfacing; default
    "breaking",  # weakened the theorem; integrity gate should ideally catch
)

MILESTONE_NAMES = (
    "lake-build-clean",
    "lake-build-fail",          # per-build failure (Phase 2 LOOP); pairs with lake-build-clean
    "sorry-zero",
    "sorry-proved",             # one sorry just got proved (Phase 2 process_result)
    "yaml-complete",
    "skeleton-locked",
    "pdf-extracted",
    "proof-verified",
    "promoted",
    "dispatch-batch-start",     # /prove-deep DAG cycle entry (Phase 2 LOOP open)
    "subagent-stuck",           # one sub-agent reported `stuck` for a sorry
    "dag-cycle-done",           # /prove-deep DAG cycle exit (Phase 3 end)
    "memory-md-updated",        # prove_deep_end.py wrote MEMORY.md (Phase 3 strict)
    "subtasks-split",           # need_sub_lemma decomposition was accepted
    "decomposition-rejected",   # validate_decomposition.py rejected (size-monotone fail)
    "sorry-pool-snapshot",      # after each process_result: count, delta, depth_histogram
    "working-tree-stashed",     # PR4: prove_deep_end / cancel auto-stashed residual WIP
    "state-drift-detected",     # P2-6: orchestrator-side reconcile noticed events.jsonl ↔ sandbox file disagreement
    "retreat-triggered",        # czy newloop port: sub-tree retreat — children removed, parent reset to INITIALIZED with history_log entry
    "reference-extracted",      # E4 helper-reference: extract_references.py finalized one parent's reference assessments → wrote references[]/coverage_state to backlog
    "restrategize-triggered",   # A1: stuck_rounds=3 → clear children + bump attempts; preserves decomposition strategy across rounds (see docs/A1_RESTRATEGIZE_SPEC.md)
    "citation-verified",        # E11: a citation candidate ran through the verifier (PASS or FAIL); details carry verdict + verifier mode + done_reason_set (see docs/E11_CITATION_VERIFY_SPEC.md)
    "informal-round",           # Slice 03: one refinement round of InformalAgent ran on a parent — verdict ∈ {refined, noAdjustment, converged_pre_dispatch, cap_reached, parse_error} (see docs/SLICE_03_INFORMAL_AGENT_SPEC.md)
    "other",
)

AGENT_STATES = (
    "thinking",         # model is generating tokens
    "tool-call",        # tool is executing
    "awaiting-input",   # blocked on user response (request_user_decision)
    "idle",             # turn done, waiting for next user turn
    "done",             # session finished
)


def _now_ms() -> int:
    return int(time.time() * 1000)


def _append_event(sandbox: Path, event: dict) -> None:
    sandbox = sandbox.resolve()
    if not sandbox.exists():
        print(
            f"[emit_event] sandbox does not exist: {sandbox}",
            file=sys.stderr,
        )
        sys.exit(2)
    if not sandbox.is_dir():
        print(
            f"[emit_event] sandbox is not a directory: {sandbox}",
            file=sys.stderr,
        )
        sys.exit(2)
    target = sandbox / "events.jsonl"
    # Single-line JSON to preserve jsonl-per-line invariant.
    line = json.dumps(event, ensure_ascii=False, separators=(",", ":")) + "\n"
    # O_APPEND makes the write atomic wrt other writers as long as
    # the payload fits in PIPE_BUF (4096 on Linux). Our events are
    # tiny so this holds.
    fd = os.open(
        target,
        os.O_WRONLY | os.O_APPEND | os.O_CREAT,
        mode=0o644,
    )
    try:
        os.write(fd, line.encode("utf-8"))
    finally:
        os.close(fd)


def _cmd_step(args: argparse.Namespace) -> dict:
    if args.status == "start" and not args.title:
        print("[emit_event] step start requires --title", file=sys.stderr)
        sys.exit(2)
    event: dict = {
        "ts": _now_ms(),
        "kind": "step",
        "id": args.id,
        "status": args.status,
    }
    if args.title:
        event["title"] = args.title
    return event


def _cmd_artifact(args: argparse.Namespace) -> dict:
    # path is relative-to-sandbox by convention so the web UI can
    # display it without leaking absolute server paths.
    #
    # kind_tag defaults from path if --kind-tag is omitted. The shared
    # classifier (mirror of artifactClassifier.ts) covers the canonical
    # taxonomy so skill authors don't have to repeat themselves. If
    # caller passes --kind-tag explicitly AND it disagrees with the
    # path-inferred kind, we still honour the explicit value here — the
    # web side runs reconcileKindTag and surfaces the mismatch as
    # telemetry, which is the right place to flag drift.
    declared = args.kind_tag
    inferred = classify_artifact_path(args.path) if args.path else None
    effective = declared or inferred
    if effective is None:
        print(
            f"[emit_event] artifact path '{args.path}' is not classifiable "
            "and --kind-tag was not supplied; refusing to emit untagged artifact.",
            file=sys.stderr,
        )
        sys.exit(2)
    event: dict = {
        "ts": _now_ms(),
        "kind": "artifact",
        "kind_tag": effective,
        "path": args.path,
    }
    # Record the inferred kind alongside so the web side can compare
    # without re-running the classifier (and so events.jsonl is self-
    # describing for forensic replay).
    if inferred is not None and inferred != effective:
        event["kind_tag_inferred"] = inferred
    if args.size is not None:
        event["size"] = args.size
    # Allow callers to pass --size auto to resolve from disk.
    if args.size is None and args.path:
        abs_path = (Path(args.sandbox) / args.path).resolve()
        if abs_path.exists() and abs_path.is_file():
            event["size"] = abs_path.stat().st_size
    return event


def _cmd_error(args: argparse.Namespace) -> dict:
    return {
        "ts": _now_ms(),
        "kind": "error",
        "code": args.code,
        "msg": args.msg,
    }


def _parse_json_details(raw: str | None) -> dict | None:
    """Parse --details payloads (JSON object). Caller-fatal on bad shape.

    Accepts `None` (caller omitted --details) and returns `None` so the
    event omits the field entirely. Anything else must parse to a JSON
    object; non-objects (lists / scalars) are rejected so consumers can
    rely on `event["details"]` being a dict when present.
    """
    if raw is None:
        return None
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError as e:
        print(
            f"[emit_event] --details is not valid JSON: {e}",
            file=sys.stderr,
        )
        sys.exit(2)
    if not isinstance(parsed, dict):
        print(
            f"[emit_event] --details must be a JSON object, got {type(parsed).__name__}",
            file=sys.stderr,
        )
        sys.exit(2)
    return parsed


def _cmd_delta(args: argparse.Namespace) -> dict:
    """formalization_delta — agent declares a notable math-content change.

    Used by the Rule 3 gates: Layer 4 judge consumes deltas during
    promotion; the web UI surfaces `severity=notable|breaking` deltas in
    the LifecyclePanel so the user can review before approving.
    """
    if not args.summary or not args.summary.strip():
        print("[emit_event] delta requires non-empty --summary", file=sys.stderr)
        sys.exit(2)
    event: dict = {
        "ts": _now_ms(),
        "kind": "formalization_delta",
        "change_type": args.change_type,
        "summary": args.summary,
        "severity": args.severity,
    }
    if args.before_path:
        event["before_path"] = args.before_path
    if args.after_path:
        event["after_path"] = args.after_path
    details = _parse_json_details(args.details)
    if details is not None:
        event["details"] = details
    return event


def _cmd_milestone(args: argparse.Namespace) -> dict:
    """sandbox_milestone — sandbox crossed a meaningful gate.

    Triggers downstream daemons (sandbox_watcher, Step 4) and gives the
    UI clean transition points without parsing tool prose.
    """
    event: dict = {
        "ts": _now_ms(),
        "kind": "sandbox_milestone",
        "name": args.name,
    }
    if args.path:
        event["path"] = args.path
    details = _parse_json_details(args.details)
    if details is not None:
        event["details"] = details
    return event


def _cmd_agent_state(args: argparse.Namespace) -> dict:
    """agent_state — explicit turn-state stream.

    Replaces the SDK's `session_state_changed` (V2-unstable, never
    actually emitted in stream-json IPC mode). Skill authors emit on
    state transitions; the web side reduces to a single Lifecycle state
    via Step 3's agentStateReducer.
    """
    if args.since_ms is not None and args.since_ms < 0:
        print(
            f"[emit_event] --since-ms must be >= 0, got {args.since_ms}",
            file=sys.stderr,
        )
        sys.exit(2)
    event: dict = {
        "ts": _now_ms(),
        "kind": "agent_state",
        "state": args.state,
    }
    if args.since_ms is not None:
        event["since_ms"] = args.since_ms
    if args.prompt:
        event["prompt"] = args.prompt
    return event


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--sandbox",
        required=True,
        help="Absolute path to the job sandbox (Statlean/Web/<jobId>/).",
    )
    sub = ap.add_subparsers(dest="kind", required=True)

    p_step = sub.add_parser("step", help="Step boundary event.")
    p_step.add_argument("--id", type=int, required=True)
    p_step.add_argument("--title")
    p_step.add_argument(
        "--status",
        choices=["start", "done", "error"],
        required=True,
    )

    p_art = sub.add_parser("artifact", help="Artifact-ready event.")
    p_art.add_argument(
        "--kind-tag",
        required=False,
        default=None,
        help=(
            "UI artifact classifier: pdf-extract | yaml | lean-skeleton "
            "| lean-live | sorry-list | sub-agent-result. "
            "Optional — defaults to the path-inferred kind via "
            "_artifact_classify.classify_artifact_path. Pass explicitly only "
            "when emitting an out-of-taxonomy kind (e.g. sub-agent-result)."
        ),
    )
    p_art.add_argument(
        "--path",
        required=True,
        help="Relative path inside the sandbox.",
    )
    p_art.add_argument(
        "--size",
        type=int,
        help="Bytes. Omit to auto-stat from --path.",
    )

    p_err = sub.add_parser("error", help="Structured error event.")
    p_err.add_argument("--code", required=True, help="Enum from ui-signals.md §3.")
    p_err.add_argument("--msg", required=True)

    # ── delta / milestone / agent-state — Step 2 of elegant-plan ────
    p_delta = sub.add_parser(
        "delta",
        help="Formalization delta event — agent declares a math-content change.",
    )
    p_delta.add_argument(
        "--change-type",
        required=True,
        choices=DELTA_CHANGE_TYPES,
        help="Categorical kind of change. See ui-signals.md §6.",
    )
    p_delta.add_argument(
        "--summary",
        required=True,
        help="Short human-readable description of what changed and why.",
    )
    p_delta.add_argument(
        "--severity",
        choices=DELTA_SEVERITIES,
        default="notable",
        help="Default 'notable'. Use 'info' for cosmetic, 'breaking' for weakening.",
    )
    p_delta.add_argument(
        "--before-path",
        help="Relative path of the artifact before the change (e.g. theorems.yaml).",
    )
    p_delta.add_argument(
        "--after-path",
        help="Relative path of the artifact after the change (e.g. Main.lean).",
    )
    p_delta.add_argument(
        "--details",
        help="Optional JSON object with extra fields (e.g. {\"old_type\":\"ℝ\",\"new_type\":\"ℕ\"}).",
    )

    p_ms = sub.add_parser(
        "milestone",
        help="Sandbox milestone event — gate crossed; downstream daemons may react.",
    )
    p_ms.add_argument(
        "--name",
        required=True,
        choices=MILESTONE_NAMES,
        help="Canonical milestone name. See ui-signals.md §7.",
    )
    p_ms.add_argument(
        "--path",
        help="Optional relative path of the artifact that triggered the milestone.",
    )
    p_ms.add_argument(
        "--details",
        help="Optional JSON object with extra fields (e.g. {\"count_before\":3}).",
    )

    p_state = sub.add_parser(
        "agent-state",
        help="Agent turn-state event — explicit unified lifecycle stream.",
    )
    p_state.add_argument(
        "--state",
        required=True,
        choices=AGENT_STATES,
        help="Canonical state. See ui-signals.md §8.",
    )
    p_state.add_argument(
        "--since-ms",
        type=int,
        help="Optional: how long the agent has been in this state (ms).",
    )
    p_state.add_argument(
        "--prompt",
        help="Optional: when state=awaiting-input, the question being asked.",
    )

    args = ap.parse_args()
    if args.kind == "step":
        event = _cmd_step(args)
    elif args.kind == "artifact":
        event = _cmd_artifact(args)
    elif args.kind == "error":
        event = _cmd_error(args)
    elif args.kind == "delta":
        event = _cmd_delta(args)
    elif args.kind == "milestone":
        event = _cmd_milestone(args)
    elif args.kind == "agent-state":
        event = _cmd_agent_state(args)
    else:
        ap.error(f"unknown kind: {args.kind}")

    try:
        _append_event(Path(args.sandbox), event)
    except OSError as e:
        print(f"[emit_event] write failed: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

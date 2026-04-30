#!/usr/bin/env python3
"""process_sorry_result.py — bundle all side effects after a sub-agent returns.

Replaces the narrative "agent should emit X, run Y, update Z" chain in
prove-deep.md `process_result(...)`. One script call atomically:
  - Updates sorry_backlog.yaml (status mutation only; full reconcile is
    sync_sorry_backlog.py's job)
  - Refreshes sorry_list.json via extract_sorries.py
  - Emits the appropriate per-result milestone (sorry-proved /
    lake-build-fail / subagent-stuck / decomposition-rejected /
    subtasks-split)
  - Emits sorry-pool-snapshot for telemetry (count + delta + depth_histogram)
  - For status=need_sub_lemma: validates the decomposition first via
    validate_decomposition.py; rejected decompositions don't add children
    and mark parent stuck instead.

Per CLAUDE.md Rule 9 Q3 (determinism gate): bundling these side effects
into one script means individual steps cannot be silently skipped. The
previous form (~5 narrative emit_event lines spread across prove-deep.md)
was routinely under-executed by agents, breaking sorry_list freshness
and downstream consumers.

Exit 0 always (best-effort sub-steps; failures are logged but don't
abort the overall finalization). Use the emitted milestones to verify
which sub-step landed.
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
EXTRACT_SORRIES = SCRIPTS_DIR / "extract_sorries.py"
VALIDATE_DECOMP = SCRIPTS_DIR / "validate_decomposition.py"
PROPAGATE_DONE = SCRIPTS_DIR / "propagate_done.py"
SAVE_LAST_WRONG = SCRIPTS_DIR / "save_last_wrong_attempt.py"
BACKLOG_PATH = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

# czy newloop merge: schema_version=2 fields. Idempotent migration on load.
sys.path.insert(0, str(SCRIPTS_DIR))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort emit; logs but doesn't abort on emit_event failure."""
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", name,
                "--details", json.dumps(details),
            ],
            check=True,
            timeout=30,
        )
    except Exception as e:
        print(f"[process_sorry_result] emit {name} failed: {e}", file=sys.stderr)


def _refresh_sorry_list(sandbox: Path, lean_file: Path | None) -> int:
    """Re-run extract_sorries; return current sorry count."""
    out = sandbox / "sorry_list.json"
    cmd = ["python3", str(EXTRACT_SORRIES), "--output", str(out)]
    if lean_file and lean_file.exists():
        cmd += ["--lean-file", str(lean_file), "--job-id", sandbox.name]
    else:
        cmd += ["--sandbox", str(sandbox)]
    try:
        subprocess.run(cmd, check=False, timeout=60)
    except subprocess.TimeoutExpired:
        print("[process_sorry_result] extract_sorries timed out", file=sys.stderr)
    if not out.exists():
        return 0
    try:
        return len(json.loads(out.read_text()))
    except Exception:
        return 0


def _read_stuck_rounds(sorry_id: str) -> int:
    """Read current stuck_rounds for a sorry; default 0 if absent.

    Slice 3.B helper: process_sorry_result bumps this on status=stuck;
    prove-deep.md narrative compares against threshold (3) to decide
    whether to call record_retreat.py.
    """
    if not BACKLOG_PATH.exists():
        return 0
    try:
        data = yaml.safe_load(BACKLOG_PATH.read_text()) or {}
    except yaml.YAMLError:
        return 0
    for item in (data.get("sorry_items") or []):
        if item.get("id") == sorry_id:
            return int(item.get("stuck_rounds", 0))
    return 0


def _update_backlog_status(sorry_id: str, mutations: dict) -> None:
    """Targeted mutation of one sorry's status fields. Full reconcile is
    sync_sorry_backlog.py's job."""
    if not BACKLOG_PATH.exists():
        return
    try:
        data = yaml.safe_load(BACKLOG_PATH.read_text()) or {}
    except yaml.YAMLError as e:
        print(f"[process_sorry_result] backlog parse failed: {e}", file=sys.stderr)
        return
    # czy newloop merge: idempotent v1→v2 migration on load.
    migrate_yaml_v1_to_v2(data)
    items = data.get("sorry_items") or []
    for item in items:
        if item.get("id") == sorry_id:
            item.update(mutations)
            break
    BACKLOG_PATH.write_text(
        yaml.safe_dump(data, sort_keys=False, allow_unicode=True)
    )


def _depth_histogram(sandbox: Path) -> dict:
    out = sandbox / "sorry_list.json"
    if not out.exists():
        return {}
    try:
        items = json.loads(out.read_text())
    except Exception:
        return {}
    hist: dict = {}
    for it in items:
        # `depth` is an optional schema field added when sorry was generated
        # by Phase 1 decomposition. Default 0 = top-level (from skeleton).
        d = str(it.get("depth", 0))
        hist[d] = hist.get(d, 0) + 1
    return hist


def main() -> None:
    global BACKLOG_PATH
    ap = argparse.ArgumentParser(
        description="Bundle post-result side effects for one sorry"
    )
    ap.add_argument("--sandbox", required=True)
    ap.add_argument("--sorry-id", required=True)
    ap.add_argument(
        "--status",
        required=True,
        choices=[
            "proved", "stuck", "need_sub_lemma", "lake_build_fail",
            # E12 phase 03: write/edit failure persistence.
            "write_fail", "edit_fail",
            # E12 phase 03 stub: replace_fail deferred to Phase 04 (D-7 Option A).
            "replace_fail",
        ],
    )
    ap.add_argument("--module",
                    help="Lean module (e.g. Statlean.Variance.UStatistic)")
    ap.add_argument("--lean-file",
                    help="Path to .lean file (for extract_sorries refresh)")
    ap.add_argument("--blocker", default="",
                    help="One-line reason (stuck / lake_build_fail)")
    ap.add_argument("--children-decomposition",
                    help="JSON array (need_sub_lemma) — children metrics")
    ap.add_argument("--parent-metrics",
                    help="JSON object (need_sub_lemma) — parent metrics")
    # M5 auto_tactic pre-pass: callers tag the closer that proved the
    # sorry so downstream telemetry can attribute origin (cost
    # accounting, audit). Default `"prover"` preserves backward-compat
    # for all current callers in `~/statlean-merge/.claude/commands/*.md`
    # and `~/statlean-merge/theme/scripts/*.py` (none pass --closer).
    # M5 passes `--closer auto_tactic`. New value space MAY be extended
    # by future closers (e.g. lsp_pre_pass) without protocol break —
    # consumers should treat unknown values as opaque telemetry.
    ap.add_argument("--closer", default="prover",
                    help="Origin of the proof closure ('prover' default; "
                         "'auto_tactic' for M5 pre-pass)")
    # M5 §8 code review S2.4: callers running outside the default
    # statlean tree (L2 tests, multi-tenant invocations) must be able
    # to override the backlog path. All helpers below read BACKLOG_PATH
    # at call time, so reassigning the module global here propagates.
    ap.add_argument("--backlog-path", default=None,
                    help="Override default backlog path "
                         "(<scripts>/../input/sorry_backlog.yaml)")
    # E12 phase 03: write_fail / edit_fail content persistence args.
    ap.add_argument("--content", default=None,
                    help="Path to a file containing the failed .lean content "
                         "(for write_fail / edit_fail)")
    ap.add_argument("--diagnostics", default="[]",
                    help="LSP diagnostics JSON string for write_fail / edit_fail "
                         "(3 shapes accepted by save_last_wrong_attempt.py)")
    args = ap.parse_args()

    if args.backlog_path:
        BACKLOG_PATH = Path(args.backlog_path).resolve()

    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists():
        print(f"[process_sorry_result] sandbox missing: {sandbox}",
              file=sys.stderr)
        sys.exit(2)

    lean_file = Path(args.lean_file).resolve() if args.lean_file else None

    # Snapshot pool size BEFORE refresh so we can compute delta.
    sl = sandbox / "sorry_list.json"
    pre_count = 0
    if sl.exists():
        try:
            pre_count = len(json.loads(sl.read_text()))
        except Exception:
            pass

    # ---- Status-specific emits + backlog mutations ------------------
    if args.status == "proved":
        # M3 (per docs/M3_DONE_REASON_PROVED_SPEC.md §10 D-3): extend
        # `sorry-proved` payload with `done_reason_set: "proved"` for
        # telemetry parity with E11's `citation-verified` payload
        # (which carries done_reason_set for library_verified /
        # reference_axiom). Same shape across both writers means
        # downstream consumers (events.jsonl analyzers, audit scripts)
        # have a uniform key for "which done_reason value was set this
        # invocation."
        # M5 (per docs/M5_AUTO_TACTIC_SPEC.md §4 D-4): extend
        # `sorry-proved` payload with `closer` so downstream telemetry
        # can attribute the origin (`prover` default vs `auto_tactic`
        # from M5's pre-pass). czy emits the same signal via freeform
        # log prefix `[AUTO-TACTIC] ✓ line N: closed by 'rfl'`
        # (proofLoop.ts:1255-1257); SDK-bridge restores it as a
        # structured payload key. Consumers ignoring `closer` continue
        # to work (JSON-extensibility; M3 D-3 precedent).
        _emit(sandbox, "sorry-proved",
              {
                  "sorry_id": args.sorry_id,
                  "module": args.module,
                  "done_reason_set": "proved",
                  "closer": args.closer,
              })
        # czy newloop port slice 3.B: in addition to status=proved, also
        # set state=DONE and done_reason=proved (v2 schema), so cascade
        # propagation has a consistent state-machine signal upward.
        # M3 (D-1): czy proofState.ts:64-82 documents `"proved"` as the
        # success-mode marker WITHOUT a deferral annotation (contrast
        # `done_by_dependency` lines 75-77 which IS annotated "Reserved
        # /Not currently emitted"). czy never writes `"proved"` despite
        # documenting it — implementation gap, not deferred design.
        # SDK-bridge writing it preserves czy's documented intent at
        # the docstring level. Same framing as A1's D-1/D-2.
        _update_backlog_status(args.sorry_id, {
            "status": "proved",
            "state": "DONE",
            "done_reason": "proved",
        })
        # Cascade DONE up the parent chain (T2 chain). Best-effort —
        # propagate_done is no-op if the node has no parent or sibling
        # is still in flight.
        try:
            subprocess.run(
                ["python3", str(PROPAGATE_DONE),
                 "--node-id", args.sorry_id,
                 "--sandbox", str(sandbox),
                 "--backlog-path", str(BACKLOG_PATH)],
                check=True,
            )
        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            print(f"[process_sorry_result] propagate_done failed: {e}",
                  file=sys.stderr)

    elif args.status == "lake_build_fail":
        # E12 phase 02: invoke match_pitfall.py to append a routing hint to
        # --blocker before emitting the event (T1 within T2 per spec §7).
        # The hint is written into events.jsonl (persistent, not transient
        # tool-result string) — deliberate +1 over czy's transient injection
        # (D-6 persistence dimension).
        blocker_with_hint = args.blocker or ""
        try:
            result = subprocess.run(
                [sys.executable,
                 str(SCRIPTS_DIR / "match_pitfall.py"),
                 "--error-text", args.blocker or ""],
                capture_output=True, text=True, timeout=5,
            )
            if result.returncode == 0 and result.stdout.strip():
                blocker_with_hint = (args.blocker or "") + "\n" + result.stdout.strip()
        except Exception as e:
            print(f"[process_sorry_result] match_pitfall failed: {e}",
                  file=sys.stderr)
        _emit(sandbox, "lake-build-fail",
              {"sorry_id": args.sorry_id, "blocker": blocker_with_hint,
               "module": args.module})
        _update_backlog_status(args.sorry_id, {"status": "pending"})

    elif args.status == "stuck":
        _emit(sandbox, "subagent-stuck",
              {"sorry_id": args.sorry_id, "blocker": args.blocker})
        # czy newloop port slice 3.B: bump stuck_rounds. Threshold (3)
        # is checked by prove-deep.md narrative, which calls
        # record_retreat.py when reached. The bump itself is determinist;
        # the threshold logic is T3 narrative because the agent decides
        # WHICH retreat reason to record.
        # §8 review fix (P1): use locked_backlog for atomic
        # read+modify+write so concurrent stuck submissions on the same
        # sorry can't lose a bump.
        from _yaml_io import atomic_write_yaml as _aw, locked_backlog as _lb
        try:
            with _lb(BACKLOG_PATH) as data:
                items = data.get("sorry_items") or []
                for it in items:
                    if it.get("id") == args.sorry_id:
                        prev = int(it.get("stuck_rounds", 0))
                        it["stuck_rounds"] = prev + 1
                        it["status"] = "pending"
                        break
                _aw(BACKLOG_PATH, data)
        except Exception as e:
            # Fallback to non-locked path so we still emit the milestone
            # — pre-existing process_sorry_result writes weren't locked
            # either; this is best-effort hardening for the new bump.
            print(f"[process_sorry_result] flock-bump failed, fallback: {e}",
                  file=sys.stderr)
            new_stuck = _read_stuck_rounds(args.sorry_id) + 1
            _update_backlog_status(args.sorry_id, {
                "status": "pending",
                "stuck_rounds": new_stuck,
            })

    elif args.status == "need_sub_lemma":
        if not args.parent_metrics or not args.children_decomposition:
            print(
                "[process_sorry_result] need_sub_lemma requires "
                "--parent-metrics and --children-decomposition",
                file=sys.stderr,
            )
            sys.exit(2)
        validate = subprocess.run(
            [
                "python3", str(VALIDATE_DECOMP),
                "--parent-metrics", args.parent_metrics,
                "--children-metrics", args.children_decomposition,
            ],
            capture_output=True, text=True,
        )
        if validate.returncode != 0:
            _emit(sandbox, "decomposition-rejected", {
                "sorry_id": args.sorry_id,
                "reason": (validate.stderr or "").strip()[:500],
            })
            _update_backlog_status(args.sorry_id, {"status": "pending"})
            print("[process_sorry_result] decomposition REJECTED; "
                  "parent marked pending", file=sys.stderr)
        else:
            try:
                children = json.loads(args.children_decomposition)
            except json.JSONDecodeError:
                children = []
            _emit(sandbox, "subtasks-split", {
                "sorry_id": args.sorry_id,
                "children": children,
            })
            # Adding children to sorry_backlog.yaml is the caller's
            # responsibility (prove-deep.md Phase 1 step 4 still owns
            # the schema for new sorry-item entries). This script only
            # validates + emits.

    elif args.status in ("write_fail", "edit_fail"):
        # E12 phase 03: persist annotated last-wrong-attempt.lean.
        # Calls save_last_wrong_attempt.py (T1 within T2 chain per spec §7):
        # once this branch runs, the file write + milestone emit are
        # structurally guaranteed regardless of agent compliance.
        fail_type = "write" if args.status == "write_fail" else "edit"
        sla_cmd = [
            sys.executable, str(SAVE_LAST_WRONG),
            "--sandbox", str(sandbox),
            "--fail-type", fail_type,
            "--diagnostics", args.diagnostics or "[]",
        ]
        if args.sorry_id:
            sla_cmd += ["--sorry-id", args.sorry_id]

        stdin_data: str | None = None
        if args.content:
            sla_cmd += ["--content", args.content]
        else:
            # No content file provided — write a placeholder so the file
            # still appears in the sandbox (agent can read it).
            sla_cmd += ["--content-stdin"]
            stdin_data = (
                "-- last_wrong_attempt.lean: content not provided "
                "(--content missing from process_sorry_result call)\n"
            )

        try:
            run_kwargs: dict = dict(
                capture_output=True, text=True, timeout=15,
            )
            if stdin_data is not None:
                run_kwargs["input"] = stdin_data
            proc = subprocess.run(sla_cmd, **run_kwargs)
            if proc.returncode == 0:
                print(f"[process_sorry_result] {args.status}: {proc.stdout.strip()}")
            else:
                print(
                    f"[process_sorry_result] save_last_wrong_attempt failed "
                    f"(rc={proc.returncode}): {proc.stderr.strip()[:200]}",
                    file=sys.stderr,
                )
        except subprocess.TimeoutExpired:
            print(
                "[process_sorry_result] save_last_wrong_attempt timed out "
                "(graceful degradation — continuing)",
                file=sys.stderr,
            )
        except Exception as e:
            print(
                f"[process_sorry_result] save_last_wrong_attempt error: {e}",
                file=sys.stderr,
            )
        # Also emit a lake-build-fail for telemetry compatibility.
        _emit(sandbox, "lake-build-fail",
              {"sorry_id": args.sorry_id, "blocker": args.blocker or "",
               "module": args.module, "fail_type": fail_type})
        _update_backlog_status(args.sorry_id, {"status": "pending"})

    elif args.status == "replace_fail":
        # E12 phase 03 stub: applyReplaceSorry Python port deferred to Phase 04.
        # D-7 Option A: log warning only, NO save_last_wrong_attempt call.
        # TODO Phase 04: add --tactic <str> --line <int> args to
        # save_last_wrong_attempt.py and perform sorry→(by tactic) substitution
        # (Python port of applyReplaceSorry from lastWrongAttempt.ts:227-243).
        print(
            "[process_sorry_result] replace_fail: last-wrong-attempt deferred to Phase 04 "
            "(applyReplaceSorry not yet ported). Blocker logged only.",
            file=sys.stderr,
        )
        _emit(sandbox, "lake-build-fail",
              {"sorry_id": args.sorry_id, "blocker": args.blocker or "",
               "module": args.module, "fail_type": "replace"})
        _update_backlog_status(args.sorry_id, {"status": "pending"})

    # ---- Always: refresh + telemetry --------------------------------
    post_count = _refresh_sorry_list(sandbox, lean_file)
    _emit(sandbox, "sorry-pool-snapshot", {
        "count": post_count,
        "delta": post_count - pre_count,
        "depth_histogram": _depth_histogram(sandbox),
    })

    print(f"[process_sorry_result] {args.sorry_id}  status={args.status}  "
          f"pool: {pre_count} → {post_count}")


if __name__ == "__main__":
    main()

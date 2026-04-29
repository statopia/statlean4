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
    ap = argparse.ArgumentParser(
        description="Bundle post-result side effects for one sorry"
    )
    ap.add_argument("--sandbox", required=True)
    ap.add_argument("--sorry-id", required=True)
    ap.add_argument(
        "--status",
        required=True,
        choices=["proved", "stuck", "need_sub_lemma", "lake_build_fail"],
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
    args = ap.parse_args()

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
        _emit(sandbox, "sorry-proved",
              {"sorry_id": args.sorry_id, "module": args.module})
        _update_backlog_status(args.sorry_id, {"status": "proved"})

    elif args.status == "lake_build_fail":
        _emit(sandbox, "lake-build-fail",
              {"sorry_id": args.sorry_id, "blocker": args.blocker,
               "module": args.module})
        _update_backlog_status(args.sorry_id, {"status": "pending"})

    elif args.status == "stuck":
        _emit(sandbox, "subagent-stuck",
              {"sorry_id": args.sorry_id, "blocker": args.blocker})
        _update_backlog_status(args.sorry_id, {"status": "pending"})

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

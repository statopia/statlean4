#!/usr/bin/env python3
"""prove_deep_end.py — finalize a /prove-deep DAG cycle.

Called by /prove-deep at the end of Phase 3. Bundles all post-cycle
side effects so individual steps can't be silently skipped. Replaces
the narrative "Phase 3 step 3-6" instructions in prove-deep.md (which
agents routinely skipped, especially MEMORY.md updates).

Required side effects (REJECT cycle if any fails):
  1. --memory-summary must be non-empty (>= 20 chars) — agent must
     supply natural-language summary of what this round learned
  2. Run sync_sorry_backlog.py (subprocess; non-fatal if it fails)
  3. Append memory-summary to MEMORY.md under a dated section
  4. If --new-knowledge-file given: run ingest_knowledge.py
  5. Emit milestone "memory-md-updated"
  6. Emit milestone "dag-cycle-done" with stats

Per CLAUDE.md Rule 9 Q3 (determinism gate): bundles Phase 3 finalization
into one named call. Crucially, the --memory-summary requirement makes
"Update MEMORY.md" structural rather than aspirational — empty/short
summaries cause exit 1 and the cycle is not considered finalized.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
STATLEAN_ROOT = SCRIPTS_DIR.parent.parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
SYNC_BACKLOG = SCRIPTS_DIR / "sync_sorry_backlog.py"
INGEST_KNOWLEDGE = STATLEAN_ROOT / "scripts" / "ingest_knowledge.py"
MEMORY_MD = STATLEAN_ROOT / "MEMORY.md"

MIN_SUMMARY_CHARS = 20


def _emit(sandbox: Path, name: str, details: dict) -> None:
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


def _append_memory(target: str, summary: str, stats: dict) -> None:
    today = dt.datetime.now().strftime("%Y-%m-%d %H:%M")
    section = (
        f"\n## {today} — `{target}`\n\n"
        f"**Stats**: proved={stats['proved']}  stuck={stats['stuck']}  "
        f"remaining={stats['remaining']}\n\n"
        f"**Summary**:\n\n{summary.strip()}\n"
    )
    if MEMORY_MD.exists():
        MEMORY_MD.write_text(MEMORY_MD.read_text() + section)
    else:
        MEMORY_MD.write_text(
            "# Statlean Project Memory\n\n"
            "Auto-appended by `theme/scripts/prove_deep_end.py` after each "
            "/prove-deep cycle. Each section: dated + target + stats + "
            "agent's natural-language summary of what was learned.\n"
            + section
        )


def main() -> None:
    ap = argparse.ArgumentParser(description="prove-deep DAG cycle finalize")
    ap.add_argument("--sandbox", required=True)
    ap.add_argument("--target", required=True,
                    help="What this cycle attacked (sorry-id, 'next', 'all-leaves')")
    ap.add_argument("--proved", type=int, required=True)
    ap.add_argument("--stuck", type=int, required=True)
    ap.add_argument("--remaining", type=int, required=True)
    ap.add_argument(
        "--memory-summary",
        required=True,
        help=(
            "Natural-language summary of this cycle's learning, in agent's "
            f"own words. Required, must be >= {MIN_SUMMARY_CHARS} chars after "
            "trim. Empty / placeholder values cause non-zero exit and the "
            "cycle is NOT marked finalized."
        ),
    )
    ap.add_argument(
        "--new-knowledge-file",
        help="Optional path to YAML for proof_knowledge ingestion",
    )
    args = ap.parse_args()

    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists():
        print(f"[prove_deep_end] sandbox does not exist: {sandbox}",
              file=sys.stderr)
        sys.exit(2)

    summary = args.memory_summary.strip()
    if len(summary) < MIN_SUMMARY_CHARS:
        print(
            f"[prove_deep_end] --memory-summary must be >= "
            f"{MIN_SUMMARY_CHARS} chars after trim "
            f"(got {len(summary)}). Phase 3 NOT finalized. "
            f"Re-run with a real summary of what this cycle learned.",
            file=sys.stderr,
        )
        sys.exit(1)

    stats = {
        "proved": args.proved,
        "stuck": args.stuck,
        "remaining": args.remaining,
    }

    # 1. sync sorry_backlog (non-fatal — best effort)
    if SYNC_BACKLOG.exists():
        try:
            subprocess.run(["python3", str(SYNC_BACKLOG)], check=False,
                           timeout=60)
        except subprocess.TimeoutExpired:
            print("[prove_deep_end] sync_sorry_backlog timed out, continuing",
                  file=sys.stderr)

    # 2. append MEMORY.md (mandatory)
    _append_memory(args.target, summary, stats)

    # 3. ingest_knowledge (optional)
    if args.new_knowledge_file:
        nkf = Path(args.new_knowledge_file)
        if nkf.exists() and INGEST_KNOWLEDGE.exists():
            subprocess.run(
                ["python3", str(INGEST_KNOWLEDGE), "--input", str(nkf)],
                check=False,
            )

    # 4. milestones — order matters: memory before dag-cycle-done so
    #    consumers can verify MEMORY.md was actually updated before
    #    treating the cycle as complete.
    _emit(sandbox, "memory-md-updated", {
        "target": args.target,
        "summary_chars": len(summary),
    })

    # 5. PR4 (D1+D2 from CLI_WEB_CONFORMANCE.md §0.3): auto-stash residual
    #    uncommitted work so the next job inherits a clean baseline.
    #    Solves the 100+ file dirty-tree accumulation observed in
    #    jobmofvoxwsav8y. Stash recoverable via `git stash list` /
    #    `git stash pop`. Env opt-out for CLI users with intentional WIP:
    #      STATLEAN_NO_AUTO_STASH=1 disables; default = on.
    if os.environ.get("STATLEAN_NO_AUTO_STASH") != "1":
        try:
            r = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=STATLEAN_ROOT, capture_output=True, text=True, timeout=10,
            )
            if r.returncode == 0 and r.stdout.strip():
                files = [l for l in r.stdout.splitlines() if l.strip()]
                stash_msg = (
                    f"auto-{args.target}-"
                    f"{dt.datetime.now().strftime('%Y%m%d-%H%M%S')}"
                )
                # -u so untracked .lean files (typical for new sub-lemma
                # scaffold) also get stashed. -m sets the message.
                stash = subprocess.run(
                    ["git", "stash", "push", "-u", "-m", stash_msg],
                    cwd=STATLEAN_ROOT, capture_output=True, text=True, timeout=30,
                )
                if stash.returncode == 0 and "No local changes to save" not in stash.stdout:
                    _emit(sandbox, "working-tree-stashed", {
                        "target": args.target,
                        "stash_msg": stash_msg,
                        "files_count": len(files),
                        "files_preview": files[:10],
                    })
                    print(
                        f"[prove_deep_end] auto-stashed {len(files)} file(s) "
                        f"as '{stash_msg}'. Recover: git stash list | "
                        f"grep {stash_msg} && git stash pop ..."
                    )
        except Exception as e:
            # Best-effort; never let stash failure prevent dag-cycle-done emit
            print(f"[prove_deep_end] auto-stash failed: {e}", file=sys.stderr)

    _emit(sandbox, "dag-cycle-done", {"target": args.target, **stats})

    print(f"[prove_deep_end] cycle complete  target={args.target}  "
          f"proved={args.proved}  stuck={args.stuck}  "
          f"remaining={args.remaining}")


if __name__ == "__main__":
    main()

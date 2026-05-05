#!/usr/bin/env python3
"""prove_deep_end.py — finalize a /prove-deep DAG cycle.

Two modes:

* **Agent-finalize (default).** Called by /prove-deep at the end of Phase 3.
  Bundles all post-cycle side effects so individual steps can't be silently
  skipped. Replaces the narrative "Phase 3 step 3-6" instructions in
  prove-deep.md (which agents routinely skipped, especially MEMORY.md updates).
  Required side effects (REJECT cycle if any fails):
    1. --memory-summary must be non-empty (>= 20 chars) — agent must supply
       natural-language summary of what this round learned
    2. Run sync_sorry_backlog.py (subprocess; non-fatal if it fails)
    3. Append memory-summary to MEMORY.md under a dated section
    4. If --new-knowledge-file given: run ingest_knowledge.py
    5. Emit milestone "memory-md-updated"
    6. Auto-stash residual WIP (stash_prefix=auto)
    7. Emit milestone "dag-cycle-done" with stats

* **Hygiene-only (--hygiene-only).** Called by the web orchestrator on the
  fallback paths where the agent never ran the agent-finalize call —
  dag-cycle-done timer fired (Step 6 done + 30s) or SSE was cancelled. Runs
  only sync_sorry_backlog + auto-stash + working-tree-stashed emit. Stash
  prefix is "fallback" or "cancel" (vs "auto") so the stash list shows which
  path triggered. MEMORY.md / dag-cycle-done emits are intentionally skipped
  in this mode — orchestrator-fallback already emitted dag-cycle-done from
  TS, and there's no agent summary to write.

Per CLAUDE.md Rule 9 Q3 (determinism gate): the --memory-summary requirement
makes "Update MEMORY.md" structural rather than aspirational in the
agent-finalize path; --hygiene-only gives the web orchestrator a single
named call for post-cycle hygiene that doesn't depend on the agent.
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
    ap.add_argument("--proved", type=int, default=0)
    ap.add_argument("--stuck", type=int, default=0)
    ap.add_argument("--remaining", type=int, default=0)
    ap.add_argument(
        "--memory-summary",
        default="",
        help=(
            "Natural-language summary of this cycle's learning, in agent's "
            f"own words. Required (>= {MIN_SUMMARY_CHARS} chars after trim) "
            "in normal mode. Ignored under --hygiene-only."
        ),
    )
    ap.add_argument(
        "--new-knowledge-file",
        help="Optional path to YAML for proof_knowledge ingestion",
    )
    ap.add_argument(
        "--hygiene-only",
        action="store_true",
        help=(
            "Orchestrator-fallback mode: skip MEMORY.md append, ingest, and "
            "memory-md-updated / dag-cycle-done emits. Run only sync_sorry_backlog "
            "+ auto-stash + working-tree-stashed emit. Lets web orchestrator "
            "reach the post-cycle hygiene path even when the agent skipped "
            "calling this script in the agent-finalize path."
        ),
    )
    ap.add_argument(
        "--stash-prefix",
        default="auto",
        choices=["auto", "cancel", "fallback"],
        help=(
            "Label embedded in the stash message: 'auto' (agent-finalize, default), "
            "'cancel' (web /cancel + SSE-disconnect cleanup), 'fallback' "
            "(orchestrator post-cycle hygiene). Pure observability — same recovery "
            "command regardless of prefix."
        ),
    )
    args = ap.parse_args()

    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists():
        print(f"[prove_deep_end] sandbox does not exist: {sandbox}",
              file=sys.stderr)
        sys.exit(2)

    summary = args.memory_summary.strip()
    if not args.hygiene_only and len(summary) < MIN_SUMMARY_CHARS:
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

    # 2. append MEMORY.md (mandatory in agent-finalize mode; skipped under --hygiene-only)
    if not args.hygiene_only:
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
    #    jobmofvoxwsav8y, which was specifically *untracked scaffolding
    #    files* (sub-lemma `.lean` drafts, `/tmp/...` copies committed in
    #    error, etc).
    #
    #    Tracked-file modifications are intentionally NOT stashed — they
    #    are typically deliberate cycle-finalization edits (e.g. updating
    #    `Statlean.Verified` to add the newly proved module, MEMORY.md
    #    rollups, sorry_backlog.yaml after sync) that the user wants to
    #    commit immediately after `prove_deep_end` returns. Stashing them
    #    silently disrupted that workflow (observed 2026-05-06).
    #
    #    Stash recoverable via `git stash list` / `git stash pop`.
    #    Env opt-out: STATLEAN_NO_AUTO_STASH=1 (skip even untracked).
    if os.environ.get("STATLEAN_NO_AUTO_STASH") != "1":
        try:
            # Only consider untracked files (porcelain prefix `??`).
            r = subprocess.run(
                ["git", "status", "--porcelain"],
                cwd=STATLEAN_ROOT, capture_output=True, text=True, timeout=10,
            )
            if r.returncode == 0 and r.stdout.strip():
                untracked = [
                    l[3:] for l in r.stdout.splitlines()
                    if l.startswith("?? ")
                ]
                if untracked:
                    stash_msg = (
                        f"{args.stash_prefix}-{args.target}-"
                        f"{dt.datetime.now().strftime('%Y%m%d-%H%M%S')}"
                    )
                    # `git stash push -u -- <pathspec>` stashes only the
                    # listed untracked paths and leaves tracked WIP alone.
                    stash = subprocess.run(
                        ["git", "stash", "push", "-u", "-m", stash_msg, "--",
                         *untracked],
                        cwd=STATLEAN_ROOT, capture_output=True, text=True,
                        timeout=30,
                    )
                    if (stash.returncode == 0
                            and "No local changes to save" not in stash.stdout):
                        _emit(sandbox, "working-tree-stashed", {
                            "target": args.target,
                            "stash_msg": stash_msg,
                            "files_count": len(untracked),
                            "files_preview": untracked[:10],
                            "scope": "untracked-only",
                        })
                        print(
                            f"[prove_deep_end] auto-stashed {len(untracked)} "
                            f"untracked file(s) as '{stash_msg}' (tracked "
                            f"modifications kept). "
                            f"Recover: git stash list | "
                            f"grep {stash_msg} && git stash pop ..."
                        )
        except Exception as e:
            # Best-effort; never let stash failure prevent dag-cycle-done emit
            print(f"[prove_deep_end] auto-stash failed: {e}", file=sys.stderr)

    if not args.hygiene_only:
        _emit(sandbox, "dag-cycle-done", {"target": args.target, **stats})
        print(f"[prove_deep_end] cycle complete  target={args.target}  "
              f"proved={args.proved}  stuck={args.stuck}  "
              f"remaining={args.remaining}")
    else:
        print(f"[prove_deep_end] hygiene-only complete  target={args.target}  "
              f"prefix={args.stash_prefix}")


if __name__ == "__main__":
    main()

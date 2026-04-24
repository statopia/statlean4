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
    event: dict = {
        "ts": _now_ms(),
        "kind": "artifact",
        "kind_tag": args.kind_tag,
        "path": args.path,
    }
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
        required=True,
        help="UI artifact classifier: pdf-extract | yaml | lean-skeleton | lean-live | sorry-list | sub-agent-result",
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

    args = ap.parse_args()
    if args.kind == "step":
        event = _cmd_step(args)
    elif args.kind == "artifact":
        event = _cmd_artifact(args)
    elif args.kind == "error":
        event = _cmd_error(args)
    else:
        ap.error(f"unknown kind: {args.kind}")

    try:
        _append_event(Path(args.sandbox), event)
    except OSError as e:
        print(f"[emit_event] write failed: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

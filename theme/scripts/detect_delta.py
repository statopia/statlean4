#!/usr/bin/env python3
"""detect_delta.py — auto-detect math-content drift between two
artifacts and (optionally) emit a `formalization_delta` event.

Pairs with `_delta_detector.py` (pure prompt + parse) and
`emit_event.py delta` (event emitter). The full chain:

    BEFORE artifact + AFTER artifact  →  LLM compare  →
    parsed JSON (change / no change)  →  emit_event.py delta

Used by skills that touch the math content of theorems.yaml or
Main.lean to flag drift the agent didn't self-report. Without an
external detector the only path to a `formalization_delta` event is
the agent volunteering one, which is exactly the failure mode
jobmoe1utvq3yq5 surfaced.

Invocation from a skill (Bash):

    python3 theme/scripts/detect_delta.py \\
        --before "$SANDBOX/theorems.yaml" \\
        --after "$SANDBOX/Main.lean" \\
        --before-rel theorems.yaml \\
        --after-rel Main.lean \\
        --sandbox "$SANDBOX"

Behaviour:
  - exits 0 with stdout "no change" when content is byte-identical or
    the LLM returns `change_detected: false`.
  - exits 0 with stdout "delta emitted" when a change was detected and
    the event was successfully appended to events.jsonl.
  - exits 1 on hard errors: file not found, LLM unreachable, LLM
    returns unparseable response. Skills should NOT block on this —
    treat it as informational.

Cost notes:
  - Defaults to `--model claude-haiku-4-5-20251001` (the cheap one).
    Override with `--model` for accuracy on tricky compares.
  - Skips the LLM call when before/after are byte-identical (cheap
    pre-check via `texts_are_trivially_identical`).
  - One LLM round trip per invocation — skills should call this once
    per material edit, not in a hot loop.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _delta_detector import (  # noqa: E402
    build_prompt,
    parse_response,
    texts_are_trivially_identical,
)


# Default model. Cheap and fast; the comparison task is well within
# Haiku's pay-grade. Override via --model when you want a deeper read.
DEFAULT_MODEL = "claude-haiku-4-5-20251001"
DEFAULT_TIMEOUT_S = 90


def call_claude(prompt: str, model: str, timeout_s: int) -> str:
    """Spawn `claude -p` with the given prompt on stdin. Returns the
    captured stdout. Mirrors the pattern in
    `scripts/auto_prove.py::call_claude`.

    `--dangerously-skip-permissions` because no tool calls are
    expected — we want a one-shot completion. If the binary isn't on
    PATH or returns non-zero, the caller surfaces it as a hard error.
    """
    result = subprocess.run(
        [
            "claude",
            "-p",
            "--model", model,
            "--dangerously-skip-permissions",
        ],
        input=prompt,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"claude -p exited rc={result.returncode}: {result.stderr.strip()[:300]}"
        )
    return result.stdout


def emit_via_emit_event(
    sandbox: Path,
    parsed: dict,
    before_rel: str | None,
    after_rel: str | None,
) -> None:
    """Shell out to emit_event.py to append the formalization_delta.
    Reusing the emitter keeps a single write path into events.jsonl.
    """
    emit_script = Path(__file__).resolve().parent / "emit_event.py"
    cmd: list[str] = [
        sys.executable, str(emit_script),
        "--sandbox", str(sandbox),
        "delta",
        "--change-type", parsed["change_type"],
        "--summary", parsed["summary"],
        "--severity", parsed["severity"],
    ]
    if before_rel:
        cmd += ["--before-path", before_rel]
    if after_rel:
        cmd += ["--after-path", after_rel]
    if "details" in parsed:
        cmd += ["--details", json.dumps(parsed["details"])]
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        raise RuntimeError(
            f"emit_event.py exited rc={result.returncode}: {result.stderr.strip()}"
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--before", required=True, help="Path to BEFORE artifact (absolute or cwd-relative).")
    ap.add_argument("--after", required=True, help="Path to AFTER artifact.")
    ap.add_argument(
        "--before-rel",
        help="Sandbox-relative path of BEFORE, included in the emitted "
             "event's `before_path` field. Defaults to basename of --before.",
    )
    ap.add_argument(
        "--after-rel",
        help="Sandbox-relative path of AFTER, included in the emitted "
             "event's `after_path` field. Defaults to basename of --after.",
    )
    ap.add_argument(
        "--sandbox",
        help="Sandbox dir for emit_event.py. Omit to skip emission "
             "(detect-only mode — useful for dry runs / tests).",
    )
    ap.add_argument("--model", default=DEFAULT_MODEL, help=f"Default: {DEFAULT_MODEL}.")
    ap.add_argument(
        "--timeout-s",
        type=int,
        default=DEFAULT_TIMEOUT_S,
        help=f"Subprocess timeout for `claude -p`. Default: {DEFAULT_TIMEOUT_S}.",
    )
    ap.add_argument(
        "--mock-response",
        help="TEST-ONLY: skip the claude -p call and use this string as "
             "the model response. Lets unit tests exercise the parse +"
             " emit path deterministically.",
    )
    ap.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress stdout output; only exit code conveys outcome.",
    )
    args = ap.parse_args()

    before_path = Path(args.before)
    after_path = Path(args.after)
    if not before_path.is_file():
        print(f"[detect_delta] BEFORE not found: {before_path}", file=sys.stderr)
        sys.exit(1)
    if not after_path.is_file():
        print(f"[detect_delta] AFTER not found: {after_path}", file=sys.stderr)
        sys.exit(1)

    before_text = before_path.read_text(encoding="utf-8", errors="replace")
    after_text = after_path.read_text(encoding="utf-8", errors="replace")

    # Cheap pre-check: skip the LLM round trip if the artifacts are
    # byte-identical after stripping outer whitespace. No-op writes
    # are common in retry-heavy skill flows.
    if texts_are_trivially_identical(before_text, after_text):
        if not args.quiet:
            print("no change (byte-identical)")
        sys.exit(0)

    before_label = args.before_rel or before_path.name
    after_label = args.after_rel or after_path.name
    prompt = build_prompt(before_text, after_text, before_label, after_label)

    if args.mock_response is not None:
        raw = args.mock_response
    else:
        try:
            raw = call_claude(prompt, args.model, args.timeout_s)
        except (FileNotFoundError, subprocess.TimeoutExpired, RuntimeError) as e:
            print(f"[detect_delta] LLM call failed: {e}", file=sys.stderr)
            sys.exit(1)

    parsed = parse_response(raw)
    if parsed is None:
        print(
            f"[detect_delta] could not parse LLM response: {raw[:300]!r}",
            file=sys.stderr,
        )
        sys.exit(1)

    if not parsed["change_detected"]:
        if not args.quiet:
            print("no change")
        sys.exit(0)

    if not args.sandbox:
        # Detect-only mode (no sandbox). Print the parsed delta to
        # stdout so the caller can pipe / inspect.
        if not args.quiet:
            print(json.dumps(parsed, ensure_ascii=False))
        sys.exit(0)

    sandbox = Path(args.sandbox)
    if not sandbox.is_dir():
        print(f"[detect_delta] sandbox not a directory: {sandbox}", file=sys.stderr)
        sys.exit(1)

    try:
        emit_via_emit_event(sandbox, parsed, args.before_rel, args.after_rel)
    except (FileNotFoundError, subprocess.TimeoutExpired, RuntimeError) as e:
        print(f"[detect_delta] emit failed: {e}", file=sys.stderr)
        sys.exit(1)

    if not args.quiet:
        print("delta emitted")


if __name__ == "__main__":
    main()

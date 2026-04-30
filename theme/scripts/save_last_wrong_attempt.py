#!/usr/bin/env python3
"""save_last_wrong_attempt.py — Python port of lastWrongAttempt.ts.

Persists an annotated last-wrong-attempt to $SANDBOX/last_wrong_attempt.lean
so the agent can re-read its previous (broken) code with inline error markers
at the exact failing lines plus pitfall routing hints in a footer block.

This implements:
  - parseLspDiagnostics (3 input shapes, per lastWrongAttempt.ts:29-91)
  - annotateContent (per-line ERROR markers + HINT tags, per lastWrongAttempt.ts:143-211)
  - saveLastWrongAttempt logic (write file, return one-line summary)

Mirrors czy's lastWrongAttempt.ts (ba49507 + 9ff6536 commits). Called by:
  - process_sorry_result.py --status write_fail / --status edit_fail (T2 narrative)
  - (T1 escalation via hook_post_tool.py, if traces show >20% skipping)

Per spec §3.6 (D-6), applyReplaceSorry is NOT ported here (deferred to Phase 04,
D-7 Option A). replace_fail path is stubbed in process_sorry_result.py.

CLI:
    python3 theme/scripts/save_last_wrong_attempt.py \\
        --sandbox <path>           # sandbox root dir
        --content <path-to-file>   # path to the raw failed .lean content
        --diagnostics <json>       # LSP diagnostics JSON (3 shapes)
        [--sorry-id <id>]          # for milestone payload
        [--fail-type write|edit|replace]  # for milestone payload
        [--content-stdin]          # read content from stdin instead of --content

Exit codes:
  0 — annotated file written; prints one-line summary to stdout
  1 — argument error / write failed
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
MATCH_PITFALL = SCRIPTS_DIR / "match_pitfall.py"

# Keyword-driven fallback categories (mirrors pitfallsSuggestionHint fallback,
# honestyRules.ts:122-140 — used when match_pitfall.py subprocess is unavailable).
_KW_FALLBACKS = [
    (
        re.compile(r"Measure|gaussian|integral|ae_zero|∀ᵐ|condExp|Integrable|measurable", re.IGNORECASE),
        "`docs/pitfalls/measure_theory_patterns.md` (CE / integrability / AE) or "
        "`docs/pitfalls/instance_pollution.md` (multi-MeasurableSpace)",
    ),
    (
        re.compile(
            r"failed to synthesize|typeclass|HSub|HMul|HAdd|inferInstance"
            r"|heartbeats|deterministic timeout",
            re.IGNORECASE,
        ),
        "`docs/pitfalls/typeclass_errors.md` (instance synthesis + perf)",
    ),
    (
        re.compile(
            r"expected\s+(Prop|Type)|elaboration|unexpected token|expected token"
            r"|Unknown identifier|type mismatch",
            re.IGNORECASE,
        ),
        "`docs/pitfalls/lean_syntax_errors.md` (parser / elaboration)",
    ),
    (
        re.compile(
            r"Matrix|mulVec|trace|rank|PosDef|PosSemidef|Tendsto|atTop"
            r"|gaussianReal|variance|IndepFun",
            re.IGNORECASE,
        ),
        "`docs/pitfalls/statistics_domain.md` (distributions / matrix / convergence)",
    ),
]


@dataclass
class ParsedError:
    """1-indexed line + column + compiler message.

    Mirrors ParsedError interface from lastWrongAttempt.ts:17-24.
    """
    line: int
    column: int
    message: str


def parse_lsp_diagnostics(filtered_json: str) -> list[ParsedError]:
    """Parse LSP diagnostics JSON into a flat list of ParsedError (1-indexed).

    Accepts THREE input shapes (mirrors lastWrongAttempt.ts:29-91, ba49507 fix):
      1. Flat array of LSP-raw items (0-indexed):
           [{severity, message, range:{start:{line,character}}}, ...]
      2. Flat array of pre-flattened items (1-indexed, from lean-lsp-mcp server):
           [{severity, message, line, column}, ...]
      3. Wrapped form: {success, items:[...]} or {errors:[...]}, items match (1) or (2).

    Warnings and info are filtered out (only severity="error" items returned).
    Items with line <= 0 are skipped.
    """
    if not filtered_json or filtered_json.strip() in ("", "[]"):
        return []
    try:
        parsed = json.loads(filtered_json)
    except json.JSONDecodeError:
        return []

    # Normalise to flat list.
    if isinstance(parsed, list):
        raw_items = parsed
    elif isinstance(parsed, dict):
        raw_items = (
            parsed.get("items")
            or parsed.get("errors")
            or []
        )
    else:
        return []

    out: list[ParsedError] = []
    for it in raw_items:
        if not isinstance(it, dict):
            continue
        if it.get("severity") != "error":
            continue
        message = str(it.get("message") or "").strip()
        if not message:
            continue

        line_n = 0
        col_n = 0
        if isinstance(it.get("line"), (int, float)) and it["line"] > 0:
            # Shape 2: server already 1-indexed.
            line_n = int(it["line"])
            col_val = it.get("column")
            col_n = int(col_val) if isinstance(col_val, (int, float)) and col_val > 0 else 1
        elif isinstance(it.get("range"), dict):
            # Shape 1: LSP raw 0-indexed.
            start = it["range"].get("start") or {}
            line0 = start.get("line", -1)
            col0 = start.get("character", 0)
            line_n = int(line0) + 1 if isinstance(line0, (int, float)) and line0 >= 0 else 0
            col_n = int(col0) + 1 if isinstance(col0, (int, float)) else 1
        if line_n <= 0:
            continue
        out.append(ParsedError(line=line_n, column=col_n, message=message))
    return out


def _match_pitfall_subprocess(message: str) -> Optional[tuple[str, str, str]]:
    """Call match_pitfall.py as subprocess, return (file, section, hint) or None.

    Falls back to None if the subprocess is unavailable (R6 graceful degradation).
    Returns a 3-tuple matching czy's matchPitfallSuggestion result shape.
    """
    if not MATCH_PITFALL.exists():
        return None
    try:
        result = subprocess.run(
            [sys.executable, str(MATCH_PITFALL), "--error-text", message],
            capture_output=True, text=True, timeout=5,
        )
        if result.returncode == 0 and result.stdout.strip():
            # Output is the full hint string; extract file/section from it.
            # Format: "📚 Similar error pattern → see `<file>` <section>. <hint>"
            line = result.stdout.strip()
            m = re.search(r"`(docs/pitfalls/[^`]+)`\s+(§[A-Z0-9.]+)", line)
            if m:
                return (m.group(1), m.group(2), line)
            # No structured parse possible but we have a hint.
            return ("docs/pitfalls/README.md", "§index", line)
    except Exception:
        pass
    return None


def _keyword_fallback_hint(all_messages: list[str]) -> Optional[str]:
    """Keyword-driven fallback when match_pitfall.py returns no match.

    Mirrors pitfallsSuggestionHint fallback path (honestyRules.ts:122-140).
    Returns a footer hint line or None.
    """
    combined = " ".join(all_messages)
    candidates: list[str] = []
    for pattern, label in _KW_FALLBACKS:
        if pattern.search(combined):
            candidates.append(label)
    if not candidates:
        return None
    return "Likely relevant: " + "; ".join(candidates)


def annotate_content(content: str, errors: list[ParsedError]) -> str:
    """Append inline ERROR markers + HINT tags + a footer block to content.

    Body mirrors annotateContent from lastWrongAttempt.ts:143-211 (9ff6536).
    SDK-bridge addition (spec D-9): a keyword fallback footer renders
    pitfall hints derived from the diagnostic text via match_pitfall.py
    re-invocation when the per-line HINT tags didn't surface a match.
    This footer is NOT in czy and is honestly labeled as an additive
    +1 (per spec D-9).

    - Per-line markers: `  -- [ERROR col N: <msg>]` appended to the errored line.
    - HINT tag: `[HINT: see <file> <section> — <hint slice>]` after the error marker
      when match_pitfall.py returns a match for the first error on that line.
    - Idempotent: lines already containing `[ERROR col ` are not re-annotated.
    - Footer: full verbatim error messages + PITFALL ROUTING HINTS block.
    - Keyword fallback footer when match_pitfall.py unavailable/no match.
    """
    if not errors:
        return content

    lines = content.split("\n")
    # Group errors by line number.
    grouped: dict[int, list[ParsedError]] = {}
    for e in errors:
        if e.line < 1 or e.line > len(lines):
            continue
        grouped.setdefault(e.line, []).append(e)

    # Annotate each errored line.
    for line_num, errs in grouped.items():
        idx = line_num - 1
        cur = lines[idx]
        if "[ERROR col " in cur:
            continue  # idempotent guard
        tag = " ".join(
            f"[ERROR col {e.column}: {e.message.replace(chr(10), ' ').replace(chr(13), ' ')[:200]}]"
            for e in errs
        )
        # HINT tag from first matching error on this line.
        hint_tag = ""
        for e in errs:
            match = _match_pitfall_subprocess(e.message)
            if match:
                _file, _section, _hint = match
                # Slice hint to 140 chars matching czy's hintTag slice.
                short_hint = _hint[:140]
                hint_tag = f" [HINT: see {_file} {_section} — {short_hint}]"
                break
        lines[idx] = f"{cur}  -- {tag}{hint_tag}"

    # Build footer.
    footer_lines: list[str] = [
        "",
        "-- ============================================================",
        "-- COMPILER ERRORS (verbatim — main file has been reverted)",
        "-- ============================================================",
    ]

    # Collect distinct pitfall suggestions across all errors.
    seen_suggestions: set[str] = set()
    suggestions: list[tuple[str, str, str]] = []  # (file, section, hint)
    for e in errors:
        indented = e.message.replace("\n", "\n--   ")
        footer_lines.append(f"-- line {e.line} col {e.column}: {indented}")
        match = _match_pitfall_subprocess(e.message)
        if match:
            _file, _section, _hint = match
            key = f"{_file}#{_section}"
            if key not in seen_suggestions:
                seen_suggestions.add(key)
                suggestions.append((_file, _section, _hint))

    if suggestions:
        footer_lines.append("")
        footer_lines.append("-- ─── PITFALL ROUTING HINTS ───────────────────────────")
        footer_lines.append(
            "-- The errors above match documented patterns. Read the indicated"
        )
        footer_lines.append("-- file/section before retrying — agent should call:")
        footer_lines.append('--   read_file path="<file>"')
        footer_lines.append("-- to load the full context.")
        for _file, _section, _hint in suggestions:
            footer_lines.append(f"-- → {_file} {_section}: {_hint}")
    else:
        # Keyword-driven fallback when no regex rule matched.
        all_messages = [e.message for e in errors]
        kw_hint = _keyword_fallback_hint(all_messages)
        if kw_hint:
            footer_lines.append("")
            footer_lines.append("-- ─── PITFALL ROUTING HINTS (keyword fallback) ────────")
            footer_lines.append(f"-- {kw_hint}")

    return "\n".join(lines) + "\n".join(footer_lines) + "\n"


def save_last_wrong_attempt(
    sandbox: Path,
    content: str,
    errors: list[ParsedError],
    sorry_id: Optional[str] = None,
    fail_type: Optional[str] = None,
) -> str:
    """Write annotated last-wrong-attempt.lean to sandbox root and return summary.

    Mirrors saveLastWrongAttempt from lastWrongAttempt.ts:256-309 (9ff6536).

    Path: $SANDBOX/last_wrong_attempt.lean  (D-10: sandbox root, not module subdir).
    File is overwritten on each subsequent failure (not appended).

    Returns a one-line summary string suitable for embedding in tool-result tail.
    Emits "last-wrong-attempt-saved" milestone via emit_event.py (best-effort).
    """
    annotated = annotate_content(content, errors)
    out_path = sandbox / "last_wrong_attempt.lean"
    try:
        out_path.write_text(annotated, encoding="utf-8")
    except OSError as e:
        return f"(failed attempt could not be saved to {out_path}: {e})"

    # Emit milestone (best-effort).
    if sorry_id:
        _emit_milestone(sandbox, sorry_id, fail_type or "write", len(errors) > 0)

    if not errors:
        return (
            f"Saved your failed attempt to `last_wrong_attempt.lean` "
            f"(no structured errors parsed; read it to see the verbatim code you just wrote)."
        )

    first = errors[0]
    first_msg = first.message.split("\n")[0][:200]

    # Build pitfall tail for summary (mirrors saveLastWrongAttempt's pitfallTail).
    pitfall_tail = ""
    for e in errors:
        match = _match_pitfall_subprocess(e.message)
        if match:
            _file, _section, _hint = match
            pitfall_tail = (
                f" 📚 ROUTING HINT — this error pattern is documented in "
                f"`{_file}` {_section}: {_hint} "
                f'Call `read_file path="{_file}"` for full context.'
            )
            break

    n = len(errors)
    return (
        f"Saved your failed attempt to `last_wrong_attempt.lean` with inline error markers "
        f"({n} error{'s' if n != 1 else ''}; first at line {first.line} col {first.column}: {first_msg}). "
        f"Read this file next turn to see the broken code with errors annotated at the right lines."
        + pitfall_tail
    )


def _emit_milestone(
    sandbox: Path, sorry_id: str, fail_type: str, pitfall_matched: bool
) -> None:
    """Emit last-wrong-attempt-saved milestone (best-effort)."""
    if not EMIT_EVENT.exists():
        return
    try:
        subprocess.run(
            [
                sys.executable, str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", "last-wrong-attempt-saved",
                "--details", json.dumps({
                    "sorry_id": sorry_id,
                    "fail_type": fail_type,
                    "pitfall_matched": pitfall_matched,
                }),
            ],
            check=True,
            timeout=10,
        )
    except Exception as e:
        print(
            f"[save_last_wrong_attempt] emit last-wrong-attempt-saved failed: {e}",
            file=sys.stderr,
        )


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sandbox", required=True,
                    help="Sandbox root dir; file written to $SANDBOX/last_wrong_attempt.lean")
    ap.add_argument("--content", default=None,
                    help="Path to a file containing the failed .lean content")
    ap.add_argument("--content-stdin", action="store_true",
                    help="Read content from stdin instead of --content")
    ap.add_argument("--diagnostics", default="[]",
                    help="LSP diagnostics JSON string (3 shapes accepted)")
    ap.add_argument("--sorry-id", default=None,
                    help="Sorry ID for milestone payload")
    ap.add_argument("--fail-type", choices=["write", "edit", "replace"], default="write",
                    help="Failure type for milestone payload")
    args = ap.parse_args()

    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists() or not sandbox.is_dir():
        print(f"[save_last_wrong_attempt] sandbox missing or not a dir: {sandbox}",
              file=sys.stderr)
        sys.exit(1)

    # Read content.
    if args.content_stdin:
        content = sys.stdin.read()
    elif args.content:
        content_path = Path(args.content)
        if not content_path.exists():
            print(f"[save_last_wrong_attempt] content file not found: {content_path}",
                  file=sys.stderr)
            sys.exit(1)
        content = content_path.read_text(encoding="utf-8")
    else:
        print("[save_last_wrong_attempt] must supply --content or --content-stdin",
              file=sys.stderr)
        sys.exit(1)

    errors = parse_lsp_diagnostics(args.diagnostics)
    summary = save_last_wrong_attempt(
        sandbox=sandbox,
        content=content,
        errors=errors,
        sorry_id=args.sorry_id,
        fail_type=args.fail_type,
    )
    print(summary)


if __name__ == "__main__":
    main()

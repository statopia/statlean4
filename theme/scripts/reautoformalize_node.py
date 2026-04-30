#!/usr/bin/env python3
"""reautoformalize_node.py — H4-reautoformalize prep script (T2 bundling).

Per `docs/H4_REAUTOFORMALIZE_SPEC.md`. Reads assumption_hints[] from the
targeted sorry row in sorry_backlog.yaml, checks whether the Lean file is
locked, and prepares the enriched description for agent-driven skeleton
rewrite (or writes hint context for prompt-augment fallback).

This script is the PREPARATION half of the two-script pipeline:
  1. reautoformalize_node.py (this) — prep; writes ZERO yaml, ZERO Lean
     files; exits before any agent LLM work.
  2. agent narrative (T3) — reads enriched desc, rewrites Lean skeleton.
  3. commit_reautoformalize.py — commits enriched theorem text back to yaml.

Lock detection (D-2): presence of `$SANDBOX/.integrity.json` indicates
the Lean skeleton is locked (written by SDK-bridge `lock_signatures` tool /
`toolRunner.ts` `lockSignatures` which writes INTEGRITY_FILE=".integrity.json").
The sentinel-comment approach does NOT exist anywhere in the SDK-bridge
codebase. When `.integrity.json` is absent → unlocked → skeleton-rewrite
path is safe. When `.integrity.json` is present → locked → fallback to
prompt-augment (write hint context file for prover injection).

Verdicts emitted via `reautoformalized` milestone:
  - `enriching`              — enriched desc written; agent skeleton-rewrite step pending
  - `locked_fallback_prompt` — .integrity.json present; hint context written for prover
  - `no_hints`               — assumption_hints[] empty; no-op (idempotent)
  - `parse_error`            — sub_problem_id missing or validation failure (exit 2)

Layer 1 invariant: this script writes ZERO yaml and ZERO Lean files.
Only temp files are written:
  - `$SANDBOX/_enrich_desc_${id}_${ts}.txt`  — for skeleton-rewrite path
  - `$SANDBOX/_assumption_context_${id}.txt` — for prompt-augment path

Exit codes:
  0 — milestone emitted (any verdict)
  2 — validation error (sub_problem_id missing, backlog unreadable)

CLI:
    python3 theme/scripts/reautoformalize_node.py \\
        --sub-problem-id <id> \\
        --sandbox /path/to/sandbox \\
        [--backlog-path PATH]

TODO H5/H6: when H5/H6 land, extend this script to read assembledContext
from their output files and inject via the prompt-augment path.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

# .integrity.json filename (mirrors toolRunner.ts INTEGRITY_FILE constant)
INTEGRITY_FILE = ".integrity.json"

# Verdicts (D-8: single milestone name, verdict discriminates phase)
VERDICT_ENRICHING = "enriching"
VERDICT_LOCKED_FALLBACK = "locked_fallback_prompt"
VERDICT_NO_HINTS = "no_hints"
VERDICT_PARSE_ERROR = "parse_error"

# Description cap (D-5): enriched theorem text clamped to 4000 chars total.
# Original theorem may be truncated; hints are preserved intact.
ENRICHED_DESC_MAX_CHARS = 4000

# Optional assumption_analysis cap (Q-3 resolution: include when non-empty)
ANALYSIS_EXCERPT_MAX_CHARS = 300


sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import locked_backlog  # noqa: E402


def _check_locked(sandbox: Path) -> bool:
    """Return True if sandbox has .integrity.json (i.e. signatures locked).

    D-2: presence of $SANDBOX/.integrity.json is the lock indicator.
    Written by lock_signatures tool (toolRunner.ts `lockSignatures`).
    Absence → unlocked → skeleton-rewrite path is safe.
    """
    return (sandbox / INTEGRITY_FILE).exists()


def _build_enriched_desc(
    theorem: str,
    assumption_hints: List[str],
    assumption_analysis: str,
) -> str:
    """Build the enriched NL description.

    Structure:
      <original theorem text>

      **Missing hypotheses (from diagnostics):**
      - <hint 1>
      - <hint 2>

      **Analysis:** <analysis text>   (optional — Q-3)

    D-5: total text is clamped at ENRICHED_DESC_MAX_CHARS (4000 chars).
    Hints and analysis are preserved in full when budget allows;
    original theorem is truncated from the end if needed (asymmetric
    truncation — hints are load-bearing). Pathological case: if the
    hints+analysis suffix alone exceeds 4000 chars (unreachable under
    H7's normal output: ≤5 hints × ≤400 chars each ≈ 2000 chars
    suffix max), the suffix itself is truncated to 4000 chars and
    later hints may be dropped.
    """
    hints_block = "\n\n**Missing hypotheses (from diagnostics):**\n" + "\n".join(
        f"- {h}" for h in assumption_hints
    )
    analysis_block = ""
    if assumption_analysis and assumption_analysis.strip():
        truncated_analysis = assumption_analysis[:ANALYSIS_EXCERPT_MAX_CHARS]
        if len(assumption_analysis) > ANALYSIS_EXCERPT_MAX_CHARS:
            truncated_analysis += "…"
        analysis_block = f"\n\n**Analysis:** {truncated_analysis}"

    suffix = hints_block + analysis_block
    budget = ENRICHED_DESC_MAX_CHARS - len(suffix)

    if budget < 0:
        # Hints + analysis alone exceed cap — truncate suffix (unusual;
        # only possible if hints are extremely numerous or long despite
        # H7's 400-char per-hint limit)
        return suffix[:ENRICHED_DESC_MAX_CHARS]

    base = theorem[:budget] if len(theorem) > budget else theorem
    return base + suffix


def _read_hints(
    backlog_path: Path,
    sub_problem_id: str,
) -> Dict[str, Any]:
    """Read assumption_hints + assumption_analysis from backlog under flock.

    Returns dict with keys:
      found (bool), assumption_hints (list), assumption_analysis (str),
      theorem (str), error (str | None).

    Never raises. Missing backlog or missing sub_problem_id returns
    `{found: False, error: <reason>, ...}` so the caller can map the
    failure to a verdict (`backlog_missing` / `sub_problem_missing`)
    rather than handle an exception. Contrast with
    `commit_reautoformalize.py:apply_commit` which DOES raise on a
    missing sub_problem_id (commit-path failure is non-recoverable
    and should fail loudly).
    """
    if not backlog_path.exists():
        return {
            "found": False,
            "assumption_hints": [],
            "assumption_analysis": "",
            "theorem": "",
            "error": f"backlog not found: {backlog_path}",
        }

    with locked_backlog(backlog_path) as data:
        items = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sub_problem_id), None)
        if item is None:
            return {
                "found": False,
                "assumption_hints": [],
                "assumption_analysis": "",
                "theorem": "",
                "error": f"sub_problem_id not in sorry_items: {sub_problem_id}",
            }
        return {
            "found": True,
            "assumption_hints": list(item.get("assumption_hints") or []),
            "assumption_analysis": str(item.get("assumption_analysis") or ""),
            "theorem": str(item.get("theorem") or ""),
            "error": None,
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
            f"[reautoformalize_node] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def run_prep(
    backlog_path: Path,
    sub_problem_id: str,
    sandbox: Path,
) -> Dict[str, Any]:
    """Core prep logic. Returns milestone payload dict.

    Does NOT call emit — caller emits after this returns so tests can
    inspect the payload without subprocess.
    """
    started_ms = int(time.time() * 1000)

    # Step 1: read hints from backlog
    row = _read_hints(backlog_path, sub_problem_id)
    if not row["found"]:
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "hint_count": 0,
            "took_ms": int(time.time() * 1000) - started_ms,
            "error": row["error"],
        }

    hints: List[str] = row["assumption_hints"]
    analysis: str = row["assumption_analysis"]
    theorem: str = row["theorem"]

    # Step 2: gate on non-empty hints (D-4: no_hints is silent no-op)
    if not hints:
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_NO_HINTS,
            "hint_count": 0,
            "took_ms": int(time.time() * 1000) - started_ms,
        }

    # Step 3: check lock state (D-2)
    if _check_locked(sandbox):
        # Locked fallback: write hint context for prover injection
        context_file = sandbox / f"_assumption_context_{sub_problem_id}.txt"
        hint_text = (
            "The following mathematical hypotheses were diagnosed as likely missing "
            "— consider whether to add them as Lean hypotheses or check whether "
            "they can be derived from existing ones:\n\n"
            + "\n".join(f"- {h}" for h in hints)
        )
        if analysis and analysis.strip():
            hint_text += f"\n\nAnalysis: {analysis[:ANALYSIS_EXCERPT_MAX_CHARS]}"
        context_file.write_text(hint_text, encoding="utf-8")
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_LOCKED_FALLBACK,
            "hint_count": len(hints),
            "context_file": str(context_file),
            "took_ms": int(time.time() * 1000) - started_ms,
        }

    # Step 4: build enriched description and write temp file
    # TODO H5/H6: when webProbe / referenceProbe slices land, extend
    # _build_enriched_desc to also consume webprobe_findings[] and
    # referenceprobe_findings[] from the parent's yaml row. czy
    # `controlAgent.ts:547-558` discards all three helper results
    # uniformly — restoring all three is symmetric design-intent
    # restoration. MVP wires only assumption_hints[] (H7 territory).
    enriched = _build_enriched_desc(theorem, hints, analysis)
    ts = int(time.time() * 1000)
    enrich_file = sandbox / f"_enrich_desc_{sub_problem_id}_{ts}.txt"
    enrich_file.write_text(enriched, encoding="utf-8")

    return {
        "sub_problem_id": sub_problem_id,
        "verdict": VERDICT_ENRICHING,
        "hint_count": len(hints),
        "enrich_file": str(enrich_file),
        "enriched_desc_len": len(enriched),
        "took_ms": int(time.time() * 1000) - started_ms,
    }


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--sub-problem-id", required=True)
    p.add_argument("--sandbox", required=True)
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()

    sandbox = Path(args.sandbox).resolve()
    backlog_path = Path(args.backlog_path).resolve()

    try:
        payload = run_prep(
            backlog_path=backlog_path,
            sub_problem_id=args.sub_problem_id,
            sandbox=sandbox,
        )
    except yaml.YAMLError as e:
        print(f"[reautoformalize_node] yaml parse failed: {e}", file=sys.stderr)
        return 2
    except OSError as e:
        print(f"[reautoformalize_node] IO failure: {e}", file=sys.stderr)
        return 2

    _emit(sandbox, "reautoformalized", payload)

    verdict = payload["verdict"]
    print(
        f"[reautoformalize_node] sub={args.sub_problem_id} "
        f"verdict={verdict} "
        f"hints={payload.get('hint_count', 0)}"
    )

    if verdict == VERDICT_PARSE_ERROR:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())

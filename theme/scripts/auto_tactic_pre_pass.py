#!/usr/bin/env python3
"""auto_tactic_pre_pass.py — M5 slice port of czy's 9-tactic pre-pass.

Source-of-truth: docs/M5_AUTO_TACTIC_SPEC.md (post §8 review fixups).

What this does
==============

Before Phase 1 spends decompose / research budget on a sorry, run a
fixed 9-tactic ladder (`rfl`, `trivial`, `decide`, `ring`, `linarith`,
`omega`, `norm_num`, `simp`, `aesop`) at each eligible sorry's body
line. First tactic that closes the goal → write `state=DONE`,
`status=proved`, `done_reason=proved` and emit `sorry-proved`
milestone with `closer="auto_tactic"`. Failures fall through silently
to the existing Phase 1/2 flow.

czy parity is byte-faithful on:

  - Tactic order (`proofLoop.ts:1227`)
  - Complex-file regex (`proofLoop.ts:1218-1219`):
    `\\bMeasureTheory\\b|\\bProbabilityTheory\\b|\\bENNReal\\b|\\bIsProbabilityMeasure\\b|\\bFiniteMeasure\\b|\\bStochasticProcess\\b`
  - First-pass-wins semantic (line 1251)
  - Body-only mutation (Layer 1 invariant; locked theorem signature
    untouched; relies on `_try_tactic`'s revert-on-fail contract)

Deliberate +1 deviation (D-6 in spec): SDK-bridge does NOT have
`lean_multi_attempt` LSP infra; M5 ships the lake-build ladder via
shared `_lean_tactic_attempt._try_tactic`. This is a known degraded
mechanism vs czy's CURRENT shipped behavior (per-tactic ~10s lake
build vs LSP single-roundtrip ~instant). Cost ceilings making the
regression tolerable until LSP slice lands:

  - Complex-file skip (czy parity, mandatory)
  - First-pass-wins (czy parity, mandatory)
  - `--max-sorries N` per-cycle cap (default 20)
  - Per-tactic 60s timeout (inherited from `_try_tactic`)

SDK-bridge +ε vs czy: skip rows whose `coverage_state ∈
{cited_by_library, cited_by_reference}` so M5 doesn't double-spend
with R7 (E11 already ran by the time M5 fires; czy doesn't have R7).

CLI
===

  python3 theme/scripts/auto_tactic_pre_pass.py \\
      --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
      [--statlean-root /home/gavin/statlean-merge]   # default: cwd \\
      [--backlog-path PATH] \\
      [--max-sorries N]   # default 20

Exit codes (CLI-shape):
  0  — pre-pass ran (zero or more sorries closed; failures fall through)
  2  — validation error (sandbox missing, backlog parse error, …)

The script is best-effort on individual sorries: any per-sorry exception
is logged + that sorry skipped; the pre-pass continues.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
PROCESS_SORRY_RESULT = SCRIPTS_DIR / "process_sorry_result.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _lean_tactic_attempt import _try_tactic  # noqa: E402

# ── czy parity constants (D-1 + D-2) ──────────────────────────────────

# czy `proofLoop.ts:1227` — verbatim order, no reorder, no additions.
# Roughly fastest-first: `rfl`/`trivial`/`decide` exit in <100ms on
# success; `aesop` can take seconds. L1.2 test pins this against the
# constant.
QUICK_TACTICS: List[str] = [
    "rfl",
    "trivial",
    "decide",
    "ring",
    "linarith",
    "omega",
    "norm_num",
    "simp",
    "aesop",
]

# czy `proofLoop.ts:1218-1219` — verbatim port. Six keywords;
# case-sensitive; word-boundary-anchored. Defends against the
# lake-build-disaster scenario (czy comment :1213-1216 → "27 tactics
# × ~10s ≈ 4-5 minutes of silent waiting" on measure-theory files).
COMPLEX_MATH_PATTERNS = re.compile(
    r"\bMeasureTheory\b|\bProbabilityTheory\b|\bENNReal\b"
    r"|\bIsProbabilityMeasure\b|\bFiniteMeasure\b|\bStochasticProcess\b"
)

# SDK-bridge +ε (D-2): skip rows where E11 R7 already attempted /
# claimed the sorry. czy doesn't have R7-style citation states so
# the question doesn't arise there. Documented as deliberate +ε.
_R7_OWNED_COVERAGE_STATES = {"cited_by_library", "cited_by_reference"}


def is_complex_file(file_content: str) -> bool:
    """True iff the .lean file imports any complex-math signal that
    would make lake-build-based pre-pass cost-prohibitive."""
    return bool(COMPLEX_MATH_PATTERNS.search(file_content))


# ── Eligibility predicate (spec §6) ───────────────────────────────────


def _is_eligible(item: Dict[str, Any]) -> bool:
    """czy parity (`state=INITIALIZED, no children, simple file`) plus
    SDK-bridge +ε (skip R7-owned coverage_states).

    Note: complex-file skip is checked separately because it requires
    reading the .lean file content, which we do once per file rather
    than once per backlog item.
    """
    if item.get("state") != "INITIALIZED":
        return False
    if item.get("children"):
        return False
    if item.get("coverage_state") in _R7_OWNED_COVERAGE_STATES:
        return False
    return True


# ── Per-sorry attempt ─────────────────────────────────────────────────


def _attempt_sorry(
    file_path: Path,
    sorry_line: int,
    tactics: List[str],
    module_path: Optional[str],
    try_tactic_fn,
) -> Optional[str]:
    """Run the tactic ladder against one sorry. Returns the winning
    tactic name on PASS, None on full FAIL or any per-tactic exception.

    First-pass-wins: stops at the first tactic that returns
    `(True, _)`. czy parity — `proofLoop.ts:1245-1248` picks the
    first item with empty goals; we iterate the ladder serially and
    bail at first PASS.
    """
    for tactic in tactics:
        try:
            passed, _output = try_tactic_fn(
                file_path, sorry_line, tactic, module_path
            )
        except Exception as e:
            # Per-tactic exception → fall through to next tactic.
            # Same fall-through semantic as verify_citation library
            # path (czy `:143-156` "tool exception treated as
            # fall-through"). Logged once, no abort.
            print(
                f"[auto-tactic] line {sorry_line}: tactic {tactic!r} "
                f"raised {e}; trying next",
                file=sys.stderr,
            )
            continue
        if passed:
            return tactic
    return None


# ── Backlog iteration ─────────────────────────────────────────────────


def _module_path_from_id(rel_file: str) -> Optional[str]:
    """Convert backlog `file` (e.g. "Statlean/Foo/Bar.lean") → lake
    target ("Statlean.Foo.Bar"). Returns None if the path doesn't
    match the expected `Statlean/.*\\.lean` shape.
    """
    if not rel_file or not rel_file.endswith(".lean"):
        return None
    stem = rel_file[: -len(".lean")]
    return stem.replace("/", ".")


def _invoke_process_sorry_result(
    sandbox: Path,
    sorry_id: str,
    module: Optional[str],
    lean_file: Optional[Path],
    backlog_path: Optional[Path] = None,
) -> None:
    """Bundle the post-PASS side-effects through process_sorry_result.py
    so the standard backlog write + sorry_list refresh +
    propagate_done cascade + sorry-proved milestone all fire as
    one atomic step. M5 only differs by passing `--closer auto_tactic`.

    Best-effort: a non-zero exit from process_sorry_result is logged
    but does not abort the pre-pass (other sorries may still close).

    `backlog_path` is forwarded so L2 tests / multi-tenant invocations
    that override M5's backlog also override PSR's backlog (M5 §8 code
    review S2.4).
    """
    cmd = [
        "python3", str(PROCESS_SORRY_RESULT),
        "--status", "proved",
        "--sorry-id", sorry_id,
        "--sandbox", str(sandbox),
        "--closer", "auto_tactic",
    ]
    if module:
        cmd += ["--module", module]
    if lean_file is not None:
        cmd += ["--lean-file", str(lean_file)]
    if backlog_path is not None:
        cmd += ["--backlog-path", str(backlog_path)]
    try:
        subprocess.run(cmd, check=True, timeout=120)
    except subprocess.CalledProcessError as e:
        print(
            f"[auto-tactic] process_sorry_result failed for "
            f"{sorry_id}: rc={e.returncode}",
            file=sys.stderr,
        )
    except subprocess.TimeoutExpired:
        print(
            f"[auto-tactic] process_sorry_result timed out for {sorry_id}",
            file=sys.stderr,
        )


def run_pre_pass(
    backlog_path: Path,
    statlean_root: Path,
    sandbox: Path,
    max_sorries: int = 20,
    try_tactic_fn=None,
) -> Dict[str, Any]:
    """Iterate the backlog, run the 9-tactic ladder against each
    eligible sorry, return a summary dict.

    The post-PASS side-effects (backlog write, sorry-proved milestone,
    sorry_list refresh, propagate_done) are routed through
    `process_sorry_result.py --status proved --closer auto_tactic`.
    No direct backlog mutation here — keep all `done_reason=proved`
    writes in one canonical place.

    `try_tactic_fn` is injected for tests (defaults to real
    `_try_tactic`).

    Returns:
        {
          "attempted": int,   # sorries we ran the ladder on
          "closed":    int,   # sorries that PASSed
          "skipped":   int,   # sorries skipped by eligibility / file-complex
          "cap_hit":   bool,  # True iff we stopped at --max-sorries
        }
    """
    fn = try_tactic_fn or _try_tactic

    if not backlog_path.exists():
        return {"attempted": 0, "closed": 0, "skipped": 0, "cap_hit": False}

    try:
        data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as e:
        print(f"[auto-tactic] backlog parse failed: {e}", file=sys.stderr)
        return {"attempted": 0, "closed": 0, "skipped": 0, "cap_hit": False}

    items = data.get("sorry_items") or []

    # File-content cache: many sorries share a file; read each once
    # for the complex-file check.
    file_content_cache: Dict[Path, str] = {}

    attempted = 0
    closed = 0
    skipped = 0
    cap_hit = False

    for item in items:
        if attempted >= max_sorries:
            cap_hit = True
            break

        if not _is_eligible(item):
            skipped += 1
            continue

        rel_file = item.get("file") or ""
        line_n_raw = item.get("line", 0)
        try:
            line_n = int(line_n_raw or 0)
        except (TypeError, ValueError):
            line_n = 0
        if not rel_file or line_n <= 0:
            skipped += 1
            continue

        file_path = (statlean_root / rel_file).resolve()
        if not file_path.is_file():
            # Source file missing — defer to Phase 1/2 reporting.
            skipped += 1
            continue

        # Complex-file check (czy parity — D-2). Cached per file.
        if file_path not in file_content_cache:
            try:
                file_content_cache[file_path] = file_path.read_text(
                    encoding="utf-8"
                )
            except OSError as e:
                print(
                    f"[auto-tactic] cannot read {file_path}: {e}; skipping",
                    file=sys.stderr,
                )
                file_content_cache[file_path] = ""  # cache the failure
                skipped += 1
                continue
        if is_complex_file(file_content_cache[file_path]):
            print(
                f"[AUTO-TACTIC] pre-pass: complex math imports detected "
                f"in {rel_file} — skipping {item.get('id')} to avoid "
                f"slow lake builds",
                file=sys.stderr,
            )
            skipped += 1
            continue

        attempted += 1
        sorry_id = str(item.get("id") or "")
        module = _module_path_from_id(rel_file)

        print(
            f"[AUTO-TACTIC] pre-pass: {sorry_id} (line {line_n}) — "
            f"trying {len(QUICK_TACTICS)}-tactic ladder",
            file=sys.stderr,
        )
        winner = _attempt_sorry(
            file_path, line_n, QUICK_TACTICS, module, fn,
        )
        if winner is not None:
            closed += 1
            print(
                f"[AUTO-TACTIC] ✓ {sorry_id} line {line_n}: closed by "
                f"`{winner}`",
                file=sys.stderr,
            )
            # Bundle all post-PASS side effects through
            # process_sorry_result. The lean source has already been
            # mutated in place by `_try_tactic`; we just commit the
            # state-machine writes + telemetry.
            _invoke_process_sorry_result(
                sandbox=sandbox,
                sorry_id=sorry_id,
                module=module,
                lean_file=file_path,
                backlog_path=backlog_path,
            )
            # Cache invalidation: the file content changed (sorry was
            # replaced), so subsequent eligibility checks for OTHER
            # sorries in the same file should re-read. Drop the entry.
            file_content_cache.pop(file_path, None)
        else:
            print(
                f"[AUTO-TACTIC] pre-pass: {sorry_id} line {line_n} not "
                f"trivially closeable — skipping",
                file=sys.stderr,
            )

    return {
        "attempted": attempted,
        "closed": closed,
        "skipped": skipped,
        "cap_hit": cap_hit,
    }


# ── CLI ───────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="M5 auto_tactic pre-pass — czy 9-tactic ladder "
                    "via lake build (D-6 degraded mechanism)"
    )
    p.add_argument("--sandbox", required=True,
                   help="Sandbox dir (where events.jsonl + sorry_list.json live)")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT),
                   help="Path to sorry_backlog.yaml (default: theme/input/...)")
    p.add_argument("--statlean-root",
                   help="Repo root (parent of Statlean/). "
                        "Defaults to backlog parent's parent")
    p.add_argument("--max-sorries", type=int, default=20,
                   help="Per-cycle cap on sorries the ladder runs against. "
                        "Default 20; lake-build cost-ceiling per spec §8 R1")
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    sandbox = Path(args.sandbox).resolve()
    if not sandbox.exists():
        print(
            f"[auto-tactic] sandbox missing: {sandbox}",
            file=sys.stderr,
        )
        return 2

    backlog_path = Path(args.backlog_path).resolve()
    statlean_root = (
        Path(args.statlean_root).resolve()
        if args.statlean_root
        else backlog_path.parent.parent
    )

    if args.max_sorries < 0:
        print(
            f"[auto-tactic] --max-sorries must be >= 0, got {args.max_sorries}",
            file=sys.stderr,
        )
        return 2

    summary = run_pre_pass(
        backlog_path=backlog_path,
        statlean_root=statlean_root,
        sandbox=sandbox,
        max_sorries=args.max_sorries,
    )

    print(
        f"[auto-tactic] pre-pass: attempted={summary['attempted']} "
        f"closed={summary['closed']} skipped={summary['skipped']} "
        f"cap_hit={summary['cap_hit']}"
    )
    # Telemetry-only batch summary line (best-effort; no failure
    # mode aborts the pre-pass).
    print(json.dumps({"auto_tactic_pre_pass": summary}))
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""assemble_helper_context.py — T2 bundling script for prover injection (PROVER_INJECT slice).

Per `docs/PROVER_INJECT_SPEC.md`. Reads three helper output sources from
sorry_backlog.yaml and sandbox temp files, assembles them into a single
markdown context block, and writes `$SANDBOX/_helper_context_${id}.md`
for the prover agent to include in its Task prompt.

Sources (read-only yaml access):
  1. webprobe_context (str) — H5 `extract_web_probe.py` output
  2. referenceprobe_findings[-1].assembledContext (str) — H6 `extract_reference_probe.py`
     output; only the most-recent entry is read (D-3)
  3. $SANDBOX/_assumption_context_${id}.txt — H4-reauto `reautoformalize_node.py`
     locked_fallback_prompt path; read only when `_enrich_desc_${id}_*.txt` is
     absent (D-2 enriching-path gate)

Output:
  $SANDBOX/_helper_context_${id}.md — single assembled markdown block, or
  empty file if no sources are present.

Layer 1 invariants (CLAUDE.md Rule 3):
  - WRITES ZERO yaml. Only writes $SANDBOX/_helper_context_${id}.md.
  - Does NOT modify any Lean files.
  - locked theorem signature untouched.
  - yaml read is under flock (read-only; no atomic_write_yaml called).

Per-source caps: webprobe ≤ 3000, refprobe ≤ 3000, assumption ≤ 2000.
Aggregate cap: 6000 chars on the assembled block (D-5).

Non-blocking-on-error contract (D-6): all errors are soft. Script NEVER
exits non-zero. On any parse / IO error, writes an empty context file and
emits parse_error milestone. This ensures a script bug never kills the
prover dispatch.

Emits `helper-context-assembled` milestone with:
  verdict ∈ {assembled, empty, parse_error}
  sources: list of contributing source names
  webprobe_len, refprobe_len, assumption_len, output_len, took_ms

Exit codes: 0 always.

CLI:
    python3 theme/scripts/assemble_helper_context.py \\
        --sub-problem-id <id> \\
        --sandbox $SANDBOX \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import fcntl
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

# Per-source caps (D-5)
WEBPROBE_CAP = 3000   # H5 renderer cap (czy `renderWebProbeContext` `:664`)
REFPROBE_CAP = 3000   # H6 buildAssembledContext cap (czy `:540`)
ASSUMPTION_CAP = 2000  # PROVER_INJECT-side read cap (D-5 S2.1 correction)
# Aggregate cap — applied to the fully assembled block (D-5 deliberate +1)
AGGREGATE_CAP = 6000

# Milestone name
MILESTONE_NAME = "helper-context-assembled"

# Verdicts
VERDICT_ASSEMBLED = "assembled"
VERDICT_EMPTY = "empty"
VERDICT_PARSE_ERROR = "parse_error"


# ── Yaml read (read-only under flock) ─────────────────────────────────

def _read_backlog_item(
    backlog_path: Path,
    sub_problem_id: str,
) -> Optional[Dict[str, Any]]:
    """Read the sorry_item dict for sub_problem_id under flock.

    Returns the item dict if found, or None on any error.
    Read-only: does NOT call atomic_write_yaml.
    """
    if not backlog_path.exists():
        return None
    try:
        with open(backlog_path, "rb") as lock_f:
            fcntl.flock(lock_f, fcntl.LOCK_SH)  # shared read lock
            try:
                data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
            finally:
                fcntl.flock(lock_f, fcntl.LOCK_UN)
    except (OSError, yaml.YAMLError):
        return None

    items: List[Dict[str, Any]] = data.get("sorry_items") or []
    return next((it for it in items if it.get("id") == sub_problem_id), None)


# ── Section assemblers ─────────────────────────────────────────────────

def _build_webprobe_section(webprobe_context: str) -> str:
    """Build the webprobe section string (empty string if no content)."""
    text = webprobe_context.strip()
    if not text:
        return ""
    return "### Web Probe (most-recent)\n\n" + text[:WEBPROBE_CAP]


def _build_refprobe_section(referenceprobe_findings: List[Any]) -> str:
    """Build the refprobe section from referenceprobe_findings[-1].assembledContext.

    Per D-3: read only the most-recent entry.
    Returns empty string if list is empty, latest entry absent, or assembledContext
    is empty/trivial (len <= 10).
    """
    if not referenceprobe_findings:
        return ""
    latest = referenceprobe_findings[-1]
    if not isinstance(latest, dict):
        return ""
    assembled = latest.get("assembledContext", "") or ""
    if not isinstance(assembled, str):
        assembled = ""
    assembled = assembled.strip()
    if len(assembled) <= 10:
        return ""
    return "### Reference Probe (most-recent)\n\n" + assembled[:REFPROBE_CAP]


def _build_assumption_section(
    sandbox: Path,
    sub_problem_id: str,
) -> str:
    """Build assumption section from _assumption_context_${id}.txt.

    Per D-2: skip if _enrich_desc_${id}_*.txt exists in sandbox
    (enriching path — hints already baked into skeleton).
    Returns empty string if file absent, empty, or enriching path active.
    """
    # D-2 gate: check for enriching-path sentinel file
    enrich_files = list(sandbox.glob(f"_enrich_desc_{sub_problem_id}_*.txt"))
    if enrich_files:
        # Enriching path is active — hints are baked into the skeleton
        return ""

    ctx_file = sandbox / f"_assumption_context_{sub_problem_id}.txt"
    if not ctx_file.exists():
        return ""
    try:
        stat = ctx_file.stat()
        if stat.st_size == 0:
            return ""
        hint_text = ctx_file.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return ""

    if not hint_text:
        return ""

    hint_text = hint_text[:ASSUMPTION_CAP]
    return (
        "### Diagnosed missing hypotheses\n\n"
        "The following mathematical hypotheses were diagnosed as likely "
        "missing — consider whether to add them as Lean hypotheses or "
        "check whether they can be derived from existing ones:\n\n"
        + hint_text
    )


# ── Milestone emission ─────────────────────────────────────────────────

def _emit(sandbox: Path, details: Dict[str, Any]) -> None:
    """Best-effort milestone emission; logs but doesn't abort (D-6)."""
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", MILESTONE_NAME,
                "--details", json.dumps(details, ensure_ascii=False),
            ],
            check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(
            f"[assemble_helper_context] emit_event {MILESTONE_NAME} failed: {e}",
            file=sys.stderr,
        )


# ── Core assembly ──────────────────────────────────────────────────────

def assemble(
    backlog_path: Path,
    sub_problem_id: str,
    sandbox: Path,
) -> Dict[str, Any]:
    """Assemble helper context from all three sources.

    Returns milestone payload dict. Caller writes output file and emits.

    Non-blocking: returns parse_error payload on any failure, never raises.
    """
    started_ms = int(time.time() * 1000)

    # Step 1: read backlog item (shared flock, read-only)
    item = _read_backlog_item(backlog_path, sub_problem_id)
    if item is None:
        elapsed = int(time.time() * 1000) - started_ms
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "sources": [],
            "webprobe_len": 0,
            "refprobe_len": 0,
            "assumption_len": 0,
            "output_len": 0,
            "took_ms": elapsed,
            "error": f"sub_problem_id not found in backlog or backlog unreadable: {sub_problem_id}",
        }

    # Step 2: webprobe_context
    try:
        webprobe_raw = item.get("webprobe_context", "") or ""
        if not isinstance(webprobe_raw, str):
            webprobe_raw = ""
    except Exception:
        webprobe_raw = ""
    webprobe_section = _build_webprobe_section(webprobe_raw)

    # Step 3: referenceprobe_findings[-1]
    try:
        refprobe_findings = item.get("referenceprobe_findings", []) or []
        if not isinstance(refprobe_findings, list):
            refprobe_findings = []
    except Exception:
        refprobe_findings = []
    refprobe_section = _build_refprobe_section(refprobe_findings)

    # Step 4: assumption context file (H4-reauto locked fallback path)
    try:
        assumption_section = _build_assumption_section(sandbox, sub_problem_id)
    except Exception:
        assumption_section = ""

    # Step 5: collect non-empty sections
    sources: List[str] = []
    section_map = [
        ("webprobe", webprobe_section),
        ("refprobe", refprobe_section),
        ("assumption", assumption_section),
    ]
    active_sections: List[str] = []
    for name, sec in section_map:
        if sec:
            sources.append(name)
            active_sections.append(sec)

    elapsed = int(time.time() * 1000) - started_ms

    if not active_sections:
        return {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_EMPTY,
            "sources": [],
            "webprobe_len": 0,
            "refprobe_len": 0,
            "assumption_len": 0,
            "output_len": 0,
            "took_ms": elapsed,
        }

    # Step 6: assemble with separators + aggregate cap (D-5).
    # The outer wrapper header (### or ##) is added by the prove-deep.md
    # narrative when this file is included in task_reference.md. The
    # script writes ONLY the `### Web Probe / ### Reference Probe /
    # ### Diagnosed missing hypotheses` subsections so the consumer can
    # nest them under whatever outer header it chooses. Per czy parity:
    # czy `proverAgent.ts:611` adds the `## Helper context` header at
    # injection time, not in the helper assembled body. PROVER_INJECT
    # §8 code review S5.1 fixup: previous draft prepended an extra
    # `## Helper coverage context` here which would produce double `##`
    # nesting under the agent's wrapper header.
    assembled_block = "\n\n---\n\n".join(active_sections)

    # Apply 6000-char aggregate cap (D-5 deliberate +1)
    if len(assembled_block) > AGGREGATE_CAP:
        assembled_block = assembled_block[:AGGREGATE_CAP]

    return {
        "sub_problem_id": sub_problem_id,
        "verdict": VERDICT_ASSEMBLED,
        "sources": sources,
        "webprobe_len": len(webprobe_section),
        "refprobe_len": len(refprobe_section),
        "assumption_len": len(assumption_section),
        "output_len": len(assembled_block),
        "took_ms": elapsed,
        "_assembled_block": assembled_block,  # internal: caller writes to file
    }


# ── CLI ────────────────────────────────────────────────────────────────

def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--sub-problem-id",
        required=True,
        help="The sorry_item id to assemble helper context for.",
    )
    p.add_argument(
        "--sandbox",
        required=True,
        help="Path to the job sandbox directory.",
    )
    p.add_argument(
        "--backlog-path",
        default=str(BACKLOG_DEFAULT),
        help="Path to sorry_backlog.yaml (default: theme/input/sorry_backlog.yaml).",
    )
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()
    sub_problem_id = args.sub_problem_id

    output_file = sandbox / f"_helper_context_{sub_problem_id}.md"

    # Non-blocking wrapper: catch all exceptions, degrade to empty output + parse_error
    try:
        payload = assemble(backlog_path, sub_problem_id, sandbox)
    except Exception as e:
        print(
            f"[assemble_helper_context] unexpected error: {e}",
            file=sys.stderr,
        )
        # Write empty file and emit parse_error (D-6)
        try:
            output_file.write_text("", encoding="utf-8")
        except OSError as write_e:
            print(
                f"[assemble_helper_context] could not write empty output: {write_e}",
                file=sys.stderr,
            )
        _emit(sandbox, {
            "sub_problem_id": sub_problem_id,
            "verdict": VERDICT_PARSE_ERROR,
            "sources": [],
            "webprobe_len": 0,
            "refprobe_len": 0,
            "assumption_len": 0,
            "output_len": 0,
            "took_ms": 0,
            "error": str(e)[:200],
        })
        return 0  # Always exit 0 (D-6)

    # Write output file
    assembled_block = payload.pop("_assembled_block", "")
    try:
        output_file.write_text(assembled_block, encoding="utf-8")
    except OSError as e:
        print(
            f"[assemble_helper_context] could not write output file: {e}",
            file=sys.stderr,
        )
        # Degrade to empty output (D-6)
        assembled_block = ""
        payload["verdict"] = VERDICT_PARSE_ERROR
        payload["output_len"] = 0
        payload["error"] = str(e)[:200]

    # Emit milestone
    _emit(sandbox, payload)

    verdict = payload.get("verdict", "?")
    sources = payload.get("sources", [])
    output_len = payload.get("output_len", 0)
    print(
        f"[assemble_helper_context] sub={sub_problem_id} "
        f"verdict={verdict} "
        f"sources={sources} "
        f"output_len={output_len}"
    )
    return 0  # Always exit 0 (D-6)


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""extract_references.py — bundle the side-effect chain for a helper-
reference Task sub-agent's output (E4 slice).

Per `docs/E4_REFERENCE_SUBAGENT_SPEC.md`. Replaces the narrative
"agent should: parse JSON, validate, write yaml fields, emit event"
chain with a single named script. Per CLAUDE.md Rule 9 §3 (T-tier):
T2 single-script bundling. Agent invokes once; script enforces all
sub-steps atomically.

Inputs (mirrors czy `assessAllSubProblems` `:419-455`):
  - The helper-reference Task subagent emits a JSON array to stdout.
    Format per czy `helperReferenceSubAgent.ts:64-79` REFERENCE_ASSESS_SYSTEM:
        [
          {
            "subProblemId": "<id from input>",
            "coverage": "cited_by_reference" | "partial_coverage" | "no_coverage",
            "assessment": "<5-part NL>",
            "matching_statement": "<theorem text>" | null
          }
        ]
  - The orchestrator reads the subagent output and pipes it via
    `--subagent-json-file` (file path; we don't take stdin to avoid
    shell-quoting hazards on JSON containing newlines).

Side-effects (atomic under flock):
  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Locates the parent sorry_item by `--parent-id`
  - Validates the JSON: array, per-entry shape, sub_problem_id matching
    against the parent's children (case-insensitive trim-equality;
    czy R2 mitigation)
  - Coalesces unknown coverage values to `no_coverage` (czy `:443-445`)
  - Drops `matching_statement` when coverage != `cited_by_reference`
    (czy `:446-448` short-circuit)
  - Writes the parent's `references[]`, `coverage_state` (aggregate),
    and `coverage_citation` (only when ANY entry is cited)
  - Emits one `reference-extracted` milestone with payload schema
    matching spec §4

Rule 3 Layer 1 invariant (per `record_retreat.py:11-13` precedent):
mutates ONLY `references`, `coverage_state`, `coverage_citation` on
the targeted sorry row. Locked theorem signature / file / line /
theorem / parent_id / children / state / history_log untouched.

Exit codes:
  0  — extraction applied successfully
  2  — validation error (parent not found, malformed JSON, empty body, …)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/extract_references.py \\
        --parent-id <node id> \\
        --subagent-json-file /path/to/subagent-output.json \\
        --pdf-proof-body-len <int> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]

`--pdf-proof-body-len` is recorded in the milestone payload as
operational telemetry (lets us correlate skip-rate with body length
when we later build the audit script per E4 spec §6 T1 escalation).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402
from _reference_types import (  # noqa: E402
    ReferenceEntry,
    aggregate_coverage_state,
    coalesce_coverage,
    make_coverage_citation,
)
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# ── JSON unwrap (czy `:419-431`) ──────────────────────────────────────


_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def unwrap_fenced_json(s: str) -> str:
    """LLMs often wrap JSON output in markdown fences. czy strips with
    `/```(?:json)?\\s*\\n?([\\s\\S]*?)\\n?```/`. We mirror it byte-for-
    byte. If no fence present, return input unchanged.
    """
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── Validation ─────────────────────────────────────────────────────────


def _normalize_id(s: Any) -> str:
    """Case-insensitive trim — czy R2 mitigation per spec §8 R2.
    LLMs sometimes change id casing or pad with whitespace; we want
    matching to be tolerant."""
    return str(s).strip().lower() if s is not None else ""


def parse_subagent_output(
    raw_text: str,
    expected_sub_problem_ids: List[str],
) -> List[ReferenceEntry]:
    """Parse helper-reference subagent JSON output. Mirrors czy
    `assessAllSubProblems:419-455` defensive contract:

      - Strip markdown fence
      - JSON.parse → expect array
      - For each EXPECTED sub_problem_id, find a matching entry
        (case-insensitive trim); if none → default `no_coverage` with
        assessment "LLM did not return coverage for this sub-problem"
      - Coalesce coverage to one of three values
      - Drop matching_statement when coverage != cited_by_reference

    Raises ValueError on malformed JSON or non-array root.
    """
    unwrapped = unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        raise ValueError("subagent output is empty after unwrap")
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        raise ValueError(f"subagent output is not valid JSON: {e}") from e
    if not isinstance(parsed, list):
        raise ValueError(
            f"subagent output root must be array, got {type(parsed).__name__}"
        )

    by_norm_id: Dict[str, Dict[str, Any]] = {}
    for entry in parsed:
        if not isinstance(entry, dict):
            continue
        eid = _normalize_id(entry.get("subProblemId"))
        if eid:
            by_norm_id[eid] = entry

    out: List[ReferenceEntry] = []
    for sp_id in expected_sub_problem_ids:
        norm = _normalize_id(sp_id)
        match = by_norm_id.get(norm)
        if match is None:
            # Subagent omitted this sub-problem — czy `:435-441` falls
            # back to `no_coverage`. Be honest about why in assessment.
            out.append(
                ReferenceEntry(
                    sub_problem_id=sp_id,
                    coverage="no_coverage",
                    assessment="LLM did not return coverage for this sub-problem",
                    matching_statement=None,
                    replacement_statement=None,
                )
            )
            continue
        coverage = coalesce_coverage(match.get("coverage"))
        # czy `:446-448`: matching_statement is meaningful ONLY when
        # cited_by_reference. Drop otherwise.
        ms = match.get("matching_statement")
        if coverage != "cited_by_reference" or not (
            isinstance(ms, str) and ms.strip()
        ):
            ms = None
        # replacement_statement is set when cited_by_reference per
        # czy convention — czy itself derives it from matching_statement
        # at the InformalAgent boundary. We mirror by using the same
        # text; downstream slice 03 may rewrite it as needed.
        rs = ms if coverage == "cited_by_reference" else None
        out.append(
            ReferenceEntry(
                sub_problem_id=sp_id,  # use the canonical id, not the LLM's casing
                coverage=coverage,
                assessment=str(match.get("assessment") or ""),
                matching_statement=ms,
                replacement_statement=rs,
            )
        )
    return out


# ── Core ──────────────────────────────────────────────────────────────


def apply_extraction(
    backlog_path: Path,
    parent_id: str,
    subagent_text: str,
) -> Tuple[List[ReferenceEntry], str, str | None]:
    """Apply extraction under flock + atomic write. Returns the
    (entries, aggregate_coverage_state, coverage_citation_or_None).

    Raises ValueError on validation failure.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        children: List[str] = list(parent.get("children") or [])
        if not children:
            raise ValueError(
                f"parent {parent_id} has no children — nothing to assess"
            )

        entries = parse_subagent_output(subagent_text, children)
        coverage_state = aggregate_coverage_state(entries)

        # Pick the citation: first cited_by_reference entry's matching
        # statement is the canonical citation for the parent. Multiple
        # cited entries → take the first deterministically (entries are
        # in expected_sub_problem_ids order, which matches parent.children).
        citation: str | None = None
        for e in entries:
            if e.coverage == "cited_by_reference" and e.matching_statement:
                citation = make_coverage_citation(e.matching_statement)
                break

        # Mutate ONLY the three allow-listed fields. Rule 3 Layer 1:
        # signature / file / line / theorem / state / parent_id /
        # children / history_log are NOT touched. The dep-rebuild logic
        # in sync_sorry_backlog handles the unlocks chain.
        for it in items:
            if it.get("id") == parent_id:
                it["references"] = [e.to_yaml() for e in entries]
                it["coverage_state"] = coverage_state
                if citation is not None:
                    it["coverage_citation"] = citation
                else:
                    # Slice 03 may want to overwrite when this becomes
                    # `cited_by_reference` later; clear stale citation
                    # if a previous extraction had one but THIS round
                    # didn't (the parent's children may have changed).
                    it.pop("coverage_citation", None)
                break

        atomic_write_yaml(backlog_path, data)
        return entries, coverage_state, citation


# ── CLI ───────────────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort
    (matches record_retreat pattern)."""
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
            f"[extract_references] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _truncate(s: str | None, n: int = 200) -> str | None:
    if s is None:
        return None
    return s if len(s) <= n else s[: n - 1] + "…"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--subagent-json-file",
        required=True,
        help="path to a file containing the helper-reference subagent's JSON output",
    )
    p.add_argument(
        "--pdf-proof-body-len",
        type=int,
        default=0,
        help="length of the pdfProofBody fed to the subagent (telemetry only)",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    args = _parse_args()

    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[extract_references] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[extract_references] read failed: {e}", file=sys.stderr)
        return 4

    if args.pdf_proof_body_len < 10:
        # czy short-circuit `:176-185` — refuse to call when input is
        # too small to be meaningful. We extend the guard one layer
        # deeper: even if the orchestrator dispatched the subagent
        # anyway, refuse to write a meaningful coverage_state for a
        # zero-context call.
        print(
            "[extract_references] pdf_proof_body_len < 10; refusing to write coverage_state",
            file=sys.stderr,
        )
        return 2

    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        entries, coverage_state, citation = apply_extraction(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            subagent_text=subagent_text,
        )
    except ValueError as e:
        print(f"[extract_references] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[extract_references] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[extract_references] IO failure: {e}", file=sys.stderr)
        return 4

    covered = sum(1 for e in entries if e.coverage == "cited_by_reference")
    partial = sum(1 for e in entries if e.coverage == "partial_coverage")
    no_cov = sum(1 for e in entries if e.coverage == "no_coverage")
    # Spec §4 invariant — count partition is total
    assert covered + partial + no_cov == len(entries), (
        f"coverage count mismatch: {covered}+{partial}+{no_cov} != {len(entries)}"
    )

    payload = {
        "parent_id": args.parent_id,
        "sub_problem_count": len(entries),
        "covered_count": covered,
        "partial_count": partial,
        "no_coverage_count": no_cov,
        "coverage_state": coverage_state,
        "pdf_proof_body_len": args.pdf_proof_body_len,
        "references": [
            {
                "sub_problem_id": e.sub_problem_id,
                "coverage_state": e.coverage,
                "matching_statement": _truncate(e.matching_statement, 200),
            }
            for e in entries
        ],
    }
    if citation is not None:
        payload["coverage_citation"] = _truncate(citation, 200)

    _emit(sandbox, "reference-extracted", payload)

    print(
        f"reference extracted: parent={args.parent_id} "
        f"coverage_state={coverage_state} "
        f"covered={covered}/{len(entries)} "
        f"partial={partial} no_coverage={no_cov}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

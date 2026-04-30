#!/usr/bin/env python3
"""extract_library_coverage.py — T2 bundling script for the H3
helper-library-coverage slice.

Per `docs/H3_LIBRARY_COVERAGE_SPEC.md` §3.3. Parses the SKILL's stdout
JSON, validates the `library_hit` struct, and writes `coverage_state +
library_hit` to `sorry_backlog.yaml` under flock. Single named script —
all sub-steps atomic (T2 per CLAUDE.md Rule 9 §3).

Inputs:
  - `--parent-id <id>` — id of the parent sorry_item whose children are
    being updated
  - `--subagent-json-file <path>` — path to file containing the SKILL's
    stdout JSON array
  - `--sandbox <path>` — sandbox directory for milestone emission

Side-effects (atomic under flock):
  1. Lock backlog (flock) + read sorry_backlog.yaml; migrate v1 → v2
  2. Find parent sorry by id; validate it exists (failure → exit 2)
  3. Parse --subagent-json-file: must be a JSON array (failure → exit 2)
  4. For each result entry in the array:
     a. Find child sorry_item in backlog matching sub_problem_id
        If not found → skip entry with a warning log; continue
     b. If entry.coverage == "cited_by_library":
        - Validate matched_name is non-empty
        - Set child.coverage_state = "cited_by_library"
        - Set child.library_hit = {name, source, location?, kind?}
        - Idempotence: same name → no-op; different name → overwrite with log
     c. If entry.coverage == "needs_proof":
        - Do NOT touch child.coverage_state (preserve existing value;
          H3 never downgrades a "cited_by_reference" set by E4)
        - Do NOT write library_hit
  5. Aggregate counts: covered=N, needs_proof=M, skipped=K
  6. Write updated backlog atomically (atomic_write_yaml)
  7. Emit single library-coverage-extracted milestone
  8. Exit 0

Layer 1 invariant: mutates ONLY `coverage_state` (to "cited_by_library")
and `library_hit` on child sorry_items. Never touches `state`,
`done_reason`, `file`, `line`, locked theorem signature fields, or
parent sorry fields. Test L1.8 enforces this.

Exit codes:
  0  — extraction applied successfully
  2  — validation error (parent not found, malformed JSON, missing field)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
    python3 theme/scripts/extract_library_coverage.py \\
        --parent-id <id> \\
        --subagent-json-file /path/to/_library_coverage_<id>.json \\
        --sandbox /path/to/sandbox \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402
from _library_types import LibraryCoverageResult, MatchedLemma  # noqa: E402
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402


# ── JSON fence unwrap (same pattern as extract_references.py) ─────────

_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def unwrap_fenced_json(s: str) -> str:
    """Strip markdown fences if present. LLMs sometimes wrap JSON output
    in ```json ... ``` fences even when instructed not to."""
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


# ── Parse SKILL output ─────────────────────────────────────────────────


def parse_skill_output(
    raw_text: str,
    known_child_ids: List[str],
) -> List[LibraryCoverageResult]:
    """Parse the H3 SKILL stdout JSON array.

    Returns a list of LibraryCoverageResult. Entries whose sub_problem_id
    is not in known_child_ids are preserved in the parse result — the
    caller skips them and counts as `skipped`.

    Raises ValueError on:
      - empty after fence-strip
      - non-JSON
      - non-array root

    Does NOT raise on individual malformed entries — those are silently
    dropped (same defensive pattern as extract_references).
    """
    unwrapped = unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        raise ValueError("SKILL output is empty after fence-strip")
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        raise ValueError(f"SKILL output is not valid JSON: {e}") from e
    if not isinstance(parsed, list):
        raise ValueError(
            f"SKILL output root must be array, got {type(parsed).__name__}"
        )

    results: List[LibraryCoverageResult] = []
    for entry in parsed:
        if not isinstance(entry, dict):
            continue
        sub_id = entry.get("sub_problem_id")
        if not sub_id or not isinstance(sub_id, str):
            continue
        try:
            result = LibraryCoverageResult.from_skill_json(entry)
            results.append(result)
        except (KeyError, TypeError, ValueError):
            # Malformed entry — skip silently
            continue
    return results


# ── Core: apply extraction to backlog ─────────────────────────────────


def apply_extraction(
    backlog_path: Path,
    parent_id: str,
    subagent_text: str,
    start_ms: Optional[int] = None,
) -> Tuple[int, int, int, str]:
    """Apply library coverage extraction under flock + atomic write.

    Returns (covered_count, needs_proof_count, skipped_count, verdict).

    `verdict` values per spec §4.2:
      - "all_covered"  — every entry is cited_by_library
      - "partial"      — at least one but not all cited_by_library
      - "none_covered" — all needs_proof
      - "parse_error"  — only if caller catches; shouldn't reach here

    Raises ValueError on validation failure (parent not found, parse fail).
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []

        # Step 2: find parent
        parent = next((it for it in items if it.get("id") == parent_id), None)
        if parent is None:
            raise ValueError(f"parent_id not in sorry_items: {parent_id}")

        children: List[str] = list(parent.get("children") or [])
        # We allow running on a parent with no children — just emit none_covered.

        # Step 3: parse SKILL output
        results = parse_skill_output(subagent_text, children)

        # Build lookup maps
        child_set = set(children)
        items_by_id: Dict[str, Dict[str, Any]] = {
            it.get("id"): it for it in items if it.get("id")
        }

        covered_count = 0
        needs_proof_count = 0
        skipped_count = 0

        # Step 4: apply results
        for result in results:
            child_id = result.sub_problem_id

            # 4a: if not in children list, skip
            if child_id not in child_set:
                print(
                    f"[extract_library_coverage] skip: sub_problem_id '{child_id}'"
                    f" not a child of parent '{parent_id}'",
                    file=sys.stderr,
                )
                skipped_count += 1
                continue

            child_item = items_by_id.get(child_id)
            if child_item is None:
                print(
                    f"[extract_library_coverage] skip: child '{child_id}'"
                    f" not found in sorry_items",
                    file=sys.stderr,
                )
                skipped_count += 1
                continue

            if result.coverage == "cited_by_library":
                # 4b: write coverage_state + library_hit
                if not result.matched_lemma or not result.matched_lemma.name:
                    print(
                        f"[extract_library_coverage] skip: cited_by_library entry"
                        f" for '{child_id}' has empty matched_name",
                        file=sys.stderr,
                    )
                    skipped_count += 1
                    continue

                existing_state = child_item.get("coverage_state", "needs_proof")
                existing_hit = child_item.get("library_hit")
                new_name = result.matched_lemma.name

                # Spec §5 rule 2: H3 NEVER overwrites cited_by_reference
                # (E4 territory). Idempotent re-runs where E4 has already
                # promoted a child to cited_by_reference must preserve
                # E4's classification — H3 fires BEFORE R6 in normal
                # flow, so this case only appears under re-runs or
                # cross-cycle resumption, but the guard is still
                # required. H3 §8 code review S3.1 fixup.
                if existing_state == "cited_by_reference":
                    skipped_count += 1
                    continue

                # Idempotence guard
                if (
                    existing_state == "cited_by_library"
                    and existing_hit is not None
                    and existing_hit.get("name") == new_name
                ):
                    # Same name — no-op
                    covered_count += 1
                    continue

                if existing_state == "cited_by_library" and existing_hit is not None:
                    old_name = existing_hit.get("name", "?")
                    print(
                        f"[extract_library_coverage] overwrite: '{child_id}' "
                        f"already cited_by_library with '{old_name}'; "
                        f"overwriting with '{new_name}'",
                        file=sys.stderr,
                    )

                # Layer 1 invariant: only touch coverage_state + library_hit
                child_item["coverage_state"] = "cited_by_library"
                child_item["library_hit"] = result.matched_lemma.to_yaml()
                covered_count += 1

            elif result.coverage == "needs_proof":
                # 4c: do NOT touch coverage_state (preserve cited_by_reference)
                # Do NOT write library_hit
                needs_proof_count += 1

            else:
                # Unknown coverage value — treat as needs_proof fallthrough
                needs_proof_count += 1

        # Determine verdict
        total_entries = covered_count + needs_proof_count
        # (skipped_count excluded from verdict computation per spec §4.2 invariant note)
        if total_entries == 0:
            verdict = "none_covered"
        elif covered_count == total_entries:
            verdict = "all_covered"
        elif covered_count == 0:
            verdict = "none_covered"
        else:
            verdict = "partial"

        # Step 6: atomic write
        atomic_write_yaml(backlog_path, data)

    return covered_count, needs_proof_count, skipped_count, verdict


# ── Milestone emission ─────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
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
            f"[extract_library_coverage] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


# ── CLI ───────────────────────────────────────────────────────────────


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--parent-id", required=True)
    p.add_argument(
        "--subagent-json-file",
        required=True,
        help="path to file containing H3 SKILL stdout JSON array",
    )
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))
    return p.parse_args()


def main() -> int:
    import time
    start_ms = int(time.time() * 1000)

    args = _parse_args()

    json_path = Path(args.subagent_json_file).resolve()
    if not json_path.is_file():
        print(
            f"[extract_library_coverage] subagent json file not found: {json_path}",
            file=sys.stderr,
        )
        return 2

    try:
        subagent_text = json_path.read_text(encoding="utf-8")
    except OSError as e:
        print(f"[extract_library_coverage] read failed: {e}", file=sys.stderr)
        return 4

    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        covered, needs_proof, skipped, verdict = apply_extraction(
            backlog_path=backlog_path,
            parent_id=args.parent_id,
            subagent_text=subagent_text,
            start_ms=start_ms,
        )
    except ValueError as e:
        err_str = str(e)
        print(f"[extract_library_coverage] validation: {err_str}", file=sys.stderr)
        # Emit parse_error milestone so absence is detectable
        took_ms = int(1000 * 0) + (int(__import__("time").time() * 1000) - start_ms)
        _emit(sandbox, "library-coverage-extracted", {
            "parent_id": args.parent_id,
            "sub_problems_checked": 0,
            "cited_by_library_count": 0,
            "needs_proof_count": 0,
            "skipped_count": 0,
            "library_hits": [],
            "verdict": "parse_error",
            "took_ms": took_ms,
        })
        return 2
    except yaml.YAMLError as e:
        print(
            f"[extract_library_coverage] yaml parse failed: {e}", file=sys.stderr
        )
        return 3
    except OSError as e:
        print(f"[extract_library_coverage] IO failure: {e}", file=sys.stderr)
        return 4

    took_ms = int(__import__("time").time() * 1000) - start_ms
    sub_problems_checked = covered + needs_proof + skipped

    # Re-read to collect library_hits for payload
    # (we don't keep them in memory above — re-parse the JSON for telemetry)
    library_hits_payload: list = []
    try:
        raw2 = json_path.read_text(encoding="utf-8")
        unwrapped2 = unwrap_fenced_json(raw2.strip())
        if unwrapped2.strip():
            parsed2 = json.loads(unwrapped2)
            if isinstance(parsed2, list):
                for entry in parsed2:
                    if (
                        isinstance(entry, dict)
                        and entry.get("coverage") == "cited_by_library"
                        and entry.get("matched_name")
                    ):
                        library_hits_payload.append({
                            "sub_problem_id": str(entry.get("sub_problem_id", "")),
                            "name": str(entry.get("matched_name", "")),
                            "source": str(entry.get("matched_source") or "mathlib"),
                            "reasoning": str(entry.get("reasoning") or ""),
                        })
    except (json.JSONDecodeError, OSError):
        pass  # Best-effort telemetry; don't fail on payload build error

    payload = {
        "parent_id": args.parent_id,
        "sub_problems_checked": sub_problems_checked,
        "cited_by_library_count": covered,
        "needs_proof_count": needs_proof,
        "skipped_count": skipped,
        "library_hits": library_hits_payload,
        "verdict": verdict,
        "took_ms": took_ms,
    }
    _emit(sandbox, "library-coverage-extracted", payload)

    print(
        f"library-coverage-extracted: parent={args.parent_id} "
        f"verdict={verdict} "
        f"covered={covered} needs_proof={needs_proof} skipped={skipped}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

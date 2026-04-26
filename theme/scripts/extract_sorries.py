#!/usr/bin/env python3
"""extract_sorries.py — scan Lean files for `sorry` occurrences and emit
a structured sorry_list.json.

Used by /pipeline (Step 5.5 / 6) so the web UI has a canonical sorry
list instead of the browser doing its own regex scan
(src/lib/sorryParse.ts). Roadmap item A3 in
website/docs/OPTIMIZATION_ROADMAP.md.

Invocation:

    python3 theme/scripts/extract_sorries.py \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        --output  /home/gavin/statlean/Statlean/Web/$JOB_ID/sorry_list.json

    # Single file:
    python3 theme/scripts/extract_sorries.py \\
        --lean-file path/to/Foo.lean \\
        --job-id JOB \\
        --output path/to/sorry_list.json

Design:
  - Heuristic, not a real Lean parser. Mirrors the TS parseSorriesFromLean
    to the letter so swapping consumer paths doesn't change behavior.
  - Strips `-- ...` single-line comments and `/- ... -/` block comments
    before looking for `\\bsorry\\b`.
  - Emits one entry per declaration that contains sorry (not one per
    sorry site).
  - Paths in the JSON are relative to the sandbox root (or to --lean-file
    when that single-file mode is used).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable


DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(?:theorem|lemma|def|abbrev)\s+(\S+)"
)
SORRY_RE = re.compile(r"\bsorry\b")


@dataclass
class SorryTarget:
    id: str
    jobId: str
    theorem: str
    file: str
    startLine: int
    endLine: int
    context: str = ""
    dependencies: list[str] = field(default_factory=list)


def _strip_comments(lines: list[str]) -> Iterable[str]:
    """Yield (line_index, comment-free line). Keeps 1:1 correspondence
    with input line numbers so downstream code can reference them."""
    in_block = False
    for i, raw in enumerate(lines):
        line = raw
        if in_block:
            close = line.find("-/")
            if close == -1:
                yield i, ""
                continue
            line = line[close + 2:]
            in_block = False
        # Strip matched `/- ... -/` on this line, possibly multiple.
        while True:
            open_idx = line.find("/-")
            if open_idx == -1:
                break
            close = line.find("-/", open_idx + 2)
            if close == -1:
                in_block = True
                line = line[:open_idx]
                break
            line = line[:open_idx] + line[close + 2:]
        # Strip `--` single-line comments.
        comment = line.find("--")
        if comment != -1:
            line = line[:comment]
        yield i, line


def extract_sorries_from_content(
    content: str,
    job_id: str,
    file_path: str,
) -> list[SorryTarget]:
    """Pure function form. Extracted so tests don't need disk I/O."""
    lines = content.splitlines()
    out: list[SorryTarget] = []
    current_name = ""
    current_start = 0
    emitted: set[str] = set()

    for i, clean in _strip_comments(lines):
        decl = DECL_RE.match(clean)
        if decl:
            current_name = decl.group(1)
            current_start = i + 1
            # do NOT continue — the decl line may be `theorem foo := sorry`
        if current_name and SORRY_RE.search(clean):
            if current_name not in emitted:
                emitted.add(current_name)
                out.append(SorryTarget(
                    id=f"{job_id}.{current_name}.L{i + 1}",
                    jobId=job_id,
                    theorem=current_name,
                    file=file_path,
                    startLine=current_start,
                    endLine=i + 1,
                ))
    return out


def _scan_sandbox(sandbox: Path, job_id: str) -> list[SorryTarget]:
    out: list[SorryTarget] = []
    for lean in sorted(sandbox.rglob("*.lean")):
        try:
            text = lean.read_text(encoding="utf-8")
        except OSError as e:
            print(
                f"[extract_sorries] cannot read {lean}: {e}",
                file=sys.stderr,
            )
            continue
        rel = str(lean.relative_to(sandbox)).replace("\\", "/")
        out.extend(extract_sorries_from_content(text, job_id, rel))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument(
        "--sandbox",
        help="Scan every .lean file under this directory. Job id is "
        "derived from the directory basename unless --job-id is given.",
    )
    g.add_argument(
        "--lean-file",
        help="Single .lean file mode. Requires --job-id.",
    )
    ap.add_argument("--job-id", help="Override job id (string).")
    ap.add_argument(
        "--output",
        required=True,
        help="Write JSON to this path. Use '-' for stdout.",
    )

    args = ap.parse_args()

    if args.sandbox:
        sandbox = Path(args.sandbox).resolve()
        if not sandbox.is_dir():
            print(f"[extract_sorries] sandbox not a directory: {sandbox}", file=sys.stderr)
            sys.exit(2)
        job_id = args.job_id or sandbox.name
        targets = _scan_sandbox(sandbox, job_id)
    else:
        lean = Path(args.lean_file).resolve()
        if not lean.is_file():
            print(f"[extract_sorries] not a file: {lean}", file=sys.stderr)
            sys.exit(2)
        if not args.job_id:
            print(
                "[extract_sorries] --lean-file mode requires --job-id",
                file=sys.stderr,
            )
            sys.exit(2)
        targets = extract_sorries_from_content(
            lean.read_text(encoding="utf-8"),
            args.job_id,
            lean.name,
        )

    payload = [asdict(t) for t in targets]
    text = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    if args.output == "-":
        sys.stdout.write(text)
    else:
        Path(args.output).write_text(text, encoding="utf-8")
        print(
            f"[extract_sorries] wrote {len(payload)} sorry target(s) to {args.output}",
            file=sys.stderr,
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env bash
set -euo pipefail

PDF=${1:?usage: pdf_extract.sh <pdf_file> <output_dir> [backend] [extra_args...]}
OUTPUT_DIR=${2:?usage: pdf_extract.sh <pdf_file> <output_dir> [backend] [extra_args...]}
BACKEND=${3:-pymupdf}
shift 3 2>/dev/null || shift $# 2>/dev/null
EXTRA_ARGS=("$@")

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
OUTPUT_DIR=$(python3 -c 'import os,sys; print(os.path.abspath(sys.argv[1]))' "$OUTPUT_DIR")

# Resolve PDF input:
# 1) exact file path (absolute or relative)
# 2) fuzzy keyword match against *.pdf under common roots (input/raw first)
PDF=$(python3 - "$PDF" "$OUTPUT_DIR" "$SCRIPT_DIR" <<'PY'
from __future__ import annotations
import os
import sys
from pathlib import Path


def unique_paths(paths: list[Path]) -> list[Path]:
    seen: set[str] = set()
    out: list[Path] = []
    for p in paths:
        rp = str(p.resolve())
        if rp not in seen:
            seen.add(rp)
            out.append(p.resolve())
    return out


def score_match(path: Path, needle: str) -> tuple[int, int, str]:
    name = path.name.lower()
    stem = path.stem.lower()
    full = str(path).lower()
    # Lower tuple is better.
    if stem == needle or name == needle or name == f"{needle}.pdf":
        return (0, len(name), full)
    if stem.startswith(needle) or name.startswith(needle):
        return (1, len(name), full)
    if needle in stem or needle in name:
        return (2, len(name), full)
    if needle in full:
        return (3, len(name), full)
    return (9, len(name), full)


raw_input = sys.argv[1].strip()
output_dir = Path(sys.argv[2]).resolve()
script_dir = Path(sys.argv[3]).resolve()
theme_dir = script_dir.parent
repo_root = theme_dir.parent

raw_path = Path(raw_input).expanduser()

# 1) exact path resolution
exact_candidates = []
if raw_path.is_absolute():
    exact_candidates.append(raw_path)
else:
    exact_candidates.extend(
        [
            (Path.cwd() / raw_path),
            (repo_root / raw_path),
            (theme_dir / raw_path),
            (output_dir / raw_path),
            (output_dir / "raw" / raw_path),
        ]
    )

for cand in unique_paths(exact_candidates):
    if cand.is_file():
        print(str(cand))
        sys.exit(0)

# 2) fuzzy keyword matching
needle = raw_path.name.lower()
if needle.endswith(".pdf"):
    needle = needle[:-4]

search_roots = unique_paths(
    [
        output_dir / "raw",
        output_dir,
        theme_dir / "input" / "raw",
        repo_root,
    ]
)

all_pdfs: list[Path] = []
for root in search_roots:
    if root.is_dir():
        all_pdfs.extend(root.rglob("*.pdf"))
        all_pdfs.extend(root.rglob("*.PDF"))

all_pdfs = unique_paths(all_pdfs)
if not all_pdfs:
    print("[pdf-extract] ERROR: no PDF files found in searchable roots.", file=sys.stderr)
    print(
        f"[pdf-extract] searched: {', '.join(str(r) for r in search_roots if r.is_dir()) or '(none)'}",
        file=sys.stderr,
    )
    sys.exit(2)

matched = [p for p in all_pdfs if score_match(p, needle)[0] < 9]
matched.sort(key=lambda p: score_match(p, needle))

if len(matched) == 1:
    print(str(matched[0]))
    sys.exit(0)

if len(matched) == 0:
    print(f"[pdf-extract] ERROR: no PDF matched query '{raw_input}'.", file=sys.stderr)
    print("[pdf-extract] available PDFs:", file=sys.stderr)
    for p in sorted(all_pdfs)[:20]:
        print(f"  - {p}", file=sys.stderr)
    sys.exit(2)

print(f"[pdf-extract] ERROR: ambiguous PDF query '{raw_input}'.", file=sys.stderr)
print("[pdf-extract] candidates:", file=sys.stderr)
for p in matched[:20]:
    print(f"  - {p}", file=sys.stderr)
print("[pdf-extract] please pass a more specific path or filename.", file=sys.stderr)
sys.exit(2)
PY
)

python3 "$SCRIPT_DIR/pdf_extract.py" \
  --pdf "$PDF" \
  --output-dir "$OUTPUT_DIR" \
  --backend "$BACKEND" \
  "${EXTRA_ARGS[@]}"

echo "{\"phase\":\"pdf-extract\",\"status\":\"ok\",\"pdf\":\"$PDF\",\"output_dir\":\"$OUTPUT_DIR\",\"backend\":\"$BACKEND\"}"

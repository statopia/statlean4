#!/usr/bin/env python3
"""Extract declaration signatures from .lean files (no proof bodies).

Usage:
  python3 scripts/extract_signatures.py Statlean/Gaussian/Poincare.lean
  python3 scripts/extract_signatures.py --all          # all Statlean/**/*.lean
  python3 scripts/extract_signatures.py --sorry-only   # only files with sorry

Output (stdout): concise index of declarations with line numbers and types.
Designed to be piped into an agent's context instead of reading full files.
"""

import argparse
import re
import sys
from pathlib import Path

DECL_RE = re.compile(
    r'^(\s*)((?:noncomputable\s+)?(?:private\s+)?'
    r'(?:protected\s+)?'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom)'
    r')\s+(\S+)',
    re.MULTILINE
)

SORRY_RE = re.compile(r'\bsorry\b')
SECTION_RE = re.compile(r'^\s*(section|namespace)\s+(.*)', re.MULTILINE)
END_RE = re.compile(r'^\s*(end)\s+(.*)', re.MULTILINE)
IMPORT_RE = re.compile(r'^import\s+(.+)', re.MULTILINE)


def find_code_sorry_lines(lines: list[str]) -> list[int]:
    """Find lines containing `sorry` in actual code (not comments or docstrings).

    Skips:
      - Line comments: `-- ...`
      - Block comments / docstrings: `/- ... -/`, `/-! ... -/`, `/-- ... -/`
    Returns 1-indexed line numbers.
    """
    sorry_lines = []
    in_block_comment = False
    for i, line in enumerate(lines):
        # Track block comment state
        j = 0
        code_part = []
        while j < len(line):
            if in_block_comment:
                # Look for end of block comment
                end_idx = line.find('-/', j)
                if end_idx >= 0:
                    in_block_comment = False
                    j = end_idx + 2
                else:
                    break  # rest of line is in block comment
            else:
                # Check for line comment
                if line[j:j+2] == '--':
                    break  # rest of line is a comment
                # Check for block comment start
                if line[j:j+2] == '/-':
                    in_block_comment = True
                    j += 2
                    continue
                code_part.append(line[j])
                j += 1
        code_str = ''.join(code_part)
        if SORRY_RE.search(code_str):
            sorry_lines.append(i + 1)
    return sorry_lines


def extract_signature_block(lines: list[str], start: int) -> str:
    """Extract the type signature from a declaration start line.
    Collects lines until ':=' or 'where' or ':= by' or next declaration."""
    sig_lines = []
    depth = 0
    for i in range(start, min(start + 30, len(lines))):
        line = lines[i]
        sig_lines.append(line.rstrip())
        # Track parenthesis depth
        depth += line.count('(') + line.count('{') + line.count('[')
        depth -= line.count(')') + line.count('}') + line.count(']')
        # Stop at ':= by', ':= {', ':= fun', bare ':=', 'where'
        stripped = line.strip()
        if depth <= 0:
            if ':= by' in line or ':= fun' in line or ':= {' in line:
                # Truncate at ':='
                last = sig_lines[-1]
                idx = last.find(':=')
                if idx >= 0:
                    sig_lines[-1] = last[:idx].rstrip()
                break
            if stripped.endswith(':=') or stripped == 'where':
                sig_lines[-1] = sig_lines[-1].rstrip().removesuffix(':=').removesuffix('where').rstrip()
                break
            if re.match(r'^\s*\|', stripped) and i > start:
                sig_lines.pop()
                break
    return '\n'.join(sig_lines)


def process_file(path: Path) -> dict:
    """Process a single .lean file and return structured info."""
    text = path.read_text(encoding='utf-8')
    lines = text.split('\n')

    imports = IMPORT_RE.findall(text)
    sorry_lines = find_code_sorry_lines(lines)
    has_sorry = len(sorry_lines) > 0

    # Collect all declaration start lines first
    decl_matches = list(DECL_RE.finditer(text))
    decl_start_lines = []
    for m in decl_matches:
        decl_start_lines.append(text[:m.start()].count('\n') + 1)

    declarations = []
    for idx, m in enumerate(decl_matches):
        line_no = decl_start_lines[idx]
        kind_raw = m.group(2).strip()
        # Normalize kind
        for k in ('theorem', 'lemma', 'def', 'abbrev', 'instance',
                   'structure', 'class', 'inductive', 'axiom'):
            if k in kind_raw:
                kind = k
                break
        else:
            kind = kind_raw
        name = m.group(3)
        sig = extract_signature_block(lines, line_no - 1)
        # Check if this declaration has sorry — only within its own span
        # (from this decl start to next decl start, capped at +60 lines)
        next_line = decl_start_lines[idx + 1] if idx + 1 < len(decl_start_lines) else line_no + 60
        end_line = min(next_line, line_no + 60)
        decl_has_sorry = any(line_no <= sl < end_line for sl in sorry_lines)
        declarations.append({
            'line': line_no,
            'kind': kind,
            'name': name,
            'signature': sig,
            'sorry': decl_has_sorry,
        })

    return {
        'path': str(path),
        'imports': imports,
        'has_sorry': has_sorry,
        'sorry_count': len(sorry_lines),
        'declarations': declarations,
    }


def format_output(info: dict, verbose: bool = False) -> str:
    """Format extracted info as concise text."""
    out = []
    p = info['path']
    sorry_tag = f" [SORRY: {info['sorry_count']}]" if info['has_sorry'] else " [CLEAN]"
    out.append(f"# {p}{sorry_tag}")
    out.append("")

    if verbose and info['imports']:
        out.append("## Imports")
        for imp in info['imports']:
            out.append(f"  import {imp}")
        out.append("")

    out.append("## Declarations")
    for d in info['declarations']:
        sorry_mark = " *** SORRY ***" if d['sorry'] else ""
        out.append(f"### L{d['line']} [{d['kind']}] {d['name']}{sorry_mark}")
        # Indent signature
        for sl in d['signature'].split('\n'):
            out.append(f"  {sl}")
        out.append("")

    return '\n'.join(out)


def main():
    parser = argparse.ArgumentParser(description="Extract Lean declaration signatures")
    parser.add_argument('files', nargs='*', help='.lean files to process')
    parser.add_argument('--all', action='store_true', help='Process all Statlean/**/*.lean')
    parser.add_argument('--sorry-only', action='store_true', help='Only files with sorry')
    parser.add_argument('--verbose', '-v', action='store_true', help='Include imports')
    parser.add_argument('--names-only', action='store_true', help='Just name:line list')
    args = parser.parse_args()

    root = Path(__file__).parent.parent

    if args.all or args.sorry_only:
        files = sorted(root.glob('Statlean/**/*.lean'))
    else:
        files = [Path(f) for f in args.files]

    if not files:
        print("No files specified. Use --all or provide file paths.", file=sys.stderr)
        sys.exit(1)

    for f in files:
        if not f.exists():
            # Try relative to root
            f = root / f
        if not f.exists():
            print(f"WARNING: {f} not found", file=sys.stderr)
            continue

        info = process_file(f)

        if args.sorry_only and not info['has_sorry']:
            continue

        if args.names_only:
            for d in info['declarations']:
                sorry_mark = " [sorry]" if d['sorry'] else ""
                print(f"{info['path']}:{d['line']}  {d['kind']} {d['name']}{sorry_mark}")
        else:
            print(format_output(info, verbose=args.verbose))
            print("---")


if __name__ == '__main__':
    main()

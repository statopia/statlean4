#!/usr/bin/env python3
"""Extract proof pattern candidates from Lean 4 files.

Usage:
  # Scan all zero-sorry files
  python3 scripts/extract_proof_patterns.py --scan-all

  # Extract from a specific theorem
  python3 scripts/extract_proof_patterns.py Statlean/Testing/Basic.lean np_lemma

  # Extract from a specific file
  python3 scripts/extract_proof_patterns.py Statlean/Testing/Basic.lean
"""

import argparse
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent


def get_zero_sorry_files() -> list[Path]:
    """Find .lean files with zero sorry (excluding Verified.lean itself)."""
    lean_files = sorted(PROJECT_ROOT.glob("Statlean/**/*.lean"))
    zero_sorry = []
    for f in lean_files:
        if f.name == "Verified.lean":
            continue
        content = f.read_text()
        # Count sorry that are not in comments
        lines = content.split("\n")
        sorry_count = 0
        for line in lines:
            stripped = line.strip()
            if stripped.startswith("--"):
                continue
            if "sorry" in stripped and not stripped.startswith("/-"):
                # Simple heuristic: count `sorry` as a keyword
                sorry_count += stripped.count("sorry")
        if sorry_count == 0:
            zero_sorry.append(f)
    return zero_sorry


def extract_theorems(filepath: Path) -> list[dict]:
    """Extract theorem/lemma declarations and their proof bodies."""
    content = filepath.read_text()
    lines = content.split("\n")
    theorems = []
    current = None

    for i, line in enumerate(lines):
        # Match theorem/lemma/def declarations
        m = re.match(r"^(theorem|lemma|private\s+(?:theorem|lemma)|def)\s+(\w+)", line)
        if m:
            if current:
                current["end_line"] = i - 1
                current["body"] = "\n".join(lines[current["start_line"]:i])
                theorems.append(current)
            current = {
                "kind": m.group(1),
                "name": m.group(2),
                "start_line": i,
                "file": str(filepath.relative_to(PROJECT_ROOT)),
            }

    if current:
        current["end_line"] = len(lines) - 1
        current["body"] = "\n".join(lines[current["start_line"]:])
        theorems.append(current)

    return theorems


def extract_tactic_ngrams(body: str, n: int = 2) -> list[tuple]:
    """Extract tactic n-grams from a proof body."""
    # Find tactic lines (indented lines after `by`)
    lines = body.split("\n")
    tactics = []
    in_proof = False

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("--") or stripped.startswith("/-"):
            continue
        if ":= by" in line or line.strip() == "by":
            in_proof = True
            continue
        if in_proof and stripped:
            # Extract the main tactic (first word)
            tactic_match = re.match(r"[·\|]?\s*(\w+)", stripped)
            if tactic_match:
                tactics.append(tactic_match.group(1))

    # Generate n-grams
    ngrams = []
    for i in range(len(tactics) - n + 1):
        ngrams.append(tuple(tactics[i:i + n]))

    return ngrams


def extract_api_references(body: str) -> list[str]:
    """Extract Mathlib API references from exact/apply/rw calls."""
    apis = []
    # Match exact, apply, rw patterns
    patterns = [
        r"exact\s+(@?\w[\w.]*)",
        r"apply\s+(@?\w[\w.]*)",
        r"rw\s+\[([^\]]+)\]",
        r"simp\s+only\s+\[([^\]]+)\]",
        r"have\s+\w+\s*:=\s+(@?\w[\w.]*)",
    ]
    for pattern in patterns:
        for match in re.finditer(pattern, body):
            text = match.group(1)
            # Split rw/simp lists
            for item in text.split(","):
                item = item.strip().lstrip("←").strip()
                if item and not item.startswith("fun") and len(item) > 3:
                    apis.append(item)

    return apis


def extract_proof_skeleton(body: str) -> str:
    """Extract top-level tactic skeleton of a proof."""
    lines = body.split("\n")
    skeleton_parts = []
    in_proof = False
    indent_level = None

    for line in lines:
        if ":= by" in line or line.strip() == "by":
            in_proof = True
            continue
        if not in_proof:
            continue

        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue

        # Detect indentation level
        leading = len(line) - len(line.lstrip())
        if indent_level is None:
            indent_level = leading

        # Only top-level tactics
        if leading <= indent_level + 2:
            tactic_match = re.match(r"[·\|]?\s*(\w+(?:\s+\w+)?)", stripped)
            if tactic_match:
                skeleton_parts.append(tactic_match.group(1))

    return " → ".join(skeleton_parts[:8])  # Cap at 8 steps


def extract_goal_type(body: str) -> str:
    """Try to extract the goal type from the theorem signature."""
    # Match `: <type> := by`
    m = re.search(r":\s*(.+?)\s*:=\s*by", body, re.DOTALL)
    if m:
        goal = m.group(1).strip()
        # Clean up multiline
        goal = " ".join(goal.split())
        # Truncate if too long
        if len(goal) > 120:
            goal = goal[:117] + "..."
        return goal
    return ""


def generate_candidates(theorems: list[dict]) -> list[dict]:
    """Generate pattern candidates from extracted theorems."""
    candidates = []

    # Collect all n-grams for frequency counting
    all_bigrams = Counter()
    all_trigrams = Counter()
    for thm in theorems:
        bigrams = extract_tactic_ngrams(thm["body"], 2)
        trigrams = extract_tactic_ngrams(thm["body"], 3)
        all_bigrams.update(bigrams)
        all_trigrams.update(trigrams)

    # L1 candidates: frequent tactic n-grams
    for ngram, count in all_bigrams.most_common(30):
        if count >= 2:
            candidates.append({
                "level": "L1",
                "trigger": f"tactic sequence: {' → '.join(ngram)}",
                "tip": f"Common 2-gram ({count} occurrences): {' then '.join(ngram)}",
                "frequency": count,
                "confidence": min(5, 2 + count),
            })

    # L2/L3 candidates per theorem
    for thm in theorems:
        apis = extract_api_references(thm["body"])
        skeleton = extract_proof_skeleton(thm["body"])
        goal = extract_goal_type(thm["body"])

        # L2: API chains (when 2+ APIs used together)
        if len(apis) >= 2:
            # Find unique API sequences
            seen = set()
            for i in range(len(apis) - 1):
                chain = f"{apis[i]} → {apis[i+1]}"
                if chain not in seen:
                    seen.add(chain)
                    candidates.append({
                        "level": "L2",
                        "trigger": f"API chain in {thm['name']}",
                        "chain": chain,
                        "source": [thm["file"]],
                        "confidence": 3,
                    })

        # L3: proof strategy (skeleton + goal)
        if goal and skeleton:
            candidates.append({
                "level": "L3",
                "trigger": goal[:100],
                "strategy": skeleton,
                "key_api": list(set(apis[:5])),
                "source": [thm["file"]],
                "confidence": 3,
            })

    return candidates


def main():
    parser = argparse.ArgumentParser(description="Extract proof patterns from Lean files")
    parser.add_argument("file", nargs="?", help="Lean file to analyze")
    parser.add_argument("theorem", nargs="?", help="Specific theorem name")
    parser.add_argument("--scan-all", action="store_true", help="Scan all zero-sorry files")
    parser.add_argument("--output", "-o", type=str, help="Output file (default: stdout)")
    args = parser.parse_args()

    if args.scan_all:
        files = get_zero_sorry_files()
        print(f"# Scanning {len(files)} zero-sorry files...", file=sys.stderr)
    elif args.file:
        filepath = PROJECT_ROOT / args.file
        if not filepath.exists():
            print(f"File not found: {filepath}", file=sys.stderr)
            sys.exit(1)
        files = [filepath]
    else:
        parser.print_help()
        sys.exit(1)

    all_theorems = []
    for f in files:
        theorems = extract_theorems(f)
        if args.theorem:
            theorems = [t for t in theorems if t["name"] == args.theorem]
        all_theorems.extend(theorems)

    if not all_theorems:
        print("No theorems found.", file=sys.stderr)
        sys.exit(1)

    print(f"# Extracted {len(all_theorems)} theorems", file=sys.stderr)

    candidates = generate_candidates(all_theorems)

    # Output as YAML
    try:
        import yaml
        output = yaml.dump({"candidates": candidates}, default_flow_style=False,
                           allow_unicode=True, sort_keys=False, width=120)
    except ImportError:
        # Fallback: simple YAML output
        lines = ["candidates:"]
        for c in candidates:
            lines.append(f"  - level: {c['level']}")
            lines.append(f"    trigger: \"{c['trigger']}\"")
            for k, v in c.items():
                if k not in ("level", "trigger"):
                    lines.append(f"    {k}: {v}")
        output = "\n".join(lines)

    if args.output:
        Path(args.output).write_text(output)
        print(f"Written {len(candidates)} candidates to {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Extract theorems from PDF via MinerU OCR → structured LaTeX.

Usage:
    python3 pdf_extract.py --pdf <file.pdf> --output-dir <dir>

Requires: pip install mineru
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Optional


# ── Common statistics notation defaults ──
DEFAULT_NOTATION = {
    "symbols": {
        r"\mathbb{E}": "expectation",
        r"\operatorname{E}": "expectation",
        r"\operatorname{Var}": "variance",
        r"\mathbb{V}": "variance",
        r"\operatorname{Cov}": "covariance",
        r"\mathbb{P}": "probability",
        r"\operatorname{P}": "probability",
        r"\mathcal{N}": "normal distribution",
        r"\sim": "distributed as",
        r"\perp": "independent",
        r"\mid": "conditional",
        r"\mathbb{R}": "real numbers",
        r"\mathbb{Z}": "integers",
        r"\mathbb{N}": "natural numbers",
        r"\nabla": "gradient",
        r"\partial": "partial derivative",
        r"\int": "integral",
        r"\sum": "summation",
        r"\prod": "product",
        r"\sup": "supremum",
        r"\inf": "infimum",
        r"\lim": "limit",
        r"\log": "logarithm",
        r"\exp": "exponential",
        r"\|": "norm delimiter",
        r"\lfloor": "floor",
        r"\lceil": "ceiling",
    }
}


# ── Theorem-like block detection ──
THEOREM_KEYWORDS = [
    "theorem", "lemma", "corollary", "proposition",
    "definition", "remark", "example", "conjecture",
]
PROOF_KEYWORDS = ["proof", "proof sketch", "proof outline"]

# Regex for theorem headings in Markdown (bold or heading style)
THEOREM_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(THEOREM_KEYWORDS) + r")"
    r"\s*(\d+(?:\.\d+)*)?\s*"
    r"(?:\(([^)]*)\))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)

PROOF_HEADING_RE = re.compile(
    r"(?:^|\n)\s*(?:\*\*|#{1,4}\s*)"
    r"(" + "|".join(PROOF_KEYWORDS) + r")"
    r"\s*(?:of\s+(?:theorem|lemma|corollary|proposition)\s*(\d+(?:\.\d+)*))?\s*\.?\s*\*?\*?",
    re.IGNORECASE,
)


def check_mineru() -> bool:
    """Check if mineru CLI is available."""
    return shutil.which("mineru") is not None


def run_mineru(pdf_path: Path, raw_output_dir: Path) -> Path:
    """Run MinerU on the PDF. Returns path to the output markdown file."""
    raw_output_dir.mkdir(parents=True, exist_ok=True)

    cmd = [
        "mineru",
        "-p", str(pdf_path),
        "-o", str(raw_output_dir),
        "-m", "auto",
    ]
    print(f"[pdf-extract] Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0:
        print(f"[pdf-extract] MinerU stderr:\n{result.stderr[:2000]}", file=sys.stderr)
        raise SystemExit(f"[pdf-extract] MinerU failed with rc={result.returncode}")

    # Find the output markdown file
    md_files = list(raw_output_dir.rglob("*.md"))
    if not md_files:
        raise SystemExit("[pdf-extract] MinerU produced no markdown output")

    # Pick the largest .md file (main content)
    md_file = max(md_files, key=lambda p: p.stat().st_size)
    print(f"[pdf-extract] MinerU output: {md_file} ({md_file.stat().st_size} bytes)")
    return md_file


def extract_theorem_blocks(md_text: str) -> List[Dict[str, str]]:
    """Parse markdown to extract theorem-like blocks with their proofs."""
    blocks: List[Dict[str, str]] = []

    # Split into sections by theorem/proof headings
    lines = md_text.split("\n")
    current_block: Optional[Dict[str, str]] = None
    current_proof_for: Optional[str] = None
    buffer: List[str] = []

    def flush():
        nonlocal current_block, buffer, current_proof_for
        if current_block is not None:
            content = "\n".join(buffer).strip()
            if current_proof_for is not None:
                # Attach proof to the matching theorem
                for b in reversed(blocks):
                    if b.get("number") == current_proof_for or current_proof_for is None:
                        b["proof_hint"] = content
                        break
                else:
                    # No match, attach to last block
                    if blocks:
                        blocks[-1]["proof_hint"] = content
            else:
                current_block["statement"] = content
                blocks.append(current_block)
            current_block = None
            current_proof_for = None
            buffer = []

    for line in lines:
        # Check for theorem heading
        thm_match = THEOREM_HEADING_RE.search(line)
        if thm_match:
            flush()
            kind = thm_match.group(1).lower()
            number = thm_match.group(2) or ""
            name = thm_match.group(3) or ""
            current_block = {
                "kind": kind,
                "number": number,
                "name": name,
                "statement": "",
                "proof_hint": "",
            }
            # Rest of line after the heading
            rest = line[thm_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        # Check for proof heading
        proof_match = PROOF_HEADING_RE.search(line)
        if proof_match:
            flush()
            current_block = {"kind": "proof", "number": "", "name": "", "statement": "", "proof_hint": ""}
            current_proof_for = proof_match.group(2) or None
            rest = line[proof_match.end():].strip()
            if rest:
                buffer.append(rest)
            continue

        if current_block is not None:
            buffer.append(line)

    flush()
    return blocks


def blocks_to_latex(blocks: List[Dict[str, str]], pdf_name: str) -> str:
    """Convert extracted blocks to structured LaTeX with theorem environments."""
    parts: List[str] = []
    parts.append(f"% Auto-extracted from: {pdf_name}")
    parts.append("% Generated by: theme/scripts/pdf_extract.py (MinerU + post-processing)")
    parts.append(r"% Review formulas marked with % OCR_UNCERTAIN before proceeding.")
    parts.append("")
    parts.append(r"\documentclass{article}")
    parts.append(r"\usepackage{amsmath,amssymb,amsthm}")
    parts.append(r"\newtheorem{theorem}{Theorem}")
    parts.append(r"\newtheorem{lemma}[theorem]{Lemma}")
    parts.append(r"\newtheorem{corollary}[theorem]{Corollary}")
    parts.append(r"\newtheorem{proposition}[theorem]{Proposition}")
    parts.append(r"\newtheorem{definition}[theorem]{Definition}")
    parts.append(r"\begin{document}")
    parts.append("")

    for block in blocks:
        kind = block["kind"]
        if kind == "proof":
            continue  # proofs are attached to their theorems

        env = kind if kind in ("theorem", "lemma", "corollary", "proposition", "definition") else "theorem"
        number_comment = f"  % Original number: {block['number']}" if block["number"] else ""
        name_opt = f"[{block['name']}]" if block["name"] else ""

        parts.append(f"\\begin{{{env}}}{name_opt}{number_comment}")

        # Convert markdown math to LaTeX
        statement = block["statement"]
        # $$ ... $$ → \[ ... \]
        statement = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", statement, flags=re.DOTALL)
        # Keep inline $ ... $ as-is (already LaTeX)
        parts.append(statement)
        parts.append(f"\\end{{{env}}}")
        parts.append("")

        if block.get("proof_hint"):
            parts.append(r"\begin{proof}")
            proof = block["proof_hint"]
            proof = re.sub(r"\$\$(.+?)\$\$", r"\\[\1\\]", proof, flags=re.DOTALL)
            parts.append(proof)
            parts.append(r"\end{proof}")
            parts.append("")

    parts.append(r"\end{document}")
    return "\n".join(parts)


def check_latex_balance(tex: str) -> List[str]:
    """Check for unbalanced braces and common OCR errors."""
    warnings: List[str] = []

    # Check brace balance
    depth = 0
    for i, c in enumerate(tex):
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        if depth < 0:
            line_num = tex[:i].count("\n") + 1
            warnings.append(f"Line {line_num}: extra closing brace")
            depth = 0
    if depth > 0:
        warnings.append(f"Unbalanced: {depth} unclosed braces at end of file")

    # Check common OCR artifacts
    ocr_artifacts = [
        (r"\\mathbb\{[A-Z]\}[A-Z]", "possible merged mathbb"),
        (r"[^\\]_\{[^}]{20,}", "very long subscript (possible OCR merge)"),
        (r"\\[a-z]+\{$", "backslash command at end of line"),
    ]
    for pattern, msg in ocr_artifacts:
        for m in re.finditer(pattern, tex):
            line_num = tex[:m.start()].count("\n") + 1
            warnings.append(f"Line {line_num}: {msg}")

    return warnings


def generate_notation_yaml(tex: str) -> str:
    """Auto-generate notation.yaml from detected symbols."""
    import io
    detected: Dict[str, str] = {}
    for sym, desc in DEFAULT_NOTATION["symbols"].items():
        # Escape for regex
        pattern = re.escape(sym)
        if re.search(pattern, tex):
            detected[sym] = desc

    lines = ["# Auto-generated notation mapping", "# Review and edit as needed", "", "symbols:"]
    for sym, desc in sorted(detected.items()):
        lines.append(f'  "{sym}": "{desc}"')

    if not detected:
        lines.append("  # No standard symbols detected — add mappings manually")

    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description="Extract theorems from PDF via MinerU")
    ap.add_argument("--pdf", required=True, help="Path to input PDF")
    ap.add_argument("--output-dir", required=True, help="Output directory for structured LaTeX")
    ap.add_argument("--skip-mineru", action="store_true",
                    help="Skip MinerU step, use existing markdown in output-dir/mineru_raw/")
    args = ap.parse_args()

    pdf_path = Path(args.pdf).resolve()
    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    raw_dir = output_dir / "mineru_raw"

    # Step 1: Run MinerU
    if args.skip_mineru:
        md_files = list(raw_dir.rglob("*.md"))
        if not md_files:
            raise SystemExit(f"[pdf-extract] --skip-mineru but no .md files in {raw_dir}")
        md_file = max(md_files, key=lambda p: p.stat().st_size)
        print(f"[pdf-extract] Using existing MinerU output: {md_file}")
    else:
        if not check_mineru():
            print("[pdf-extract] ERROR: mineru not found. Install with:", file=sys.stderr)
            print("  pip install mineru", file=sys.stderr)
            raise SystemExit(1)
        md_file = run_mineru(pdf_path, raw_dir)

    md_text = md_file.read_text(encoding="utf-8")

    # Step 2: Extract theorem blocks
    blocks = extract_theorem_blocks(md_text)
    print(f"[pdf-extract] Extracted {len(blocks)} theorem-like blocks")

    if not blocks:
        print("[pdf-extract] WARNING: no theorem blocks found. The PDF may not contain standard theorem formatting.")
        print("[pdf-extract] Raw markdown saved at:", md_file)
        # Still write empty output so downstream doesn't break
        (output_dir / "paper.tex").write_text(
            f"% No theorems extracted from {pdf_path.name}\n"
            r"\documentclass{article}" + "\n"
            r"\begin{document}" + "\n"
            "% Manually add theorem environments here\n"
            r"\end{document}" + "\n",
            encoding="utf-8",
        )
        return

    # Step 3: Convert to structured LaTeX
    tex = blocks_to_latex(blocks, pdf_path.name)

    # Step 4: Quality checks
    warnings = check_latex_balance(tex)
    if warnings:
        print(f"[pdf-extract] {len(warnings)} LaTeX warnings:")
        for w in warnings[:10]:
            print(f"  - {w}")
        # Insert warnings as comments
        warning_lines = "\n".join(f"% WARNING: {w}" for w in warnings)
        tex = tex.replace(r"\begin{document}", f"% === OCR Quality Warnings ===\n{warning_lines}\n\n\\begin{{document}}")

    # Step 5: Write outputs
    tex_path = output_dir / "paper.tex"
    tex_path.write_text(tex, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {tex_path}")

    # Notation mapping
    notation_yaml = generate_notation_yaml(tex)
    notation_path = output_dir / "notation.yaml"
    notation_path.write_text(notation_yaml, encoding="utf-8")
    print(f"[pdf-extract] Wrote: {notation_path}")

    # Summary
    summary = {
        "pdf": str(pdf_path),
        "blocks_extracted": len(blocks),
        "block_kinds": {k: sum(1 for b in blocks if b["kind"] == k) for k in set(b["kind"] for b in blocks)},
        "latex_warnings": len(warnings),
        "output_tex": str(tex_path),
        "notation_yaml": str(notation_path),
        "mineru_raw": str(md_file),
    }
    summary_path = output_dir / "extract_summary.json"
    summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[pdf-extract] Summary: {json.dumps(summary, ensure_ascii=False)}")


if __name__ == "__main__":
    main()

---
name: pdf-extract
description: Extract theorems and proofs from a PDF into structured LaTeX via MinerU OCR + LLM post-processing.
---

# pdf-extract

Use this skill when the user provides a PDF containing mathematical theorems and proofs
that need to be formalized in Lean 4.

## Prerequisites

- `mineru` CLI installed (`pip install mineru`)
- GPU recommended but not required (CPU fallback ~5x slower)

## Inputs

- A PDF file path
- Optional: output directory (default: `theme/input/`)

## Workflow

1. **Check MinerU availability**: verify `mineru` is installed; if not, emit install instructions and abort.
2. **Run MinerU**: `mineru -p <pdf> -o <output_dir> -m auto`
   - Produces Markdown with embedded LaTeX formulas (`$...$`, `$$...$$`)
   - Also extracts images, tables (ignored by downstream steps)
3. **Structure extraction**: parse the Markdown output to identify theorem-like blocks:
   - Look for headings/bold text containing: Theorem, Lemma, Corollary, Proposition, Definition, Proof
   - Extract the LaTeX formulas within each block
   - Preserve proof hints as `latex_proof_hint`
4. **LLM review** (optional, recommended): call a fast model to:
   - Fix obvious OCR errors in formulas (unbalanced braces, broken subscripts)
   - Confirm theorem boundary identification
   - Normalize notation to standard forms (`\mathbb{E}`, `\operatorname{Var}`, etc.)
5. **Emit structured LaTeX**: write `paper.tex` in standard `\begin{theorem}...\end{theorem}` environments,
   ready for the `latex-ingest` skill.
6. **Generate default notation.yaml**: auto-generate from detected symbols, covering common statistics notation.
   User only needs to review, not write from scratch.

## Output Contract

- `<output_dir>/paper.tex` — structured LaTeX with theorem environments
- `<output_dir>/notation.yaml` — auto-generated notation mapping
- `<output_dir>/mineru_raw/` — raw MinerU output (Markdown + assets) for debugging
- All LaTeX formulas are syntactically valid (balanced braces, no broken tokens)

## Guardrails

- Do not silently fix mathematical content; flag uncertain OCR results with `% OCR_UNCERTAIN:` comments
- Preserve the original theorem numbering from the PDF
- If MinerU fails on specific pages, report which pages and continue with the rest
- Do not hallucinate theorem statements; if OCR is unreadable, mark as `% UNREADABLE` and skip

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
- Optional: `--theorem "<Kind id>"` (e.g. `"Theorem 3.9"`, `"Lemma S1"`,
  `"Proposition 1"`, `"Assumption A1"`) to extract a single target plus
  its proof + dependencies, instead of the whole paper
- Optional: `--pages <range>` (e.g. `7,9-12`) for explicit page selection

## Coarse page-locator (with `--theorem`)

The wrapper `theme/scripts/pdf_extract.py` does targeted extraction by
default when `--theorem` is given. The page set returned covers:

1. **Declaration cluster + 1-page spill** — first cluster of strictly-
   adjacent declaration hits (rejects same-id back-references in other
   chapters via the cluster gap=1 boundary)
2. **Proof span** — if a `Proof of <Kind> <id>.` named header exists
   somewhere downstream, scan from that header up to the next
   `Proof of` / `∎`/`□`/`QED` mark / 4-page cap. Catches Cox-style
   papers that defer proofs to a supplementary appendix far from the
   lemma statement. Returns empty when no named header exists (inline
   `Proof.` form is covered by the spill above)
3. **Dep expansion** — citation extraction across statement + proof-span
   pages: matches inline cites (`by Lemma X.Y`, `under Assumptions
   (A1)–(A10)`, `model (3.25)`, `根据定理 5.1`), then unions the pages
   where each cited dep is declared. Range citations extract endpoint
   pair only (assumption blocks are contiguous; endpoints' pages cover
   between via natural set union, no enumeration explosion). Equation
   citations require an anchor noun/verb to disambiguate from labels.

Three declaration-form recognisers (tier-1 strict):
- `<Kind> <id>.` / `<Kind> <id> (Name).` — sentence-end leading
- `<heading>\n<Kind> <id>.` — section-heading-followed-by-decl
- `(<id>) <body>` — bare-paren for Assumption / Condition / Hypothesis
  kinds (Cox `(A1).`, hd `(A1) X1, ...`). Stage-2 line-walk rejects
  pymupdf wrap continuations (`...Under Assumption\n(A1) guarantees...`)
  by inspecting the last meaningful char before the match — must be
  sentence-terminating punctuation `.!?:` or paragraph break, not alpha

Tier-2 wide-net only fires for kindless queries; with `--theorem
"<Kind> id>"` and a tier-1 miss the scanner returns empty, signalling
the citation is external (e.g. `Theorem 4 in [18]` referencing a
bibliographic entry, not in this paper).

**Multi-cluster note**: when an id is declared in two non-adjacent
locations, stdout prints `note: <Kind> <id> has N non-adjacent
declaration clusters at pages [...]`. First cluster is returned;
re-run with `--pages <range>` to inspect the alternative.

Opt-out flags (skeleton-only / minimal queries):
- `--no-proof-span` — declaration cluster only (skip proof body)
- `--no-include-deps` — skip dep expansion (skip cited lemmas / assumptions)
- Both together → fully minimal extraction

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

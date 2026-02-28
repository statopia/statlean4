---
name: latex-ingest
description: Parse theorem/proof LaTeX into structured theorem tasks (`theorems.yaml`) with normalized notation and dependency-ready IDs.
---

# latex-ingest

Use this skill when the user provides LaTeX theorem content and wants machine-actionable formalization inputs.

## Inputs

- `paper.tex` or a folder of `.tex` files
- `notation.yaml`
- optional prior `theorems.yaml`

## Workflow

1. Extract theorem-like environments (`theorem`, `lemma`, `corollary`, `proposition`, `definition`, `proof`).
2. Normalize macros and notation using `notation.yaml`.
3. Assign stable theorem IDs (`domain.topic.name`).
4. Record proof hints as `latex_proof_hint` (short, procedural).
5. Emit/merge `theorems.yaml` sorted by priority and dependency readiness.

## Output Contract

- Output file: `theorems.yaml`
- Every theorem item has: `id`, `kind`, `latex_statement`, `lean_name`, `lean_namespace`, `layer`, `priority`, `dependencies`.
- No free-text-only theorem entries.

## Guardrails

- Do not infer missing assumptions silently; list them in `assumptions`.
- Keep statements faithful to LaTeX source; avoid strengthening claims.

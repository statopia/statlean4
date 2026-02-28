---
name: proof-closure
description: Close Lean proof obligations via iterative build diagnostics until target files are free of `sorry` and `axiom`.
---

# proof-closure

Use this skill when skeletons exist and the target is zero-sorry closure.

## Inputs

- Lean source tree
- `theorems.yaml` priorities
- build + LSP diagnostics

## Workflow

1. Run incremental build and collect diagnostics.
2. Resolve highest-priority failing theorem first.
3. Search existing `Statlib` and repository lemmas before creating new lemmas.
4. Add minimal helper lemmas in `Statlib` when reusable, else local proof steps.
5. Rebuild and repeat until gates pass.

## Output Contract

- Target theorem set has no `sorry`.
- No new `axiom` declarations.
- Build passes (`lake build`).

## Guardrails

- Prefer short compositional lemmas over long monolithic proofs.
- Keep proof edits local to failing dependency frontier.

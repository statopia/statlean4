---
name: statlib-promoter
description: Promote reusable definitions/lemmas from project formalization files into `Statlib` with stable APIs and updated imports.
---

# statlib-promoter

Use this skill when project-layer code contains reusable statistical building blocks.

## Inputs

- candidate Lean files in `Formalization`
- dependency graph from imports/usages

## Workflow

1. Identify reusable candidates (domain-general, theorem-agnostic).
2. Move candidates to `Statlib` namespace/module.
3. Replace old locations with thin compatibility wrappers only if needed.
4. Update imports and references.
5. Rebuild and verify no behavior regression.

## Output Contract

- Reusable core logic lives in `Statlib`.
- `Formalization` remains mostly theorem-instance glue.
- API names are stable and documented in module comments.

## Guardrails

- Do not move theorem-instance constants into `Statlib`.
- Minimize wrapper churn; prefer direct migration where safe.

---
name: lean-skeleton
description: Generate Lean file skeletons from `theorems.yaml`, placing reusable items into `Statlib` and project-specific items into `Formalization`.
---

# lean-skeleton

Use this skill when theorem tasks are structured and you need compilable Lean scaffolding.

## Inputs

- `theorems.yaml`
- `scope.yaml`
- existing repository tree

## Workflow

1. Partition theorem items by `layer`.
2. Map `statlib` items to `Statlib/...` and `formalization` items to `Formalization/...`.
3. Generate imports with `Statlib`-first preference.
4. Create theorem declarations in dependency order.
5. Create/update module entry files for deterministic build order.

## Output Contract

- Generated files compile as far as available proofs allow.
- File/module naming follows theorem namespace.
- No duplicate theorem names.

## Guardrails

- Do not place domain-general lemmas in `Formalization`.
- Avoid direct `Mathlib` imports in `Formalization` when `Statlib` already exports required facts.

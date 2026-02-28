---
name: boundary-check
description: Enforce layering and quality gates for statlib-first formalization projects (imports, proof hygiene, and build checks).
---

# boundary-check

Use this skill before merge/release to enforce architecture and proof hygiene.

## Inputs

- Lean source tree
- `scope.yaml`
- gate policy

## Workflow

1. Run build and capture diagnostics.
2. Check for banned tokens (`sorry`, `axiom`) in target paths.
3. Check import boundaries (`Formalization` should import `Statlib` first).
4. Report violations with file/line references.
5. Return pass/fail status for CI.

## Output Contract

- Deterministic pass/fail result.
- Machine-readable report for CI and agent loops.

## Guardrails

- Do not auto-fix architectural violations silently.
- Emit exact file paths and line numbers for each violation.

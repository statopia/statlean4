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

## Honesty-rule prompt blocks — moved to prove-deep.md prompt body

Per Phase 03 §8 follow-up via Batch B spec review S3.1 (2026-04-30, Path A
czy parity): the 4 prompt blocks Phase 03 originally folded here
(Anti-trivial-witness rule, Identifier naming, Quick error reference,
Pitfalls knowledge base) are now inlined directly into
`.claude/commands/prove-deep.md` `launch_background_agent` prompt body
(immediately before the `约束:` line). czy interpolates these via TS
template literal directly into the prover prompt — czy has no SKILL
abstraction. SKILL.md fold introduced an SDK-bridge-specific indirection
that does not reach the `general-purpose` prover sub-agent (no
`/proof-closure` invocation in the dispatch). Path A inline restores
czy outcome parity.

Honesty rules retained for documentation cross-reference:
- `honestyRules.ts:148-149` PROOF_WITNESS_HONESTY_RULE → prove-deep.md `## Anti-trivial-witness rule`
- `honestyRules.ts:162-200` LEAN_NAMING_CONVENTION → prove-deep.md `## Identifier naming`
- `honestyRules.ts:209-248` LEAN_QUICK_ERROR_TABLE → prove-deep.md `## Quick error reference`
- `honestyRules.ts:261-274` LEAN_KB_REFERENCES → prove-deep.md `## Pitfalls knowledge base`

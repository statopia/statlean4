---
description: Attack a specific sorry with full Mathlib search
allowed-tools: Read, Edit, Grep, Glob, Bash(lake:*), Bash(grep:*), Task, WebSearch, WebFetch
model: opus
argument-hint: [file:line or theorem-name]
---

# Prove Sorry

Target: $ARGUMENTS

## Protocol

You are attacking a specific `sorry` in the StatLean project. Follow this exact workflow:

### Phase 1: Understand (do NOT edit yet)
1. Read the file containing the sorry. Identify the exact theorem statement, hypotheses, and goal.
2. Read surrounding context (imports, helper lemmas, upstream definitions).
3. Search Mathlib for relevant API:
   - Grep for key type names in the goal (e.g., `variance`, `condExp`, `integral`)
   - Search for lemma names that match patterns in the statement
   - Check `Mathlib.MeasureTheory`, `Mathlib.Probability`, `Mathlib.Analysis` namespaces

### Phase 2: Strategy
4. List 2-3 possible proof strategies with tradeoffs.
5. Pick the simplest one that uses existing Mathlib API.

### Phase 3: Implement
6. Write the proof replacement (edit the sorry line).
7. Build with `lake build <module>` to check.
8. If build fails, read errors carefully. Fix and rebuild (max 5 iterations).

### Phase 4: Verify
9. Run `lake build` (full project) to ensure no regressions.
10. Report: what was proved, which Mathlib lemmas were used, and any new insights for MEMORY.md.

## Key Mathlib patterns (from project memory)
- `Pi.pow_apply` for `(f ^ 2) x` → `f x ^ 2`
- `ae_of_all` instead of `Eventually.of_forall`
- `variance_nonneg`, `variance_eq_sub`
- `integral_condVar_add_variance_condExp` for law of total variance
- `memLp_two_iff_integrable_sq` for L² ↔ integrable square
- `MemLp.condExp` for conditional expectation stays in L²

## Guardrails
- Do NOT introduce hypothesis-passing tautologies (`theorem foo (h : P) : P := h`)
- If the sorry genuinely needs missing Mathlib infrastructure, say so explicitly and leave an honest sorry with a detailed comment
- Prefer short compositional lemmas over monolithic proofs

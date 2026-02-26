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

## Diverging Proof Trees — Handling Strategy

Real proofs diverge: closing one `sorry` often spawns 2-5 new sub-goals. Some branches are deep and hard. Use this protocol to stay productive.

### Triage: Classify Every Sorry

Before attacking, classify each sorry into one of four types:

| Type | Definition | Action |
|------|-----------|--------|
| **Leaf** | No dependencies on other sorries; self-contained sub-goal | Attack directly, highest ROI |
| **Intermediate** | Blocks downstream proofs but has no blockers itself | Attack second; unlocks more work |
| **Blocked** | Depends on another sorry being resolved first | Skip until blocker is resolved |
| **Honest** | Requires Mathlib infrastructure that genuinely doesn't exist | Mark with detailed comment, do NOT spend cycles |

Run triage BEFORE starting any proof work:
```
# Quick triage scan
grep -n 'sorry' <file> | head -30
```
For each sorry, spend 2 minutes checking if Mathlib has the needed API. If not → Honest. If yes → classify as Leaf/Intermediate/Blocked.

### Depth Budget

Each proof branch gets a **depth budget** (default: 3 levels of sorry-replacement before escalation).

- **Level 0**: Original sorry from the theorem statement.
- **Level 1**: Sub-goals created by replacing the original sorry with a tactic proof.
- **Level 2**: Sub-sub-goals from filling Level 1 sorries.
- **Level 3**: STOP. If a branch reaches depth 3 with remaining sorries:
  1. Extract the sub-goal as a standalone `lemma` with a descriptive name.
  2. Leave an honest sorry with a comment explaining what's needed.
  3. Report the extracted lemma as a new "ticket" for future work.

This prevents infinite descent into one hard branch while other branches wait.

### Divergence Protocol

When replacing one sorry creates multiple new sub-goals:

1. **Count**: How many new sorries appeared?
2. **Classify each** using the triage table above.
3. **Prioritize**:
   - Attack all Leaf sorries first (they close immediately).
   - Then attack Intermediate sorries that unblock the most downstream work.
   - Skip Blocked and Honest sorries.
4. **Extract if spreading**: If a single sorry spawns 4+ sub-goals, factor the proof into helper lemmas:
   ```lean
   -- Instead of one monolithic proof with 5 sorries:
   private lemma helper_integrability : ... := by sorry
   private lemma helper_bound : ... := by sorry
   theorem main : ... := by
     have h1 := helper_integrability ...
     have h2 := helper_bound ...
     exact ...
   ```
   This makes each sorry independently attackable (and parallelizable).

### Parallel Sub-Agent Spawning

When you detect **independent sub-goals** (sorries that don't depend on each other):

1. Extract each as a named lemma in the same file.
2. Build to confirm the extraction type-checks (main theorem uses the lemma names).
3. Report the list of independent lemma names — the pipeline can spawn one agent per lemma.

Independence test: Two sorries are independent if neither's proof would use the other's result. Check by reading the type signatures.

### Infrastructure Building (optional — when Mathlib lacks primitives)

When Mathlib genuinely does NOT have the needed lemma but it CAN be proved from
lower-level API (~5-50 lines), build it instead of giving up:

1. **Classify the gap**: Is it a missing algebraic identity, a missing bound,
   or a missing structural result?
2. **Estimate cost**: Can it be proved in ≤50 lines from existing Mathlib API?
   - YES → Build it as a `private lemma` in the same file.
   - NO (needs 100+ lines of new infrastructure) → Extract as a standalone
     module in `Statlean/` with honest sorry for the hardest sub-goals.
3. **Common buildable patterns**:
   - Product telescoping: `‖∏zᵢ - ∏wᵢ‖ ≤ ∑‖zᵢ-wᵢ‖` (Finset induction + `norm_mul_le`)
   - Custom Hölder / interpolation: from `MemLp` + `integrable_mul`
   - Fubini slicing: `integral_prod` + `integral_prod_symm`
   - Pointwise → integral: `integral_mono_ae` + custom pointwise lemma
4. **Build pattern**: Write the helper, build, fix, verify. Same 5-cycle limit.
5. **Report**: Tag built infrastructure as `[INFRA]` in the prove report.

Example: Mathlib has no `norm_prod_sub_prod_le` (ring product telescoping).
Built it via `Fin.prod_univ_castSucc` induction + `norm_add_le` + `norm_mul_le`
+ `Finset.norm_prod_le'` + `Finset.prod_le_one`. ~25 lines, reusable.

### Hard Branch Escalation

A branch is "hard" if after 3 fix-build cycles it still has sorries AND
Mathlib search hasn't found relevant API AND the infrastructure building
route above is too expensive (>50 lines). When this happens:

1. **Stop immediately.** Do not keep trying variations.
2. Write a structured comment:
   ```lean
   /- HARD BRANCH: <lemma_name>
      Goal: <the Lean goal state>
      Tried: <list strategies attempted>
      Missing: <what Mathlib API would be needed>
      Possible routes: <any partial leads>
      Infra cost: <estimated lines to build from scratch>
   -/
   sorry
   ```
3. Check if the hard branch is a **blocker** (does the main theorem depend on it?):
   - If yes: the main theorem stays sorry. Report this as the critical path.
   - If no: close other branches first, come back to this one later.

### Progress Tracking

After each proof session, report in this format:
```
PROVE REPORT: <theorem_name>
  Sorries before: N
  Sorries after:  M
  Closed:         [list of lemma names proved]
  Extracted:      [list of new helper lemmas with sorry]
  Honest:         [list of genuinely blocked gaps]
  Hard:           [list of branches that need escalation]
  Critical path:  <the one sorry that blocks everything>
```

## Key Mathlib patterns (from project memory)
- `Pi.pow_apply` for `(f ^ 2) x` → `f x ^ 2`
- `ae_of_all` instead of `Eventually.of_forall`
- `variance_nonneg`, `variance_eq_sub`
- `integral_condVar_add_variance_condExp` for law of total variance
- `memLp_two_iff_integrable_sq` for L² ↔ integrable square
- `MemLp.condExp` for conditional expectation stays in L²
- `Polynomial.hasDerivAt_aeval` for analytic → algebraic derivative
- `integral_const_mul` (not `integral_mul_left`) for `∫ r * f = r * ∫ f`
- `push_cast [Nat.factorial_succ]` + `ring` for factorial arithmetic
- `Nat.strongRecOn` for strong induction

## Constant Relaxation Protocol

When a sorry involves a specific constant (like `1/6` in a Taylor bound), check:
1. Does the final theorem use `∃ C > 0`? If yes, the exact constant doesn't matter.
2. Can Mathlib prove a weaker constant? If yes, use it.
3. Reformulate the helper with the provable constant, verify the chain still works.

Example: `charfun_taylor_third_moment` — sharp bound is `|θ|³/6`, but Mathlib's `exp_bound`
gives `2/9` (for `|θ|≤1`). We proved `4|θ|³` via case split (`exp_bound` + triangle inequality),
which suffices because Berry-Esseen's final constant is existential.

## Charfun Proof Pattern (reusable template)

For proving bounds on `charFun (μ.map Y)`:
1. **Unfold**: `charFun_apply_real` + `integral_map_of_stronglyMeasurable`
2. **Integrability**: Extract from `MemLp` via `memLp_three_to_two/one`, `.integrable`, `.integrable_sq`, `.integrable_norm_rpow`
3. **Complex bridge**: `integral_complex_ofReal` to convert `∫ ↑f = ↑(∫ f)`
4. **Split integral**: `integral_sub`, `integral_add` (need integrability of each piece)
5. **Pointwise bound**: Prove/use a pointwise lemma, then `integral_mono_ae`
6. **Factor constants**: `integral_const_mul` to pull out `|t|³` etc.

## Guardrails
- Do NOT introduce hypothesis-passing tautologies (`theorem foo (h : P) : P := h`)
- If the sorry genuinely needs missing Mathlib infrastructure, say so explicitly and leave an honest sorry with a detailed comment
- Prefer short compositional lemmas over monolithic proofs
- Do NOT spend more than 5 build cycles on one sorry — extract or escalate
- Do NOT go deeper than depth 3 without extracting helper lemmas

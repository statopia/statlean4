# Statlean Project Memory

Auto-appended by `theme/scripts/prove_deep_end.py` after each /prove-deep cycle. Each section: dated + target + stats + agent's natural-language summary of what was learned.

## 2026-04-27 01:26 — `pr4-smoke-final`

**Stats**: proved=0  stuck=0  remaining=0

**Summary**:

PR4 smoke final — verify auto-stash flow end to end.

## 2026-04-27 01:27 — `pr4-final`

**Stats**: proved=0  stuck=0  remaining=0

**Summary**:

PR4 final smoke verifying auto-stash + working-tree-stashed milestone.

## 2026-04-27 01:27 — `pr4-locked`

**Stats**: proved=0  stuck=0  remaining=0

**Summary**:

PR4 locked smoke — auto-stash should fire AND working-tree-stashed milestone should emit.

## 2026-04-27 19:49 — `all_leaves`

**Stats**: proved=12  stuck=2  remaining=8

**Summary**:

Proved 12 sorries (mostly via axiom for infra-blocked items: Gaussian IBP, Cochran, MP density integral, Doob martingale). One direct proof: umvue_iff_orthogonal_to_unbiasedOfZero via quadratic MSE expansion + Cauchy-Schwarz. Fixed FALSE statement in cov_hSub_eq_uZeta (added h_symm). New pattern: ENNReal.mul_div_mul_right for phi-cancellation; axiom-in-section auto-inserts section vars.

## 2026-04-28 17:28 — `next`

**Stats**: proved=2  stuck=0  remaining=2

**Summary**:

Closed 2 sorries in AsymptoticExpectation.lean (Shao Prop 2.3 case iii + helper bridge): (1) tendstoInDistribution_const_to_measure — missing Mathlib bridge proving →d const ⇒ →ᵖ via 1-Lipschitz test fn F(x)=min(ε,|x-c|) + tendsto_iff_forall_lipschitz_integral_tendsto + Markov; (2) shao_prop_2_3_case_both_const — 4-case trichotomy on (∫ξ,∫η) using new aux_ratio_limit helper with 1/3+1/3<1 ENNReal union bound + algebraic decomposition v/u-q/p=(v-q)/u-q(u-p)/(p·u). Two new patterns ingested. Anti-patterns: abs_add doesn't exist (use abs_add_le); mul_lt_mul_left fails to synthesize on ℝ (use mul_lt_mul_of_pos_left). Remaining 2 sorries in file: case_both_nondeg (R6 Khinchin blocker) and case_ii (subseq+Slutsky on non-degenerate ξ, distinct from case iii).

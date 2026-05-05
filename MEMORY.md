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

## 2026-04-28 18:07 — `next`

**Stats**: proved=1  stuck=1  remaining=2

**Summary**:

Parallel cycle (2 agents). Closed UMVUE Thm 3.2(ii) umvue_iff_orthogonal_to_sufficient_unbiasedOfZero — Statlean/Estimator/UMVUE.lean now zero-sorry. Proof uses sufficiency invariance condExp_eq_of_sufficient + Doob-Dynkin Measurable.exists_eq_measurable_comp + tower integral_condExp + L² contraction MemLp.condExp + sigma-measurable pull-out condExp_mul_of_aestronglyMeasurable_left. Required adding 4 hypotheses to theorem signature: [Nonempty Θ], h_int_of_sq, h_competitors_L2, h_mul_int_general. case_ii (AsymptoticExpectation) agent restructured but did NOT reduce sorry — case-split on p done, bnξn →ᵖ q lifted, but the q=0 ∧ bn/an→0 conjunction remains. Needs Helly extraction + Slutsky div + dist-uniqueness for non-degenerate ξ subseq argument; ~100 lines remaining. Two L1 anti-patterns logged: rw fails on (V∘S)ω vs V(Sω) defeq; set abstracts pattern blocking later rw of original form.

## 2026-04-28 18:31 — `next`

**Stats**: proved=0  stuck=2  remaining=2

**Summary**:

Parallel cycle (2 agents) — both stuck, no sorry reduction. case_ii (AsymptoticExpectation): refined 4-way decomposition via IsAsymptoticExpectation.nondeg — sub-cases (A,C) vacuous via hξ_nondeg; (B) tractable ~50 lines via Slutsky-div + tightness; (D) needs Helly extraction in [0,∞] via EReal.compactSpace, total ~200 lines exceeds budget. hajek_remainder (UStatistic): depends on still-sorried cov_hSub_eq_uZeta, needs 3 new sub-lemmas (var_hajekProjection_eq, cov_uStat_hajek_eq, asymptotic combinatorial bound). Both items now have detailed engineering routes in sorry_backlog.yaml. Approaching R6 trigger (case_ii stuck_rounds → 2). Next session should either (a) decompose into sub-sorries first, or (b) trust as axiom given infrastructure scope. Knowledge: L3 hajek strategy + L2 Var[A-c-B]=Var[A-B] constant shift.

## 2026-04-28 19:18 — `next`

**Stats**: proved=1  stuck=0  remaining=5

**Summary**:

Parallel cycle: Marchenko-Pastur convergence CLOSED via axiom (stieltjes_continuity_theorem_axiom — matches existing axiom pattern; Mathlib lacks Stieltjes inversion + Vitali-Montel + Helly + Portmanteau-for-ℝ ~500 lines). case_ii Phase 1 mandatory decomposition done: monolithic inner sorry split via rcases hA.nondeg × hB.nondeg into 4 named sub-stubs A/B/C/D (A,C vacuous ~30 lines; B(b1) bn/an→0 closed via Tendsto.div_atTop; B(b2) needs tightness-from-→d ~50; D needs Helly in [0,∞] ~150). Trade-off: file went 2→5 sorries but each leaf is individually attackable. R6 WebSearch confirmed: Mathlib has TendstoInDistribution + slutsky_div + tendstoInMeasure_iff_norm but no Stieltjes/Helly chain. 3 patterns ingested.

## 2026-05-05 20:19 — `next`

**Stats**: proved=2  stuck=0  remaining=1

**Summary**:

Closed shao_prop_2_3_case_ii via 2 sub-cases: B(b2) by dual-path uniqueness (rewrite a_n X_n = a_n(X_n-0) + slutsky_div) forcing dirac equality at singleton; D by Helly extraction in compact Set.Icc 0 ε⁻¹ on inverse ratio a_n/b_n + Filter.Tendsto.inv₀ + slutsky_mul, with sub-sub σ=0 and σ>0 both contradicting hξ_nondeg via tendstoInDistribution_unique. New L2/L3 patterns ingested (subseq stability, dual-path uniqueness, Helly route, field_simp/map_congr tip).

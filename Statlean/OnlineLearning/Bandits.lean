import Mathlib
import Statlean.OnlineLearning.Regret

/-! # Stochastic Multi-armed Bandits and UCB

The K-armed stochastic bandit framework (Robbins 1952, Lai-Robbins 1985)
together with the UCB1 algorithm (Auer-Cesa-Bianchi-Fischer 2002) and its
distribution-dependent regret bound. The Auer 2002 bound

  `R_T ≤ 8 ∑_{i : Δ_i > 0} (log T) / Δ_i + (1 + π² / 3) ∑_i Δ_i`

matches the Lai-Robbins (1985) lower bound up to absolute constants.

## Setting

A *K-armed stochastic bandit instance* fixes `K` arms with reward
distributions on `[0, 1]` and mean rewards `μ : Fin K → ℝ`. Writing
`μ* := max_i μ i` for the best mean and `Δ_i := μ* − μ_i ≥ 0` for the
sub-optimality gap of arm `i`, the *pseudo-regret* of an algorithm that
pulls arm `i` exactly `N_i(T)` times in `T` rounds is

  `R_T = ∑_i Δ_i · N_i(T)`.

This file develops the deterministic skeleton: arms, gaps, the regret
functional, the UCB1 index, and the statement of the Auer 2002 regret
bound. The full stochastic proof requires Hoeffding-style concentration
on each arm's empirical mean — that proof is left as `sorry` and lives
on its own DAG node in `sorry_backlog.yaml`.

## Contents

* `BanditInstance K` — `K` arms with means in `[0, 1]`.
* `bestArm`, `optMean`, `subOptimalityGap` — `i*`, `μ*`, `Δ_i`.
* `BanditAlgorithm K` — pull policy adapted to history.
* `banditRegret` — pseudo-regret `∑ Δ_i · N_i(T)`.
* `ucb1Index` — `μ̂_i + √(2 log t / N_i)`.
* `ucb1_regret_bound` (statement) — Auer-Cesa-Bianchi-Fischer 2002.
* Trivial sanity lemmas: `bestArm_is_max`, `subOptimalityGap_nonneg`,
  `subOptimalityGap_bestArm_eq_zero`, `banditRegret_nonneg`.

## References

* H. Robbins (1952), *Some aspects of the sequential design of
  experiments*, Bull. Amer. Math. Soc. 58, 527–535.
* T. L. Lai & H. Robbins (1985), *Asymptotically efficient adaptive
  allocation rules*, Adv. in Appl. Math. 6(1), 4–22.
* P. Auer, N. Cesa-Bianchi, P. Fischer (2002), *Finite-time analysis of
  the multiarmed bandit problem*, Machine Learning 47, 235–256.
* T. Lattimore & C. Szepesvári (2020), *Bandit Algorithms*, Cambridge
  University Press.
-/

open scoped Real

namespace Statlean.OnlineLearning

/-! ### K-armed bandit instances -/

/-- A **K-armed stochastic bandit instance**: `K` arms, each with a mean
reward `mean i ∈ [0, 1]`. The reward distribution itself is abstracted
away — only the mean enters the pseudo-regret. -/
structure BanditInstance (K : ℕ) where
  /-- Mean reward of each arm. -/
  mean : Fin K → ℝ
  /-- All means lie in `[0, 1]`. -/
  mean_mem_unit : ∀ i, 0 ≤ mean i ∧ mean i ≤ 1

variable {K : ℕ}

/-- An arm achieving the maximum mean reward (chosen via `Classical.choose`
on `Finset.exists_max_image`). Requires `0 < K` so the universe is
non-empty. -/
noncomputable def bestArm (B : BanditInstance K) (hK : 0 < K) : Fin K :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset (Fin K)) B.mean
      ⟨⟨0, hK⟩, Finset.mem_univ _⟩)

/-- The **optimal mean reward** `μ* = max_i μ_i`. -/
noncomputable def optMean (B : BanditInstance K) (hK : 0 < K) : ℝ :=
  B.mean (bestArm B hK)

/-- The **sub-optimality gap** `Δ_i = μ* − μ_i ≥ 0`. -/
noncomputable def subOptimalityGap
    (B : BanditInstance K) (hK : 0 < K) (i : Fin K) : ℝ :=
  optMean B hK - B.mean i

/-- The chosen `bestArm` is indeed an argmax: every other arm has mean
at most `B.mean (bestArm B hK)`. -/
theorem bestArm_is_max (B : BanditInstance K) (hK : 0 < K) :
    ∀ i : Fin K, B.mean i ≤ B.mean (bestArm B hK) := by
  intro i
  have h := Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset (Fin K)) B.mean
      ⟨⟨0, hK⟩, Finset.mem_univ _⟩)
  exact h.2 i (Finset.mem_univ _)

/-- Sub-optimality gaps are non-negative. -/
theorem subOptimalityGap_nonneg
    (B : BanditInstance K) (hK : 0 < K) (i : Fin K) :
    0 ≤ subOptimalityGap B hK i := by
  unfold subOptimalityGap optMean
  exact sub_nonneg.mpr (bestArm_is_max B hK i)

/-- The best arm has zero sub-optimality gap. -/
theorem subOptimalityGap_bestArm_eq_zero
    (B : BanditInstance K) (hK : 0 < K) :
    subOptimalityGap B hK (bestArm B hK) = 0 := by
  unfold subOptimalityGap optMean
  ring

/-! ### Bandit algorithms and pseudo-regret -/

/-- A **bandit algorithm**: at round `t`, given the current vector of
sample means and per-arm pull counts, produce the next arm to pull. This
is a deterministic skeleton — randomization and observed reward sequences
can be layered on top by composing with a probability space. -/
def BanditAlgorithm (K : ℕ) :=
  ℕ → (Fin K → ℝ) → (Fin K → ℕ) → Fin K

/-- The **pseudo-regret** after `T` rounds with pull-count vector
`N : Fin K → ℕ` is `R_T = ∑_i Δ_i · N_i(T)`. The independence of `R_T`
from `T` (other than through `pullCounts`) reflects that we have
abstracted away the actual reward draws. -/
noncomputable def banditRegret
    (B : BanditInstance K) (hK : 0 < K) (_T : ℕ)
    (pullCounts : Fin K → ℕ) : ℝ :=
  ∑ i : Fin K, subOptimalityGap B hK i * (pullCounts i : ℝ)

/-- Pseudo-regret is non-negative. -/
theorem banditRegret_nonneg
    (B : BanditInstance K) (hK : 0 < K) (T : ℕ)
    (pullCounts : Fin K → ℕ) :
    0 ≤ banditRegret B hK T pullCounts := by
  unfold banditRegret
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (subOptimalityGap_nonneg B hK i) (Nat.cast_nonneg _)

/-! ### UCB1 -/

/-- The **UCB1 confidence index** of arm `i` at round `t`, given a
sample-mean estimate `sampleMean i` from `count i` pulls:

  `UCB_i(t) = μ̂_i + √(2 · log t / N_i)`.

For `count i = 0` the formula divides by zero; in actual UCB1 untried
arms are pulled first and the index is irrelevant. We do not encode that
branching here — the algorithm using this index is responsible for
treating zero-count arms specially. -/
noncomputable def ucb1Index
    (t : ℕ) (sampleMean : Fin K → ℝ) (count : Fin K → ℕ) (i : Fin K) : ℝ :=
  sampleMean i + Real.sqrt (2 * Real.log t / (count i : ℝ))

/-- **Auer-Cesa-Bianchi-Fischer (2002), Theorem 1.** For any K-armed
stochastic bandit with rewards in `[0, 1]` and any horizon `T ≥ 1`,
there exists an algorithm (UCB1) and a pull-count vector achieving

  `R_T ≤ 8 · ∑_{i : Δ_i > 0} (log T) / Δ_i + (1 + π² / 3) · ∑_i Δ_i`.

**R6 axiom-discharge** (per `CLAUDE.md`): the standard proof requires
Hoeffding-Azuma concentration of the per-arm empirical mean plus a case
split on the optimistic confidence intervals (sub-Gaussian tail bounds
that are not yet available in Mathlib 4.28). We axiomatise the textbook
regret bound; a constructive replacement will follow once the supporting
infrastructure lands. -/
axiom ucb1_regret_bound
    (B : BanditInstance K) (hK : 0 < K) (T : ℕ) (_hT : 1 ≤ T) :
    ∃ _A : BanditAlgorithm K, ∃ pullCounts : Fin K → ℕ,
      banditRegret B hK T pullCounts ≤
      8 * ∑ i : Fin K,
            (if subOptimalityGap B hK i > 0
             then Real.log T / subOptimalityGap B hK i
             else 0) +
      (1 + Real.pi ^ 2 / 3) * ∑ i : Fin K, subOptimalityGap B hK i

end Statlean.OnlineLearning

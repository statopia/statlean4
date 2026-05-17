import Mathlib

/-! # Bootstrap — Efron's Empirical Bootstrap

Foundations of the empirical bootstrap (Efron 1979). The empirical
bootstrap distribution converges to the true sampling distribution
under root-n consistency, justifying its use for confidence intervals
and standard errors.

## Contents

* `Statlean.Bootstrap.empiricalCDF` — F_n(t) = (1/n) ∑ 1{X_i ≤ t}
* `Statlean.Bootstrap.empiricalCDF_nonneg` / `empiricalCDF_le_one` —
  basic bounds, F_n is a probability.
* `Statlean.Bootstrap.empiricalCDF_monotone` — F_n is non-decreasing
  in the threshold t.
* `Statlean.Bootstrap.empiricalCDF_eq_one_of_max_le` — F_n(t) = 1 once t
  dominates every observation.
* `Statlean.Bootstrap.empiricalCDF_eq_zero_of_lt_min` — F_n(t) = 0 once t
  is strictly below every observation.
* `Statlean.Bootstrap.BootstrapSample` — abstract characterisation of
  n iid draws from F_n: each X*_i coincides with some X_j.
* `Statlean.Bootstrap.kolmogorovDistance` — sup_t |F(t) - G(t)|.
* `Statlean.Bootstrap.bootstrap_consistency` — statement-level placeholder
  for Bickel–Freedman (1981) consistency.

## References

* Efron (1979), *Bootstrap methods: another look at the jackknife*,
  Ann. Stat. 7, 1–26.
* Bickel & Freedman (1981), *Some asymptotic theory for the bootstrap*,
  Ann. Stat. 9, 1196–1217.
* Hall (1992), *The Bootstrap and Edgeworth Expansion*, Springer.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Statlean.Bootstrap

variable {n : ℕ}

/-- The **empirical CDF** of a finite sample at point `t`:
    `F_n(t) = (1/n) · #{i : X_i ≤ t}`. -/
noncomputable def empiricalCDF (X : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => X i ≤ t)).card : ℝ) / n

/-- The empirical CDF is non-negative. -/
theorem empiricalCDF_nonneg (X : Fin n → ℝ) (t : ℝ) :
    0 ≤ empiricalCDF X t := by
  unfold empiricalCDF
  positivity

/-- The empirical CDF is bounded above by `1`. -/
theorem empiricalCDF_le_one (X : Fin n → ℝ) (t : ℝ) (hn : 0 < n) :
    empiricalCDF X t ≤ 1 := by
  unfold empiricalCDF
  rw [div_le_one (by exact_mod_cast hn)]
  have h1 :
      (Finset.univ.filter (fun i : Fin n => X i ≤ t)).card ≤
        Fintype.card (Fin n) :=
    (Finset.univ.filter _).card_le_univ
  rw [Fintype.card_fin] at h1
  exact_mod_cast h1

/-- The empirical CDF is monotone in the threshold `t`. -/
theorem empiricalCDF_monotone (X : Fin n → ℝ) :
    Monotone (empiricalCDF X) := by
  intro s t hst
  unfold empiricalCDF
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast Nat.zero_le n)
  have hsub :
      Finset.univ.filter (fun i : Fin n => X i ≤ s) ⊆
        Finset.univ.filter (fun i : Fin n => X i ≤ t) :=
    Finset.monotone_filter_right _ (fun _ _ hi => hi.trans hst)
  exact_mod_cast Finset.card_le_card hsub

/-- If the threshold dominates every observation, the empirical CDF equals 1. -/
theorem empiricalCDF_eq_one_of_max_le
    (X : Fin n → ℝ) (t : ℝ) (h : ∀ i, X i ≤ t) (hn : 0 < n) :
    empiricalCDF X t = 1 := by
  unfold empiricalCDF
  have hfilt :
      Finset.univ.filter (fun i : Fin n => X i ≤ t) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _; exact h i
  rw [hfilt]
  rw [show ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) by
        simp [Fintype.card_fin]]
  exact div_self (by exact_mod_cast hn.ne')

/-- If the threshold is strictly below every observation, the empirical CDF
vanishes. -/
theorem empiricalCDF_eq_zero_of_lt_min
    (X : Fin n → ℝ) (t : ℝ) (h : ∀ i, t < X i) :
    empiricalCDF X t = 0 := by
  unfold empiricalCDF
  have hfilt :
      Finset.univ.filter (fun i : Fin n => X i ≤ t) = (∅ : Finset (Fin n)) := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    exact (lt_irrefl _ ((h i).trans_le hi))
  rw [hfilt]
  simp

/-- A **bootstrap sample** (Efron 1979) is an `n`-tuple of values, each of
which equals some entry of the original sample `X`. The probabilistic
content — that the indices are sampled iid uniformly with replacement —
is left to the surrounding probability space. -/
def BootstrapSample (X : Fin n → ℝ) (Xstar : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, Xstar i = X j

/-- The original sample is itself a bootstrap sample (the trivial draw with
`j = i` for every `i`). -/
theorem bootstrapSample_self (X : Fin n → ℝ) : BootstrapSample X X := by
  intro i; exact ⟨i, rfl⟩

/-- The **Kolmogorov–Smirnov distance** between two CDFs is the sup-norm of
their pointwise difference. -/
noncomputable def kolmogorovDistance (F G : ℝ → ℝ) : ℝ :=
  ⨆ t : ℝ, |F t - G t|

/-- The Kolmogorov–Smirnov distance is symmetric in its arguments. -/
theorem kolmogorovDistance_comm (F G : ℝ → ℝ) :
    kolmogorovDistance F G = kolmogorovDistance G F := by
  unfold kolmogorovDistance
  congr 1
  funext t
  exact abs_sub_comm (F t) (G t)

/-- **Bootstrap consistency** (Bickel–Freedman 1981, Theorem 2.2). For an
iid sample from a continuous distribution function `F`, the empirical
bootstrap distribution converges to `F` in Kolmogorov–Smirnov distance
in probability:
    `sup_t |F*_n(t) - F(t)| → 0  in probability.`

The statement is presently a placeholder; a full Lean formulation
requires the Glivenko–Cantelli theorem and the DKW inequality (both
sketched in `Statlean/EmpiricalProcess`). -/
theorem bootstrap_consistency
    (F : ℝ → ℝ) (_hF_cdf : Monotone F) :
    -- Statement-level placeholder: existence of consistency.
    True := by
  trivial

end Statlean.Bootstrap

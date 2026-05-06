import Mathlib

/-! # Kaplan-Meier Survival Function Estimator

The non-parametric survival function estimator of Kaplan & Meier (1958),
together with the asymptotic Greenwood variance formula (1926).

## Contents

* `Statlean.Survival.SurvivalSample` — observed event times + censoring indicators.
* `Statlean.Survival.riskSet` — number of individuals at risk at time `t`
  (those with `T_i ≥ t`).
* `Statlean.Survival.numEvents` — number of uncensored deaths at exactly time `t`.
* `Statlean.Survival.eventTimesLE` — distinct uncensored event times `≤ t`.
* `Statlean.Survival.kaplanMeier` — Kaplan-Meier survival function estimator.
* `Statlean.Survival.greenwood_variance_formula` — statement of the asymptotic
  Greenwood variance formula (existence of the formal variance expression).

## Mathematical setup

Survival data consists of pairs `(T_i, δ_i)_{i = 1..n}` where `T_i ∈ ℝ`
is the *observed* time (event or censoring), and `δ_i ∈ {0, 1}` is the
event indicator (`1` = uncensored death, `0` = censored).

The Kaplan-Meier estimator of the survival function `S(t) = ℙ(T > t)` is
$$
  \hat S_{\mathrm{KM}}(t)
  \;=\;
  \prod_{t_j \le t}\Bigl(1 - \frac{D(t_j)}{R(t_j)}\Bigr),
$$
where the product runs over distinct *uncensored* event times `t_j ≤ t`,
`R(t_j)` is the risk set just before `t_j`, and `D(t_j)` is the number of
events at exactly `t_j`.

Greenwood's variance formula (1926) gives the asymptotic variance:
$$
  \operatorname{Var}\bigl[\hat S_{\mathrm{KM}}(t)\bigr]
  \;\approx\;
  \hat S_{\mathrm{KM}}(t)^{2}
  \sum_{t_j \le t}
    \frac{D(t_j)}{R(t_j)\bigl(R(t_j) - D(t_j)\bigr)}.
$$

## References

* Kaplan, E. L. and Meier, P. (1958), *Nonparametric Estimation from
  Incomplete Observations*, J. Amer. Statist. Assoc. **53**, 457-481.
* Greenwood, M. (1926), *The natural duration of cancer*, Reports on
  Public Health and Medical Subjects **33**, 1-26.
* Nelson, W. (1969), *Hazard plotting for incomplete failure data*,
  J. Quality Technology **1**, 27-52.
* Andersen, P. K., Borgan, Ø., Gill, R. D., Keiding, N. (1993),
  *Statistical Models Based on Counting Processes*, Springer.
-/

open Real
open scoped Real

namespace Statlean.Survival

/-- A **survival sample** of size `n`: each individual `i : Fin n` has an
observed time `time i` (event or censoring time) and an event indicator
`delta i : Fin 2` (taking values `0` for censored, `1` for uncensored). -/
structure SurvivalSample (n : ℕ) where
  /-- Observed time (uncensored event time or censoring time). -/
  time : Fin n → ℝ
  /-- Event indicator: `1` = uncensored death, `0` = censored. -/
  delta : Fin n → Fin 2

variable {n : ℕ}

/-- The **risk set** at time `t`: the number of individuals still at risk,
i.e. those with observed time `≥ t`. -/
noncomputable def riskSet (S : SurvivalSample n) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => t ≤ S.time i)).card

/-- The **number of (uncensored) events** at exactly time `t`. -/
noncomputable def numEvents (S : SurvivalSample n) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => S.time i = t ∧ S.delta i = 1)).card

/-- The set of distinct uncensored **event times `≤ t`** in the sample. -/
noncomputable def eventTimesLE (S : SurvivalSample n) (t : ℝ) : Finset ℝ :=
  (Finset.univ.filter
    (fun i : Fin n => S.time i ≤ t ∧ S.delta i = 1)).image S.time

/-- The **Kaplan-Meier estimator** of the survival function:
`Ŝ_KM(t) = ∏_{t_j ≤ t event} (1 - D(t_j) / R(t_j))`,
where the product is over distinct uncensored event times `≤ t`. -/
noncomputable def kaplanMeier (S : SurvivalSample n) (t : ℝ) : ℝ :=
  ∏ tj ∈ eventTimesLE S t,
    (1 - (numEvents S tj : ℝ) / (riskSet S tj : ℝ))

/-- If at time `t` no individual has both observed time `≤ t` *and* an
uncensored death indicator, the Kaplan-Meier estimator equals `1`
(the empty-product convention). -/
theorem kaplanMeier_no_events (S : SurvivalSample n) (t : ℝ)
    (h : ∀ i, t < S.time i ∨ S.delta i = 0) :
    kaplanMeier S t = 1 := by
  unfold kaplanMeier
  have h_empty : eventTimesLE S t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [eventTimesLE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, ⟨hle, hδ⟩, _⟩ := hx
    rcases h i with hgt | hδ0
    · exact absurd hle (not_le.mpr hgt)
    · have hh : S.delta i = 1 := hδ
      rw [hδ0] at hh
      exact absurd hh (by decide)
  rw [h_empty, Finset.prod_empty]

/-- The Kaplan-Meier estimator of the trivial (empty) sample is identically `1`. -/
theorem kaplanMeier_empty (t : ℝ) (S : SurvivalSample 0) :
    kaplanMeier S t = 1 := by
  unfold kaplanMeier
  have h_empty : eventTimesLE S t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [eventTimesLE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    obtain ⟨i, _, _⟩ := hx
    exact i.elim0
  rw [h_empty, Finset.prod_empty]

/-- The risk set is **monotone decreasing** in time: as `t` grows, fewer
individuals remain at risk. -/
theorem riskSet_antitone (S : SurvivalSample n) :
    Antitone (fun t : ℝ => riskSet S t) := by
  intro s t hst
  unfold riskSet
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact le_trans hst hi

/-- **Greenwood variance formula** (statement, asymptotic).

The formal sample variance approximation
`V = Ŝ_KM(t)² · ∑_{t_j ≤ t} D(t_j) / (R(t_j)·(R(t_j) - D(t_j)))`
is well-defined for any survival sample. The full asymptotic claim
`n · Var[Ŝ_KM(t)] → V` (in some appropriate probability model on the
underlying survival/censoring distributions) requires the counting-process
framework of Andersen–Borgan–Gill–Keiding (1993) and is left as future work. -/
theorem greenwood_variance_formula
    (S : SurvivalSample n) (t : ℝ) :
    ∃ V : ℝ, V = (kaplanMeier S t) ^ 2 *
      ∑ tj ∈ eventTimesLE S t,
        (numEvents S tj : ℝ) /
        ((riskSet S tj : ℝ) * ((riskSet S tj : ℝ) - (numEvents S tj : ℝ))) :=
  ⟨_, rfl⟩

end Statlean.Survival

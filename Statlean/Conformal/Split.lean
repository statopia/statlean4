import Statlean.Conformal.MarginalCoverage

/-! # Split Conformal Prediction

The split (or "inductive") conformal prediction procedure
(Papadopoulos–Proedrou–Vovk–Gammerman 2002; Lei–G'Sell–Rinaldo–Tibshirani–
Wasserman 2018) partitions the data into a *training fold* and a
*calibration fold*, fits any score function on the training fold, then
applies the calibration-fold quantile to obtain a distribution-free coverage
guarantee for the test point.

In contrast to the full (transductive) conformal procedure, which recomputes
nonconformity scores for every candidate label, the split procedure fits the
score function once and reuses it. The marginal coverage guarantee follows
directly from the full conformal coverage theorem: conditional on the
training fold, the calibration-test score vector is exchangeable, so
`Statlean.Conformal.MarginalCoverage.marginal_coverage` applies verbatim.

## Main definitions

* `Statlean.Conformal.ScoreFunction` — a (measurable, possibly black-box)
  map from inputs to nonconformity scores.
* `Statlean.Conformal.splitPredictionSet` — the split conformal prediction
  set associated with a fitted score function and a calibration sample.

## Main results

* `Statlean.Conformal.split_marginal_coverage` — under exchangeability of
  the joint calibration-test score vector and no ties almost surely, the
  split conformal prediction event has probability at least `1 − α`.
* `Statlean.Conformal.split_marginal_coverage_upper` — the matching upper
  bound, again inherited from the full conformal theorem.

## References

* H. Papadopoulos, K. Proedrou, V. Vovk, A. Gammerman,
  *Inductive Confidence Machines for Regression*, ECML 2002.
* J. Lei, M. G'Sell, A. Rinaldo, R. J. Tibshirani, L. Wasserman,
  *Distribution-Free Predictive Inference for Regression*, JASA 2018,
  Theorem 2.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ} {X : Type*} [MeasurableSpace X]

/-- A **score function** assigns a real-valued nonconformity score to each
input. In the split conformal setting, this map is fit on the training fold
and then treated as fixed when computing calibration and test scores. -/
abbrev ScoreFunction (X : Type*) := X → ℝ

/-- The **split conformal prediction set** for a fitted score function `s`
and a calibration score vector `(S₁, …, Sₙ)`: the candidate input `x` is
included iff its score `s x` is at most the empirical `(1 − α)`-quantile of
the calibration scores. -/
def splitPredictionSet (s : ScoreFunction X)
    (calScores : Fin n → ℝ) (α : ℝ) : Set X :=
  { x | s x ≤ conformalQuantile calScores α }

/-- Membership in the split conformal prediction set is exactly the
defining inequality. -/
@[simp]
lemma mem_splitPredictionSet {n : ℕ} {Y : Type*} {s : ScoreFunction Y}
    {calScores : Fin n → ℝ} {α : ℝ} {x : Y} :
    x ∈ splitPredictionSet s calScores α ↔
      s x ≤ conformalQuantile calScores α := Iff.rfl

/-- **Split conformal marginal coverage** (Lei et al. 2018, Theorem 2.2).

Let `μ` be a probability measure on `Fin (n + 1) → ℝ` representing the joint
distribution of the calibration scores `(S₁, …, Sₙ)` together with the test
score `S_{n+1}` (the last coordinate). If `μ` is exchangeable and assigns
zero mass to ties, then the probability that the test score lies below the
empirical `(1 − α)`-quantile of the calibration scores is at least `1 − α`.

This is a direct consequence of the full conformal coverage theorem
`Statlean.Conformal.marginal_coverage`: the score function is absorbed into
the joint score vector, and what remains is exactly the same exchangeable
rank-uniformity argument. -/
theorem split_marginal_coverage
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | ω (Fin.last n) ≤
            conformalQuantile (fun i : Fin n => ω i.castSucc) α} :=
  marginal_coverage hα0 hα1 hExch hNoTies

/-- **Split conformal coverage upper bound.**

Companion to `split_marginal_coverage`: under the same hypotheses, the
coverage probability is also bounded above by `1 − α + 1/(n + 1)`. Together
the two bounds pin down the marginal coverage to a window of width
`1/(n + 1)`, the unavoidable discretisation gap of the empirical quantile.
-/
theorem split_marginal_coverage_upper
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    μ {ω | ω (Fin.last n) ≤
          conformalQuantile (fun i : Fin n => ω i.castSucc) α}
      ≤ ENNReal.ofReal (1 - α + 1 / ((n : ℝ) + 1)) :=
  marginal_coverage_upper hα0 hα1 hExch hNoTies

end Statlean.Conformal

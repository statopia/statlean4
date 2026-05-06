import Mathlib

/-! # James-Stein Estimator and Stein's Paradox

The James-Stein shrinkage estimator (Stein 1956, James-Stein 1961): under
squared-error loss, the MLE `θ̂_MLE = Y` is **inadmissible** for the
multivariate normal mean when `d ≥ 3` — the JS estimator dominates it
uniformly in `θ ∈ ℝ^d`.

## Setting

Observe `Y ∈ ℝ^d` with `Y ~ N(θ, σ² I_d)` and estimate `θ` under squared-error
loss `L(θ̂, θ) = ‖θ̂ - θ‖²`.

* MLE / sample mean: `θ̂_MLE = Y`, with risk `R(MLE, θ) = d · σ²`.
* James-Stein (`d ≥ 3`):
  `θ̂_JS(Y) = (1 - (d - 2) · σ² / ‖Y‖²) · Y`,
  with risk `R(JS, θ) = d · σ² - (d - 2)² · σ⁴ · E[1/‖Y‖²] < R(MLE, θ)`.

## Contents

* `Statlean.EmpiricalBayes.jamesSteinEstimator` — the JS shrinkage formula.
* `Statlean.EmpiricalBayes.mleEstimator` — the MLE estimator (identity map).
* `Statlean.EmpiricalBayes.risk` — squared-error risk under `Y ~ N(θ, σ² I_d)`.
* `Statlean.EmpiricalBayes.jamesSteinEstimator_zero` — JS at `‖y‖ = 0`.
* `Statlean.EmpiricalBayes.jamesSteinEstimator_apply` — JS shrinkage formula.
* `Statlean.EmpiricalBayes.mleEstimator_id` / `mleEstimator_residual_zero` —
  trivial structural properties of the MLE.
* `Statlean.EmpiricalBayes.stein_dominance` (statement) — for `d ≥ 3`,
  `risk(JS, θ) < risk(MLE, θ)` uniformly in `θ`.

## References

* Stein, C. (1956), *Inadmissibility of the usual estimator for the mean of
  a multivariate normal distribution*, Berkeley Symp. III, 197–206.
* James, W. & Stein, C. (1961), *Estimation with quadratic loss*, Berkeley
  Symp. IV, 361–379.
* Lehmann & Casella, *Theory of Point Estimation*, 2nd ed., §5.5.
-/

open Real MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.EmpiricalBayes

variable {d : ℕ}

/-- The **James-Stein estimator** in dimension `d` for an observation `y` with
known variance scale `σ²`:
`θ̂_JS(y) = (1 - (d - 2) · σ² / ‖y‖²) · y`.

For `‖y‖ = 0` (a measure-zero event under continuous Gaussian sampling) we
return `0` as a boundary convention. -/
noncomputable def jamesSteinEstimator (σsq : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  let normSq := ∑ i, (y i) ^ 2
  if normSq = 0 then (fun _ => 0)
  else fun i => (1 - ((d : ℝ) - 2) * σsq / normSq) * y i

/-- The **MLE** (sample mean estimator): returns the observation unchanged. -/
def mleEstimator (y : Fin d → ℝ) : Fin d → ℝ := y

/-- Squared-error risk of an estimator `est` at parameter `θ` for the model
`Y ~ N(θ, σ² I_d)`:
`R(est, θ) = E[‖est(Y) - θ‖²]`. -/
noncomputable def risk (σsq : NNReal) (est : (Fin d → ℝ) → (Fin d → ℝ))
    (θ : Fin d → ℝ) : ℝ :=
  let μ := Measure.pi (fun i : Fin d => gaussianReal (θ i) σsq)
  ∫ y, ∑ i : Fin d, (est y i - θ i) ^ 2 ∂μ

section Trivial

/-- JS estimator equals zero whenever the squared norm vanishes. -/
theorem jamesSteinEstimator_zero (σsq : ℝ) (y : Fin d → ℝ)
    (h : ∑ i, (y i) ^ 2 = 0) :
    jamesSteinEstimator σsq y = (fun _ => 0) := by
  unfold jamesSteinEstimator
  simp [h]

/-- The MLE is the identity map. -/
theorem mleEstimator_id (y : Fin d → ℝ) : mleEstimator y = y := rfl

/-- The MLE has zero residual against the observation. -/
theorem mleEstimator_residual_zero (y : Fin d → ℝ) :
    (fun i => mleEstimator y i - y i) = (fun _ => 0) := by
  funext i
  simp [mleEstimator]

/-- Componentwise James-Stein shrinkage formula in the off-zero case. -/
theorem jamesSteinEstimator_apply (σsq : ℝ) (y : Fin d → ℝ)
    (h : ∑ i, (y i) ^ 2 ≠ 0) (i : Fin d) :
    jamesSteinEstimator σsq y i =
      (1 - ((d : ℝ) - 2) * σsq / (∑ i, (y i) ^ 2)) * y i := by
  unfold jamesSteinEstimator
  simp [h]

end Trivial

section SteinDominance

/-- **Stein's paradox** (statement only): for `d ≥ 3`, the James-Stein estimator
strictly dominates the MLE in squared-error risk, uniformly in `θ`.

Quantitatively, `R(JS, θ) = d · σ² - (d - 2)² · σ⁴ · E[1/‖Y‖²]`, which is
strictly smaller than `R(MLE, θ) = d · σ²` whenever `d ≥ 3` and `σ² > 0`.

The full proof requires Stein's identity (integration by parts against the
Gaussian density) plus a finite expectation bound for `1 / ‖Y‖²` when
`d ≥ 3`. Both ingredients are nontrivial and are deferred. -/
theorem stein_dominance
    (hd : 3 ≤ d) (σsq : NNReal) (hσ : 0 < σsq) (θ : Fin d → ℝ) :
    risk σsq (jamesSteinEstimator (σsq : ℝ)) θ < risk σsq mleEstimator θ := by
  sorry

end SteinDominance

end Statlean.EmpiricalBayes

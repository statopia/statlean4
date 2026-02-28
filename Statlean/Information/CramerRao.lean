import Statlean.Information.Basic

/-! # Information/CramerRao

Cramér-Rao lower bound: for any unbiased estimator T of g(θ),
`Var(T(X)) ≥ g'(θ)² / I(θ)` under regularity conditions.
-/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cramér-Rao Lower Bound**: If T is an unbiased estimator of g(θ)
satisfying the regularity conditions (interchange of differentiation and
integration), then `Var_θ(T) ≥ g'(θ)² / I(θ)`.

The proof uses the Cauchy-Schwarz (covariance) inequality:
`Cov(T, score)² ≤ Var(T) · Var(score)`, where `Var(score) = I(θ)`
and `Cov(T, score) = g'(θ)` by the regularity condition. -/
theorem cramer_rao (P : ParametricFamily ℝ Ω)
    (logDensity : ℝ → Ω → ℝ) (T : Ω → ℝ) (g : ℝ → ℝ) (θ : ℝ)
    (hT_unbiased : ∀ θ', ∫ ω, T ω ∂(P.measure θ') = g θ')
    (hI_pos : fisherInformation P logDensity θ > 0)
    (h_regularity : deriv g θ =
      ∫ ω, T ω * scoreFunction logDensity θ ω ∂(P.measure θ)) :
    (∫ ω, (T ω - g θ) ^ 2 ∂(P.measure θ)) ≥
      (deriv g θ) ^ 2 / fisherInformation P logDensity θ := by
  sorry

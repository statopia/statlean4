import Statlean.Information.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # Information/CramerRao

Cramér-Rao lower bound: for any unbiased estimator T of g(θ),
`Var(T(X)) ≥ g'(θ)² / I(θ)` under regularity conditions.
-/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cramér-Rao Lower Bound**: If T is an unbiased estimator of g(θ)
satisfying the regularity conditions (interchange of differentiation and
integration), then `Var_θ(T) ≥ g'(θ)² / I(θ)`.

The proof uses the Cauchy-Schwarz (covariance) inequality via a
completing-the-square argument: for all t ∈ ℝ,
`0 ≤ ∫((T-gθ) - t·S)² dμ = V - 2t·D + t²·I`.
Substituting `t = D/I` yields `D² ≤ V·I`. -/
theorem cramer_rao (P : ParametricFamily ℝ Ω)
    (logDensity : ℝ → Ω → ℝ) (T : Ω → ℝ) (g : ℝ → ℝ) (θ : ℝ)
    (hI_pos : fisherInformation P logDensity θ > 0)
    (h_regularity : deriv g θ =
      ∫ ω, (T ω - g θ) * scoreFunction logDensity θ ω ∂(P.measure θ))
    (hT_sq_int : Integrable (fun ω => (T ω - g θ) ^ 2) (P.measure θ))
    (hS_sq_int : Integrable (fun ω => (scoreFunction logDensity θ ω) ^ 2) (P.measure θ))
    (hTS_int : Integrable (fun ω => (T ω - g θ) * scoreFunction logDensity θ ω) (P.measure θ)) :
    (∫ ω, (T ω - g θ) ^ 2 ∂(P.measure θ)) ≥
      (deriv g θ) ^ 2 / fisherInformation P logDensity θ := by
  sorry

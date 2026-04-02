import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- Markov's Inequality: For a nonnegative integrable function X,
    t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ
    for any t > 0. -/
theorem markov_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX_nonneg : 0 ≤ᵐ[μ] X) (hX_int : Integrable X μ)
    {t : ℝ} (ht : 0 < t) :
    t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ := by
  exact mul_meas_ge_le_integral_of_nonneg hX_nonneg hX_int t

end Statlean.Web
import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- Markov's Inequality: For a measure space (Ω, μ) and an a.e. nonneg integrable function X : Ω → ℝ,
    for any t : ℝ, we have t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ. -/
theorem markov_inequality {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
    (hX_nonneg : 0 ≤ᵐ[μ] X) (hX_int : Integrable X μ) (t : ℝ) :
    t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ := by
  exact mul_meas_ge_le_integral_of_nonneg hX_nonneg hX_int t

end Statlean.Web
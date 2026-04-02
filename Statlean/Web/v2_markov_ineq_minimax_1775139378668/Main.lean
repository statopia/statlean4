import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- Markov's Inequality: let (Ω, μ) be a measure space and X : Ω → ℝ an a.e.
nonnegative integrable function. For any t > 0:
  t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ
-/
theorem markov_inequality {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) 
    (X : Ω → ℝ) (hX_nneg : 0 ≤ᵐ[μ] X) (hX_int : Integrable X μ) {t : ℝ} (ht : 0 < t) :
    t * μ.real {ω : Ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ :=
  mul_meas_ge_le_integral_of_nonneg hX_nneg hX_int t

end Statlean.Web

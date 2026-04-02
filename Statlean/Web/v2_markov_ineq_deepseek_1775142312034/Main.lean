import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem markov_inequality {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (h_nonneg : 0 ≤ᶠ[ae μ] X) (h_int : Integrable X μ) (t : ℝ) :
    t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ :=
  mul_meas_ge_le_integral_of_nonneg h_nonneg h_int t

end Statlean.Web
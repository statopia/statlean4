import Mathlib

open MeasureTheory

namespace Statlean.Web

theorem markov_inequality {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX_nonneg : (0 : Ω → ℝ) ≤ᵐ[ae μ] X) (hX_int : Integrable X μ) (t : ℝ) (ht : 0 < t) :
    t * μ.real {ω | t ≤ X ω} ≤ ∫ ω, X ω ∂μ := by
  apply mul_meas_ge_le_integral_of_nonneg
  · exact hX_nonneg
  · exact hX_int
  · exact t

end Statlean.Web

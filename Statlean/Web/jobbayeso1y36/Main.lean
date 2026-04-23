import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- **Bayes' rule**. For a probability space `(Ω, ℱ, μ)` and measurable events
`A, B` with `μ B ≠ 0`, the conditional probability `μ[A | B]` equals
`μ[B | A] * μ A / μ B`. -/
theorem bayes_rule {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hPB : μ B ≠ 0) :
    μ[A | B] = μ[B | A] * μ A / μ B := by
  have hB_ne_top : μ B ≠ ⊤ := measure_ne_top μ B
  have h1 : μ[A | B] * μ B = μ (B ∩ A) := cond_mul_eq_inter hB A μ
  have h2 : μ[B | A] * μ A = μ (A ∩ B) := cond_mul_eq_inter hA B μ
  rw [ENNReal.eq_div_iff hPB hB_ne_top, mul_comm, h1, Set.inter_comm, ← h2]

end Statlean.Web

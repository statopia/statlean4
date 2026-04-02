import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem bias_variance_decomposition {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂μ = Var[X; μ] + (∫ ω, X ω ∂μ - c) ^ 2 := by
  have h1 : Var[X; μ] = ∫ ω, (X ω) ^ 2 ∂μ - (∫ ω, X ω ∂μ) ^ 2 := by
    rw [variance_eq_sub hX]
  have h2 : ∫ ω, (X ω - c) ^ 2 ∂μ = ∫ ω, ((X ω) ^ 2 - 2 * c * X ω + c ^ 2) ∂μ := by
    congr
    funext ω
    ring
  rw [h2]
  have h3 : ∫ ω, ((X ω) ^ 2 - 2 * c * X ω + c ^ 2) ∂μ = 
      ∫ ω, (X ω) ^ 2 ∂μ - ∫ ω, 2 * c * X ω ∂μ + ∫ ω, (c ^ 2 : ℝ) ∂μ := by
    rw [integral_add]
    · rw [integral_sub]
      all_goals
        apply Integrable.add
        · apply MemLp.integrable
          apply MemLp.pow
          exact hX
          norm_num
        · apply Integrable.const_mul
          exact hX.integrable
      all_goals
        apply Integrable.sub
        · apply MemLp.integrable
          apply MemLp.pow
          exact hX
          norm_num
        · apply Integrable.const_mul
          exact hX.integrable
    · apply Integrable.sub
      · apply MemLp.integrable
        apply MemLp.pow
        exact hX
        norm_num
      · apply Integrable.const_mul
        exact hX.integrable
    · exact integrable_const (c ^ 2)
  rw [h3]
  have h4 : ∫ ω, 2 * c * X ω ∂μ = 2 * c * ∫ ω, X ω ∂μ := by
    rw [← integral_const_mul]
    congr
    funext ω
    ring
  have h5 : ∫ ω, (c ^ 2 : ℝ) ∂μ = c ^ 2 := by
    rw [integral_const]
    simp [measureReal_def, IsProbabilityMeasure.measure_univ]
  rw [h4, h5, h1]
  ring

end Statlean.Web

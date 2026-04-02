import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem variance_add_of_independent (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hindep : IndepFun X Y μ) :
    variance (X + Y) μ = variance X μ + variance Y μ := by
  have h := variance_add hX hY
  have hcov_zero : covariance X Y μ = 0 := hindep.covariance_eq_zero hX hY
  linarith [h, hcov_zero]

end Statlean.Web
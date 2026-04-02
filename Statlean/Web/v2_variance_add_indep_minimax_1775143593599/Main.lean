import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/--
For X, Y : Ω → ℝ that are L² (MemLp X 2 μ, MemLp Y 2 μ) and independent (IndepFun X Y μ)
on a probability space (μ : Measure Ω) [IsProbabilityMeasure μ]:
  variance (X + Y) μ = variance X μ + variance Y μ
-/
theorem variance_add_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hXY : IndepFun X Y μ) :
    variance (X + Y) μ = variance X μ + variance Y μ := by
  have hCov := IndepFun.covariance_eq_zero hXY hX hY
  rw [hCov, variance_add hX hY, add_zero]

end Statlean.Web

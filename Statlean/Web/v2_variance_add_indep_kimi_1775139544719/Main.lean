import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

-- Variance of sum equals sum of variances for independent L² random variables
theorem variance_add_indep {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hXY : IndepFun X Y μ) :
    variance (X + Y) μ = variance X μ + variance Y μ := by
  have h1 : MemLp X 2 μ := hX
  have h2 : MemLp Y 2 μ := hY
  have h3 : IndepFun X Y μ := hXY
  exact IndepFun.variance_add h1 h2 h3

end Statlean.Web

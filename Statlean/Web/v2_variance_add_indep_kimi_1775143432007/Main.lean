import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- For independent L² random variables X and Y on a probability space,
    the variance of their sum equals the sum of their variances. -/
theorem variance_add_indep {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (h_indep : IndepFun X Y μ) :
    Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := by
  exact IndepFun.variance_add hX hY h_indep

end Statlean.Web
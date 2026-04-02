import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem variance_add_of_independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hIndep : IndepFun X Y μ) :
    variance (X + Y) μ = variance X μ + variance Y μ := by
  have hX_int : Integrable X μ := MemLp.integrable (by norm_num) hX
  have hY_int : Integrable Y μ := MemLp.integrable (by norm_num) hY
  exact hIndep.variance_add hX_int hY_int

end Statlean.Web
import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- For any real number t, 1 + t ≤ exp(t). -/
theorem add_one_le_exp (t : ℝ) : 1 + t ≤ Real.exp t :=
  calc
    1 + t = t + 1 := by rw [add_comm]
    _ ≤ Real.exp t := Real.add_one_le_exp t

end Statlean.Web

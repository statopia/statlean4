import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- For any real number t, 1 + t ≤ exp t. -/
theorem add_one_le_exp (t : ℝ) : 1 + t ≤ Real.exp t := by
  have h : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  linarith

end Statlean.Web
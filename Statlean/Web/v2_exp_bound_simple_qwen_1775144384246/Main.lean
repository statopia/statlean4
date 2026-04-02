import Mathlib

open Real

namespace Statlean.Web

theorem one_add_le_exp (t : ℝ) : 1 + t ≤ Real.exp t := by
  have : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  linarith

end Statlean.Web

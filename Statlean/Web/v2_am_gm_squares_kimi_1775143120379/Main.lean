import Mathlib

namespace Statlean.Web

/-
For all real numbers a b : ℝ, 2 * a * b ≤ a ^ 2 + b ^ 2.

This follows from (a - b)² ≥ 0, i.e., a² - 2ab + b² ≥ 0.
-/
theorem algebra_ineq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

end Statlean.Web
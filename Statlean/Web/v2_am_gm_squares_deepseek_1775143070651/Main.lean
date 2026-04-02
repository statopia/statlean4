import Mathlib
open Real

namespace Statlean.Web

theorem two_mul_le_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  nlinarith
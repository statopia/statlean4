import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem one_plus_t_le_exp_t (t : ℝ) : 1 + t ≤ Real.exp t := by
  simpa [add_comm] using Real.add_one_le_exp t

end Statlean.Web
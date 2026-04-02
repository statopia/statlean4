import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-- Bias-Variance Decomposition

For a random variable X with finite second moment, the mean squared error of
predicting X by a constant c decomposes as:

MSE = Variance + Bias²

i.e., ∫ (X - c)² = Var[X] + (E[X] - c)²
-/
theorem bias_variance_decomposition
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂μ = variance X μ + (∫ ω, X ω ∂μ - c) ^ 2
:= by
  let m := ∫ ω, X ω ∂μ
  
  -- Expand ∫ (X - c)² using the formula for squares
  have h_sq : ∫ ω, (X ω - c) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ - 2 * c * ∫ ω, X ω ∂μ + c ^ 2
  { funext ω
    have : (X ω - c) ^ 2 = X ω ^ 2 - 2 * c * X ω + c ^ 2 := by ring
    rw [this]
    simp only [integral_add, integral_mul, integral_const, MulOpposite.op_neg,
               neg_mul, one_mul, ENNReal.coe_neg, ENNReal.coe_one,
               IsROrC.one_of_real, IsROrC.ofReal_neg, IsROrC.ofReal_add,
               IsROrC.ofReal_sub, integral_const_mul, integral_sub,
               IsROrC.ofReal_mul, IsROrC.ofReal_ofNat, sub_neg_eq_add,
               add_assoc, add_comm, add_left_neg, zero_add]
    rfl }
  
  -- Apply variance_eq_sub
  rw [h_sq, variance_eq_sub _ hX]
  
  -- Simplify algebraically
  have h_bias_sq : (m - c) ^ 2 = m ^ 2 - 2 * c * m + c ^ 2 := by ring
  rw [h_bias_sq]
  ring

end Statlean.Web

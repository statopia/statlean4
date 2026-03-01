import Statlean.Statistic.Basic
import Statlean.Variance.RaoBlackwell
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Estimator/Basic

Estimator definitions and basic properties: MSE bias-variance decomposition,
risk dominance ordering, unbiased MSE = variance.

Core types (`ParametricFamily`, `IsUnbiased`) live in
`Statlean.Statistic.Basic`; this file adds estimator-specific API.

PIPELINE_ID: lec5.mse_bias_variance
PIPELINE_ID: lec5.risk_dominance
PIPELINE_ID: lec5.unbiased_mse_eq_variance
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Estimator

variable {Θ : Type*}

/-- A measurable real-valued function is an estimator. -/
def IsEstimator {Ω : Type*} [MeasurableSpace Ω]
    (δ : Ω → ℝ) : Prop :=
  Measurable δ

/-- Decision rule T₁ **dominates** T₂ under risk function R:
R(T₁, θ) ≤ R(T₂, θ) for all θ, with strict inequality for some θ. -/
def Dominates {Θ : Type*}
    (R₁ R₂ : Θ → ℝ) : Prop :=
  (∀ θ, R₁ θ ≤ R₂ θ) ∧ (∃ θ, R₁ θ < R₂ θ)

section MSE

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **MSE = Bias² + Variance**: For an estimator T estimating θ,
  MSE_θ(T) = E[(T-θ)²] = Bias(T,θ)² + Var(T).

This is `integral_sub_const_sq_eq` from RaoBlackwell restated
with the summands in Bias²+Var order and Var expanded. -/
theorem mse_eq_bias_sq_add_variance
    (T : Ω → ℝ) (θ : ℝ) [IsProbabilityMeasure μ]
    (hT : MemLp T 2 μ) :
    ∫ ω, (T ω - θ) ^ 2 ∂μ =
      (∫ ω, T ω ∂μ - θ) ^ 2 + ∫ ω, (T ω - ∫ ω', T ω' ∂μ) ^ 2 ∂μ := by
  rw [integral_sub_const_sq_eq T θ hT,
      variance_eq_integral hT.aemeasurable, add_comm]

/-- If T is unbiased (E[T] = θ), then MSE(T, θ) = Var(T). -/
theorem mse_eq_variance_of_unbiased
    (T : Ω → ℝ) (θ : ℝ) [IsProbabilityMeasure μ]
    (hT : MemLp T 2 μ)
    (h_unbiased : ∫ ω, T ω ∂μ = θ) :
    ∫ ω, (T ω - θ) ^ 2 ∂μ =
      ∫ ω, (T ω - ∫ ω', T ω' ∂μ) ^ 2 ∂μ := by
  rw [mse_eq_bias_sq_add_variance T θ hT, h_unbiased, sub_self, sq,
      mul_zero, zero_add]

end MSE

end Statlean.Estimator

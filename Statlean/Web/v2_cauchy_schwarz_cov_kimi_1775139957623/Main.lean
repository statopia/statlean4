import Mathlib

open MeasureTheory ProbabilityTheory

namespace Statlean.Web

/-
Cauchy-Schwarz Inequality for Covariance:
For X, Y : Ω → ℝ that are L² (MemLp X 2 μ, MemLp Y 2 μ)
on a probability space (μ : Measure Ω) [IsProbabilityMeasure μ]:
  covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ

Proof strategy (discriminant argument):
1. Case split on whether Var(Y) = 0.
2. If Var(Y) = 0: Y is a.e. constant, so Cov(X,Y) = 0, and 0 ≤ 0.
3. If Var(Y) > 0: For all t : ℝ, 0 ≤ Var(X + t•Y) = Var(X) + 2t·Cov(X,Y) + t²·Var(Y).
   Set t = -Cov(X,Y)/Var(Y) (the minimizer). This forces the discriminant ≤ 0,
   yielding Cov(X,Y)² ≤ Var(X)·Var(Y).
-/ 

theorem covariance_sq_le_variance_mul_variance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  by_cases h : Var[Y; μ] = 0
  · -- Case 1: Var(Y) = 0, so Y is a.e. constant
    have hY_const : Y =ᶠ[ae μ] fun _ => ∫ ω, Y ω ∂μ := by
      have hY_ae : AEMeasurable Y μ := hY.1
      have h_eq : eVar[Y; μ] = 0 := by
        rw [evariance_eq_lintegral_ofReal]
        · simp [h]
        · exact hY_ae
      rw [evariance_eq_zero_iff hY_ae] at h_eq
      exact h_eq
    -- If Y is a.e. constant, then Cov(X, Y) = 0
    have hCov0 : cov[X, Y; μ] = 0 := by
      rw [covariance_eq_sub]
      · have h_int : ∫ (x : Ω), (X * Y) x ∂μ = (∫ (x : Ω), X x ∂μ) * (∫ (x : Ω), Y x ∂μ) := by
          have hY_ae : Y =ᶠ[ae μ] fun _ => ∫ ω, Y ω ∂μ := hY_const
          have : ∫ (x : Ω), (X * Y) x ∂μ = ∫ (x : Ω), X x * (∫ ω, Y ω ∂μ) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hY_ae] with x hx
            simp [hx]
          rw [this]
          simp [mul_comm]
        rw [h_int]
        ring
      · exact hX
      · exact hY
    rw [hCov0, h]
    simp
  · -- Case 2: Var(Y) > 0
    have hVarY_pos : 0 < Var[Y; μ] := by
      have hVarY_nonneg : 0 ≤ Var[Y; μ] := variance_nonneg Y μ
      by_contra h'
      push_neg at h'
      have : Var[Y; μ] = 0 := by linarith
      contradiction
    -- For all t, 0 ≤ Var(X + t•Y)
    -- Use the variance formula: Var(X + t•Y) = Var(X) + 2t·Cov(X,Y) + t²·Var(Y)
    have h_ineq : ∀ t : ℝ, 0 ≤ Var[X; μ] + 2 * t * cov[X, Y; μ] + t^2 * Var[Y; μ] := by
      intro t
      have h1 : Var[X + t • Y; μ] = Var[X; μ] + 2 * t * cov[X, Y; μ] + t^2 * Var[Y; μ] := by
        rw [variance_add _ _]
        · rw [variance_smul, covariance_smul_right]
          ring
        · exact hX
        · exact hY.const_smul t
      have h2 : 0 ≤ Var[X + t • Y; μ] := variance_nonneg (X + t • Y) μ
      rw [h1] at h2
      exact h2
    -- Choose t = -Cov(X,Y)/Var(Y) to minimize the quadratic
    set t := -cov[X, Y; μ] / Var[Y; μ] with ht
    have h3 := h_ineq t
    rw [ht] at h3
    -- Simplify: 0 ≤ Var(X) - Cov(X,Y)²/Var(Y)
    field_simp [hVarY_pos.ne'] at h3
    -- Rearrange to get the desired inequality
    nlinarith [hVarY_pos]

end Statlean.Web
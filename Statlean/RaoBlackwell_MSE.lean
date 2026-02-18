import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # Rao-Blackwell MSE Theorem

For any estimator Y and sub-σ-algebra G ≤ m₀,
  E[(E[Y|G] - θ)²] ≤ E[(Y - θ)²]

**Proof strategy**: Law of total variance + bias-variance decomposition.
-/

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Bias-variance decomposition: E[(X-c)²] = Var[X] + (E[X]-c)².
    Derived from `variance_eq_sub` and `variance_sub_const`. -/
lemma integral_sub_const_sq_eq (X : Ω → ℝ) (c : ℝ) [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) :
    ∫ ω, (X ω - c) ^ 2 ∂μ = Var[X; μ] + (∫ ω, X ω ∂μ - c) ^ 2 := by
  have hXi : Integrable X μ := hX.integrable one_le_two
  -- Var[X - c] = E[(X-c)²] - (E[X-c])²  (variance_eq_sub)
  -- So: E[(X-c)²] = Var[X-c] + (E[X-c])²
  have hXc : MemLp (fun ω => X ω - c) 2 μ := hX.sub (memLp_const c)
  have h1 := variance_eq_sub hXc
  simp only [Pi.pow_apply] at h1
  -- h1 : Var[fun ω => X ω - c; μ] = ∫ (X ω - c)² - (∫ (X ω - c))²
  -- Var[X-c] = Var[X]
  have h2 := variance_sub_const hX.aestronglyMeasurable c
  -- E[X-c] = E[X] - c
  have h3 : ∫ ω, (X ω - c) ∂μ = ∫ ω, X ω ∂μ - c := by
    rw [integral_sub hXi (integrable_const c), integral_const]
    simp [Measure.real]
  -- Combine: E[(X-c)²] = Var[X-c] + (E[X-c])² = Var[X] + (E[X] - c)²
  have h4 : ∫ ω, (X ω - c) ^ 2 ∂μ = Var[fun ω => X ω - c; μ] +
      (∫ ω, (X ω - c) ∂μ) ^ 2 := by linarith
  rw [h4, h2, h3]

/-- **Rao-Blackwell Theorem (MSE reduction)**: conditioning on a sub-σ-algebra
reduces mean squared error. -/
theorem rb_mse_reduction
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ
      ≤
    ∫ ω, (Y ω - θ) ^ 2 ∂μ := by
  have hYG : MemLp (μ[Y|G]) 2 μ := hY.condExp
  -- Step 1: Var[E[Y|G]] ≤ Var[Y]  (from law of total variance)
  have h_var_le : Var[μ[Y|G]; μ] ≤ Var[Y; μ] := by
    have h_total := integral_condVar_add_variance_condExp hG hY
    have h_nonneg : 0 ≤ μ[Var[Y; μ | G]] := by
      apply integral_nonneg_of_ae
      exact condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)
    linarith
  -- Step 2: Tower property E[E[Y|G]] = E[Y]
  have h_tower : ∫ ω, μ[Y|G] ω ∂μ = ∫ ω, Y ω ∂μ := integral_condExp hG
  -- Step 3: Apply bias-variance decomposition to both sides
  rw [integral_sub_const_sq_eq _ θ hYG, integral_sub_const_sq_eq _ θ hY, h_tower]
  -- Goal: Var[E[Y|G]] + (E[Y] - θ)² ≤ Var[Y] + (E[Y] - θ)²
  linarith

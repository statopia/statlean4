import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integrable

/-! # Moments/Covariance

Covariance and correlation theorems, using Mathlib's `ProbabilityTheory.covariance`
and `ProbabilityTheory.variance`.

## Main results

* `variance_add_eq` — Var(X+Y) = Var(X) + 2Cov(X,Y) + Var(Y)
* `sq_covariance_le_variance_mul` — Cov(X,Y)² ≤ Var(X)·Var(Y) (Cauchy-Schwarz)
* `correlation_abs_le_one` — |ρ(X,Y)| ≤ 1
* `variance_sum_independent` — Var(X+Y) = Var(X) + Var(Y) for independent X,Y
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section VarianceAdd

/-- **Variance of a sum**: `Var(X+Y) = Var(X) + 2 Cov(X,Y) + Var(Y)`.
This is a direct restatement of `ProbabilityTheory.variance_add`. -/
theorem variance_add_eq [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ProbabilityTheory.variance (X + Y) μ =
      ProbabilityTheory.variance X μ + 2 * ProbabilityTheory.covariance X Y μ +
      ProbabilityTheory.variance Y μ :=
  ProbabilityTheory.variance_add hX hY

end VarianceAdd

section CauchySchwarz

/-- **Cauchy-Schwarz for covariance**: `Cov(X,Y)² ≤ Var(X) · Var(Y)`.

The proof uses the discriminant argument: for all `t : ℝ`,
`0 ≤ Var(X + t·Y)  =  Var(X) + 2t · Cov(X,Y) + t² · Var(Y)`.
Setting `t = -Cov(X,Y) / Var(Y)` forces the discriminant ≤ 0. -/
theorem sq_covariance_le_variance_mul [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ProbabilityTheory.covariance X Y μ ^ 2 ≤
      ProbabilityTheory.variance X μ * ProbabilityTheory.variance Y μ := by
  sorry -- BENCHMARK: proof removed for evaluation (C-level, Cauchy-Schwarz for covariance)

/-- **Correlation coefficient** of X and Y (using Mathlib's covariance/variance).
`ρ(X,Y) = Cov(X,Y) / (√Var(X) · √Var(Y))`.
Returns 0 when either variance is zero. -/
noncomputable def corrCoeff (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  if ProbabilityTheory.variance X μ = 0 ∨ ProbabilityTheory.variance Y μ = 0 then 0
  else ProbabilityTheory.covariance X Y μ /
       ((ProbabilityTheory.variance X μ).sqrt * (ProbabilityTheory.variance Y μ).sqrt)

/-- `|ρ(X,Y)| ≤ 1` (Cauchy-Schwarz). -/
theorem corrCoeff_abs_le_one [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |corrCoeff μ X Y| ≤ 1 := by
  unfold corrCoeff
  split_ifs with h
  · simp
  · push_neg at h
    obtain ⟨hvx, hvy⟩ := h
    have hvx_pos : 0 < ProbabilityTheory.variance X μ :=
      lt_of_le_of_ne (ProbabilityTheory.variance_nonneg X μ) (Ne.symm hvx)
    have hvy_pos : 0 < ProbabilityTheory.variance Y μ :=
      lt_of_le_of_ne (ProbabilityTheory.variance_nonneg Y μ) (Ne.symm hvy)
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_le_one (mul_pos (Real.sqrt_pos.mpr hvx_pos) (Real.sqrt_pos.mpr hvy_pos))]
    calc |ProbabilityTheory.covariance X Y μ|
        = (ProbabilityTheory.covariance X Y μ ^ 2).sqrt := by
          rw [Real.sqrt_sq_eq_abs]
      _ ≤ (ProbabilityTheory.variance X μ * ProbabilityTheory.variance Y μ).sqrt := by
          exact Real.sqrt_le_sqrt (sq_covariance_le_variance_mul hX hY)
      _ = (ProbabilityTheory.variance X μ).sqrt *
          (ProbabilityTheory.variance Y μ).sqrt := by
          exact Real.sqrt_mul (ProbabilityTheory.variance_nonneg X μ) _

end CauchySchwarz

section Independent

/-- For X, Y with zero covariance:
`Var(X+Y) = Var(X) + Var(Y)`. -/
theorem variance_sum_of_covariance_zero [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (h_cov : ProbabilityTheory.covariance X Y μ = 0) :
    ProbabilityTheory.variance (X + Y) μ =
      ProbabilityTheory.variance X μ + ProbabilityTheory.variance Y μ := by
  sorry -- BENCHMARK: proof removed for evaluation

/-- For independent X, Y: `Var(X+Y) = Var(X) + Var(Y)`. -/
theorem variance_sum_independent [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (h_ind : IndepFun X Y μ) :
    ProbabilityTheory.variance (X + Y) μ =
      ProbabilityTheory.variance X μ + ProbabilityTheory.variance Y μ := by
  sorry -- BENCHMARK: proof removed for evaluation

end Independent

end Statlean.Moments

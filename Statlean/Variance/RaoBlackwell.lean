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
  sorry -- BENCHMARK: proof removed for evaluation (A-level, bias-variance decomposition)

/-- **Rao-Blackwell Theorem (MSE reduction)**: conditioning on a sub-σ-algebra
reduces mean squared error. -/
theorem rb_mse_decomposition
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    ∫ ω, (Y ω - θ) ^ 2 ∂μ =
      ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ + μ[Var[Y; μ | G]] := by
  have hYG : MemLp (μ[Y|G]) 2 μ := hY.condExp
  have h_total := integral_condVar_add_variance_condExp hG hY
  have h_tower : ∫ ω, μ[Y|G] ω ∂μ = ∫ ω, Y ω ∂μ := integral_condExp hG
  rw [integral_sub_const_sq_eq _ θ hY, integral_sub_const_sq_eq _ θ hYG, h_tower]
  linarith

/-- Nonnegativity of integrated conditional variance. -/
lemma condVar_integral_nonneg
    (G : MeasurableSpace Ω)
    (Y : Ω → ℝ) :
    0 ≤ μ[Var[Y; μ | G]] := by
  apply integral_nonneg_of_ae
  exact condExp_nonneg (ae_of_all μ fun ω => sq_nonneg _)

/-- Law of total variance in Rao-Blackwell form:
`Var(Y) = Var(E[Y|G]) + E[Var(Y|G)]`. -/
theorem rb_variance_decomposition
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[Y; μ] = Var[μ[Y|G]; μ] + μ[Var[Y; μ | G]] := by
  simpa [add_comm] using (integral_condVar_add_variance_condExp (μ := μ) hG hY).symm

/-- Conditioning reduces variance: `Var(E[Y|G]) ≤ Var(Y)`. -/
theorem rb_variance_reduction
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[μ[Y|G]; μ] ≤ Var[Y; μ] := by
  have h_nonneg : 0 ≤ μ[Var[Y; μ | G]] :=
    condVar_integral_nonneg (μ := μ) (m₀ := m₀) G Y
  have h_decomp := rb_variance_decomposition (μ := μ) G hG Y hY
  linarith

/-- Exact variance gap identity for Rao-Blackwell:
`Var(Y) - Var(E[Y|G]) = E[Var(Y|G)]`. -/
theorem rb_variance_gap_eq_condVar
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    Var[Y; μ] - Var[μ[Y|G]; μ] = μ[Var[Y; μ | G]] := by
  have h_decomp := rb_variance_decomposition (μ := μ) G hG Y hY
  linarith

/-- The variance improvement gap in Rao-Blackwell is always nonnegative. -/
theorem rb_variance_gap_nonneg
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    0 ≤ Var[Y; μ] - Var[μ[Y|G]; μ] := by
  have h_nonneg : 0 ≤ μ[Var[Y; μ | G]] :=
    condVar_integral_nonneg (μ := μ) (m₀ := m₀) G Y
  have h_gap := rb_variance_gap_eq_condVar (μ := μ) G hG Y hY
  linarith

/-- Equality case for variance reduction in Rao-Blackwell. -/
theorem rb_variance_reduction_eq_iff_condVar_zero
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    (Var[μ[Y|G]; μ] = Var[Y; μ]) ↔
    μ[Var[Y; μ | G]] = 0 := by
  have h_gap := rb_variance_gap_eq_condVar (μ := μ) G hG Y hY
  constructor
  · intro hEq
    linarith
  · intro hZero
    linarith

/-- If `Y` is already `G`-measurable, conditioning does not change variance. -/
theorem rb_variance_reduction_eq_of_stronglyMeasurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[G] Y) :
    Var[μ[Y|G]; μ] = Var[Y; μ] := by
  have hYint : Integrable Y μ := hY.integrable one_le_two
  have hce : μ[Y|G] = Y :=
    condExp_of_stronglyMeasurable (μ := μ) (m := G) hG hYm hYint
  simp [hce]

/-- Measurable version of `rb_variance_reduction_eq_of_stronglyMeasurable`. -/
theorem rb_variance_reduction_eq_of_measurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : Measurable[G] Y) :
    Var[μ[Y|G]; μ] = Var[Y; μ] :=
  rb_variance_reduction_eq_of_stronglyMeasurable (μ := μ) G hG Y hY hYm.stronglyMeasurable

/-- Pythagorean form of Rao-Blackwell:
`MSE(Y) = MSE(E[Y|G]) + E[(Y - E[Y|G])²]`. -/
theorem rb_mse_pythagorean
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    ∫ ω, (Y ω - θ) ^ 2 ∂μ =
      ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ +
      ∫ ω, (Y ω - μ[Y|G] ω) ^ 2 ∂μ := by
  have h_decomp := rb_mse_decomposition (μ := μ) G hG Y θ hY
  have hYres : Integrable (fun ω => (Y ω - μ[Y|G] ω) ^ 2) μ := by
    exact (hY.sub hY.condExp).integrable_sq
  have h_condVar :
      μ[Var[Y; μ | G]] = ∫ ω, (Y ω - μ[Y|G] ω) ^ 2 ∂μ := by
    calc
      μ[Var[Y; μ | G]] = ∫ ω in Set.univ, (Var[Y; μ | G]) ω ∂μ := by simp
      _ = ∫ ω in Set.univ, (Y ω - (μ[Y|G]) ω) ^ 2 ∂μ :=
        setIntegral_condVar (m := G) (hm := hG) (μ := μ) (X := Y) (s := Set.univ) hYres
          (by simp)
      _ = ∫ ω, (Y ω - μ[Y|G] ω) ^ 2 ∂μ := by simp
  linarith

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
  have h_nonneg : 0 ≤ μ[Var[Y; μ | G]] :=
    condVar_integral_nonneg (μ := μ) (m₀ := m₀) G Y
  have h_decomp := rb_mse_decomposition (μ := μ) G hG Y θ hY
  linarith

/-- The Rao-Blackwell improvement gap equals the integral of conditional variance,
hence is nonnegative. -/
theorem rb_mse_gap_nonneg
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    0 ≤
      (∫ ω, (Y ω - θ) ^ 2 ∂μ) -
      (∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ) := by
  have h_nonneg : 0 ≤ μ[Var[Y; μ | G]] :=
    condVar_integral_nonneg (μ := μ) (m₀ := m₀) G Y
  have h_decomp := rb_mse_decomposition (μ := μ) G hG Y θ hY
  linarith

/-- Exact Rao-Blackwell gap identity:
`MSE(Y) - MSE(E[Y|G]) = E[Var(Y|G)]`. -/
theorem rb_mse_gap_eq_condVar
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    (∫ ω, (Y ω - θ) ^ 2 ∂μ) -
      (∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ) =
    μ[Var[Y; μ | G]] := by
  have h_decomp := rb_mse_decomposition (μ := μ) G hG Y θ hY
  linarith

/-- Equality case for Rao-Blackwell MSE reduction. -/
theorem rb_mse_reduction_eq_iff_condVar_zero
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    (∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ =
      ∫ ω, (Y ω - θ) ^ 2 ∂μ) ↔
    μ[Var[Y; μ | G]] = 0 := by
  have h_gap := rb_mse_gap_eq_condVar (μ := μ) G hG Y θ hY
  constructor
  · intro hEq
    linarith
  · intro hZero
    linarith

/-- If `Y` is already `G`-measurable, Rao-Blackwell does not change MSE. -/
theorem rb_mse_reduction_eq_of_stronglyMeasurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[G] Y) :
    ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ =
      ∫ ω, (Y ω - θ) ^ 2 ∂μ := by
  have hYint : Integrable Y μ := hY.integrable one_le_two
  have hce : μ[Y|G] = Y :=
    condExp_of_stronglyMeasurable (μ := μ) (m := G) hG hYm hYint
  simp [hce]

/-- Measurable version of `rb_mse_reduction_eq_of_stronglyMeasurable`. -/
theorem rb_mse_reduction_eq_of_measurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : Measurable[G] Y) :
    ∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ =
      ∫ ω, (Y ω - θ) ^ 2 ∂μ :=
  rb_mse_reduction_eq_of_stronglyMeasurable (μ := μ) G hG Y θ hY hYm.stronglyMeasurable

/-- If `Y` is already `G`-measurable, then the integrated conditional variance vanishes. -/
theorem condVar_integral_eq_zero_of_stronglyMeasurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[G] Y) :
    μ[Var[Y; μ | G]] = 0 := by
  have hVarEq : Var[μ[Y|G]; μ] = Var[Y; μ] :=
    rb_variance_reduction_eq_of_stronglyMeasurable (μ := μ) G hG Y hY hYm
  exact (rb_variance_reduction_eq_iff_condVar_zero (μ := μ) G hG Y hY).1 hVarEq

/-- Measurable version of `condVar_integral_eq_zero_of_stronglyMeasurable`. -/
theorem condVar_integral_eq_zero_of_measurable
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ)
    (hYm : Measurable[G] Y) :
    μ[Var[Y; μ | G]] = 0 :=
  condVar_integral_eq_zero_of_stronglyMeasurable (μ := μ) G hG Y hY hYm.stronglyMeasurable

/-- Equality in MSE reduction is equivalent to equality in variance reduction. -/
theorem rb_mse_reduction_eq_iff_variance_reduction_eq
    (G : MeasurableSpace Ω) (hG : G ≤ m₀)
    (Y : Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure μ]
    (hY : MemLp Y 2 μ) :
    (∫ ω, (μ[Y|G] ω - θ) ^ 2 ∂μ =
      ∫ ω, (Y ω - θ) ^ 2 ∂μ) ↔
    (Var[μ[Y|G]; μ] = Var[Y; μ]) := by
  constructor
  · intro hMSE
    have hZero : μ[Var[Y; μ | G]] = 0 :=
      (rb_mse_reduction_eq_iff_condVar_zero (μ := μ) G hG Y θ hY).1 hMSE
    exact (rb_variance_reduction_eq_iff_condVar_zero (μ := μ) G hG Y hY).2 hZero
  · intro hVar
    have hZero : μ[Var[Y; μ | G]] = 0 :=
      (rb_variance_reduction_eq_iff_condVar_zero (μ := μ) G hG Y hY).1 hVar
    exact (rb_mse_reduction_eq_iff_condVar_zero (μ := μ) G hG Y θ hY).2 hZero

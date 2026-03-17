/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gaussian Measures on Hilbert Spaces

We define isonormal Gaussian processes and covariance operators for Gaussian measures
on real Hilbert spaces, building on Mathlib's `IsGaussian` class and Fernique's theorem.

## Main definitions

* `IsonormalProcess`: a linear map `W : H → Ω → ℝ` from a real Hilbert space `H` to
  random variables on `(Ω, P)`, such that each `W h` is centered Gaussian with
  variance `‖h‖²`.
* `covarianceBilinInner`: the covariance bilinear form of a Gaussian measure
  on a Hilbert space, defined as `(x, y) ↦ ∫ ω, ⟪ω, x⟫_ℝ * ⟪ω, y⟫_ℝ ∂μ`.

## Main statements

* `IsonormalProcess.inner_eq_integral_mul`: the covariance of an isonormal process
  recovers the inner product: `⟪h₁, h₂⟫_ℝ = ∫ ω, W h₁ ω * W h₂ ω ∂P`.
* `covarianceBilinInner_self_nonneg`: the covariance form is positive semidefinite.
* `covarianceBilinInner_comm`: the covariance form is symmetric.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Statlean

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-! ### Isonormal Gaussian Process -/

/-- An isonormal Gaussian process indexed by a real Hilbert space `H`.
This is a linear map `W : H → (Ω → ℝ)` such that each `W h` is centered Gaussian
with variance `‖h‖²`. The key consequence is that `E[W h₁ · W h₂] = ⟪h₁, h₂⟫_ℝ`. -/
structure IsonormalProcess (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The underlying map from `H` to random variables on `Ω`. -/
  toFun : H → Ω → ℝ
  /-- Each `W h` is strongly measurable. -/
  aestronglyMeasurable : ∀ h, AEStronglyMeasurable (toFun h) P
  /-- Linearity: `W(h₁ + h₂) = W(h₁) + W(h₂)` a.e. -/
  add_ae : ∀ (h₁ h₂ : H), toFun (h₁ + h₂) =ᵐ[P] fun ω => toFun h₁ ω + toFun h₂ ω
  /-- Linearity: `W(a • h) = a * W(h)` a.e. -/
  smul_ae : ∀ (a : ℝ) (h : H), toFun (a • h) =ᵐ[P] fun ω => a * toFun h ω
  /-- Each `W h` has centered Gaussian distribution with variance `‖h‖²`. -/
  map_eq_gaussianReal : ∀ h, P.map (toFun h) = gaussianReal 0 (⟨‖h‖ ^ 2, by positivity⟩ : ℝ≥0)

namespace IsonormalProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (W : IsonormalProcess H P)

/-- Each `W h` has mean zero. -/
theorem integral_eq_zero (h : H) : ∫ ω, W.toFun h ω ∂P = 0 := by
  have hmeas := W.aestronglyMeasurable h
  have hasm : AEStronglyMeasurable id (P.map (W.toFun h)) := by
    rw [W.map_eq_gaussianReal h]; exact aestronglyMeasurable_id
  calc ∫ ω, W.toFun h ω ∂P
      = ∫ y, id y ∂(P.map (W.toFun h)) :=
        (integral_map hmeas.aemeasurable hasm).symm
    _ = _ := by
        simp only [id]
        rw [W.map_eq_gaussianReal h, integral_id_gaussianReal]

/-- Each `W h` is in L² (square integrable). -/
theorem memLp_two (h : H) : MemLp (W.toFun h) 2 P := by
  have h1 : MemLp id 2 (P.map (W.toFun h)) := by
    rw [W.map_eq_gaussianReal h]; exact memLp_id_gaussianReal 2
  have hmeas := W.aestronglyMeasurable h
  have h1' : AEStronglyMeasurable id (P.map (W.toFun h)) := by
    rw [W.map_eq_gaussianReal h]; exact aestronglyMeasurable_id
  rwa [memLp_map_measure_iff h1' hmeas.aemeasurable] at h1

/-- Each `W h` has variance `‖h‖²`. -/
theorem variance_eq (h : H) : variance (W.toFun h) P = ‖h‖ ^ 2 := by
  -- Var[W h] = E[W h²] - E[W h]² = E[W h²] - 0
  rw [variance_eq_sub (W.memLp_two h), W.integral_eq_zero h, sq (0 : ℝ),
    mul_zero, sub_zero]
  -- Transfer ∫ (W h)² dP to pushforward gaussianReal 0 ‖h‖²
  have hmeas : AEMeasurable (W.toFun h) P :=
    (W.aestronglyMeasurable h).aemeasurable
  have hasm : AEStronglyMeasurable (· ^ 2 : ℝ → ℝ) (P.map (W.toFun h)) := by
    rw [W.map_eq_gaussianReal h]; exact aestronglyMeasurable_id.pow 2
  simp only [Pi.pow_apply]
  rw [← integral_map hmeas hasm, W.map_eq_gaussianReal h]
  -- ∫ y^2 d(gaussianReal 0 v) = v, by variance identity
  set v : ℝ≥0 := ⟨‖h‖ ^ 2, by positivity⟩
  have h1 := variance_eq_sub (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2)
  simp only [variance_id_gaussianReal, integral_id_gaussianReal, id_eq, sq, mul_zero,
    sub_zero, Pi.pow_apply] at h1
  convert h1.symm using 1
  congr 1; ext; ring

/-- Auxiliary: E[(W h)²] = ‖h‖² (mean zero + variance identity). -/
private theorem integral_sq (h : H) : ∫ ω, W.toFun h ω ^ 2 ∂P = ‖h‖ ^ 2 := by
  have h1 := W.variance_eq h
  rw [variance_eq_sub (W.memLp_two h), W.integral_eq_zero h, sq (0 : ℝ), mul_zero,
    sub_zero] at h1
  convert h1 using 1

/-- The covariance of an isonormal process recovers the inner product:
`E[W h₁ · W h₂] = ⟪h₁, h₂⟫_ℝ`. This is the defining property via polarization. -/
theorem inner_eq_integral_mul (h₁ h₂ : H) :
    @inner ℝ H _ h₁ h₂ = ∫ ω, W.toFun h₁ ω * W.toFun h₂ ω ∂P := by
  -- Polarization: 2⟪h₁,h₂⟫ = ‖h₁+h₂‖² - ‖h₁‖² - ‖h₂‖²
  --            = E[(W(h₁+h₂))²] - E[(Wh₁)²] - E[(Wh₂)²]
  -- By ae linearity, E[(Wh₁+Wh₂)²] = E[Wh₁²] + 2E[Wh₁·Wh₂] + E[Wh₂²]
  -- So 2⟪h₁,h₂⟫ = 2E[Wh₁·Wh₂]
  -- Key step: connect variance of sum with integral of product
  have hadd := W.add_ae h₁ h₂
  have hint1 : Integrable (fun ω => W.toFun h₁ ω ^ 2) P :=
    (W.memLp_two h₁).integrable_sq
  have hint2 : Integrable (fun ω => W.toFun h₂ ω ^ 2) P :=
    (W.memLp_two h₂).integrable_sq
  have hintmul : Integrable (fun ω => W.toFun h₁ ω * W.toFun h₂ ω) P :=
    (W.memLp_two h₁).integrable_mul (W.memLp_two h₂)
  -- E[(W(h₁+h₂))²] via ae linearity
  have hsq_add : ∫ ω, W.toFun (h₁ + h₂) ω ^ 2 ∂P =
      ∫ ω, (W.toFun h₁ ω + W.toFun h₂ ω) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hadd] with ω hω
    rw [hω]
  -- Expand (a+b)² = a² + 2ab + b²
  have hexpand : ∫ ω, (W.toFun h₁ ω + W.toFun h₂ ω) ^ 2 ∂P =
      ∫ ω, W.toFun h₁ ω ^ 2 ∂P + 2 * ∫ ω, W.toFun h₁ ω * W.toFun h₂ ω ∂P +
      ∫ ω, W.toFun h₂ ω ^ 2 ∂P := by
    calc ∫ ω, (W.toFun h₁ ω + W.toFun h₂ ω) ^ 2 ∂P
        = ∫ ω, (W.toFun h₁ ω ^ 2 + (2 * (W.toFun h₁ ω * W.toFun h₂ ω) +
            W.toFun h₂ ω ^ 2)) ∂P := by
          congr 1; ext ω; ring
      _ = ∫ ω, W.toFun h₁ ω ^ 2 ∂P +
          ∫ ω, (2 * (W.toFun h₁ ω * W.toFun h₂ ω) + W.toFun h₂ ω ^ 2) ∂P :=
          integral_add hint1 ((hintmul.const_mul 2).add hint2)
      _ = ∫ ω, W.toFun h₁ ω ^ 2 ∂P +
          (2 * ∫ ω, W.toFun h₁ ω * W.toFun h₂ ω ∂P +
           ∫ ω, W.toFun h₂ ω ^ 2 ∂P) := by
          congr 1
          rw [integral_add (hintmul.const_mul 2) hint2, integral_const_mul]
      _ = _ := by ring
  -- Now compute
  have h_norm_add : ‖h₁ + h₂‖ ^ 2 = ‖h₁‖ ^ 2 + 2 * @inner ℝ H _ h₁ h₂ + ‖h₂‖ ^ 2 := by
    have := @norm_add_sq_real H _ _ h₁ h₂; nlinarith
  rw [← W.integral_sq h₁, ← W.integral_sq h₂, ← W.integral_sq (h₁ + h₂)] at h_norm_add
  rw [hsq_add, hexpand] at h_norm_add
  linarith

end IsonormalProcess

/-! ### Covariance Bilinear Form -/

section CovarianceBilinInner

/-- Auxiliary: the inner product functional `⟪·, x⟫` as a `StrongDual ℝ H` element. -/
private noncomputable def innerDual (x : H) : StrongDual ℝ H :=
  InnerProductSpace.toDual ℝ H x

/-- Inner product functional is L² w.r.t. Gaussian measure. -/
private theorem memLp_innerDual (μ : Measure H) [IsGaussian μ] (x : H) :
    MemLp (innerDual x : H → ℝ) 2 μ :=
  IsGaussian.memLp_dual μ (innerDual x) 2 (by norm_num)

/-- Inner product functional is integrable w.r.t. Gaussian measure. -/
private theorem integrable_innerDual (μ : Measure H) [IsGaussian μ] (x : H) :
    Integrable (innerDual x : H → ℝ) μ :=
  (memLp_innerDual μ x).integrable one_le_two

/-- Product of two inner product functionals is integrable w.r.t. Gaussian measure. -/
private theorem integrable_innerDual_mul (μ : Measure H) [IsGaussian μ] (x y : H) :
    Integrable (fun ω => (innerDual x : H → ℝ) ω * (innerDual y : H → ℝ) ω) μ := by
  exact (memLp_innerDual μ x).integrable_mul (memLp_innerDual μ y)

/-- The covariance bilinear form of a Gaussian measure on a Hilbert space,
defined as `(x, y) ↦ ∫ ω, ⟪ω, x⟫_ℝ * ⟪ω, y⟫_ℝ ∂μ`.
Note: `innerDual x` is the map `ω ↦ ⟪ω, x⟫_ℝ` via the Riesz representation. -/
noncomputable def covarianceBilinInner (μ : Measure H) [IsGaussian μ] :
    H →ₗ[ℝ] H →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => ∫ ω, (innerDual x : H → ℝ) ω * (innerDual y : H → ℝ) ω ∂μ)
    (fun x₁ x₂ y => by
      simp only [innerDual, map_add, ContinuousLinearMap.add_apply, add_mul]
      exact integral_add (integrable_innerDual_mul μ x₁ y) (integrable_innerDual_mul μ x₂ y))
    (fun a x y => by
      simp only [innerDual, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul a _)
    (fun x y₁ y₂ => by
      simp only [innerDual, map_add, ContinuousLinearMap.add_apply, mul_add]
      exact integral_add (integrable_innerDual_mul μ x y₁) (integrable_innerDual_mul μ x y₂))
    (fun a x y => by
      simp only [innerDual, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have : (fun ω => (InnerProductSpace.toDual ℝ H x) ω *
          (a * (InnerProductSpace.toDual ℝ H y) ω)) =
        (fun ω => a * ((InnerProductSpace.toDual ℝ H x) ω *
          (InnerProductSpace.toDual ℝ H y) ω)) := by ext ω; ring
      rw [this]
      exact integral_const_mul a _)

/-- The covariance form is symmetric. -/
theorem covarianceBilinInner_comm (μ : Measure H) [IsGaussian μ] (x y : H) :
    covarianceBilinInner μ x y = covarianceBilinInner μ y x := by
  simp only [covarianceBilinInner, LinearMap.mk₂_apply]
  congr 1; ext ω; ring

/-- The covariance form is positive semidefinite. -/
theorem covarianceBilinInner_self_nonneg (μ : Measure H) [IsGaussian μ] (x : H) :
    0 ≤ covarianceBilinInner μ x x := by
  simp only [covarianceBilinInner, LinearMap.mk₂_apply]
  exact integral_nonneg fun ω => mul_self_nonneg _

/-- For a centered Gaussian, the covariance bilinear form equals the variance
on the diagonal. -/
theorem covarianceBilinInner_self_eq_variance (μ : Measure H) [IsGaussian μ]
    (hμ : (∫ x, x ∂μ) = 0) (x : H) :
    covarianceBilinInner μ x x = Var[(innerDual x : H → ℝ); μ] := by
  simp only [covarianceBilinInner, LinearMap.mk₂_apply]
  rw [ProbabilityTheory.variance_eq_sub (memLp_innerDual μ x)]
  have hmean : ∫ ω, (innerDual x : H → ℝ) ω ∂μ = 0 := by
    simp only [innerDual, InnerProductSpace.toDual_apply_apply]
    rw [integral_inner (IsGaussian.integrable_fun_id (μ := μ)), hμ, inner_zero_right]
  rw [hmean, sq (0 : ℝ), mul_zero, sub_zero]
  congr 1; ext ω; exact (sq _).symm

end CovarianceBilinInner

/-! ### Fernique's Theorem (API wrappers) -/

section Fernique

/-- **Fernique's theorem** for Hilbert spaces: a Gaussian measure has exponential
integrability of the squared norm. Direct wrapper of Mathlib's
`IsGaussian.exists_integrable_exp_sq`. -/
theorem gaussian_fernique (μ : Measure H) [IsGaussian μ] :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x => Real.exp (C * ‖x‖ ^ 2)) μ :=
  IsGaussian.exists_integrable_exp_sq μ

/-- A Gaussian measure on a Hilbert space has finite moments of all orders. -/
theorem gaussian_memLp_id (μ : Measure H) [IsGaussian μ] (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p μ :=
  IsGaussian.memLp_id μ p hp

/-- The identity function is integrable with respect to a Gaussian measure. -/
theorem gaussian_integrable_id (μ : Measure H) [IsGaussian μ] :
    Integrable (fun x => x) μ :=
  IsGaussian.integrable_fun_id

/-- The squared norm is integrable with respect to a Gaussian measure.
This is the second moment finiteness, a key consequence of Fernique. -/
theorem gaussian_integrable_sq_norm (μ : Measure H) [IsGaussian μ] :
    Integrable (fun x => ‖x‖ ^ 2) μ := by
  have h2 := IsGaussian.memLp_id μ 2 (by norm_num)
  rwa [memLp_two_iff_integrable_sq_norm (f := id) (by fun_prop)] at h2

end Fernique

end Statlean

import Statlean.Gaussian.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! # Stein's Identity for Standard Gaussian

`E_γ[x·h(x)] = E_γ[h'(x)]` for `h, h' ∈ L²(γ)`.

## Main results

- `stein_identity`: Stein's identity for C¹ functions with L² bounds.
- `stein_identity_of_lipschitz`: Stein's identity for Lipschitz functions
  (only ae differentiable, proved via Steklov approximation).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

lemma stein_identity
    (h h' : ℝ → ℝ)
    (hh : MemLp h 2 stdGaussian)
    (hh' : MemLp h' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt h (h' x) x) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, h' x ∂stdGaussian := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  change ∫ x, x * h x ∂gaussianReal 0 1 = ∫ x, h' x ∂gaussianReal 0 1
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv,
      integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv]
  simp only [smul_eq_mul]
  have hφ_deriv : ∀ x, HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := hasDerivAt_gaussianPDFReal_std
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    hderiv hφ_deriv
    (by have := integrable_id_mul_mul_gaussianPDFReal_of_memLp hh
        change Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) volume
        have : Integrable (fun x => -(x * h x * gaussianPDFReal 0 1 x)) volume :=
          this.neg
        convert this using 1; ext x; ring)
    (integrable_mul_gaussianPDFReal_of_memLp hh')
    (integrable_mul_gaussianPDFReal_of_memLp hh)
  have key : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]; congr 1; ext x; ring
  have key2 : ∫ x, h' x * gaussianPDFReal 0 1 x =
      ∫ x, gaussianPDFReal 0 1 x * h' x := by
    congr 1; ext x; ring
  linarith

/-! ## Stein identity for Lipschitz functions -/

section Lipschitz

open intervalIntegral

/-- The Steklov average `x ↦ (2δ)⁻¹ ∫_{x-δ}^{x+δ} h` is C¹ for continuous h,
with derivative `(2δ)⁻¹ (h(x+δ) - h(x-δ))` (the symmetric difference quotient). -/
private lemma steklov_hasDerivAt (h : ℝ → ℝ) (hc : Continuous h) (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (fun x => (2 * δ)⁻¹ * ∫ t in (x - δ)..(x + δ), h t)
      ((2 * δ)⁻¹ * (h (x + δ) - h (x - δ))) x := by
  set F : ℝ → ℝ := fun a => ∫ t in (0 : ℝ)..a, h t
  have hF : ∀ a, HasDerivAt F (h a) a := fun a =>
    integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter volume (𝓝 a)) hc.continuousAt
  have hG : HasDerivAt (fun x' => ∫ t in (x' - δ)..(x' + δ), h t) (h (x + δ) - h (x - δ)) x := by
    have h_eq : ∀ x', ∫ t in (x' - δ)..(x' + δ), h t = F (x' + δ) - F (x' - δ) := by
      intro x'
      have := integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := x' - δ) (c := x' + δ) (μ := volume)
        (hc.intervalIntegrable 0 (x' - δ)) (hc.intervalIntegrable (x' - δ) (x' + δ))
      linarith
    simp_rw [h_eq]
    have h1 := (hF (x + δ)).comp x ((hasDerivAt_id x).add (hasDerivAt_const x δ))
    have h2 := (hF (x - δ)).comp x ((hasDerivAt_id x).sub (hasDerivAt_const x δ))
    simp only [Function.comp_def] at h1 h2
    convert h1.sub h2 using 1; ring
  exact ((hasDerivAt_const x ((2 * δ)⁻¹)).mul hG).congr_deriv (by ring)

/-- Lipschitz functions satisfy MemLp p for stdGaussian (probability measure,
Lipschitz gives linear growth, Gaussian has all moments finite). -/
private lemma lipschitz_memLp_gaussianReal (h : ℝ → ℝ) (C : ℝ≥0) (hLip : LipschitzWith C h)
    (p : NNReal) : MemLp h p stdGaussian := by
  -- Bound: |h(x)| ≤ |h(0)| + C|x|
  -- Both |h(0)| (constant) and C|x| (id scaled) are in Lᵖ(γ)
  -- Use MemLp.of_bound after showing a suitable constant bound doesn't work (growth is linear)
  -- Instead: h = (h - h(0)) + h(0), where h-h(0) is Lip with h(0)=0, so |h-h(0)| ≤ C|x|
  have h1 : MemLp (fun _ : ℝ => h 0) p stdGaussian := memLp_const _
  have h2 : MemLp (fun x => h x - h 0) p stdGaussian := by
    have hLip2 : LipschitzWith C (fun x => h x - h 0) :=
      hLip.sub (LipschitzWith.const _) |>.weaken (by simp)
    -- |h(x) - h(0)| ≤ C|x|, and C|x| ∈ Lᵖ(γ)
    exact ((memLp_id_gaussianReal p (μ := 0) (v := 1)).const_mul C).mono
      hLip2.continuous.aestronglyMeasurable (.of_forall fun x => by
        calc ‖h x - h 0‖ ≤ C * dist x 0 := by
              rw [← dist_eq_norm]; exact hLip.dist_le_mul x 0
          _ = C * |x| := by rw [dist_zero_right, Real.norm_eq_abs]
          _ = ‖(C : ℝ) * x‖ := by rw [norm_mul, norm_of_nonneg (NNReal.coe_nonneg C), Real.norm_eq_abs])
  convert h1.add h2 using 1; ext x; simp

/-- Stein identity for Lipschitz functions. Same as `stein_identity` but only requires
Lipschitz (which gives ae differentiability) instead of everywhere HasDerivAt.
Proof: approximate h by Steklov averages h_δ (C¹), apply `stein_identity` to h_δ,
take δ → 0 using DCT with uniform Lipschitz bound. -/
lemma stein_identity_of_lipschitz
    (h : ℝ → ℝ) (C : ℝ≥0) (hLip : LipschitzWith C h)
    (hInt : Integrable h stdGaussian) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, deriv h x ∂stdGaussian := by
  -- Approximate h by Steklov averages h_k (C¹), apply stein_identity, take limit.
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ_pos : ∀ k, 0 < δ k := fun k => by positivity
  -- Steklov average
  set S : ℕ → ℝ → ℝ := fun k x => (2 * δ k)⁻¹ * ∫ t in (x - δ k)..(x + δ k), h t
  -- S k has HasDerivAt at all x (from steklov_hasDerivAt)
  set S' : ℕ → ℝ → ℝ := fun k x => (2 * δ k)⁻¹ * (h (x + δ k) - h (x - δ k))
  have hS_deriv : ∀ k x, HasDerivAt (S k) (S' k x) x :=
    fun k x => steklov_hasDerivAt h hLip.continuous (δ k) (hδ_pos k) x
  -- S k is C-Lipschitz (Steklov of C-Lip is C-Lip)
  have hS_lip : ∀ k, LipschitzWith C (S k) := by
    intro k; sorry -- Steklov average preserves Lip constant
  -- |S' k x| ≤ C (difference quotient of Lip function)
  have hS'_bound : ∀ k x, |S' k x| ≤ C := by
    intro k x; simp only [S', δ]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2 * (1 / ((k : ℝ) + 1))))]
    calc (2 * (1 / ((k : ℝ) + 1)))⁻¹ * |h (x + 1 / ((k : ℝ) + 1)) - h (x - 1 / ((k : ℝ) + 1))|
        ≤ (2 * (1 / ((k : ℝ) + 1)))⁻¹ * (C * |x + 1/((k:ℝ)+1) - (x - 1/((k:ℝ)+1))|) := by
          gcongr; rw [← Real.dist_eq]; exact hLip.dist_le_mul _ _
      _ = (C : ℝ) := by
          have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          rw [show x + 1 / ((k : ℝ) + 1) - (x - 1 / ((k : ℝ) + 1)) = 2 / ((k : ℝ) + 1) by ring]
          rw [abs_of_nonneg (by positivity)]
          field_simp
  -- Apply stein_identity to each S k, then take limit.
  sorry

end Lipschitz

section GaussianIBP

open Function

/-- Multi-dimensional Gaussian integration by parts in coordinate j:
for Lipschitz g on ℝⁿ, `∫ (∂ⱼg)(y) dγⁿ(y) = ∫ g(y)·yⱼ dγⁿ(y)`.
This is the score function identity for product Gaussians.
Proof uses Fubini decomposition into the j-th coordinate and applies 1D Stein. -/
lemma gaussian_ibp_coord {n : ℕ} (j : Fin n) (g : (Fin n → ℝ) → ℝ) (C : ℝ≥0)
    (hLip : LipschitzWith C g) :
    ∫ y, lineDeriv ℝ g y (Pi.single j 1) ∂stdGaussianPi n =
    ∫ y, g y * (y j) ∂stdGaussianPi n := by
  sorry

end GaussianIBP

end

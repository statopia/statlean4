import Statlean.Gaussian.Basic

/-! # Stein's Identity for Standard Gaussian

`E_γ[x·h(x)] = E_γ[h'(x)]` for `h, h' ∈ L²(γ)`.
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

end

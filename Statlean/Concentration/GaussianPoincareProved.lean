import Statlean.Concentration.EfronSteinProved
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Gaussian Poincaré — Proved Declarations (zero sorry)

This file contains all sorry-free declarations extracted from
`GaussianPoincare.lean`:

- `stdGaussian`, `stdGaussianPi`: standard Gaussian measures
- Integrability infrastructure for Gaussian density
- `memLp_pow_id_gaussianReal`, `memLp_polynomial_gaussianReal`:
  polynomial × Gaussian integrability
- `hasDerivAt_gaussianPDFReal_std`: Gaussian density derivative
- **`stein_identity`**: `E_γ[x·h(x)] = E_γ[h'(x)]`
- `gaussian_poincare_of_integral_bound`, `gaussian_poincare_of_efron_stein`,
  `gaussian_poincare_of_condVar_sum`: clean wrappers (hypotheses passed in)

All declarations in this file are fully proved with zero sorry.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

/-- Standard Gaussian measure on ℝ: N(0,1). -/
abbrev stdGaussian : Measure ℝ := gaussianReal 0 1

/-- Standard n-dimensional Gaussian as product measure on `Fin n → ℝ`. -/
def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => stdGaussian)

/-! ## Integrability infrastructure for Gaussian density

Key chain: `MemLp h 2 γ → Integrable h γ` (finite measure) and
`Integrable h γ ↔ Integrable (h * φ) volume` via `integrable_withDensity_iff`.
-/

/-- If `h ∈ L²(γ)`, then `h · φ ∈ L¹(Lebesgue)` where `φ` is the Gaussian density. -/
lemma integrable_mul_gaussianPDFReal_of_memLp {g : ℝ → ℝ} (hg : MemLp g 2 stdGaussian) :
    Integrable (fun x => g x * gaussianPDFReal 0 1 x) volume := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hg_int : Integrable g stdGaussian := hg.integrable one_le_two
  rw [show (stdGaussian : Measure ℝ) = volume.withDensity (gaussianPDF 0 1)
      from gaussianReal_of_var_ne_zero 0 hv] at hg_int
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hg_int
  simp only [toReal_gaussianPDF] at hg_int
  exact hg_int

/-- If `h ∈ L²(γ)`, then `x * h(x) * φ(x) ∈ L¹(Lebesgue)`. -/
lemma integrable_id_mul_mul_gaussianPDFReal_of_memLp {g : ℝ → ℝ}
    (hg : MemLp g 2 stdGaussian) :
    Integrable (fun x => x * g x * gaussianPDFReal 0 1 x) volume := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hid : MemLp id 2 stdGaussian := memLp_id_gaussianReal' 2 (by norm_num)
  have hprod : Integrable (id * g) stdGaussian := hid.integrable_mul hg
  have hprod' : Integrable (fun x => x * g x) stdGaussian := by
    convert hprod using 1
  rw [show (stdGaussian : Measure ℝ) = volume.withDensity (gaussianPDF 0 1)
      from gaussianReal_of_var_ne_zero 0 hv] at hprod'
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hprod'
  simp only [toReal_gaussianPDF] at hprod'
  exact hprod'

/-! ## Polynomial × Gaussian integrability

Power functions `x^n` are in all finite `Lp` spaces under any Gaussian measure.
This extends to arbitrary polynomial evaluations via structural induction, and
to products with the Gaussian density via `integrable_withDensity_iff`.
These results are needed for Hermite orthogonality arguments.
-/

open Polynomial in
/-- `(fun x => x ^ n)` is in `Lp q` under any Gaussian measure for finite `q`.

**Proof**: By induction on `n`. Base: `x^0 = 1` is in all `Lp` (probability measure).
Step: `x^(n+1) = id * x^n` via Hölder with `1/q = 1/(2q) + 1/(2q)`. -/
private lemma memLp_pow_id_gaussianReal_aux {μ₀ : ℝ} {v : ℝ≥0} (n : ℕ) :
    ∀ (q : ℝ≥0∞), q ≠ ⊤ → MemLp (fun x : ℝ => x ^ n) q (gaussianReal μ₀ v) := by
  induction n with
  | zero => intro q _; simp only [pow_zero]; exact memLp_const 1
  | succ n ih =>
    intro q hq
    have h2q : 2 * q ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hq
    have hid_2q : MemLp id (2 * q) (gaussianReal μ₀ v) :=
      memLp_id_gaussianReal' (2 * q) h2q
    have hpow_2q : MemLp (fun x : ℝ => x ^ n) (2 * q) (gaussianReal μ₀ v) :=
      ih (2 * q) h2q
    have hHolder : ENNReal.HolderTriple (2 * q) (2 * q) q := by
      constructor
      have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [ENNReal.mul_inv (Or.inl h2ne0) (Or.inl h2ne_top)]
      rw [← two_mul]
      rw [← mul_assoc, ENNReal.mul_inv_cancel h2ne0 h2ne_top, one_mul]
    have hmul : MemLp (fun x : ℝ => id x * x ^ n) q (gaussianReal μ₀ v) :=
      hpow_2q.mul' hid_2q (hpqr := hHolder)
    have heq : (fun x : ℝ => id x * x ^ n) =ᵐ[gaussianReal μ₀ v]
        (fun x : ℝ => x ^ (n + 1)) :=
      Filter.Eventually.of_forall fun x => by simp [pow_succ, mul_comm]
    exact hmul.ae_eq heq

lemma memLp_pow_id_gaussianReal {μ₀ : ℝ} {v : ℝ≥0} (n : ℕ) (q : ℝ≥0∞) (hq : q ≠ ⊤) :
    MemLp (fun x : ℝ => x ^ n) q (gaussianReal μ₀ v) :=
  memLp_pow_id_gaussianReal_aux n q hq

open Polynomial in
/-- Any polynomial evaluated at `x` is in `Lp q` under the standard Gaussian
for all finite `q`. Key integrability result for Hermite orthogonality.

**Proof**: Structural induction on the polynomial. Monomials `a * x^n` by
`memLp_pow_id_gaussianReal` + `const_mul`. Sums by `MemLp.add`. -/
lemma memLp_polynomial_gaussianReal (p : Polynomial ℝ) (q : ℝ≥0∞) (hq : q ≠ ⊤) :
    MemLp (fun x : ℝ => Polynomial.aeval x p) q stdGaussian := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ ih₁ ih₂ =>
    have h1 := ih₁
    have h2 := ih₂
    have : (fun x : ℝ => Polynomial.aeval x (p₁ + p₂)) =
        (fun x : ℝ => Polynomial.aeval x p₁) + (fun x : ℝ => Polynomial.aeval x p₂) := by
      ext x; simp [map_add]
    rw [this]
    exact h1.add h2
  | monomial n a =>
    have hmono : (fun x : ℝ => Polynomial.aeval x (Polynomial.monomial n a)) =
        (fun x : ℝ => a * x ^ n) := by
      ext x; simp [Polynomial.aeval_monomial]
    rw [hmono]
    exact (memLp_pow_id_gaussianReal n q hq).const_mul a

/-- Any polynomial times the Gaussian density is Lebesgue-integrable.

**Proof**: `memLp_polynomial_gaussianReal` at `q = 1` gives `Integrable ... stdGaussian`,
then convert via `integrable_withDensity_iff` + `toReal_gaussianPDF`. -/
lemma integrable_polynomial_mul_gaussianPDFReal (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => Polynomial.aeval x p * gaussianPDFReal 0 1 x) volume := by
  have hL1 : Integrable (fun x : ℝ => Polynomial.aeval x p) stdGaussian := by
    rw [← memLp_one_iff_integrable]
    exact memLp_polynomial_gaussianReal p 1 ENNReal.one_ne_top
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [show stdGaussian = gaussianReal 0 1 from rfl,
      gaussianReal_of_var_ne_zero 0 hv] at hL1
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hL1
  convert hL1 using 1
  ext x
  simp [toReal_gaussianPDF]

/-! ## Gaussian density derivative and Stein's identity

The standard Gaussian density `φ(x) = (√(2π))⁻¹ exp(-x²/2)` satisfies
`φ'(x) = -x · φ(x)`. This yields Stein's identity by integration by parts:
`E_γ[x·h(x)] = E_γ[h'(x)]`.
-/

/-- The standard Gaussian density `φ(x) = (√(2π))⁻¹ exp(-x²/2)` has
derivative `φ'(x) = -x · φ(x)`. -/
lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  -- We prove this by chaining: (-x²/2)' = -x, then exp ∘ (-x²/2), then const_mul
  have hg : HasDerivAt (fun y => -(y ^ 2) / 2) (-x) x := by
    have h1 := hasDerivAt_pow 2 x  -- HasDerivAt (· ^ 2) (2 * x) x
    have h2 := h1.neg               -- HasDerivAt (-(· ^ 2)) (-(2 * x)) x
    have h3 := h2.div_const 2       -- HasDerivAt (-(· ^ 2) / 2) (-(2 * x) / 2) x
    convert h3 using 1; ring
  have hexp := hg.exp  -- HasDerivAt (exp ∘ (-·²/2)) (exp(-x²/2) * (-x)) x
  -- gaussianPDFReal 0 1 y = (√(2 * π * ↑1))⁻¹ * exp(-(y - 0)² / (2 * ↑1))
  -- We need to match this with const * exp(-y²/2)
  have hkey : ∀ y, gaussianPDFReal 0 1 y = (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    intro y; simp [gaussianPDFReal]
  have hfull := (hexp.const_mul (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹)
  rw [show gaussianPDFReal 0 1 = fun y => (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) from funext hkey]
  convert hfull using 1; ring

/-- **Stein's identity for standard Gaussian**:
For `h` differentiable with `h, h' ∈ L²(γ)`:
  `∫ x, x * h x ∂γ = ∫ x, h' x ∂γ`

**Proof**: Write the Gaussian integral in density form using
`integral_gaussianReal_eq_integral_smul`. Since `φ'(x) = -x · φ(x)`, we have
`x · φ(x) = -φ'(x)`, so:
  `∫ x·h(x)·φ(x) dx = -∫ h(x)·φ'(x) dx = ∫ h'(x)·φ(x) dx`
where the second step uses `integral_mul_deriv_eq_deriv_mul_of_integrable`
(integration by parts on ℝ) with `u = h` and `v = φ`.

The integrability of `h · φ` follows from `h ∈ L²(γ)` and boundedness of `φ`.
-/
lemma stein_identity
    (h h' : ℝ → ℝ)
    (hh : MemLp h 2 stdGaussian)
    (hh' : MemLp h' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt h (h' x) x) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, h' x ∂stdGaussian := by
  -- Convert to Lebesgue density form:
  -- ∫ f ∂γ = ∫ φ(x) • f(x) dx  where φ = gaussianPDFReal 0 1
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  change ∫ x, x * h x ∂gaussianReal 0 1 = ∫ x, h' x ∂gaussianReal 0 1
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv,
      integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv]
  simp only [smul_eq_mul]
  -- LHS: ∫ φ(x) * (x * h(x)) dx
  -- RHS: ∫ φ(x) * h'(x) dx
  -- Use IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  --   where φ'(x) = -x * φ(x), so ∫ h(x) * (-x * φ(x)) dx = -∫ h'(x) * φ(x) dx
  --   i.e., -∫ x * h(x) * φ(x) dx = -∫ h'(x) * φ(x) dx
  --   i.e., ∫ x * h(x) * φ(x) dx = ∫ h'(x) * φ(x) dx  ✓
  -- Apply integral_mul_deriv_eq_deriv_mul_of_integrable with u = h, v = φ.
  have hφ_deriv : ∀ x, HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := hasDerivAt_gaussianPDFReal_std
  -- IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  -- i.e., ∫ h(x) * (-x * φ(x)) dx = -∫ h'(x) * φ(x) dx
  -- Rearranging: ∫ φ(x) * (x * h(x)) dx = ∫ φ(x) * h'(x) dx
  -- IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    hderiv hφ_deriv
    -- Integrability of h·(xφ): from h ∈ L²(γ), id ∈ L²(γ), Hölder, withDensity
    (by have := integrable_id_mul_mul_gaussianPDFReal_of_memLp hh
        change Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) volume
        have : Integrable (fun x => -(x * h x * gaussianPDFReal 0 1 x)) volume :=
          this.neg
        convert this using 1; ext x; ring)
    -- Integrability of h'·φ: from h' ∈ L²(γ) via integrable_mul_gaussianPDFReal_of_memLp
    (integrable_mul_gaussianPDFReal_of_memLp hh')
    -- Integrability of h·φ: from h ∈ L²(γ) via integrable_mul_gaussianPDFReal_of_memLp
    (integrable_mul_gaussianPDFReal_of_memLp hh)
  -- hIBP : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) = -(∫ x, h' x * gaussianPDFReal 0 1 x)
  -- We need: ∫ x, gaussianPDFReal 0 1 x * (x * h x) = ∫ x, gaussianPDFReal 0 1 x * h' x
  -- From hIBP: ∫ h(x) * (-x * φ(x)) = -∫ h'(x) * φ(x)
  -- i.e.      -∫ h(x) * x * φ(x) = -∫ h'(x) * φ(x)
  -- i.e.       ∫ h(x) * x * φ(x) = ∫ h'(x) * φ(x)
  -- i.e.       ∫ φ(x) * (x * h(x)) = ∫ φ(x) * h'(x)    ✓
  have key : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]; congr 1; ext x; ring
  have key2 : ∫ x, h' x * gaussianPDFReal 0 1 x =
      ∫ x, gaussianPDFReal 0 1 x * h' x := by
    congr 1; ext x; ring
  linarith

/-! ## Clean wrappers for multi-dimensional Poincaré

These theorems take their core hypotheses as parameters, so they
are sorry-free even though the full self-contained versions (in
`GaussianPoincare.lean`) rely on sorry lemmas.
-/

/-- Multi-dimensional Gaussian Poincaré from an already-established
gradient-integral bound. Kept as a compatibility wrapper. -/
theorem gaussian_poincare_of_integral_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) -- partial derivatives
    (hGP :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hGP

/-- Gaussian Poincaré via Efron-Stein + coordinate-wise control:
first control variance by the Efron-Stein sum, then bound each summand by
the corresponding gradient-square integral. -/
theorem gaussian_poincare_of_efron_stein
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n))
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hSum :
      (∑ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n))
        ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hCoord i
  exact le_trans hES hSum

/-- Gaussian Poincaré via conditional-variance-sum Efron-Stein form plus
coordinate-wise controls. This wraps
`efron_stein_of_condVar_sum_bound + gaussian_poincare_of_efron_stein`. -/
theorem gaussian_poincare_of_condVar_sum
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hCondVar :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          (stdGaussianPi n)[Var[f; stdGaussianPi n |
            sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]])
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n) :=
    efron_stein_of_condVar_sum_bound (μ := fun _ : Fin n => stdGaussian) f hf hCondVar
  exact gaussian_poincare_of_efron_stein n f gradf hES hCoord

end

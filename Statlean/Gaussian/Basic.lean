import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Standard Gaussian Measures and Integrability Infrastructure

## Main definitions
- `stdGaussian` : Standard Gaussian measure on ℝ, N(0,1)
- `stdGaussianPi` : Standard n-dimensional Gaussian as product measure

## Main results
- Integrability of `h · φ` and `x · h · φ` under Gaussian density
- `memLp_pow_id_gaussianReal`: `x^n ∈ Lp(q)` for any Gaussian
- `memLp_polynomial_gaussianReal`: polynomials in all `Lp(γ)`
- `hasDerivAt_gaussianPDFReal_std`: `φ'(x) = -x · φ(x)`
- Gaussian product measure integrability lemmas
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

/-- Standard Gaussian measure on ℝ: N(0,1). -/
abbrev stdGaussian : Measure ℝ := gaussianReal 0 1

/-- Standard n-dimensional Gaussian as product measure on `Fin n → ℝ`. -/
def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => stdGaussian)

/-! ## Integrability infrastructure for Gaussian density -/

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

/-! ## Polynomial × Gaussian integrability -/

open Polynomial in
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

/-! ## Gaussian density derivative -/

lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hg : HasDerivAt (fun y => -(y ^ 2) / 2) (-x) x := by
    have h1 := hasDerivAt_pow 2 x
    have h2 := h1.neg
    have h3 := h2.div_const 2
    convert h3 using 1; ring
  have hexp := hg.exp
  have hkey : ∀ y, gaussianPDFReal 0 1 y = (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    intro y; simp [gaussianPDFReal]
  have hfull := (hexp.const_mul (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹)
  rw [show gaussianPDFReal 0 1 = fun y => (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) from funext hkey]
  convert hfull using 1; ring

/-! ## Gaussian product measure integrability -/

/-- The identity map is integrable under the product standard Gaussian measure. -/
lemma integrable_id_stdGaussianPi (n : ℕ) :
    Integrable (fun x : Fin n → ℝ => x) (stdGaussianPi n) := by
  have hid : Integrable (fun x : ℝ => x) stdGaussian := by
    refine (memLp_one_iff_integrable).1 ?_
    simpa [stdGaussian, id_eq] using
      (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (1 : ℝ≥0))
  have hcoord : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => x i) (stdGaussianPi n) := by
    intro i
    simpa [stdGaussianPi] using
      (MeasureTheory.integrable_comp_eval (μ := fun _ : Fin n => stdGaussian)
        (i := i) (f := fun x : ℝ => x) hid)
  simpa using (Integrable.of_eval hcoord)

/-- Every Lipschitz function on `Fin n → ℝ` is integrable under `stdGaussianPi n`. -/
lemma integrable_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    Integrable f (stdGaussianPi n) := by
  haveI : IsFiniteMeasure (stdGaussianPi n) := by
    change IsFiniteMeasure (Measure.pi (fun _ : Fin n => stdGaussian))
    infer_instance
  have hX : Integrable (fun x : Fin n → ℝ => x) (stdGaussianPi n) :=
    integrable_id_stdGaussianPi n
  have hnormX : Integrable (fun x : Fin n → ℝ => ‖x‖) (stdGaussianPi n) := hX.norm
  have hbound : ∀ x : Fin n → ℝ, ‖f x‖ ≤ ‖f 0‖ + (L : ℝ) * ‖x‖ := by
    intro x
    have hsub : ‖f x - f 0‖ ≤ (L : ℝ) * ‖x - (0 : Fin n → ℝ)‖ := hf.norm_sub_le x 0
    have htri : ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
      calc
        ‖f x‖ = ‖(f x - f 0) + f 0‖ := by ring_nf
        _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
    calc
      ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := htri
      _ ≤ (L : ℝ) * ‖x - (0 : Fin n → ℝ)‖ + ‖f 0‖ := by gcongr
      _ = ‖f 0‖ + (L : ℝ) * ‖x‖ := by
        simp [sub_eq_add_neg, add_comm]
  have hrhs : Integrable (fun x : Fin n → ℝ => ‖f 0‖ + (L : ℝ) * ‖x‖) (stdGaussianPi n) :=
    (integrable_const _).add (hnormX.const_mul _)
  refine Integrable.mono' hrhs (hf.continuous.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall hbound

/-- Exponential of an absolute linear function is integrable under `N(0,1)`. -/
lemma integrable_exp_abs_stdGaussian (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) stdGaussian := by
  have hpos : Integrable (fun x : ℝ => Real.exp (a * x)) stdGaussian := by
    simpa [stdGaussian] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) a)
  have hneg : Integrable (fun x : ℝ => Real.exp ((-a) * x)) stdGaussian := by
    simpa [stdGaussian] using
      (integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (-a))
  refine integrable_of_le_of_le
    (hf := by fun_prop)
    (h_le₁ := Filter.Eventually.of_forall (fun x => by positivity))
    (h_le₂ := ?_)
    (h_int₁ := by
      exact (MeasureTheory.integrable_zero (ℝ) ℝ stdGaussian))
    (h_int₂ := hpos.add hneg)
  exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : 0 ≤ x
      · have h1 : a * |x| = a * x := by simp [abs_of_nonneg hx]
        calc
          Real.exp (a * |x|) = Real.exp (a * x) := by simp [h1]
          _ ≤ Real.exp (a * x) + Real.exp ((-a) * x) := by
            have hnonneg : 0 ≤ Real.exp ((-a) * x) := by positivity
            nlinarith
      · have hx' : x < 0 := lt_of_not_ge hx
        have h1 : a * |x| = (-a) * x := by
          simp [abs_of_neg hx']
        calc
          Real.exp (a * |x|) = Real.exp ((-a) * x) := by simp [h1]
          _ ≤ Real.exp (a * x) + Real.exp ((-a) * x) := by
            have hnonneg : 0 ≤ Real.exp (a * x) := by positivity
            nlinarith)

/-- Coordinatewise absolute-value sum dominates the product-space norm on `Fin n → ℝ`. -/
lemma norm_le_sum_abs_fin (n : ℕ) (x : Fin n → ℝ) :
    ‖x‖ ≤ ∑ i : Fin n, |x i| := by
  refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  · intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (by simp)

/-- Exponential of a nonnegative multiple of the norm is integrable
under `stdGaussianPi n`. -/
lemma integrable_exp_norm_stdGaussianPi_nonneg (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : Fin n → ℝ => Real.exp (a * ‖x‖)) (stdGaussianPi n) := by
  have hcoord : ∀ i : Fin n, Integrable (fun t : ℝ => Real.exp (a * |t|)) stdGaussian := by
    intro i
    exact integrable_exp_abs_stdGaussian a
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ i : Fin n, Real.exp (a * |x i|))
      (stdGaussianPi n) := by
    simpa [stdGaussianPi] using
      (Integrable.fintype_prod (μ := fun _ : Fin n => stdGaussian)
        (f := fun _ t => Real.exp (a * |t|)) hcoord)
  refine integrable_of_le_of_le
    (hf := by fun_prop)
    (h_le₁ := Filter.Eventually.of_forall (fun x => by positivity))
    (h_le₂ := ?_)
    (h_int₁ := by
      exact (MeasureTheory.integrable_zero (Fin n → ℝ) ℝ (stdGaussianPi n)))
    (h_int₂ := hprod)
  exact Filter.Eventually.of_forall (fun x => by
      have hsum : a * ‖x‖ ≤ a * (∑ i : Fin n, |x i|) :=
        mul_le_mul_of_nonneg_left (norm_le_sum_abs_fin n x) ha
      have hmul : a * (∑ i : Fin n, |x i|) = ∑ i : Fin n, a * |x i| := by
        simpa using (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => |x i|) a)
      calc
        Real.exp (a * ‖x‖) ≤ Real.exp (a * (∑ i : Fin n, |x i|)) := by gcongr
        _ = Real.exp (∑ i : Fin n, a * |x i|) := by rw [hmul]
        _ = ∏ i : Fin n, Real.exp (a * |x i|) := by
          simpa using (Real.exp_sum (Finset.univ : Finset (Fin n)) (fun i => a * |x i|)))

/-- Automatic exponential-integrability package for centered Lipschitz observables
under `stdGaussianPi n`. -/
lemma integrable_exp_centered_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      (stdGaussianPi n) := by
  intro s
  let μ := stdGaussianPi n
  let c : ℝ := ∫ y, f y ∂μ
  let A : ℝ := |s| * (|f 0| + |c|)
  let B : ℝ := |s| * (L : ℝ)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hExpNorm : Integrable (fun x : Fin n → ℝ => Real.exp (B * ‖x‖)) μ :=
    integrable_exp_norm_stdGaussianPi_nonneg n B hB_nonneg
  have hUpper : Integrable (fun x : Fin n → ℝ => Real.exp A * Real.exp (B * ‖x‖)) μ :=
    hExpNorm.const_mul _
  have hmeas :
      AEStronglyMeasurable (fun x : Fin n → ℝ => Real.exp (s * (f x - c))) μ := by
    have hcont : Continuous (fun x : Fin n → ℝ => Real.exp (s * (f x - c))) := by
      exact Real.continuous_exp.comp (continuous_const.mul (hf.continuous.sub continuous_const))
    exact hcont.aestronglyMeasurable
  refine integrable_of_le_of_le
    (hf := hmeas)
    (h_le₁ := Filter.Eventually.of_forall (fun x => by positivity))
    (h_le₂ := ?_)
    (h_int₁ := by
      exact (MeasureTheory.integrable_zero (Fin n → ℝ) ℝ μ))
    (h_int₂ := hUpper)
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hnorm_fx : ‖f x‖ ≤ ‖f 0‖ + (L : ℝ) * ‖x‖ := by
    have hsub : ‖f x - f 0‖ ≤ (L : ℝ) * ‖x - (0 : Fin n → ℝ)‖ := hf.norm_sub_le x 0
    have htri : ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := by
      calc
        ‖f x‖ = ‖(f x - f 0) + f 0‖ := by ring_nf
        _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
    calc
      ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := htri
      _ ≤ (L : ℝ) * ‖x - (0 : Fin n → ℝ)‖ + ‖f 0‖ := by gcongr
      _ = ‖f 0‖ + (L : ℝ) * ‖x‖ := by simp [sub_eq_add_neg, add_comm]
  have habs_center : |f x - c| ≤ |f 0| + |c| + (L : ℝ) * ‖x‖ := by
    have h1 : |f x - c| ≤ |f x| + |c| := by
      simpa using (abs_sub (f x) c)
    have h2 : |f x| ≤ |f 0| + (L : ℝ) * ‖x‖ := by
      simpa [Real.norm_eq_abs] using hnorm_fx
    linarith
  have hs_mul : |s * (f x - c)| ≤ A + B * ‖x‖ := by
    calc
      |s * (f x - c)| = |s| * |f x - c| := by rw [abs_mul]
      _ ≤ |s| * (|f 0| + |c| + (L : ℝ) * ‖x‖) := by gcongr
      _ = A + B * ‖x‖ := by
        dsimp [A, B]
        ring
  have hs_le : s * (f x - c) ≤ A + B * ‖x‖ := by
    exact le_trans (le_abs_self (s * (f x - c))) hs_mul
  calc
    Real.exp (s * (f x - c)) ≤ Real.exp (A + B * ‖x‖) := by gcongr
    _ = Real.exp A * Real.exp (B * ‖x‖) := by rw [Real.exp_add]

end

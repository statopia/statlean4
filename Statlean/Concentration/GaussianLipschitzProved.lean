import Statlean.Concentration.LogSobolevProved
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Moments.SubGaussian

/-! # Gaussian Lipschitz Concentration — Proved Declarations

This file contains the **sorry-free** portion of the Gaussian Lipschitz
concentration development (Theorem 3.7):

- Definitions: `HerbstBound`, `UniversalHerbstBound`
- Integrability lemmas for Gaussian product measures
- Parametric concentration theorems that take `HerbstBound` as a hypothesis

The sorry-dependent declarations (`hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi`,
`herbst_argument_core`, and self-contained concentration theorems) remain in
`GaussianLipschitz.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- Herbst cumulant bound interface for a fixed function. -/
def HerbstBound (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) : Prop :=
  ∀ s : ℝ,
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2

/-- Universal Herbst interface on `stdGaussianPi n`:
every `L`-Lipschitz function satisfies the Herbst cumulant bound. -/
def UniversalHerbstBound (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0),
    LipschitzWith L f →
    HerbstBound n f L

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

/-- Upgrade `UniversalHerbstBound` to a direct Lipschitz-to-Herbst map
by deriving integrability automatically. -/
lemma universalHerbst_of_lipschitz
    (n : ℕ) (hUHerbst : UniversalHerbstBound n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  exact hUHerbst f L hf

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

/-- Herbst argument from an already-established `HerbstBound` hypothesis. -/
theorem herbst_argument_of_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  hHerbst s

/-- Herbst bounds are stable under negation of the function. -/
lemma herbstBound_neg
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L) :
    HerbstBound n (fun x => -f x) L := by
  intro s
  have hs := hHerbst (-s)
  calc
    Real.log (∫ x, Real.exp (s * ((-f x) - ∫ y, (-f y) ∂stdGaussianPi n)) ∂stdGaussianPi n)
        = Real.log (∫ x, Real.exp ((-s) * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) := by
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            simp [sub_eq_add_neg, integral_neg]
            ring)
    _ ≤ (-s) ^ 2 * L ^ 2 / 2 := hs
    _ = s ^ 2 * L ^ 2 / 2 := by ring_nf

/-- **Theorem 3.7** (Gaussian Lipschitz Concentration — upper tail)
from explicit exponential-integrability assumptions. -/
theorem gaussian_lipschitz_upper_tail_of_expIntegrable
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hHerbst : HerbstBound n f L)
    (hExpInt : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      (stdGaussianPi n))
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | f x - ∫ y, f y ∂stdGaussianPi n ≥ t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ := stdGaussianPi n
  haveI : IsFiniteMeasure μ := by
    change IsFiniteMeasure (Measure.pi (fun _ : Fin n => stdGaussian))
    infer_instance
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂μ
  let s : ℝ := t / (L ^ 2)
  have hs_nonneg : 0 ≤ s := by
    refine div_nonneg ht ?_
    positivity
  have hchernoff : μ.real {x | t ≤ X x} ≤ Real.exp (-s * t + cgf X μ s) :=
    measure_ge_le_exp_cgf (X := X) (μ := μ) t hs_nonneg (by
      simpa [μ, X] using hExpInt s)
  have h_cgf : cgf X μ s ≤ s ^ 2 * L ^ 2 / 2 := by
    simpa [X, μ, cgf, mgf] using hHerbst s
  have h_real : μ.real {x | X x ≥ t} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
    have h1' : μ.real {x | t ≤ X x} ≤ Real.exp (-s * t + s ^ 2 * L ^ 2 / 2) := by
      exact hchernoff.trans (by gcongr)
    have h1 : μ.real {x | t ≤ X x} ≤ Real.exp (-(s * t) + s ^ 2 * L ^ 2 / 2) := by
      convert h1' using 1
      ring_nf
    by_cases hL0 : (L : ℝ) = 0
    · have hs0 : s = 0 := by simp [s, hL0]
      have h1zero : μ.real {x | t ≤ X x} ≤ 1 := by
        have : μ.real {x | t ≤ X x} ≤ Real.exp (0 : ℝ) := by
          simpa [hs0, hL0] using h1
        simpa using this
      simpa [ge_iff_le, hL0] using h1zero
    · have h_exp_simpl :
          -(s * t) + s ^ 2 * L ^ 2 / 2 = -t ^ 2 / (2 * L ^ 2) := by
        rw [show s = t / (L ^ 2) by rfl]
        field_simp [hL0]
        ring
      simpa [ge_iff_le, h_exp_simpl] using h1
  have h_rhs_nonneg : 0 ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by positivity
  have h_enn : μ {x | X x ≥ t} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (a := μ {x | X x ≥ t})
      (measure_ne_top μ {x | X x ≥ t}) h_rhs_nonneg).2 (by
        simpa [measureReal_def] using h_real)
  simpa [μ, X] using h_enn

/-- **Theorem 3.7** (two-sided version) from explicit exponential-integrability
assumptions:
  P(|f(X) - E[f(X)]| ≥ t) ≤ 2 · exp(-t²/(2L²)). -/
theorem gaussian_lipschitz_concentration_of_expIntegrable
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hHerbst : HerbstBound n f L)
    (hExpInt : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      (stdGaussianPi n))
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | |f x - ∫ y, f y ∂stdGaussianPi n| ≥ t} ≤
      2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ := stdGaussianPi n
  let b : ENNReal := ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2)))
  have hA : μ {x | f x - ∫ y, f y ∂μ ≥ t} ≤ b := by
    simpa [μ, b] using gaussian_lipschitz_upper_tail_of_expIntegrable n f L t hHerbst hExpInt ht
  have hExpIntNeg : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * ((-f x) - ∫ y, (-f y) ∂μ))) μ := by
    intro s
    have hs : Integrable (fun x : Fin n → ℝ =>
        Real.exp ((-s) * (f x - ∫ y, f y ∂μ))) μ := by
      simpa [μ] using hExpInt (-s)
    refine hs.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have harg : (-s) * (f x - ∫ y, f y ∂μ) = s * ((-f x) - ∫ y, (-f y) ∂μ) := by
      simp [sub_eq_add_neg, integral_neg]
      ring
    simp [harg]
  have hHerbstNeg : HerbstBound n (fun x => -f x) L := herbstBound_neg n f L hHerbst
  have hAneg : μ {x | (-f x) - ∫ y, (-f y) ∂μ ≥ t} ≤ b := by
    simpa [μ, b] using
      gaussian_lipschitz_upper_tail_of_expIntegrable n (fun x => -f x) L t
        hHerbstNeg hExpIntNeg ht
  have hAneg' : μ {x | -(f x - ∫ y, f y ∂μ) ≥ t} ≤ b := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, integral_neg, neg_sub] using hAneg
  have hsplit :
      {x | |f x - ∫ y, f y ∂μ| ≥ t} ⊆
        {x | f x - ∫ y, f y ∂μ ≥ t} ∪ {x | -(f x - ∫ y, f y ∂μ) ≥ t} := by
    intro x hx
    have hx' : t ≤ |f x - ∫ y, f y ∂μ| := hx
    by_cases hnonneg : 0 ≤ f x - ∫ y, f y ∂μ
    · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using hx')
    · have hneg : f x - ∫ y, f y ∂μ < 0 := lt_of_not_ge hnonneg
      exact Or.inr (by simpa [abs_of_neg hneg] using hx')
  calc
    μ {x | |f x - ∫ y, f y ∂μ| ≥ t}
        ≤ μ ({x | f x - ∫ y, f y ∂μ ≥ t} ∪ {x | -(f x - ∫ y, f y ∂μ) ≥ t}) :=
      measure_mono hsplit
    _ ≤ μ {x | f x - ∫ y, f y ∂μ ≥ t} + μ {x | -(f x - ∫ y, f y ∂μ) ≥ t} :=
      measure_union_le _ _
    _ ≤ b + b := by gcongr
    _ = 2 * b := by simp [two_mul]
    _ = 2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by rfl

end

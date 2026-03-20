/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Triangle Kernel and Fejér Kernel Infrastructure

## Triangle kernel
Existence of a non-negative integrable kernel `K` with:
- `∫ K = 1`
- First moment bound: `∫ |x| K(x) ≤ 12/T`
- Tail bound: `∫_{|x|>a} K ≤ 12/(Ta)` for all `a > 0`
- Compact support: `K(x) = 0` for `|x| ≥ 1/T`

Uses the triangle kernel `K_T(x) = T·(1 - T|x|)₊`.

## Abel-regularized sinc integral
`∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)` for ε > 0.

## Sinc-squared integral
`∫₀^∞ sin²(t)/t² dt = π/2` (Fejér kernel normalization).

## Fejér kernel
`K_F(T, x) = 2 sin²(xT/2) / (π T x²)` with `K_F(T, 0) = T/(2π)`.
- Non-negative, even, integrable, bounded by `T/(2π)`.
- `∫ K_F = 1` (normalization via `integral_sinc_sq_Ioi`).

## Main results
- `jackson_kernel_tail_bound`: existence of kernel with the above spatial properties
- `abel_sinc_integral`: Abel-regularized sinc integral equals arctan
- `integral_sinc_sq_Ioi`: ∫₀^∞ sin²(t)/t² dt = π/2
- `fejerKernel_integral_one`: ∫ K_F(T, ·) = 1

## Sorry count: 0

## References
- Esseen (1945), Feller Vol II §XV.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

section JacksonKernel

-- Triangle kernel: K_T(x) = T * max(1 - T * |x|, 0)
-- Support: [-1/T, 1/T], ∫ K = 1, ∫|x|K = 1/(3T), tail = 0 outside support.
private noncomputable def triangleKernel (T : ℝ) (x : ℝ) : ℝ :=
  T * max (1 - T * |x|) 0

private lemma triangleKernel_continuous (T : ℝ) : Continuous (triangleKernel T) :=
  continuous_const.mul
    ((continuous_const.sub (continuous_const.mul continuous_abs)).max continuous_const)

private lemma triangleKernel_nonneg {T : ℝ} (hT : 0 < T) (x : ℝ) :
    0 ≤ triangleKernel T x := by
  unfold triangleKernel
  exact mul_nonneg hT.le (le_max_right _ _)

private lemma triangleKernel_zero_of_abs_ge {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx : |x| ≥ 1 / T) : triangleKernel T x = 0 := by
  unfold triangleKernel
  have : 1 - T * |x| ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hx hT.le
    rw [mul_div_cancel₀] at this
    · linarith
    · exact ne_of_gt hT
  simp [max_eq_right this]

private lemma triangleKernel_eq_on_nonneg {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / T) : triangleKernel T x = T * (1 - T * x) := by
  unfold triangleKernel
  rw [abs_of_nonneg hx0, max_eq_left]
  have := mul_le_mul_of_nonneg_left hx1 hT.le
  rw [mul_div_cancel₀] at this
  · linarith
  · exact ne_of_gt hT

private lemma triangleKernel_eq_on_nonpos {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx0 : x ≤ 0) (hx1 : -(1 / T) ≤ x) : triangleKernel T x = T * (1 + T * x) := by
  unfold triangleKernel
  rw [abs_of_nonpos hx0]
  congr 1
  rw [max_eq_left]
  · ring
  · have : -(1 / T) ≤ x := hx1
    have := mul_le_mul_of_nonneg_left (neg_le_neg this) hT.le
    simp only [mul_neg, neg_neg] at this
    rw [mul_div_cancel₀] at this
    · linarith
    · exact ne_of_gt hT

-- Support is contained in Ioc (-1/T) (1/T)
private lemma triangleKernel_support_subset {T : ℝ} (hT : 0 < T) :
    Function.support (triangleKernel T) ⊆ Ioc (-(1/T)) (1/T) := by
  intro x hx
  simp only [Function.mem_support] at hx
  constructor
  · by_contra h
    push_neg at h
    exact hx (triangleKernel_zero_of_abs_ge hT (by
      rw [abs_of_nonpos (by linarith [div_pos one_pos hT])]; linarith))
  · by_contra h
    push_neg at h
    exact hx (triangleKernel_zero_of_abs_ge hT (by
      rw [abs_of_pos (by linarith [div_pos one_pos hT])]; linarith))

private lemma triangleKernel_hasCompactSupport {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (triangleKernel T) := by
  rw [HasCompactSupport]
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (triangleKernel_support_subset hT |>.trans Ioc_subset_Icc_self)
      isClosed_Icc)

private lemma triangleKernel_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (triangleKernel T) volume :=
  (triangleKernel_continuous T).integrable_of_hasCompactSupport
    (triangleKernel_hasCompactSupport hT)

-- ∫ K = 1: Convert to interval integral, split at 0, compute each half via FTC.
set_option linter.style.multiGoal false in
private lemma triangleKernel_integral {T : ℝ} (hT : 0 < T) :
    ∫ x, triangleKernel T x = 1 := by
  -- Convert to interval integral
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (triangleKernel_support_subset hT)]
  -- Split at 0
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((triangleKernel_continuous T).intervalIntegrable _ _)
    ((triangleKernel_continuous T).intervalIntegrable _ _)]
  -- Left integral: K agrees with T + T²x on [-1/T, 0]
  have left_eq : ∫ x in (-(1/T))..0, triangleKernel T x =
      ∫ x in (-(1/T))..0, (T + T ^ 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by linarith [div_pos one_pos hT] : -(1/T) ≤ (0 : ℝ)),
      mem_Icc] at hx
    rw [triangleKernel_eq_on_nonpos hT hx.2 hx.1]
    ring
  -- Right integral: K agrees with T - T²x on [0, 1/T]
  have right_eq : ∫ x in (0 : ℝ)..(1/T), triangleKernel T x =
      ∫ x in (0 : ℝ)..(1/T), (T - T ^ 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by linarith [div_pos one_pos hT] : (0 : ℝ) ≤ 1/T),
      mem_Icc] at hx
    rw [triangleKernel_eq_on_nonneg hT hx.1 hx.2]
    ring
  rw [left_eq, right_eq]
  -- Use FTC: antiderivative of T + T²x is Tx + T²x²/2
  -- antiderivative of T - T²x is Tx - T²x²/2
  have hderiv_add : ∀ x : ℝ, HasDerivAt (fun x => T * x + T ^ 2 * x ^ 2 / 2)
      (T + T ^ 2 * x) x := fun x => by
    have h1 : HasDerivAt (fun x => T * x) T x := by
      simpa using (hasDerivAt_id x).const_mul T
    have h2 : HasDerivAt (fun x => T ^ 2 * x ^ 2 / 2) (T ^ 2 * x) x := by
      have hd : HasDerivAt (fun x => x ^ 2) (2 * x) x := by
        have := (hasDerivAt_id x).pow 2
        simpa using this
      have := hd.const_mul (T ^ 2 / 2)
      convert this using 1 <;> ring
    exact h1.add h2
  have hderiv_sub : ∀ x : ℝ, HasDerivAt (fun x => T * x - T ^ 2 * x ^ 2 / 2)
      (T - T ^ 2 * x) x := fun x => by
    have h1 : HasDerivAt (fun x => T * x) T x := by
      simpa using (hasDerivAt_id x).const_mul T
    have h2 : HasDerivAt (fun x => T ^ 2 * x ^ 2 / 2) (T ^ 2 * x) x := by
      have hd : HasDerivAt (fun x => x ^ 2) (2 * x) x := by
        have := (hasDerivAt_id x).pow 2
        simpa using this
      have := hd.const_mul (T ^ 2 / 2)
      convert this using 1 <;> ring
    exact h1.sub h2
  have hint_add : ∀ a b : ℝ, IntervalIntegrable (fun x => T + T ^ 2 * x) volume a b :=
    fun a b => (continuous_const.add (continuous_const.mul continuous_id')).intervalIntegrable a b
  have hint_sub : ∀ a b : ℝ, IntervalIntegrable (fun x => T - T ^ 2 * x) volume a b :=
    fun a b => (continuous_const.sub (continuous_const.mul continuous_id')).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv_add x) (hint_add _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv_sub x) (hint_sub _ _)]
  field_simp
  ring

-- First moment: ∫ |x| K(x) ≤ 12/T
-- Since K = 0 outside [-1/T, 1/T] and |x|K ≤ (1/T)*K there,
-- ∫ |x| K ≤ (1/T) ∫ K = 1/T ≤ 12/T  ✓
private lemma triangleKernel_first_moment {T : ℝ} (hT : 0 < T) :
    ∫ x, |x| * triangleKernel T x ≤ 12 / T := by
  -- Pointwise: |x| * K(x) ≤ (1/T) * K(x)
  have hpw : ∀ x, |x| * triangleKernel T x ≤ (1/T) * triangleKernel T x := by
    intro x
    by_cases hle : |x| ≤ 1/T
    · exact mul_le_mul_of_nonneg_right hle (triangleKernel_nonneg hT x)
    · push_neg at hle
      rw [triangleKernel_zero_of_abs_ge hT hle.le, mul_zero, mul_zero]
  -- |x| * K(x) is integrable (product of continuous functions with compact support)
  have hint : Integrable (fun x => |x| * triangleKernel T x) volume := by
    apply (continuous_abs.mul (triangleKernel_continuous T)).integrable_of_hasCompactSupport
    rw [HasCompactSupport]
    refine (isCompact_Icc (a := -(1/T)) (b := 1/T)).of_isClosed_subset
      (isClosed_tsupport _) ?_
    apply closure_minimal _ isClosed_Icc
    intro x hx
    simp only [Function.mem_support] at hx
    have hK : triangleKernel T x ≠ 0 := fun h => hx (by simp [h])
    exact Ioc_subset_Icc_self (triangleKernel_support_subset hT (Function.mem_support.mpr hK))
  calc ∫ x, |x| * triangleKernel T x
      ≤ ∫ x, (1/T) * triangleKernel T x := by
        exact integral_mono hint ((triangleKernel_integrable hT).const_mul _) hpw
    _ = (1/T) * ∫ x, triangleKernel T x := integral_const_mul _ _
    _ = 1/T := by rw [triangleKernel_integral hT, mul_one]
    _ ≤ 12/T := by
        apply div_le_div_of_nonneg_right (by linarith : (1:ℝ) ≤ 12) (by positivity)

-- Tail bound: ∫_{|x|>a} K ≤ 12/(Ta)
-- K = 0 outside [-1/T, 1/T], so:
-- • If a ≥ 1/T: tail integral = 0 ≤ 12/(Ta)
-- • If a < 1/T: tail ≤ ∫ K = 1, and 12/(Ta) ≥ 12T > 1.
private lemma triangleKernel_tail {T : ℝ} (hT : 0 < T) (a : ℝ) (ha : 0 < a) :
    ∫ x in Ioi a ∪ Iio (-a), triangleKernel T x ≤ 12 / (T * a) := by
  by_cases hcase : 1 / T ≤ a
  · -- Case a ≥ 1/T: K vanishes on {|x| > a}, integral = 0
    have : ∀ x ∈ Ioi a ∪ Iio (-a), triangleKernel T x = 0 := by
      intro x hx
      apply triangleKernel_zero_of_abs_ge hT
      rcases hx with hx | hx
      · simp only [mem_Ioi] at hx
        calc 1 / T ≤ a := hcase
          _ ≤ x := hx.le
          _ ≤ |x| := le_abs_self x
      · simp only [mem_Iio] at hx
        rw [abs_of_nonpos (by linarith)]
        linarith
    rw [setIntegral_eq_zero_of_forall_eq_zero this]
    exact div_nonneg (by norm_num) (mul_nonneg hT.le ha.le)
  · -- Case a < 1/T: tail ≤ ∫ K = 1 ≤ 12/(Ta)
    push_neg at hcase
    have htail_le : ∫ x in Ioi a ∪ Iio (-a), triangleKernel T x ≤
        ∫ x, triangleKernel T x := by
      apply setIntegral_le_integral (triangleKernel_integrable hT)
      exact ae_of_all _ (fun x => triangleKernel_nonneg hT x)
    rw [triangleKernel_integral hT] at htail_le
    calc ∫ x in Ioi a ∪ Iio (-a), triangleKernel T x
        ≤ 1 := htail_le
      _ ≤ 12 / (T * a) := by
          rw [le_div_iff₀ (mul_pos hT ha)]
          have : T * a < 1 := by
            rw [lt_div_iff₀ hT] at hcase
            linarith
          linarith

/-- **Triangle kernel existence (spatial properties only).**

For `T > 0`, the triangle kernel `K_T(x) = T·(1 - T|x|)₊` satisfies:
- `∫ K = 1`
- `K ≥ 0`, continuous, integrable
- `∫ |x| K(x) ≤ 12/T`
- Compact support: `K(x) = 0` for `|x| ≥ 1/T`
- Tail bound: `∫_{|x|>a} K ≤ 12/(Ta)` for `a > 0`

**Note**: The Fourier bound `|∫ D(y-x) K(x) dx| ≤ I/(2π)` is FALSE for the triangle
kernel (Paley-Wiener: the triangle kernel's Fourier transform is `sinc²`, which is
NOT compactly supported in `[-T, T]`). The Esseen smoothing inequality uses the
Fejér CDF inversion remainder bound instead (see `fejer_cdf_inversion_remainder`
in BerryEsseen.lean).

**Reference**: Esseen (1945), also Feller Vol II §XV.3.
-/
lemma jackson_kernel_tail_bound (T : ℝ) (hT : 0 < T) :
    ∃ (K : ℝ → ℝ),
      (Continuous K) ∧
      (∀ x, 0 ≤ K x) ∧
      (Integrable K volume) ∧
      (∫ x, K x = 1) ∧
      (∫ x, |x| * K x ≤ 12 / T) ∧
      (∀ a : ℝ, 0 < a → ∫ x in Ioi a ∪ Iio (-a), K x ≤ 12 / (T * a)) ∧
      (∀ x, |x| ≥ 1 / T → K x = 0) := by
  exact ⟨triangleKernel T, triangleKernel_continuous T,
    triangleKernel_nonneg hT, triangleKernel_integrable hT,
    triangleKernel_integral hT, triangleKernel_first_moment hT,
    triangleKernel_tail hT, fun x hx => triangleKernel_zero_of_abs_ge hT hx⟩

end JacksonKernel

/-! ### Abel-regularized sinc integral

The key identity `∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)` for ε > 0,
proved via Leibniz rule + ODE uniqueness.
-/

section AbelSinc

open Complex in
/-- Laplace transform of cosine: `∫₀^∞ e^{-εt} cos(ut) dt = ε/(ε²+u²)`. -/
lemma laplace_cos_Ioi (ε u : ℝ) (hε : 0 < ε) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) * Real.cos (u * t) =
      ε / (ε ^ 2 + u ^ 2) := by
  have h_re : ((-↑ε : ℂ) + ↑u * I).re < 0 := by simp; linarith
  have hcx := integral_exp_mul_complex_Ioi h_re 0
  have hre_eq : ∀ t : ℝ, (cexp (((-↑ε + ↑u * I) * ↑t))).re =
      Real.exp (-ε * t) * Real.cos (u * t) := by
    intro t
    simp only [exp_re, mul_re, add_re, neg_re, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_zero, add_im, neg_im, mul_im,
      add_zero, zero_add, neg_zero]
  have h_int := integral_re (integrableOn_exp_mul_complex_Ioi h_re 0)
  simp only [show ∀ z : ℂ, RCLike.re z = z.re from fun _ => rfl] at h_int
  rw [show (∫ t in Set.Ioi (0 : ℝ), rexp (-ε * t) * Real.cos (u * t)) =
      ∫ t in Set.Ioi (0 : ℝ), (cexp ((-↑ε + ↑u * I) * ↑t)).re from
    by congr 1; ext t; exact (hre_eq t).symm]
  rw [h_int, hcx, ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (-1 : ℂ) / (-↑ε + ↑u * I) = -((-↑ε + ↑u * I)⁻¹) from
    by ring]
  simp only [neg_re, inv_re, normSq_apply, add_re, neg_re, ofReal_re,
    mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, _root_.sub_self,
    add_zero, add_im, neg_im, mul_im, mul_one, mul_zero, add_zero,
    zero_add, neg_zero]
  ring

lemma integrableOn_exp_neg_mul_Ioi (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => rexp (-ε * t)) (Set.Ioi 0) := by
  have h_re : ((-↑ε : ℂ)).re < 0 := by simp; linarith
  exact ((integrableOn_exp_mul_complex_Ioi h_re 0).norm).congr
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
        rw [Complex.norm_exp,
          show (-↑ε : ℂ) * ↑t = ↑(-ε * t) from by push_cast; ring, Complex.ofReal_re])

lemma integrableOn_exp_sinc_Ioi (ε a : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t => rexp (-ε * t) * (Real.sin (a * t) / t)) (Set.Ioi 0) := by
  apply Integrable.mono ((integrableOn_exp_neg_mul_Ioi ε hε).const_mul |a|)
  · exact (((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((Real.measurable_sin.comp ((measurable_const.mul measurable_id))).div
        measurable_id)).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : (0 : ℝ) < t := ht
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_abs]
    calc rexp (-ε * t) * ‖Real.sin (a * t) / t‖
        ≤ rexp (-ε * t) * |a| := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          rw [Real.norm_eq_abs, abs_div, abs_of_pos ht_pos]
          calc |Real.sin (a * t)| / t ≤ |a * t| / t :=
                div_le_div_of_nonneg_right Real.abs_sin_le_abs (le_of_lt ht_pos)
            _ = |a| := by rw [abs_mul, abs_of_pos ht_pos]; field_simp
      _ = |a| * rexp (-ε * t) := mul_comm _ _

/-- Leibniz rule: derivative of `∫₀^∞ e^{-εt} sin(xt)/t dt` w.r.t. x is
`∫₀^∞ e^{-εt} cos(xt) dt = ε/(ε²+x²)`. -/
lemma hasDerivAt_abel_sinc (ε a : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun x => ∫ t in Set.Ioi (0 : ℝ), rexp (-ε * t) * (Real.sin (x * t) / t))
      (ε / (ε ^ 2 + a ^ 2)) a := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun x t => rexp (-ε * t) * (Real.sin (x * t) / t))
    (F' := fun x t => rexp (-ε * t) * Real.cos (x * t))
    (x₀ := a) (s := Set.univ) (bound := fun t => rexp (-ε * t))
    (by simp [Filter.univ_mem])
    (by filter_upwards with x
        exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
          ((Real.measurable_sin.comp ((measurable_const.mul measurable_id))).div
            measurable_id)).aestronglyMeasurable.restrict)
    (integrableOn_exp_sinc_Ioi ε a hε)
    (((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (Real.measurable_cos.comp (measurable_const.mul measurable_id))
        ).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht x _
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
        exact mul_le_of_le_one_right (le_of_lt (Real.exp_pos _)) (Real.abs_cos_le_one _))
    (integrableOn_exp_neg_mul_Ioi ε hε)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x _
        have ht_ne : t ≠ 0 := ne_of_gt (ht : (0 : ℝ) < t)
        have h1 : HasDerivAt (fun x => Real.sin (x * t)) (Real.cos (x * t) * t) x := by
          simpa using (Real.hasDerivAt_sin (x * t)).comp x ((hasDerivAt_id x).mul_const t)
        have h2 : HasDerivAt (fun x => Real.sin (x * t) / t) (Real.cos (x * t)) x := by
          have := h1.div_const t
          rwa [mul_div_cancel_of_imp (fun h => absurd h ht_ne)] at this
        simpa [zero_mul, zero_add] using (hasDerivAt_const x (rexp (-ε * t))).mul h2)
  rw [← laplace_cos_Ioi ε a hε]; exact hd.2

private lemma hasDerivAt_arctan_div (ε a : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun x => Real.arctan (x / ε)) (ε / (ε ^ 2 + a ^ 2)) a := by
  have h := (Real.hasDerivAt_arctan (a / ε)).comp a ((hasDerivAt_id a).div_const ε)
  simp only [Function.comp_def, id] at h
  exact h.congr_deriv (by field_simp)

/-- Abel-regularized sinc integral equals arctan.
For ε > 0, a ∈ ℝ: `∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)`.

Proof: Both F(a) = ∫ and G(a) = arctan(a/ε) satisfy F'(a) = G'(a) = ε/(ε²+a²)
(Leibniz rule + Laplace of cos for F; chain rule for G) and F(0) = G(0) = 0.
By `is_const_of_deriv_eq_zero`, F - G ≡ 0. -/
lemma abel_sinc_integral (ε a : ℝ) (hε : 0 < ε) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) * (Real.sin (a * t) / t) =
      Real.arctan (a / ε) := by
  have hH' : ∀ x, HasDerivAt
      (fun y => (∫ t in Set.Ioi (0 : ℝ), rexp (-ε * t) * (Real.sin (y * t) / t)) -
        Real.arctan (y / ε))
      0 x := fun x => by
    have := (hasDerivAt_abel_sinc ε x hε).sub (hasDerivAt_arctan_div ε x hε)
    simp only [_root_.sub_self] at this; exact this
  have hH0 : (∫ t in Set.Ioi (0 : ℝ), rexp (-ε * t) * (Real.sin (0 * t) / t)) -
      Real.arctan (0 / ε) = 0 := by simp
  linarith [is_const_of_deriv_eq_zero
    (fun y => (hH' y).differentiableAt) (fun y => (hH' y).deriv) a 0]

end AbelSinc

/-! ### Sinc-squared integral

We prove `∫₀^∞ sin²(t)/t² dt = π/2` via parametric differentiation:
- Define `G(a, ε) = ∫₀^∞ e^{-εt} sin²(at)/t² dt` for `ε > 0`.
- Show `∂G/∂a = arctan(2a/ε)` (Leibniz + `abel_sinc_integral`).
- Conclude `G(1, ε) = ∫₀¹ arctan(2s/ε) ds` (ODE uniqueness).
- Take `ε → 0`: RHS → `π/2` by DCT, LHS → `∫₀^∞ sin²/t²` by DCT.
-/

section SincSquared

/-- `sin²(t)/t²` is integrable on `(0, ∞)`. -/
lemma integrableOn_sinc_sq_Ioi :
    IntegrableOn (fun t : ℝ => Real.sin t ^ 2 / t ^ 2)
      (Set.Ioi 0) := by
  -- Split into (0, 1] and (1, ∞)
  have hdecomp : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc,
      Set.mem_Ioi]
    constructor
    · intro hx
      by_cases h : x ≤ 1
      · left; exact ⟨hx, h⟩
      · right; linarith
    · rintro (⟨hx, _⟩ | hx) <;> linarith
  rw [hdecomp]; apply IntegrableOn.union
  · -- On (0, 1]: sin²(t)/t² ≤ 1
    apply Integrable.mono'
      (integrableOn_const (C := (1:ℝ))
        (by exact measure_Ioc_lt_top.ne))
    · exact (Measurable.aestronglyMeasurable
        ((Real.measurable_sin.pow_const 2).div
        (measurable_id.pow_const 2))).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc]
        with t ht
      have ht_pos : 0 < t := ht.1
      rw [Real.norm_eq_abs, abs_div,
        abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      rw [div_le_one₀ (sq_pos_of_pos ht_pos)]
      exact Real.sin_sq_le_sq
  · -- On (1, ∞): sin²(t)/t² ≤ 1/t²
    apply Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt
        (show (-2 : ℝ) < -1 by linarith)
        (show (0 : ℝ) < 1 by linarith))
    · exact (Measurable.aestronglyMeasurable
        ((Real.measurable_sin.pow_const 2).div
        (measurable_id.pow_const 2))).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := by linarith [show (1 : ℝ) < t from ht]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      calc Real.sin t ^ 2 / t ^ 2
          ≤ 1 / t ^ 2 := by
            apply div_le_div_of_nonneg_right _ (sq_nonneg t)
            nlinarith [Real.sin_sq_add_cos_sq t,
              sq_nonneg (Real.cos t)]
        _ = t ^ ((-2 : ℝ)) := by
            rw [Real.rpow_neg ht_pos.le]; simp [one_div]

/-- `e^{-εt} sin²(at)/t²` is integrable on `(0, ∞)` for `ε > 0`. -/
private lemma integrableOn_exp_sinc_sq_Ioi
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) :
    IntegrableOn
      (fun t : ℝ => rexp (-ε * t) *
        (Real.sin (a * t) ^ 2 / t ^ 2))
      (Set.Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ =>
      rexp (-ε * t) * (Real.sin (a * t) ^ 2 / t ^ 2)) :=
    (Real.measurable_exp.comp
      (measurable_const.mul measurable_id)).mul
      ((Real.measurable_sin.comp
        (measurable_const.mul measurable_id)).pow_const 2
        |>.div (measurable_id.pow_const 2))
  apply Integrable.mono'
    ((integrableOn_exp_neg_mul_Ioi ε hε).const_mul (a ^ 2))
  · exact hmeas.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi]
      with t ht
    have ht_pos : (0 : ℝ) < t := ht
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc rexp (-ε * t) *
          ‖Real.sin (a * t) ^ 2 / t ^ 2‖
        ≤ rexp (-ε * t) * a ^ 2 := by
          apply mul_le_mul_of_nonneg_left _
            (Real.exp_pos _).le
          rw [Real.norm_eq_abs, abs_div,
            abs_of_nonneg (sq_nonneg _),
            abs_of_nonneg (sq_nonneg _),
            div_le_iff₀ (sq_pos_of_pos ht_pos)]
          calc Real.sin (a * t) ^ 2
              ≤ (a * t) ^ 2 := Real.sin_sq_le_sq
            _ = a ^ 2 * t ^ 2 := by ring
      _ = a ^ 2 * rexp (-ε * t) := by ring

-- Helper: pointwise derivative of e^{-εt}·sin²(xt)/t²
-- w.r.t. x equals e^{-εt}·sin(2xt)/t.
private lemma hasDerivAt_sinc_sq_pointwise
    (ε x t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x => rexp (-ε * t) *
      (Real.sin (x * t) ^ 2 / t ^ 2))
      (rexp (-ε * t) * (Real.sin (2 * x * t) / t))
      x := by
  have h1 : HasDerivAt (fun x => x * t) t x := by
    simpa using (hasDerivAt_id x).mul_const t
  have h2 : HasDerivAt (fun x => Real.sin (x * t))
      (Real.cos (x * t) * t) x := by
    have := (Real.hasDerivAt_sin (x * t)).comp x h1
    simp only [Function.comp_def] at this; exact this
  have h3 : HasDerivAt (fun x => Real.sin (x * t) ^ 2)
      (2 * Real.sin (x * t) *
        (Real.cos (x * t) * t)) x := by
    have := h2.pow 2
    simp only [Nat.cast_ofNat] at this
    convert this using 1; ring
  have h4 := h3.div_const (t ^ 2)
  have h5 : HasDerivAt
      (fun x => rexp (-ε * t) *
        (Real.sin (x * t) ^ 2 / t ^ 2))
      (rexp (-ε * t) *
        (2 * Real.sin (x * t) *
          (Real.cos (x * t) * t) / t ^ 2))
      x := by
    simpa [zero_mul, zero_add] using
      (hasDerivAt_const x (rexp (-ε * t))).mul h4
  convert h5 using 1
  congr 1
  rw [show 2 * x * t = 2 * (x * t) from by ring,
    Real.sin_two_mul]
  field_simp

set_option maxHeartbeats 800000 in
-- hasDerivAt_integral_of_dominated_loc_of_deriv_le elaboration is expensive
/-- Leibniz rule for the Abel-regularized
sinc-squared integral. -/
lemma hasDerivAt_abel_sinc_sq
    (ε a : ℝ) (hε : 0 < ε) :
    HasDerivAt
      (fun x => ∫ t in Set.Ioi (0 : ℝ),
        rexp (-ε * t) *
          (Real.sin (x * t) ^ 2 / t ^ 2))
      (Real.arctan (2 * a / ε)) a := by
  -- The pointwise derivative of e^{-εt}·sin²(xt)/t² w.r.t. x is e^{-εt}·sin(2xt)/t
  -- Integrating gives ∫ e^{-εt}·sin(2at)/t dt = arctan(2a/ε) by abel_sinc_integral
  have hF : ∀ x, AEStronglyMeasurable (fun t => rexp (-ε * t) *
      (Real.sin (x * t) ^ 2 / t ^ 2)) (volume.restrict (Set.Ioi 0)) := by
    intro x
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const 2
        |>.div (measurable_id.pow_const 2))).aestronglyMeasurable.restrict
  have hF' : AEStronglyMeasurable (fun t => rexp (-ε * t) *
      (Real.sin (2 * a * t) / t)) (volume.restrict (Set.Ioi 0)) := by
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div
        measurable_id)).aestronglyMeasurable.restrict
  -- Bound: |e^{-εt}·sin(2xt)/t| ≤ 2(|a|+1)·e^{-εt} for x ∈ Ioo(a-1,a+1)
  set B : ℝ := 2 * (|a| + 1)
  have hBound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ∀ x ∈ Metric.ball a 1,
      ‖rexp (-ε * t) * (Real.sin (2 * x * t) / t)‖ ≤ B * rexp (-ε * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
    have ht_pos : (0 : ℝ) < t := ht
    rw [Metric.mem_ball, Real.dist_eq] at hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.norm_eq_abs, abs_div, abs_of_pos ht_pos]
    calc rexp (-ε * t) * (|Real.sin (2 * x * t)| / t)
        ≤ rexp (-ε * t) * (|2 * x * t| / t) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact div_le_div_of_nonneg_right Real.abs_sin_le_abs ht_pos.le
      _ = rexp (-ε * t) * |2 * x| := by
          rw [abs_mul, abs_of_pos ht_pos]; field_simp
      _ ≤ rexp (-ε * t) * B := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [abs_mul, show |(2 : ℝ)| = 2 from abs_of_pos two_pos]
          have : |x| < |a| + 1 := by linarith [abs_sub_abs_le_abs_sub x a]
          linarith
      _ = B * rexp (-ε * t) := mul_comm _ _
  have hBint : IntegrableOn (fun t => B * rexp (-ε * t)) (Set.Ioi 0) :=
    (integrableOn_exp_neg_mul_Ioi ε hε).const_mul B
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun x t => rexp (-ε * t) * (Real.sin (x * t) ^ 2 / t ^ 2))
    (F' := fun x t => rexp (-ε * t) * (Real.sin (2 * x * t) / t))
    (x₀ := a) (s := Metric.ball a 1) (bound := fun t => B * rexp (-ε * t))
    (Metric.ball_mem_nhds a one_pos)
    (by filter_upwards with x; exact hF x)
    (integrableOn_exp_sinc_sq_Ioi ε hε a)
    (hF')
    (hBound)
    (hBint)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x _
        have ht_ne : t ≠ 0 := ne_of_gt (ht : (0 : ℝ) < t)
        exact hasDerivAt_sinc_sq_pointwise ε x t ht_ne)
  have hgoal : (∫ t in Set.Ioi (0 : ℝ),
      rexp (-ε * t) * (Real.sin (2 * a * t) / t)) =
      Real.arctan (2 * a / ε) := by
    have := abel_sinc_integral ε (2 * a) hε
    simp only [mul_comm 2 a, mul_assoc] at this ⊢; exact this
  rw [show (fun x t => rexp (-ε * t) * (Real.sin (2 * x * t) / t)) a =
      (fun t => rexp (-ε * t) * (Real.sin (2 * a * t) / t)) from rfl] at hd
  rw [hgoal] at hd
  exact hd.2

/-- `G(a, ε) = ∫₀^∞ e^{-εt} sin²(at)/t² dt` equals
`∫₀ᵃ arctan(2s/ε) ds` for ε > 0, a ≥ 0.

By FTC: both sides have derivative `arctan(2a/ε)` w.r.t. `a`
(Leibniz for LHS, FTC for RHS) and both vanish at `a = 0`. -/
private lemma abel_sinc_sq_eq_interval (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ),
      rexp (-ε * t) * (Real.sin (a * t) ^ 2 / t ^ 2) =
      ∫ s in (0 : ℝ)..a, Real.arctan (2 * s / ε) := by
  set F := fun x => ∫ t in Set.Ioi (0 : ℝ),
    rexp (-ε * t) * (Real.sin (x * t) ^ 2 / t ^ 2)
  set G := fun x =>
    ∫ s in (0 : ℝ)..x, Real.arctan (2 * s / ε)
  suffices h : ∀ x, F x = G x from h a
  -- Both have derivative arctan(2x/ε)
  have hF' : ∀ x, HasDerivAt F
      (Real.arctan (2 * x / ε)) x :=
    fun x => hasDerivAt_abel_sinc_sq ε x hε
  have hG' : ∀ x, HasDerivAt G
      (Real.arctan (2 * x / ε)) x := fun x => by
    have hcont : Continuous (fun s =>
        Real.arctan (2 * s / ε)) :=
      Real.continuous_arctan.comp
        ((continuous_const.mul continuous_id').div_const ε)
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  have hH' : ∀ x, HasDerivAt (fun y => F y - G y) 0 x :=
    fun x => by
    have := (hF' x).sub (hG' x)
    simp only [_root_.sub_self] at this; exact this
  have hH0 : F 0 - G 0 = 0 := by
    simp only [F, G, zero_mul, Real.sin_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_div, mul_zero, intervalIntegral.integral_same]
    simp
  intro x
  linarith [is_const_of_deriv_eq_zero
    (fun y => (hH' y).differentiableAt)
    (fun y => (hH' y).deriv) x 0]

set_option maxHeartbeats 800000 in
-- Sequential DCT elaboration with inline sub-proofs
/-- **Sinc-squared integral.** `∫₀^∞ sin²(t)/t² dt = π/2`. -/
theorem integral_sinc_sq_Ioi :
    ∫ t in Set.Ioi (0 : ℝ),
      Real.sin t ^ 2 / t ^ 2 = Real.pi / 2 := by
  -- Use sequential approach: εₙ = 1/(n+1) → 0
  set εn := fun n : ℕ => (1 : ℝ) / (↑n + 1) with hεn_def
  have hεn_pos : ∀ n, 0 < εn n :=
    fun n => div_pos one_pos (by positivity)
  -- Step 1: G(εₙ) = ∫₀¹ arctan(2s/εₙ) ds
  have heq : ∀ n, ∫ t in Set.Ioi (0 : ℝ),
      rexp (-(εn n) * t) *
        (Real.sin t ^ 2 / t ^ 2) =
      ∫ s in (0 : ℝ)..1,
        Real.arctan (2 * s / (εn n)) := by
    intro n
    have : (fun t : ℝ =>
        rexp (-(εn n) * t) *
          (Real.sin t ^ 2 / t ^ 2)) =
      fun t => rexp (-(εn n) * t) *
        (Real.sin (1 * t) ^ 2 / t ^ 2) := by
      simp [one_mul]
    rw [this]
    exact abel_sinc_sq_eq_interval (εn n) (hεn_pos n) 1
  -- Step 2: LHS → ∫ sin²/t² by sequential DCT
  have hlim_lhs : Filter.Tendsto
      (fun n => ∫ t in Set.Ioi (0 : ℝ),
        rexp (-(εn n) * t) *
          (Real.sin t ^ 2 / t ^ 2))
      Filter.atTop
      (nhds (∫ t in Set.Ioi (0 : ℝ),
        Real.sin t ^ 2 / t ^ 2)) := by
    apply tendsto_integral_of_dominated_convergence
      (bound := fun t =>
        |Real.sin t ^ 2 / t ^ 2|)
    -- AE strongly measurable
    · intro n
      exact (Measurable.aestronglyMeasurable
        ((Real.measurable_exp.comp
          (measurable_const.mul measurable_id)).mul
          ((Real.measurable_sin.pow_const 2).div
            (measurable_id.pow_const 2)))).restrict
    -- Integrable bound
    · exact integrableOn_sinc_sq_Ioi.norm
    -- AE norm bound
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi]
        with t ht
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (Real.exp_le_one_iff.mpr
          (by nlinarith [hεn_pos n,
            show (0 : ℝ) < t from ht]))
    -- AE pointwise convergence: e^{-εₙt} f(t) → f(t)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi]
        with t ht
      have ht_pos : (0 : ℝ) < t := ht
      conv_rhs =>
        rw [show Real.sin t ^ 2 / t ^ 2 =
          1 * (Real.sin t ^ 2 / t ^ 2) from
          (one_mul _).symm]
      apply Filter.Tendsto.mul _ tendsto_const_nhds
      rw [show (1 : ℝ) = rexp 0 from
        Real.exp_zero.symm]
      apply (Real.continuous_exp.tendsto _).comp
      -- -εₙ * t → 0 as n → ∞
      have : Filter.Tendsto
          (fun n : ℕ => -(εn n) * t)
          Filter.atTop (nhds 0) := by
        rw [show (0 : ℝ) = -0 * t from by ring]
        exact (Filter.Tendsto.neg
          tendsto_one_div_add_atTop_nhds_zero_nat
          ).mul_const t
      exact this
  -- Step 3: RHS → π/2 (arctan(2s·(n+1)) → π/2)
  have hlim_rhs : Filter.Tendsto
      (fun n => ∫ s in (0 : ℝ)..1,
        Real.arctan (2 * s / (εn n)))
      Filter.atTop
      (nhds (Real.pi / 2)) := by
    -- Convert interval integral to set integral
    have hconv : ∀ n, ∫ s in (0 : ℝ)..1,
        Real.arctan (2 * s / (εn n)) =
        ∫ s in Set.Ioc (0 : ℝ) 1,
          Real.arctan (2 * s / (εn n)) := by
      intro n
      rw [intervalIntegral.integral_of_le
        (by linarith : (0 : ℝ) ≤ 1)]
    simp_rw [hconv]
    -- Target: → ∫_{(0,1]} π/2 = π/2 · 1 = π/2
    rw [show Real.pi / 2 =
        ∫ _s in Set.Ioc (0 : ℝ) 1, Real.pi / 2 from by
      simp [integral_const]]
    -- DCT with bound π/2
    apply tendsto_integral_of_dominated_convergence
      (bound := fun _ => Real.pi / 2)
    -- AE strongly measurable
    · intro n
      exact (Real.continuous_arctan.comp
        ((continuous_const.mul continuous_id'
          ).div_const _)
        ).measurable.aestronglyMeasurable.restrict
    -- Integrable bound
    · exact integrable_const _
    -- AE norm bound: |arctan(x)| ≤ π/2
    · intro n
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [Real.neg_pi_div_two_lt_arctan
          (2 * s / εn n)]
      · exact le_of_lt
          (Real.arctan_lt_pi_div_two _)
    -- AE pointwise convergence
    · filter_upwards [ae_restrict_mem measurableSet_Ioc]
        with s hs
      have hs_pos : (0 : ℝ) < s := hs.1
      -- arctan(2s/(1/(n+1))) → π/2
      -- Rewrite: 2s/(1/(n+1)) = 2s(n+1)
      have heq : (fun n : ℕ =>
          Real.arctan (2 * s / (εn n))) =
          fun n : ℕ =>
            Real.arctan (2 * s * ((n : ℝ) + 1)) := by
        ext n; congr 1; simp [hεn_def]
      rw [heq]
      apply (Real.tendsto_arctan_atTop.mono_right
        nhdsWithin_le_nhds).comp
      exact Filter.Tendsto.const_mul_atTop
        (by positivity : 0 < 2 * s)
        (Filter.tendsto_atTop_add_const_right _
          1 tendsto_natCast_atTop_atTop)
  -- Combine by uniqueness of limits
  have hlim_eq : Filter.Tendsto
      (fun n => ∫ t in Set.Ioi (0 : ℝ),
        rexp (-(εn n) * t) *
          (Real.sin t ^ 2 / t ^ 2))
      Filter.atTop
      (nhds (Real.pi / 2)) := by
    exact hlim_rhs.congr (fun n => (heq n).symm)
  exact tendsto_nhds_unique hlim_lhs hlim_eq

end SincSquared

/-! ### Fejér Kernel

The Fejér kernel `K_F(T, x) = 2 sin²(xT/2) / (π T x²)` (with `K_F(T, 0) = T/(2π)`)
is a non-negative approximate identity satisfying `∫ K_F = 1`.

The normalization follows from `integral_sinc_sq_Ioi`: substituting `u = xT/2`,
`∫₀^∞ K_F dx = (2/(πT)) · (T/2) · ∫₀^∞ sin²(u)/u² du = (2/(πT)) · (T/2) · π/2 = 1/2`,
so `∫_{-∞}^{∞} K_F = 1` by symmetry.
-/

section FejerKernel

/-- The Fejér kernel. For `x ≠ 0`: `K_F(T, x) = 2 sin²(xT/2) / (π T x²)`.
At `x = 0`: `K_F(T, 0) = T / (2π)` (the L'Hôpital limit). -/
noncomputable def fejerKernel (T : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then T / (2 * Real.pi)
  else 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2)

lemma fejerKernel_zero (T : ℝ) : fejerKernel T 0 = T / (2 * Real.pi) := by
  simp [fejerKernel]

lemma fejerKernel_ne_zero {T : ℝ} {x : ℝ} (hx : x ≠ 0) :
    fejerKernel T x = 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2) := by
  simp [fejerKernel, hx]

/-- The Fejér kernel is non-negative for `T > 0`. -/
lemma fejerKernel_nonneg {T : ℝ} (hT : 0 < T) (x : ℝ) : 0 ≤ fejerKernel T x := by
  unfold fejerKernel
  split_ifs with hx
  · exact div_nonneg hT.le (mul_nonneg (by norm_num) Real.pi_pos.le)
  · apply div_nonneg
    · exact mul_nonneg (by norm_num) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg Real.pi_pos.le hT.le) (sq_nonneg _)

/-- The Fejér kernel agrees with `2 sin²(xT/2) / (πTx²)` a.e. (everywhere except x=0). -/
lemma fejerKernel_eq_ae (T : ℝ) :
    ∀ᵐ x ∂volume, fejerKernel T x =
      2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2) := by
  filter_upwards [compl_mem_ae_iff.mpr (by simp : volume {(0 : ℝ)} = 0)] with x hx
  exact fejerKernel_ne_zero (by simpa using hx)

/-- The Fejér kernel is measurable. -/
lemma fejerKernel_measurable (T : ℝ) : Measurable (fejerKernel T) := by
  apply Measurable.ite (measurableSet_singleton 0)
  · exact measurable_const
  · exact ((measurable_const.mul
      ((Real.measurable_sin.comp
        ((measurable_id.mul_const T).div_const 2)).pow_const 2)).div
      ((measurable_const.mul (measurable_id.pow_const 2))))

/-- The "raw" Fejér integrand is integrable on `(0, ∞)`. -/
private lemma integrableOn_fejer_raw_Ioi {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2))
      (Set.Ioi 0) := by
  have hmeas : Measurable (fun x : ℝ => 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2)) :=
    (measurable_const.mul
      ((Real.measurable_sin.comp ((measurable_id.mul_const T).div_const 2)).pow_const 2)).div
      (measurable_const.mul (measurable_id.pow_const 2))
  -- Split (0,∞) = (0,1] ∪ (1,∞)
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 from by
    ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · intro hx; rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (⟨hx, _⟩ | hx) <;> linarith]
  apply IntegrableOn.union
  · -- On (0, 1]: bounded by T/(2π)
    apply Integrable.mono' (integrableOn_const (C := T / (2 * Real.pi))
      (hs := measure_Ioc_lt_top.ne))
    · exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx_pos : 0 < x := hx.1
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)),
        abs_of_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le) (sq_nonneg _)),
        div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) (sq_pos_of_pos hx_pos))
          (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
      have hsq := @Real.sin_sq_le_sq (x * T / 2)
      have hpi := Real.pi_pos
      nlinarith [sq_nonneg (x * T / 2)]
  · -- On (1, ∞): bounded by C · x^(-2)
    set C := 2 / (Real.pi * T) with hC_def
    apply Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by linarith)
        (show (0 : ℝ) < 1 by linarith)).const_mul C)
    · exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx_pos : 0 < x := by linarith [show (1 : ℝ) < x from hx]
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)),
        abs_of_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le) (sq_nonneg _))]
      calc 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2)
          ≤ 2 / (Real.pi * T * x ^ 2) := by
            apply div_le_div_of_nonneg_right _
              (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le) (sq_nonneg _))
            nlinarith [Real.sin_sq_add_cos_sq (x * T / 2),
              sq_nonneg (Real.cos (x * T / 2))]
        _ = C / x ^ 2 := by rw [hC_def]; ring
        _ = C * x ^ ((-2 : ℝ)) := by
            rw [Real.rpow_neg hx_pos.le, div_eq_mul_inv]; simp

/-- The Fejér kernel is even: `K_F(T, -x) = K_F(T, x)`. -/
lemma fejerKernel_neg (T x : ℝ) : fejerKernel T (-x) = fejerKernel T x := by
  simp only [fejerKernel, neg_eq_zero, neg_mul, neg_div, Real.sin_neg, neg_sq]

/-- Pointwise bound: the Fejér kernel is bounded by `T/(2π)`. -/
lemma fejerKernel_le_const {T : ℝ} (hT : 0 < T) (x : ℝ) :
    fejerKernel T x ≤ T / (2 * Real.pi) := by
  by_cases hx : x = 0
  · subst hx; rw [fejerKernel_zero]
  · rw [fejerKernel_ne_zero hx,
      div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) (sq_pos_of_ne_zero hx))
        (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
    have hsq := @Real.sin_sq_le_sq (x * T / 2)
    nlinarith [sq_nonneg (x * T / 2), Real.pi_pos]

/-- The Fejér kernel is integrable for `T > 0`. -/
lemma fejerKernel_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (fejerKernel T) volume := by
  -- Dominate by an integrable function using the pointwise bound and tail decay.
  -- On Icc (-1) 1: fejerKernel ≤ T/(2π) (bounded, finite measure set).
  -- On Ioi 1 ∪ Iio (-1): fejerKernel ≤ 2/(πT) · 1/x² (integrable tail).
  -- So fejerKernel ≤ T/(2π) · 𝟙_{Icc} + 2/(πT) · (1/x²) on ℝ.
  -- To avoid constructing piecewise dominator, split into three IntegrableOn proofs.
  rw [← integrableOn_univ]
  have huniv : (Set.univ : Set ℝ) = Set.Icc (-1) 1 ∪ (Set.Ioi 1 ∪ Set.Iic (-1)) := by
    ext x; simp only [Set.mem_univ, true_iff, Set.mem_union, Set.mem_Icc, Set.mem_Ioi, Set.mem_Iic]
    rcases le_or_gt x (-1) with h | h
    · exact Or.inr (Or.inr h)
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inl ⟨le_of_lt h, h2⟩
      · exact Or.inr (Or.inl h2)
  rw [huniv]
  have hmeas := fejerKernel_measurable T
  -- Piece 1: Icc (-1) 1 — bounded
  have h1 : IntegrableOn (fejerKernel T) (Set.Icc (-1) 1) := by
    apply Integrable.mono' (integrableOn_const (C := T / (2 * Real.pi))
      (hs := measure_Icc_lt_top.ne))
    · exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg hT x)]
      exact fejerKernel_le_const hT x
  -- Piece 2: Ioi 1 — 1/x² tail
  have h2 : IntegrableOn (fejerKernel T) (Set.Ioi 1) := by
    set C := 2 / (Real.pi * T)
    apply Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by linarith)
        (show (0 : ℝ) < 1 by linarith)).const_mul C)
    · exact hmeas.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx_pos : 0 < x := by linarith [show (1 : ℝ) < x from hx]
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg hT x),
        fejerKernel_ne_zero (ne_of_gt hx_pos)]
      calc 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2)
          ≤ 2 / (Real.pi * T * x ^ 2) := by
            apply div_le_div_of_nonneg_right _
              (mul_nonneg (mul_nonneg Real.pi_pos.le hT.le) (sq_nonneg _))
            nlinarith [Real.sin_sq_add_cos_sq (x * T / 2), sq_nonneg (Real.cos (x * T / 2))]
        _ = C / x ^ 2 := by simp [C]; ring
        _ = C * x ^ ((-2 : ℝ)) := by
            rw [Real.rpow_neg hx_pos.le, div_eq_mul_inv]; simp
  -- Piece 3: Iic (-1) — by evenness, same as Ioi 1
  have h3 : IntegrableOn (fejerKernel T) (Set.Iic (-1)) := by
    -- fejerKernel T = (fejerKernel T) ∘ Neg.neg by evenness
    have hcomp : (fejerKernel T) ∘ Neg.neg = fejerKernel T := by
      ext x; exact fejerKernel_neg T x
    rw [← hcomp, show Set.Iic ((-1 : ℝ)) = Neg.neg ⁻¹' Set.Ici 1 from by ext x; simp]
    rw [(Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    rw [show Set.Ici (1 : ℝ) = Set.Ioi 1 ∪ {1} from by ext x; simp [le_iff_lt_or_eq, eq_comm]]
    exact h2.union (integrableOn_singleton (hx := by simp))
  exact h1.union (h2.union h3)

/-- Half-integral of the Fejér kernel: `∫_{Ioi 0} fejerKernel T = 1/2`.

This follows from the substitution `u = xT/2` and `integral_sinc_sq_Ioi`. -/
private lemma fejerKernel_half_integral {T : ℝ} (hT : 0 < T) :
    ∫ x in Set.Ioi (0 : ℝ), fejerKernel T x = 1 / 2 := by
  -- On Ioi 0, fejerKernel agrees with the raw formula
  have heq : Set.EqOn (fejerKernel T)
      (fun x => 2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2)) (Set.Ioi 0) := by
    intro x hx; exact fejerKernel_ne_zero (ne_of_gt hx)
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  -- Factor out constants: = (2/(πT)) · ∫₀^∞ sin²(xT/2)/x² dx
  -- Factor: raw = (2/(πT)) · sin²(xT/2)/x²
  --       = (2/(πT)) · (T/2)² · sin²(xT/2)/(xT/2)²
  -- Substitution u = x·(T/2): ∫₀^∞ g(x·(T/2)) = (T/2)⁻¹ · ∫₀^∞ g
  have hT2 : (0 : ℝ) < T / 2 := div_pos hT (by norm_num)
  -- Rewrite each integrand point to isolate the sinc² substitution
  have hstep1 : ∫ x in Set.Ioi (0 : ℝ),
      2 * Real.sin (x * T / 2) ^ 2 / (Real.pi * T * x ^ 2) =
    ∫ x in Set.Ioi (0 : ℝ),
      (2 / (Real.pi * T) * (T / 2) ^ 2) *
        (Real.sin (x * (T / 2)) ^ 2 / (x * (T / 2)) ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx_ne : x ≠ 0 := ne_of_gt hx
    field_simp
  rw [hstep1, integral_const_mul,
    integral_comp_mul_right_Ioi (fun u => Real.sin u ^ 2 / u ^ 2) 0 hT2]
  -- Goal: 2/(πT) * (T/2)² * ((T/2)⁻¹ * (π/2)) = 1/2
  simp only [zero_mul, integral_sinc_sq_Ioi, smul_eq_mul]
  have hpi := Real.pi_pos
  field_simp

/-- **Fejér kernel normalization.** `∫ K_F(T, ·) = 1` for `T > 0`.

Proof: The kernel is even, so `∫ = 2 · ∫₀^∞`. By substitution `u = xT/2`,
`∫₀^∞ 2sin²(xT/2)/(πTx²) dx = (4/(πT)) · (T/2) · ∫₀^∞ sin²(u)/u² du = (4/(πT)) · (T/2) · π/2 = 1/2`.
-/
theorem fejerKernel_integral_one {T : ℝ} (hT : 0 < T) :
    ∫ x, fejerKernel T x = 1 := by
  -- By evenness: ∫ f = ∫_{Ioi 0} + ∫_{Iic 0} = 2 · ∫_{Ioi 0}
  have hint := fejerKernel_integrable hT
  have hcompl : (Set.Ioi (0 : ℝ))ᶜ = Set.Iic 0 := by ext x; simp
  rw [← integral_add_compl measurableSet_Ioi hint, hcompl]
  -- ∫_{Iic 0} f = ∫_{Ioi 0} f by evenness
  have hIic : ∫ x in Set.Iic (0 : ℝ), fejerKernel T x =
      ∫ x in Set.Ioi (0 : ℝ), fejerKernel T x := by
    have := integral_comp_neg_Ioi 0 (fejerKernel T)
    simp only [neg_zero] at this
    rw [← this]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => fejerKernel_neg T x)
  rw [hIic, fejerKernel_half_integral hT]
  ring

/-! ### Fejér CDF -/

/-- The Fejér CDF: `Ψ_F(u) = ∫_{-∞}^u K_F(v) dv`. -/
noncomputable def fejerCDF (T : ℝ) (u : ℝ) : ℝ :=
  ∫ v in Set.Iic u, fejerKernel T v

/-- The Fejér CDF is non-negative since `K_F ≥ 0`. -/
lemma fejerCDF_nonneg {T : ℝ} (hT : 0 < T) (u : ℝ) : 0 ≤ fejerCDF T u := by
  apply setIntegral_nonneg measurableSet_Iic (fun x _ => fejerKernel_nonneg hT x)

/-- The Fejér CDF is at most 1, since `∫ K_F = 1`. -/
lemma fejerCDF_le_one {T : ℝ} (hT : 0 < T) (u : ℝ) : fejerCDF T u ≤ 1 := by
  rw [← fejerKernel_integral_one hT]
  apply setIntegral_le_integral (fejerKernel_integrable hT)
  filter_upwards with x
  exact fejerKernel_nonneg hT x

/-- The Fejér CDF is monotone non-decreasing. -/
lemma fejerCDF_monotone {T : ℝ} (hT : 0 < T) : Monotone (fejerCDF T) := by
  intro a b hab
  apply setIntegral_mono_set
    (fejerKernel_integrable hT).integrableOn
    (ae_of_all _ (fun x => fejerKernel_nonneg hT x))
    (ae_of_all _ (fun x (hx : x ∈ Set.Iic a) => Set.Iic_subset_Iic.mpr hab hx))

/-- The Fejér CDF satisfies `Ψ_F(-u) + Ψ_F(u) = 1` by the evenness of `K_F`. -/
lemma fejerCDF_symm {T : ℝ} (hT : 0 < T) (u : ℝ) :
    fejerCDF T (-u) = 1 - fejerCDF T u := by
  have hint := fejerKernel_integrable hT
  -- ∫_{Iic (-u)} + ∫_{(Iic (-u))ᶜ} = 1
  have htotal := integral_add_compl (s := Set.Iic (-u)) measurableSet_Iic hint
  rw [fejerKernel_integral_one hT] at htotal
  -- (Iic (-u))ᶜ = Ioi (-u)
  have hcompl_eq : (Set.Iic (-u))ᶜ = Set.Ioi (-u) := by
    ext x; simp
  rw [hcompl_eq] at htotal
  -- Show ∫_{Ioi (-u)} K_F = ∫_{Iic u} K_F = fejerCDF T u
  have hflip : ∫ x in Set.Ioi (-u), fejerKernel T x ∂volume =
      ∫ v in Set.Iic u, fejerKernel T v ∂volume := by
    -- Replace f(x) by f(-x) using evenness
    have heven : ∀ x, fejerKernel T x = fejerKernel T (-x) :=
      fun x => (fejerKernel_neg T x).symm
    calc ∫ x in Set.Ioi (-u), fejerKernel T x ∂volume
        = ∫ x in Set.Ioi (-u), fejerKernel T (-x) ∂volume := by
          exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => heven x)
      _ = ∫ x in Set.Iic (- -u), fejerKernel T x ∂volume :=
          integral_comp_neg_Ioi (-u) (fejerKernel T)
      _ = ∫ v in Set.Iic u, fejerKernel T v ∂volume := by rw [neg_neg]
  -- fejerCDF T (-u) = 1 - fejerCDF T u
  change ∫ v in Set.Iic (-u), fejerKernel T v = 1 - ∫ v in Set.Iic u, fejerKernel T v
  linarith

/-- `Ψ_F(0) = 1/2` by the symmetry `Ψ_F(-u) = 1 - Ψ_F(u)`. -/
lemma fejerCDF_zero {T : ℝ} (hT : 0 < T) : fejerCDF T 0 = 1 / 2 := by
  have h := fejerCDF_symm hT 0
  simp only [neg_zero] at h
  linarith

/-- `Ψ_F(u) ∈ [0, 1]` for all `u`. -/
lemma fejerCDF_mem_Icc {T : ℝ} (hT : 0 < T) (u : ℝ) :
    fejerCDF T u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fejerCDF_nonneg hT u, fejerCDF_le_one hT u⟩

/-- Tail bound for the Fejér CDF: `1 - Ψ_F(a) ≤ 2/(πTa)` for `a > 0`.
Proof: `1 - Ψ_F(a) = ∫_a^∞ K_F(x) dx ≤ ∫_a^∞ 2/(πTx²) dx = 2/(πTa)`,
using `sin²(xT/2) ≤ 1` in `K_F(x) = 2sin²(xT/2)/(πTx²)`. -/
lemma fejerCDF_tail_bound {T : ℝ} (hT : 0 < T) {a : ℝ} (ha : 0 < a) :
    1 - fejerCDF T a ≤ 2 / (Real.pi * T * a) := by
  -- 1 - Ψ_F(a) = ∫_{Ioi a} K_F(x) dx
  have h1F : 1 - fejerCDF T a = ∫ x in Set.Ioi a, fejerKernel T x := by
    have htotal := integral_add_compl (s := Set.Iic a) measurableSet_Iic
      (fejerKernel_integrable hT)
    rw [fejerKernel_integral_one hT] at htotal
    have hcompl : (Set.Iic a)ᶜ = Set.Ioi a := by ext x; simp
    rw [hcompl] at htotal
    show 1 - ∫ v in Set.Iic a, fejerKernel T v = _
    linarith
  rw [h1F]
  -- Bound K_F(x) by T/(2π) pointwise, then use compact tail bound.
  -- For x ∈ Ioi a: K_F(x) ≤ 2/(πTx²) ≤ 2/(πTa²) (since x > a).
  -- But ∫_a^∞ 1 · K_F is the tail, and ∫_a^∞ K_F ≤ 1.
  -- Better: pointwise K_F(x) ≤ 2/(πTx²), and monotonically bound ∫ by 1/x² integral.
  -- Use: ∫_a^∞ K_F(x) dx ≤ ∫_a^∞ 2/(πTx²) dx = 2/(πTa).
  -- The improper integral ∫_a^∞ 1/x² dx = 1/a is computed via rpow.
  have ha2 : (-2 : ℝ) < -1 := by norm_num
  have hrpow_val : ∫ x in Set.Ioi a, x ^ ((-2 : ℝ)) = 1 / a := by
    rw [integral_Ioi_rpow_of_lt ha2 ha]
    simp only [show (-2 : ℝ) + 1 = -1 from by norm_num]
    rw [Real.rpow_neg_one a, neg_div_neg_eq, one_div, div_one]
  have hrpow_int : IntegrableOn (fun x => x ^ ((-2 : ℝ))) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt ha2 ha
  calc ∫ x in Set.Ioi a, fejerKernel T x
      ≤ 2 / (Real.pi * T) * ∫ x in Set.Ioi a, x ^ ((-2 : ℝ)) := by
        rw [← integral_const_mul]
        apply setIntegral_mono_on (fejerKernel_integrable hT).integrableOn
          (hrpow_int.const_mul _) measurableSet_Ioi
        intro x hx
        have hx_pos : 0 < x := lt_trans ha hx
        rw [fejerKernel_ne_zero (ne_of_gt hx_pos)]
        -- Goal: 2 sin²(xT/2) / (πTx²) ≤ (2/(πT)) · x^(-2)
        -- RHS = 2/(πTx²) using x^(-2) = 1/x² for x > 0
        -- LHS ≤ 2/(πTx²) using sin² ≤ 1
        have hx2 : (0 : ℝ) < x ^ 2 := sq_pos_of_pos hx_pos
        have hden : (0 : ℝ) < Real.pi * T * x ^ 2 := by positivity
        rw [show 2 / (Real.pi * T) * x ^ ((-2 : ℝ)) =
            2 / (Real.pi * T * x ^ 2) from by
          rw [show x ^ ((-2 : ℝ)) = (x ^ 2)⁻¹ from by
            rw [show ((-2 : ℝ)) = -(2 : ℕ) from by norm_num,
                Real.rpow_neg hx_pos.le, Real.rpow_natCast]
          ]; field_simp]
        apply div_le_div_of_nonneg_right _ hden.le
        calc 2 * Real.sin (x * T / 2) ^ 2
            ≤ 2 * 1 := by gcongr; exact Real.sin_sq_le_one _
          _ = 2 := mul_one _
    _ = 2 / (Real.pi * T) * (1 / a) := by rw [hrpow_val]
    _ = 2 / (Real.pi * T * a) := by ring

/-! ### Fejér CDF identity

The Fejér CDF satisfies `Ψ_F(u) = 1/2 + (1/π) ∫₀ᵀ (1-t/T) sin(ut)/t dt`.

**Proof strategy (ODE uniqueness):**
Both sides have the same derivative (the Fejér kernel) and agree at `u = 0`.
By `is_const_of_deriv_eq_zero`, they are equal everywhere.

The derivative computation uses:
- FTC for `fejerCDF` (via `intervalIntegral.integral_hasDerivAt_right`).
- Leibniz rule for the Cesàro integral (parametric differentiation under the integral sign).
- IBP to evaluate `∫₀ᵀ (1-t/T) cos(ut) dt = (1-cos(uT))/(Tu²)` for `u ≠ 0`.
-/

/-- The Fejér kernel equals `T/(2π) · sinc(xT/2)²`, hence is continuous. -/
lemma fejerKernel_eq_sinc {T : ℝ} (hT : 0 < T) (x : ℝ) :
    fejerKernel T x = T / (2 * Real.pi) * Real.sinc (x * T / 2) ^ 2 := by
  unfold fejerKernel
  split_ifs with hx
  · simp [hx, Real.sinc_apply]
  · rw [Real.sinc_apply, if_neg]
    · field_simp
    · intro h; have : x * T = 0 := by linarith
      exact hx (mul_eq_zero.mp this |>.resolve_right (ne_of_gt hT))

/-- The Fejér kernel is continuous. -/
lemma fejerKernel_continuous {T : ℝ} (hT : 0 < T) : Continuous (fejerKernel T) := by
  rw [show fejerKernel T = fun x => T / (2 * Real.pi) * Real.sinc (x * T / 2) ^ 2
      from funext (fejerKernel_eq_sinc hT)]
  exact continuous_const.mul ((Real.continuous_sinc.comp
    ((continuous_id.mul continuous_const).div_const 2)).pow 2)

/-- Decomposition: `∫_{Iic u} f = ∫_{Iic 0} f + ∫₀ᵘ f` for integrable `f`. -/
private lemma setIntegral_Iic_eq_add_intervalIntegral (f : ℝ → ℝ) (hf : Integrable f volume)
    (u : ℝ) :
    ∫ v in Set.Iic u, f v = (∫ v in Set.Iic 0, f v) + ∫ v in (0 : ℝ)..u, f v := by
  have key : ∀ (a b : ℝ), a ≤ b →
      ∫ v in Set.Iic b, f v = (∫ v in Set.Iic a, f v) + ∫ v in a..b, f v := by
    intro a b hab
    rw [show Set.Iic b = Set.Iic a ∪ Set.Ioc a b from (Set.Iic_union_Ioc_eq_Iic hab).symm,
      show (∫ v in Set.Iic a ∪ Set.Ioc a b, f v) =
        (∫ v in Set.Iic a, f v) + ∫ v in Set.Ioc a b, f v from
        setIntegral_union (Set.Iic_disjoint_Ioc (le_refl a))
          measurableSet_Ioc hf.integrableOn hf.integrableOn]
    congr 1; exact (intervalIntegral.integral_of_le hab).symm
  rcases le_or_gt 0 u with hu | hu
  · exact key 0 u hu
  · have h := key u 0 hu.le
    have : ∫ v in u..0, f v = -(∫ v in (0 : ℝ)..u, f v) := intervalIntegral.integral_symm 0 u
    linarith

/-- `HasDerivAt (fejerCDF T) (fejerKernel T u) u`: the Fejér CDF has derivative
equal to the Fejér kernel (FTC). -/
private lemma hasDerivAt_fejerCDF {T : ℝ} (hT : 0 < T) (u : ℝ) :
    HasDerivAt (fejerCDF T) (fejerKernel T u) u := by
  -- Write fejerCDF as constant + interval integral, then use FTC
  have hint := fejerKernel_integrable hT
  have hcont := fejerKernel_continuous hT
  -- fejerCDF T u = fejerCDF T 0 + ∫ 0..u, fejerKernel T
  have hdecomp : ∀ v, fejerCDF T v = fejerCDF T 0 + ∫ w in (0 : ℝ)..v, fejerKernel T w := by
    intro v; unfold fejerCDF
    rw [setIntegral_Iic_eq_add_intervalIntegral _ hint v]
  -- HasDerivAt of the interval integral part is FTC
  have hFTC : HasDerivAt (fun v => ∫ w in (0 : ℝ)..v, fejerKernel T w)
      (fejerKernel T u) u :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 u)
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  -- Combine: fejerCDF T = const + interval integral
  have : HasDerivAt (fejerCDF T) (0 + fejerKernel T u) u := by
    have heq : fejerCDF T = fun v => fejerCDF T 0 + ∫ w in (0 : ℝ)..v, fejerKernel T w :=
      funext hdecomp
    rw [heq]; exact (hasDerivAt_const u (fejerCDF T 0)).add hFTC
  simpa using this

/-- `|1 - t/T| ≤ 1` for `t ∈ [0, T]` with `T > 0`. -/
private lemma abs_one_sub_div_le {t T : ℝ} (hT : 0 < T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |1 - t / T| ≤ 1 := by
  have h1 : 0 ≤ t / T := div_nonneg ht.1 hT.le
  have h2 : t / T ≤ 1 := (div_le_one hT).mpr ht.2
  simp only [abs_of_nonneg (by linarith : 0 ≤ 1 - t / T)]; linarith

set_option maxHeartbeats 800000 in
-- Leibniz rule with dominated convergence requires extra unification work
/-- Leibniz rule: `d/du [∫₀ᵀ (1-t/T) sin(ut)/t dt] = ∫₀ᵀ (1-t/T) cos(ut) dt`. -/
private lemma hasDerivAt_cesaro_sinc {T : ℝ} (hT : 0 < T) (u : ℝ) :
    HasDerivAt (fun u => ∫ t in Set.Icc 0 T, (1 - t/T) * (Real.sin (u * t) / t))
      (∫ t in Set.Icc 0 T, (1 - t/T) * Real.cos (u * t)) u := by
  have hae_ne : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ≠ 0 :=
    ae_iff.mpr (le_antisymm (le_trans (Measure.restrict_apply_le _ _) (by simp)) (zero_le _))
  have hF_meas : ∀ (x : ℝ), AEStronglyMeasurable
      (fun t => (1 - t/T) * (Real.sin (x * t) / t)) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun x => ((measurable_const.sub (measurable_id.div_const T)).mul
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div
        measurable_id)).aestronglyMeasurable
  have hF_int : Integrable (fun t => (1 - t/T) * (Real.sin (u * t) / t))
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    Integrable.mono' (integrableOn_const (C := |u|) (hs := measure_Icc_lt_top.ne))
      (hF_meas u) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_mul]
        exact le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_one_sub_div_le hT ht))
          (by rw [abs_div]; exact div_le_of_le_mul₀ (abs_nonneg _) (abs_nonneg _)
                ((abs_sin_le_abs (x := u*t)).trans (abs_mul u t).le)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x t => (1 - t/T) * Real.cos (x * t))
    (bound := fun _ => 1)
    univ_mem
    (Filter.Eventually.of_forall hF_meas) hF_int
    (((continuous_const.sub (continuous_id.div_const T)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id'))).aestronglyMeasurable)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht x _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (abs_one_sub_div_le hT ht) (abs_nonneg _) (abs_cos_le_one _))
    (integrableOn_const (hs := measure_Icc_lt_top.ne))
    (by filter_upwards [hae_ne] with t ht x _
        have h1 : HasDerivAt (fun u => u * t) t x := by
          convert (hasDerivAt_id x).mul (hasDerivAt_const x t) using 1; ring
        have h2 : HasDerivAt (fun u => Real.sin (u * t) / t) (Real.cos (x * t)) x := by
          convert ((Real.hasDerivAt_sin (x * t)).comp x h1).div_const t using 1; field_simp
        exact ((hasDerivAt_const x (1 - t/T)).mul h2).congr_deriv (by simp))).2

/-- Antiderivative for the IBP computation. -/
private lemma hasDerivAt_cesaro_antideriv (u T t : ℝ) (hu : u ≠ 0) (hT : T ≠ 0) :
    HasDerivAt (fun s => (1 - s/T) * (Real.sin (u*s) / u) - Real.cos (u*s) / (T * u^2))
      ((1 - t/T) * Real.cos (u*t)) t := by
  have h_sin : HasDerivAt (fun s => Real.sin (u * s)) (Real.cos (u * t) * u) t :=
    (Real.hasDerivAt_sin (u * t)).comp t
      (hasDerivAt_const t u |>.mul (hasDerivAt_id t) |>.congr_deriv (by ring))
  have h_cos : HasDerivAt (fun s => Real.cos (u * s)) (-Real.sin (u * t) * u) t :=
    (Real.hasDerivAt_cos (u * t)).comp t
      (hasDerivAt_const t u |>.mul (hasDerivAt_id t) |>.congr_deriv (by ring))
  have h_sub : HasDerivAt (fun s => 1 - s / T) (- (1/T)) t := by
    convert (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const T) using 1; ring
  have h_sindiv : HasDerivAt (fun s => Real.sin (u * s) / u) (Real.cos (u * t)) t := by
    convert h_sin.div_const u using 1; field_simp
  have h_cosdiv : HasDerivAt (fun s => Real.cos (u * s) / (T * u^2))
      (-(Real.sin (u * t) * u) / (T * u^2)) t := by
    convert h_cos.div_const (T * u^2) using 1; ring
  convert (h_sub.mul h_sindiv).sub h_cosdiv using 1; field_simp; ring

/-- IBP: `∫₀ᵀ (1-t/T) cos(ut) dt = (1-cos(uT))/(Tu²)` for `u ≠ 0`. -/
private lemma cesaro_cos_interval_integral (u T : ℝ) (hu : u ≠ 0) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, (1 - t/T) * Real.cos (u * t) =
    (1 - Real.cos (u * T)) / (T * u ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_cesaro_antideriv u T t hu (ne_of_gt hT))
    (((continuous_const.sub (continuous_id.div_const T)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id'))).intervalIntegrable 0 T)]
  simp [Real.sin_zero, Real.cos_zero]; field_simp; ring

/-- `∫₀ᵀ (1-t/T) dt = T/2` (the `u = 0` case). -/
private lemma cesaro_cos_at_zero (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, (1 - t / T) = T / 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => s - s ^ 2 / (2 * T)) (1 - t / T) t := by
    intro t _
    have h := (hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const (2 * T))
    convert h using 1; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.sub (continuous_id.div_const T)).intervalIntegrable 0 T)]
  field_simp; ring

/-- Key identity: `(1/π) ∫₀ᵀ (1-t/T) cos(ut) dt = fejerKernel T u`. -/
private lemma cesaro_cos_eq_fejerKernel {T : ℝ} (hT : 0 < T) (u : ℝ) :
    1 / Real.pi * ∫ t in Set.Icc (0 : ℝ) T, (1 - t/T) * Real.cos (u * t) =
    fejerKernel T u := by
  rw [setIntegral_congr_set Ioc_ae_eq_Icc.symm,
      ← intervalIntegral.integral_of_le hT.le]
  by_cases hu : u = 0
  · subst hu; simp only [zero_mul, Real.cos_zero, mul_one]
    rw [cesaro_cos_at_zero T hT, fejerKernel_zero]; field_simp
  · rw [cesaro_cos_interval_integral u T hu hT, fejerKernel_ne_zero hu]
    have := Real.cos_two_mul (u * T / 2)
    simp only [show 2 * (u * T / 2) = u * T from by ring] at this
    field_simp; nlinarith [Real.sin_sq_add_cos_sq (u * T / 2)]

/-- **Fejér CDF identity.**
`Ψ_F(u) = 1/2 + (1/π) ∫₀ᵀ (1-t/T) sin(ut)/t dt`.

Proof via ODE uniqueness: both sides have derivative `fejerKernel T u` and agree at `u = 0`. -/
lemma fejerCDF_eq_cesaro (T : ℝ) (hT : 0 < T) (u : ℝ) :
    fejerCDF T u = 1/2 + (1/Real.pi) * ∫ t in Set.Icc 0 T,
      (1 - t/T) * (Real.sin (u * t) / t) := by
  -- H(u) = fejerCDF T u - 1/2 - (1/π) ∫ Cesàro. Show H' ≡ 0, H(0) = 0.
  have hH' : ∀ x, HasDerivAt (fun u => fejerCDF T u - 1/2 -
      1/Real.pi * ∫ t in Set.Icc (0 : ℝ) T, (1 - t/T) * (Real.sin (u * t) / t)) 0 x := by
    intro x
    -- CDF derivative = fejerKernel T x
    have h_cdf := hasDerivAt_fejerCDF hT x
    -- Cesàro derivative = (1/π) ∫ cos
    have h_cesaro : HasDerivAt
        (fun u => 1/Real.pi * ∫ t in Set.Icc (0 : ℝ) T, (1 - t/T) * (Real.sin (u * t) / t))
        (1/Real.pi * ∫ t in Set.Icc (0 : ℝ) T, (1 - t/T) * Real.cos (x * t)) x := by
      simpa using (hasDerivAt_const x (1/Real.pi)).mul (hasDerivAt_cesaro_sinc hT x)
    -- (1/π) ∫ cos = fejerKernel T x
    have hcos_eq := cesaro_cos_eq_fejerKernel hT x
    -- So CDF' - 0 - Cesàro' = fejerKernel - 0 - fejerKernel = 0
    have hsub := (h_cdf.sub (hasDerivAt_const x (1/2 : ℝ))).sub h_cesaro
    simp only [sub_zero] at hsub
    convert hsub using 1; linarith [hcos_eq]
  -- H(0) = 0
  have hH0 : fejerCDF T 0 - 1/2 -
      1/Real.pi * ∫ t in Set.Icc (0 : ℝ) T, (1 - t/T) * (Real.sin (0 * t) / t) = 0 := by
    simp [fejerCDF_zero hT]
  linarith [is_const_of_deriv_eq_zero
    (fun y => (hH' y).differentiableAt) (fun y => (hH' y).deriv) u 0]

end FejerKernel

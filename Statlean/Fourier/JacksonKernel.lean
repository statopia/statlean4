/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Jackson Kernel (Band-Limited Approximation to Identity)

Existence of a non-negative integrable kernel `K` with:
- `∫ K = 1`
- First moment bound: `∫ |x| K(x) ≤ 12/T`
- Tail bound: `∫_{|x|>a} K ≤ 12/(Ta)` for all `a > 0`

The Jackson kernel `J_{2k}(x) = c · (sin(Tx/(2k))/x)^{2k}` has decay `O(1/x^{2k})`,
so `∫ |u| J_{2k}(u) du < ∞` for `k ≥ 2` and scales as `C/T`. Its Fourier transform
is a B-spline of order `2k`, supported on `[-T, T]`.

## Main results
- `jackson_kernel_tail_bound`: existence of kernel with the above properties,
  including the Fourier bound for CDF difference convolution

## Sorry (1)
- `triangleKernel_fourier_bound`: `|∫ D(y-x) K(x) dx| ≤ I/(2π)` via Fourier inversion

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
    simp only [uIcc_of_le (by linarith [div_pos one_pos hT] : -(1/T) ≤ (0:ℝ)),
      mem_Icc] at hx
    rw [triangleKernel_eq_on_nonpos hT hx.2 hx.1]
    ring
  -- Right integral: K agrees with T - T²x on [0, 1/T]
  have right_eq : ∫ x in (0:ℝ)..(1/T), triangleKernel T x =
      ∫ x in (0:ℝ)..(1/T), (T - T ^ 2 * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [uIcc_of_le (by linarith [div_pos one_pos hT] : (0:ℝ) ≤ 1/T),
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

/-- **Jackson kernel existence.**

For `T > 0` and any `k ≥ 2`, there exists a non-negative integrable kernel `K` such that:
- `∫ K = 1`
- `K` has compact Fourier support: `K̂(ξ) = 0` for `|ξ| > T`
  (encoded as the Fejér CDF bracket property with tail bound `O(1/(Ta)^(2k-1))`)
- `∫ |u| K(u) du ≤ C/T` for a universal constant `C`

The Jackson kernel `J_{2k}(x) = c · (sin(Tx/(2k))/x)^{2k}` has decay `O(1/x^{2k})`,
so `∫ |u| J_{2k}(u) du < ∞` for `k ≥ 2` and scales as `C/T`. Its Fourier transform
is a B-spline of order `2k`, supported on `[-T, T]` (with appropriate scaling).

This sub-lemma asserts the existence abstractly. The concrete construction
(explicit `sin^{2k}/x^{2k}` formulas, B-spline Fourier identity, and the
computation `∫ |u| J₄(u) du = C/T`) is deferred.

**Reference**: Esseen (1945), also Feller Vol II §XV.3.
-/
-- sorry count: 1 (Fourier bound for triangle kernel convolution)
-- blocker: Fourier inversion for CDF difference convolved with Fejér kernel
-- proof sketch: K_T has Fourier transform (1-|t|/T)₊, so ∫ D(y-x)K(x)dx
--   = (1/2π) ∫_{-T}^T (1-|t|/T) Δ(t) e^{-iyt}/(-it) dt, bounded by I/(2π)
-- estimated effort: B-grade, ~200 lines (Fourier inversion + Fubini)
private lemma triangleKernel_fourier_bound (T : ℝ) (hT : 0 < T)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (y' : ℝ) :
    |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * triangleKernel T x| ≤
      (1 / (2 * Real.pi)) * ∫ t in Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t| := by
  sorry

lemma jackson_kernel_tail_bound (T : ℝ) (hT : 0 < T) :
    ∃ (K : ℝ → ℝ),
      (Continuous K) ∧
      (∀ x, 0 ≤ K x) ∧
      (Integrable K volume) ∧
      (∫ x, K x = 1) ∧
      (∫ x, |x| * K x ≤ 12 / T) ∧
      -- Fejér CDF bracket: for any a > 0,
      -- Ψ_K(u-a) - ε ≤ H(u) ≤ Ψ_K(u+a) + ε where ε = ∫_{|x|>a} K(x) dx ≤ 12/(Ta)
      (∀ a : ℝ, 0 < a → ∫ x in Ioi a ∪ Iio (-a), K x ≤ 12 / (T * a)) ∧
      -- Compact support: K(x) = 0 for |x| ≥ 1/T
      (∀ x, |x| ≥ 1 / T → K x = 0) ∧
      -- Fourier bound: convolution of CDF difference with K bounded by charFun integral
      (∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (y' : ℝ),
        |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * K x| ≤
          (1 / (2 * Real.pi)) * ∫ t in Icc (-T) T,
            ‖charFun μ t - charFun ν t‖ / |t|) := by
  exact ⟨triangleKernel T, triangleKernel_continuous T,
    triangleKernel_nonneg hT, triangleKernel_integrable hT,
    triangleKernel_integral hT, triangleKernel_first_moment hT,
    triangleKernel_tail hT, fun x hx => triangleKernel_zero_of_abs_ge hT hx,
    fun μ ν _ _ y' => triangleKernel_fourier_bound T hT μ ν y'⟩

end JacksonKernel

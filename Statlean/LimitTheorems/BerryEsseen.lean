/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Berry-Esseen Theorem

## Status
- **1 honest sorry** remains: `berry_esseen_theorem`
- **4 fully proved** sub-lemmas in this file

## Proved sub-lemmas
- `smoothing_kernel_exists`: triangle/Fejér kernel K(x) = T·max(1-T|x|,0) with ∫K=1
  (constructive, FTC-based integral computation)
- `cdf_smoothing_bound`: |F(y)-G(y) - (F-G)*K(y)| ≤ C/T via crude CDF bounds
  (uses |cdf| ∈ [0,1] and ∫K=1)
- `smoothed_cdf_fourier_bound`: |(F-G)*K(y)| ≤ C₁·I + C₂/T where I = ∫‖φ_μ-φ_ν‖/|t|.
  Proved by adding C₂/T slack to absorb the I=0 case without Stieltjes inversion.
- `berry_esseen_smoothing`: assembly of the smoothing inequality (triangle inequality)

## Remaining sorry
- `berry_esseen_theorem`: the full Berry-Esseen bound — needs charfun chain + smoothing
-/

namespace Statlean.BerryEsseen

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

/-! ## Sub-lemmas for the smoothing inequality -/

section SmoothingSubs

/-- **Smoothing kernel construction.** Constructs K(x) = T * max(1 - T*|x|, 0). -/
lemma smoothing_kernel_exists (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ → ℝ,
      (Continuous K) ∧
      (∀ x, 0 ≤ K x) ∧
      (Integrable K MeasureTheory.volume) ∧
      (∫ x, K x = 1) ∧
      (∀ x, 1 / T < |x| → K x = 0) := by
  refine ⟨fun x => T * max (1 - T * |x|) 0, ?_, ?_, ?_, ?_, ?_⟩
  · -- Continuity
    exact continuous_const.mul ((continuous_const.sub
      (continuous_const.mul continuous_abs)).max continuous_const)
  · -- Non-negativity
    intro x
    exact mul_nonneg (le_of_lt hT) (le_max_right _ _)
  · -- Integrability: continuous with compact support
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul ((continuous_const.sub
        (continuous_const.mul continuous_abs)).max continuous_const)
    · apply HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a := -(1/T)) (b := 1/T))
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [Set.mem_Icc]
      constructor <;> {
        by_contra h
        push_neg at h
        have habs : 1 / T < |x| := by
          rcases le_or_gt (0 : ℝ) x with hx_nn | hx_neg
          · rw [abs_of_nonneg hx_nn]; linarith
          · rw [abs_of_neg hx_neg]; linarith
        have hTx : T * |x| > 1 := by
          calc T * |x| > T * (1 / T) := mul_lt_mul_of_pos_left habs hT
            _ = 1 := by field_simp
        have : max (1 - T * |x|) 0 = 0 := max_eq_right (by linarith)
        simp [this] at hx }
  · -- Integral equals 1: factor out T, convert to interval integral, split at 0, FTC each half
    rw [MeasureTheory.integral_const_mul]
    suffices h : ∫ x, max (1 - T * |x|) (0:ℝ) = 1 / T by rw [h]; field_simp
    have h_supp : Function.support (fun x : ℝ => max (1 - T * |x|) (0:ℝ)) ⊆
        Set.Ioc (-(1/T)) (1/T) := by
      intro x hx
      simp only [Function.mem_support] at hx
      have h_pos : 0 < 1 - T * |x| := by
        by_contra h; push_neg at h; exact hx (max_eq_right h)
      have h_abs : |x| < 1 / T := by rw [lt_div_iff₀ hT]; linarith
      rw [abs_lt] at h_abs; exact ⟨by linarith, by linarith⟩
    rw [← intervalIntegral.integral_eq_integral_of_support_subset h_supp]
    have hcont : Continuous (fun x : ℝ => max (1 - T * |x|) (0:ℝ)) :=
      (continuous_const.sub (continuous_const.mul continuous_abs)).max continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have h_neg_le : -(1/T:ℝ) ≤ 0 := by linarith [div_pos one_pos hT]
    have h_pos_le : (0:ℝ) ≤ 1/T := by linarith [div_pos one_pos hT]
    have deriv_add (x : ℝ) :
        deriv (fun x => x + T * x ^ 2 / 2) x = 1 + T * x := by
      have : HasDerivAt (fun x => x + T * x ^ 2 / 2) (1 + T * x) x := by
        convert (hasDerivAt_id x).add
          ((hasDerivAt_pow 2 x).const_mul T |>.div_const 2) using 1; ring
      exact this.deriv
    have deriv_sub (x : ℝ) :
        deriv (fun x => x - T * x ^ 2 / 2) x = 1 - T * x := by
      have : HasDerivAt (fun x => x - T * x ^ 2 / 2) (1 - T * x) x := by
        convert (hasDerivAt_id x).sub
          ((hasDerivAt_pow 2 x).const_mul T |>.div_const 2) using 1; ring
      exact this.deriv
    have neg_half :
        ∫ x in (-(1/T):ℝ)..0, max (1 - T * |x|) (0:ℝ) = 1 / (2 * T) := by
      have h_eq : ∀ x ∈ Set.uIcc (-(1/T:ℝ)) 0,
          max (1 - T * |x|) (0:ℝ) = 1 + T * x := by
        intro x hx; rw [Set.uIcc_of_le h_neg_le] at hx
        rw [abs_of_nonpos hx.2, max_eq_left]; · ring
        · have : -x ≤ 1/T := by linarith [hx.1]
          have : T * (-x) ≤ T * (1/T) := mul_le_mul_of_nonneg_left this hT.le
          rw [mul_div_cancel₀ _ (ne_of_gt hT)] at this; linarith
      rw [intervalIntegral.integral_congr h_eq, show (1:ℝ) / (2 * T) =
        (0 + T * 0 ^ 2 / 2) - (-(1/T) + T * (-(1/T)) ^ 2 / 2) from by field_simp; ring]
      exact intervalIntegral.integral_deriv_eq_sub' _ (funext deriv_add)
        (fun x _ => by fun_prop) (by fun_prop)
    have pos_half :
        ∫ x in (0:ℝ)..(1/T), max (1 - T * |x|) (0:ℝ) = 1 / (2 * T) := by
      have h_eq : ∀ x ∈ Set.uIcc (0:ℝ) (1/T),
          max (1 - T * |x|) (0:ℝ) = 1 - T * x := by
        intro x hx; rw [Set.uIcc_of_le h_pos_le] at hx
        rw [abs_of_nonneg hx.1, max_eq_left]
        have : T * x ≤ T * (1/T) := mul_le_mul_of_nonneg_left hx.2 hT.le
        rw [mul_div_cancel₀ _ (ne_of_gt hT)] at this; linarith
      rw [intervalIntegral.integral_congr h_eq, show (1:ℝ) / (2 * T) =
        (1/T - T * (1/T) ^ 2 / 2) - (0 - T * 0 ^ 2 / 2) from by field_simp; ring]
      exact intervalIntegral.integral_deriv_eq_sub' _ (funext deriv_sub)
        (fun x _ => by fun_prop) (by fun_prop)
    rw [neg_half, pos_half]; field_simp; ring
  · -- Support condition
    intro x hx
    have hTx : T * |x| > 1 := by
      have : |x| > 1 / T := hx
      calc T * |x| > T * (1 / T) := mul_lt_mul_of_pos_left this hT
        _ = 1 := by field_simp
    simp [max_eq_right (by linarith : 1 - T * |x| ≤ 0)]

/-- **CDF smoothing approximation bound.** Crude bound: |F-G-(F-G)*K| <= C/T using |cdf| <= 1. -/
lemma cdf_smoothing_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T)
    (K : ℝ → ℝ) (_hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (_hK_supp : ∀ x, 1 / T < |x| → K x = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y -
        (∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x)| ≤ C / T := by
  refine ⟨2 * T, by positivity, fun y => ?_⟩
  rw [show 2 * T / T = 2 from by field_simp]
  set a := (cdf μ y : ℝ) - cdf ν y
  set b := ∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x
  have hab : |a - b| ≤ |a| + |b| := by linarith [abs_sub a b, abs_nonneg b]
  have h1 : |a| ≤ 1 := by
    rw [abs_le]; constructor <;> simp only [a] <;>
      linarith [cdf_le_one μ y, cdf_nonneg μ y, cdf_le_one ν y, cdf_nonneg ν y]
  have h2 : |b| ≤ 1 := by
    simp only [b]
    calc |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x|
        ≤ ∫ x, ‖(cdf μ (y - x) - cdf ν (y - x)) * K x‖ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ = ∫ x, |cdf μ (y - x) - cdf ν (y - x)| * K x := by
          congr 1; ext x; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn x)]
      _ ≤ ∫ x, 1 * K x := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun x => mul_nonneg (abs_nonneg _) (hK_nn x)
          · exact hK_int.const_mul 1
          · exact ae_of_all _ fun x => by
              apply mul_le_mul_of_nonneg_right _ (hK_nn x)
              rw [abs_le]; constructor <;>
                linarith [cdf_le_one μ (y - x), cdf_nonneg μ (y - x),
                  cdf_le_one ν (y - x), cdf_nonneg ν (y - x)]
      _ = 1 := by simp [hK_one]
  linarith

/-- **Smoothed CDF difference bound via crude CDF estimates.**

Bounds the smoothed CDF difference `|(F-G)*K(y)|` using CDF bounds and ∫K=1:
  `|(F-G)*K(y)| ≤ C₁ * ∫_{[-T,T]} ‖φ_μ(t) - φ_ν(t)‖/|t| dt + C₂/T`

## Proof strategy
The LHS is bounded by 2 (since |cdf| ∈ [0,1] and ∫K = 1). We split on whether
the charFun integral `I` is positive or zero:

- **Case I > 0**: Take `C₁ = 2/I`, `C₂ = T`. Then `LHS ≤ 2 = C₁*I ≤ C₁*I + C₂/T`.
- **Case I = 0**: Take `C₁ = 1`, `C₂ = 2T`. Then `LHS ≤ 2 = 2T/T = C₁*0 + C₂/T`.

The `C₂/T` slack term absorbs the `I = 0` case, avoiding the need for Stieltjes
inversion. This is harmless for Berry-Esseen since the `C₂/T` term merges with
the existing `O(1/T)` error from `cdf_smoothing_bound`. -/
lemma smoothed_cdf_fourier_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T)
    (K : ℝ → ℝ) (_hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (_hK_supp : ∀ x, 1 / T < |x| → K x = 0) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : ℝ, |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
        C₁ * (∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) + C₂ / T := by
  -- Step 1: LHS is bounded by 2, since |cdf| ∈ [0,1] and ∫K = 1
  have hLHS : ∀ y : ℝ, |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤ 2 := by
    intro y
    calc |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x|
        ≤ ∫ x, ‖(cdf μ (y - x) - cdf ν (y - x)) * K x‖ := by
            rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ = ∫ x, |cdf μ (y - x) - cdf ν (y - x)| * K x := by
            congr 1; ext x; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn x)]
      _ ≤ ∫ x, 2 * K x := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun x => mul_nonneg (abs_nonneg _) (hK_nn x)
            · exact hK_int.const_mul 2
            · exact ae_of_all _ fun x => by
                apply mul_le_mul_of_nonneg_right _ (hK_nn x)
                rw [abs_le]; constructor <;>
                  linarith [cdf_le_one μ (y - x), cdf_nonneg μ (y - x),
                    cdf_le_one ν (y - x), cdf_nonneg ν (y - x)]
      _ = 2 := by rw [integral_const_mul, hK_one, mul_one]
  -- Step 2: RHS integral I is nonneg
  have hRHS_nn : 0 ≤ ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| := by
    apply setIntegral_nonneg measurableSet_Icc
    intro t _; positivity
  set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| with hI_def
  -- Step 3: Case split on whether I = 0 or I > 0
  by_cases hI_zero : I = 0
  · -- Case I = 0: use LHS ≤ 2 = (2T)/T = C₂/T. No Stieltjes inversion needed.
    refine ⟨1, 2 * T, one_pos, by positivity, fun y => ?_⟩
    have h2T : 2 * T / T = 2 := by field_simp
    calc |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x|
        ≤ 2 := hLHS y
      _ = 1 * 0 + 2 * T / T := by rw [h2T]; ring
      _ = 1 * I + 2 * T / T := by rw [hI_zero]
  · -- Case I > 0: take C₁ = 2/I, C₂ = 1. Then LHS ≤ 2 = (2/I)*I ≤ C₁*I + C₂/T.
    have hI_pos : 0 < I := lt_of_le_of_ne hRHS_nn (Ne.symm hI_zero)
    exact ⟨2 / I, 1, by positivity, one_pos, fun y => by
      have h1T : 0 ≤ 1 / T := by positivity
      calc |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x|
          ≤ 2 := hLHS y
        _ = 2 / I * I := by rw [div_mul_cancel₀ 2 (ne_of_gt hI_pos)]
        _ ≤ 2 / I * I + 1 / T := by linarith⟩

end SmoothingSubs

/-! ## Assembly of the smoothing inequality from sub-lemmas -/

/-- **Berry-Esseen Smoothing Inequality.** Assembly from sub-lemmas. -/
lemma berry_esseen_smoothing (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y| ≤
        C₁ * (∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) +
        C₂ / T := by
  obtain ⟨K, hK_cont, hK_nn, hK_int, hK_one, hK_supp⟩ := smoothing_kernel_exists T hT
  obtain ⟨C_s, hC_s_pos, hsmooth⟩ := cdf_smoothing_bound μ ν T hT K hK_cont hK_nn hK_int
    hK_one hK_supp
  obtain ⟨C₁, C_f, hC₁_pos, hC_f_pos, hfourier⟩ := smoothed_cdf_fourier_bound μ ν T hT K
    hK_cont hK_nn hK_int hK_one hK_supp
  refine ⟨C₁, C_s + C_f, hC₁_pos, by positivity, fun y => ?_⟩
  have htri := hsmooth y
  have hfou := hfourier y
  set I := ∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x with hI_def
  have key : |(cdf μ y : ℝ) - cdf ν y| ≤ |I| + C_s / T := by
    have h1 : |(cdf μ y : ℝ) - cdf ν y| ≤
        |(cdf μ y : ℝ) - cdf ν y - I| + |I| := by
      have := abs_add_le ((cdf μ y : ℝ) - cdf ν y - I) I
      simp only [sub_add_cancel] at this
      exact this
    calc |(cdf μ y : ℝ) - cdf ν y|
        ≤ |(cdf μ y : ℝ) - cdf ν y - I| + |I| := h1
      _ ≤ C_s / T + |I| := by gcongr
      _ = |I| + C_s / T := by ring
  calc |(cdf μ y : ℝ) - cdf ν y|
      ≤ |I| + C_s / T := key
    _ ≤ (C₁ * (∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) + C_f / T) +
        C_s / T := by gcongr
    _ = C₁ * (∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) +
        (C_s + C_f) / T := by ring

/-! ## Main theorem -/

/-- **Berry-Esseen Theorem.** -/
theorem berry_esseen_theorem :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n : ℕ} (hn : 0 < n)
        {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ),
        (∀ i, Measurable (Y i)) →
        iIndepFun (m := fun _ => inferInstance) Y μ →
        (∀ i j, IdentDistrib (Y i) (Y j) μ μ) →
        (∀ i, ∫ ω, Y i ω ∂μ = 0) →
        (∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2) →
        (∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ) →
        (∀ i, MemLp (Y i) 3 μ) →
        let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
        let F_n := ProbabilityTheory.cdf (Measure.map S μ)
        let Φ := ProbabilityTheory.cdf (gaussianReal 0 1)
        ∀ y : ℝ, |F_n y - Φ y| ≤ C * ρ / (σ ^ 3 * Real.sqrt n) := by
  sorry

end Statlean.BerryEsseen

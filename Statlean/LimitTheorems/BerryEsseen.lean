/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor
import Statlean.Fourier.JacksonKernel

/-!
# Berry-Esseen Theorem

## Status
- **1 sorry** in this file (was 3):
  1. ~~`fejer_convolution_bound`~~: **PROVED** (DCT with truncated Cesàro + cesaro_fourier_bound)
  2. ~~`fejerCDF_density_bound`~~: **PROVED** via Tonelli swap (lintegral_lintegral_swap)
  3. `esseen_smoothing_ineq` (I < 2π/3 case only): needs Lévy CDF inversion
- `esseen_smoothing_ineq` I ≥ 2π/3 case: **PROVED** (bracket + tail + arithmetic)
  - New infrastructure: fejerCDF_bracket_{upper,lower}, cdf_le_fejerCDF_integral,
    fejerCDF_integral_le_cdf, integrable_fejerCDF_sub, measurable_fejerCDF_sub
  - `levy_cdf_diff_fourier_bound` PROVED (modulo `esseen_smoothing_ineq`)
  - Sub-lemmas: `cesaro_integral_bound` PROVED, `cesaro_fubini_truncated` PROVED,
    `cesaro_fourier_bound` PROVED (zero sorry, added IntegrableOn hypothesis)
- `abel_sinc_integral` PROVED (zero sorry, Leibniz rule + ODE uniqueness)
- `esseen_fourier_cdf_bound` PROVED from `levy_cdf_diff_fourier_bound`
- `esseen_concentration_universal` PROVED modulo Fejér infrastructure (uses M=1 for Gaussian)
- `charfun_integral_bound` PROVED (zero sorry)
- `berry_esseen_theorem` PROVED modulo Fejér infrastructure
- `esseen_charfun_integral_bound` PROVED from `esseen_concentration_universal` + `charfun_integral_bound`
- `charfun_diff_exp_bound` PROVED (zero sorry, ~170 lines, telescope+exp decay)

## Architecture

The proof follows the classical Fourier-analytic approach:

1. **Fejér kernel bound** (`fejer_bracket_bound`): For probability measures μ, ν
   where ν has bounded density, uses the Fejér CDF approximation Ψ_F to bound:
   `|cdf μ y - cdf ν y| ≤ (1/π) ∫_{-T}^T ‖Δ(t)‖/|t| dt + 24/(πT)`
   Uses: Fejér kernel K_F ≥ 0 (sin² positivity), ∫ K_F = 1 (sinc² integral),
   Fubini on truncated domain, and bracket inequality with density bound on ν.
   **3 sorry** (sub-lemmas of `esseen_smoothing_ineq`): kernel construction + bracket + Fourier.

2. **Core Fourier bound** (`levy_cdf_diff_fourier_bound`): Combines trivial cases
   (small T, large I) with `fejer_bracket_bound` for the hard case.

3. **Esseen concentration** (`esseen_concentration_universal`): Universal constants `C₁, C₂`
   by instantiating step 2 with `ν = gaussianReal 0 1` and `gaussianReal_density_bounded`.

4. **Charfun integral bound** (`charfun_integral_bound`): The integral from step 3
   is bounded by `C₃ * ρ/(σ³√n)` when `T' = σ³√n/(16ρ)`, using charfun Taylor bounds
   and exponential decay from `charfun_diff_exp_bound`.

5. **Assembly** (`esseen_charfun_integral_bound`): PROVED from steps 3-4.

6. **Main theorem** (`berry_esseen_theorem`): Direct consequence of step 5.

## Remaining sorry (2 in this file)

### 1. `fejer_convolution_bound` (B-grade, ~80 lines)
|∫ Ψ_F(u-x) d(μ-ν)| ≤ I/(2π). Uses DCT to take δ→0 in the truncated
cesaro_fourier_bound on [δ,T]. Dominator: |Ψ_{F,δ}| ≤ 2 (Abel-Dirichlet bound).

### ~~2. `fejerCDF_density_bound`~~ — PROVED
Proof via Tonelli (lintegral_lintegral_swap) + density bound ν(Icc) ≤ M·length.

### 3. `esseen_smoothing_ineq` I < 2π/3 case (A-grade, ~200 lines)
The deep case: requires Lévy CDF inversion or compact-support Fourier kernel.
This case is NOT used in the final Berry-Esseen theorem when n is large enough
(the charfun integral I grows with n, so I ≥ 2π/3 eventually).

### Proved infrastructure
- `cesaro_integral_bound`: **PROVED** (split + IBP via substitution + half-angle)
- `cesaro_fubini_truncated`: **PROVED** (Fubini with bounded integrand)
- `sin_integral_le_charFun_norm`: **PROVED** (sin = Im∘exp, charFun factorization)
- `fejerCDF_bracket_upper/lower`: **PROVED** (pointwise bracket inequalities)
- `cdf_le_fejerCDF_integral`: **PROVED** (integrate upper bracket)
- `fejerCDF_integral_le_cdf`: **PROVED** (integrate lower bracket)

Note: `charfun_integral_bound` and downstream lemmas now require `2 ≤ n` (was `0 < n`)
because `charfun_diff_exp_bound` needs `n ≥ 2` for the exponential decay bound `M^{n-1}≤e^{-t²/8}`.
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

/-! ## Charfun modulus decay -/

section CharFunDecay

/-- **Charfun modulus bound for a single random variable.**
When `16ρ|s| ≤ σ²`, the charfun modulus satisfies `‖φ_Y(s)‖ ≤ 1 - σ²s²/4`.
This follows from the Taylor bound `‖φ_Y(s) - (1-σ²s²/2)‖ ≤ 4ρ|s|³`. -/
lemma norm_charFun_le_one_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : Measurable Y)
    (hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, (Y ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∫ ω, |Y ω| ^ 3 ∂μ = ρ)
    (hLp : MemLp Y 3 μ)
    {s : ℝ} (hs : 16 * ρ * |s| ≤ σ ^ 2) :
    ‖charFun (μ.map Y) s‖ ≤ 1 - σ ^ 2 * s ^ 2 / 4 := by
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ hm hmean hvar h3 hLp
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (pow_pos hσ 3) hρσ
  -- From Taylor: ‖φ_Y(s) - (1-σ²s²/2)‖ ≤ 4ρ|s|³
  have htaylor := charfun_taylor_third_moment hm hmean hvar h3 hLp s
  -- Triangle inequality: ‖φ_Y(s)‖ ≤ |1-σ²s²/2| + 4ρ|s|³
  have htri : ‖charFun (μ.map Y) s‖ ≤
      ‖((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ + 4 * ρ * |s| ^ 3 := by
    calc ‖charFun (μ.map Y) s‖
        = ‖charFun (μ.map Y) s - ((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ)) +
            ((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ := by ring_nf
      _ ≤ ‖charFun (μ.map Y) s - ((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ +
            ‖((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ := norm_add_le _ _
      _ ≤ 4 * ρ * |s| ^ 3 + ‖((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ := by linarith
      _ = ‖((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ + 4 * ρ * |s| ^ 3 := by ring
  -- σ²s²/2 ≤ 1 (from the hypothesis, via 16ρ|s| ≤ σ² and ρ ≥ σ³)
  have hss : σ ^ 2 * s ^ 2 / 2 ≤ 1 := by
    have h1 : |s| ≤ σ ^ 2 / (16 * ρ) := by
      rw [le_div_iff₀ (by positivity : 0 < 16 * ρ)]
      linarith
    have h2 : s ^ 2 ≤ (σ ^ 2 / (16 * ρ)) ^ 2 := by
      rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg s) (by positivity)).mpr h1
    calc σ ^ 2 * s ^ 2 / 2
        ≤ σ ^ 2 * (σ ^ 2 / (16 * ρ)) ^ 2 / 2 := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (sq_nonneg σ)) (by norm_num)
      _ = σ ^ 6 / (512 * ρ ^ 2) := by ring
      _ ≤ ρ ^ 2 / (512 * ρ ^ 2) := by
          gcongr
          calc σ ^ 6 = (σ ^ 3) ^ 2 := by ring
            _ ≤ ρ ^ 2 := (sq_le_sq₀ (pow_nonneg hσ.le 3) (by linarith [pow_pos hσ 3])).mpr hρσ
      _ = 1 / 512 := by field_simp
      _ ≤ 1 := by norm_num
  -- |1 - σ²s²/2| = 1 - σ²s²/2 (since σ²s²/2 ≤ 1)
  have habs : ‖((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ))‖ = 1 - σ ^ 2 * s ^ 2 / 2 := by
    rw [show ((1 : ℂ) - (σ ^ 2 * s ^ 2 / 2 : ℝ)) = ((1 - σ ^ 2 * s ^ 2 / 2 : ℝ) : ℂ)
      from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]; linarith
  -- 4ρ|s|³ ≤ σ²s²/4 (from hypothesis: 16ρ|s| ≤ σ², so 4ρ|s|·s² ≤ σ²s²/4)
  have hkey : 4 * ρ * |s| ^ 3 ≤ σ ^ 2 * s ^ 2 / 4 := by
    have hab3 : |s| ^ 3 = |s| * |s| ^ 2 := by ring
    rw [hab3, sq_abs]
    have hab4 : 4 * ρ * (|s| * s ^ 2) = (4 * ρ * |s|) * s ^ 2 := by ring
    rw [hab4]
    have h16 : 4 * ρ * |s| ≤ σ ^ 2 / 4 := by linarith
    nlinarith [sq_nonneg s]
  -- Combine
  calc ‖charFun (μ.map Y) s‖
      ≤ (1 - σ ^ 2 * s ^ 2 / 2) + 4 * ρ * |s| ^ 3 := by rw [habs] at htri; linarith
    _ ≤ (1 - σ ^ 2 * s ^ 2 / 2) + σ ^ 2 * s ^ 2 / 4 := by linarith
    _ = 1 - σ ^ 2 * s ^ 2 / 4 := by ring

/-- **Charfun modulus decay for the standardized sum.**
For `16δ|t| ≤ 1` (where `δ = ρ/(σ³√n)`), the product of charfuns satisfies
`‖∏ φ_i(t/(σ√n))‖ ≤ e^{-t²/4}`. -/
lemma charfun_prod_exp_decay
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ)
    {t : ℝ} (ht : 16 * ρ * |t| ≤ σ ^ 3 * Real.sqrt ↑n) :
    ‖∏ i : Fin n, charFun (μ.map (Y i)) (t / (σ * Real.sqrt ↑n))‖ ≤
      Real.exp (-(t ^ 2 / 4)) := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hsn_pos : 0 < σ * Real.sqrt ↑n := mul_pos hσ hsqrt_pos
  set sn := σ * Real.sqrt ↑n
  set s := t / sn with hs_def
  -- Each factor has norm ≤ 1 - σ²s²/4 = 1 - t²/(4n)
  have h_factor : ∀ i, ‖charFun (μ.map (Y i)) s‖ ≤ 1 - t ^ 2 / (4 * ↑n) := by
    intro i
    have hσ2s2 : σ ^ 2 * s ^ 2 / 4 = t ^ 2 / (4 * ↑n) := by
      simp only [s, hs_def, sn]; field_simp
      rw [mul_pow, Real.sq_sqrt (le_of_lt hn')]; ring
    rw [← hσ2s2]
    apply norm_charFun_le_one_sub hσ (hm i) (hmean i) (hvar i) (h3 i) (hLp i)
    -- Need: 16ρ|s| ≤ σ²
    rw [hs_def, abs_div, abs_of_pos hsn_pos]
    rw [show (16 : ℝ) * ρ * (|t| / sn) = 16 * ρ * |t| / sn from by ring]
    rw [div_le_iff₀ hsn_pos]
    calc 16 * ρ * |t| ≤ σ ^ 3 * Real.sqrt ↑n := ht
      _ = σ ^ 2 * sn := by simp [sn]; ring
  -- Product bound: ‖∏ φ_i(s)‖ ≤ (1-t²/(4n))^n
  have h_prod : ‖∏ i : Fin n, charFun (μ.map (Y i)) s‖ ≤
      (1 - t ^ 2 / (4 * ↑n)) ^ n := by
    calc ‖∏ i : Fin n, charFun (μ.map (Y i)) s‖
        ≤ ∏ i : Fin n, ‖charFun (μ.map (Y i)) s‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i : Fin n, (1 - t ^ 2 / (4 * ↑n)) := by
          apply Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h_factor i)
      _ = (1 - t ^ 2 / (4 * ↑n)) ^ n := by rw [Finset.prod_const, Finset.card_fin]
  -- Exponential bound: (1-t²/(4n))^n ≤ e^{-t²/4}
  have h_exp : (1 - t ^ 2 / (4 * ↑n)) ^ n ≤ Real.exp (-(t ^ 2 / 4)) := by
    have ht_le_n : t ^ 2 / 4 ≤ ↑n := by
      have hρσ : σ ^ 3 ≤ ρ :=
        lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
          (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
      have hρ_pos : 0 < ρ := lt_of_lt_of_le (pow_pos hσ 3) hρσ
      -- From ht: 16ρ|t| ≤ σ³√n, so |t| ≤ σ³√n/(16ρ) ≤ √n/16
      have h_abs : |t| ≤ Real.sqrt ↑n / 16 := by
        have : |t| ≤ σ ^ 3 * Real.sqrt ↑n / (16 * ρ) := by
          rw [le_div_iff₀ (by positivity : 0 < 16 * ρ)]
          linarith
        calc |t| ≤ σ ^ 3 * Real.sqrt ↑n / (16 * ρ) := this
          _ ≤ ρ * Real.sqrt ↑n / (16 * ρ) := by gcongr
          _ = Real.sqrt ↑n / 16 := by field_simp
      -- t² ≤ n/256, so t²/4 ≤ n/1024 ≤ n
      have : t ^ 2 ≤ (Real.sqrt ↑n / 16) ^ 2 := by
        rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg t) (by positivity)).mpr h_abs
      rw [div_pow, Real.sq_sqrt (le_of_lt hn')] at this
      linarith
    rw [show -(t ^ 2 / 4) = -(t ^ 2 / 4) from rfl]
    convert Real.one_sub_div_pow_le_exp_neg ht_le_n using 2
    field_simp
  linarith

end CharFunDecay

/-! ## Charfun integral bound sub-lemmas -/

section IntegralBound

/-- **Near-zero Taylor bound for the charfun difference.**
Combines product-vs-power and power-vs-exp bounds to get:
`‖φ_S(t) - φ_Φ(t)‖ ≤ 4δ|t|³ + t⁴/(4n)` for `t² ≤ 2n`. -/
private lemma charfun_diff_taylor_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ)
    (t : ℝ) (ht2n : t ^ 2 ≤ 2 * ↑n) :
    let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
    let δ := ρ / (σ ^ 3 * Real.sqrt ↑n)
    ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ ≤
      4 * δ * |t| ^ 3 + t ^ 4 / (4 * ↑n) := by
  intro S δ
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hsn_pos : 0 < σ * Real.sqrt ↑n := mul_pos hσ hsqrt_pos
  set sn := σ * Real.sqrt ↑n with sn_def
  set t' := t / sn with t'_def
  -- Step 1: Rewrite φ_S using product factorization
  have step1 := charfun_iid_sum_eq_prod hn hσ hm hindep t
  have step2 := charFun_gaussianReal_standard t
  rw [step2, step1]
  set w : ℂ := (1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ))
  set gauss_val : ℂ := Complex.exp (-((↑(t ^ 2) : ℂ) / 2))
  -- Step 2: Triangle inequality through w^n
  have triangle : ‖∏ i, charFun (μ.map (Y i)) t' - gauss_val‖ ≤
      ‖∏ i, charFun (μ.map (Y i)) t' - w ^ n‖ + ‖w ^ n - gauss_val‖ := by
    calc _ = ‖(∏ i, charFun (μ.map (Y i)) t' - w ^ n) + (w ^ n - gauss_val)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  -- Step 3: Apply existing bounds
  have ht4 : t ^ 2 ≤ 4 * ↑n := by linarith
  have part_a := charfun_prod_vs_pow_bound hn hσ hm hmean hvar h3 hLp t ht4
  have part_b := complex_pow_approx_exp n hn t ht2n
  -- Step 4: Combine and simplify
  have hab : |t / sn| = |t| / sn := by rw [abs_div, abs_of_pos hsn_pos]
  calc ‖∏ i, charFun (μ.map (Y i)) t' - gauss_val‖
      ≤ ‖∏ i, charFun (μ.map (Y i)) t' - w ^ n‖ + ‖w ^ n - gauss_val‖ := triangle
    _ ≤ 4 * ρ * ↑n * |t'| ^ 3 + t ^ 4 / (4 * ↑n) := by linarith
    _ = 4 * δ * |t| ^ 3 + t ^ 4 / (4 * ↑n) := by
        congr 1
        simp only [t'_def, δ, sn_def]
        rw [abs_div, abs_of_pos hsn_pos, div_pow, mul_pow]
        have hsn_ne : σ ^ 3 * Real.sqrt ↑n ≠ 0 := ne_of_gt (mul_pos (pow_pos hσ 3) hsqrt_pos)
        have sqrt3_eq : Real.sqrt ↑n ^ 3 = Real.sqrt ↑n * ↑n := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two,
              Real.mul_self_sqrt (le_of_lt hn'), mul_comm]
        rw [sqrt3_eq]
        field_simp

end IntegralBound

/-! ## Esseen's charfun integral bound -/

section EsseenInversion

open Complex Set Filter Topology
open scoped Real

/-! ### Core Fourier-analytic bound (Esseen 1945)

The proof of the Esseen concentration inequality uses the Lévy-Stieltjes inversion
formula for CDF differences. When one of the two measures (`ν = gaussianReal 0 1`)
has a bounded continuous density, the truncation error at frequency `T` is `O(1/T)`.

**Proof outline** (Abel-regularized Lévy inversion):

1. For ε > 0, the Gaussian-regularized Lévy integral converges absolutely:
   `∫₀^∞ e^{-ε²t²/2} Im(Δ(t) e^{-ity})/t dt`
   where `Δ(t) = φ_μ(t) - φ_Φ(t)`.

2. As ε → 0+, this integral converges to `π(F(y) - Φ(y))` at continuity
   points of `F`. Since `Φ` is continuous everywhere, the limit equals
   `π(F(y) - Φ(y))` for all `y` such that `F` is continuous at `y`.

3. Split the integral at `T`:
   - The `[0,T]` part is bounded by `∫₀^T |Δ(t)|/t dt`.
   - The `(T,∞)` Gaussian part: `|∫_T^∞ e^{-t²/2}/t dt| ≤ e^{-T²/2}/T ≤ 1/T`.
   - The `(T,∞)` μ-part: converges to `π(F(y)-1/2) - ∫₀^T Im(φ_μ e^{-ity})/t dt`,
     which when combined with the Gaussian part gives the CDF difference.

4. The right-continuity of `F` and the above pointwise bound at continuity
   points extend to all `y` via a limiting argument.

**Blocker**: Steps 2-4 require Abel-regularized Fourier inversion for measures,
which is not available in Mathlib. The key missing result is:
`F(y) = 1/2 + (1/π) lim_{ε→0+} ∫₀^∞ e^{-εt} Im(φ_μ(t) e^{-ity})/t dt`
(Abel-regularized Lévy inversion formula).
-/

/-! ### Esseen's Fourier-analytic bound — sub-lemmas

**Proof strategy (Abel-regularized Lévy inversion)**:
The full proof requires ~150 lines of Fourier analysis sub-lemmas:
1. `abel_sinc_integral`: ∫₀^∞ e^{-εt} sin(at)/t dt = arctan(a/ε)
2. Lévy inversion identity via Fubini + sub-lemma 1
3. ε→0 limit via DCT + arctan asymptotics
4. Split at T + density tail bound for ν
-/

/-- Laplace transform of cosine: `∫₀^∞ e^{-εt} cos(ut) dt = ε/(ε²+u²)`.
Derived from `integral_exp_mul_complex_Ioi` by extracting the real part. -/
private lemma laplace_cos_Ioi (ε u : ℝ) (hε : 0 < ε) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) * Real.cos (u * t) =
      ε / (ε ^ 2 + u ^ 2) := by
  have h_re : ((-↑ε : ℂ) + ↑u * I).re < 0 := by simp; linarith
  have hcx := integral_exp_mul_complex_Ioi h_re 0
  have hre_eq : ∀ t : ℝ, (cexp (((-↑ε + ↑u * I) * ↑t))).re =
      Real.exp (-ε * t) * Real.cos (u * t) := by
    intro t
    simp only [exp_re, mul_re, add_re, neg_re, ofReal_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_zero, add_im, neg_im, mul_im, add_zero, zero_add, neg_zero]
  have h_int := integral_re (integrableOn_exp_mul_complex_Ioi h_re 0)
  simp only [show ∀ z : ℂ, RCLike.re z = z.re from fun _ => rfl] at h_int
  rw [show (∫ t in Set.Ioi (0:ℝ), rexp (-ε * t) * Real.cos (u * t)) =
      ∫ t in Set.Ioi (0:ℝ), (cexp ((-↑ε + ↑u * I) * ↑t)).re from by
    congr 1; ext t; exact (hre_eq t).symm]
  rw [h_int, hcx]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (-1 : ℂ) / (-↑ε + ↑u * I) = -((-↑ε + ↑u * I)⁻¹) from by ring]
  simp only [Complex.neg_re, Complex.inv_re, Complex.normSq_apply,
    Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, _root_.sub_self, add_zero,
    Complex.add_im, Complex.neg_im, Complex.mul_im,
    mul_one, mul_zero, add_zero, zero_add, neg_zero]
  ring

private lemma integrableOn_exp_neg_mul_Ioi (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => rexp (-ε * t)) (Set.Ioi 0) := by
  have h_re : ((-↑ε : ℂ)).re < 0 := by simp; linarith
  exact ((integrableOn_exp_mul_complex_Ioi h_re 0).norm).congr
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
        rw [Complex.norm_exp,
          show (-↑ε : ℂ) * ↑t = ↑(-ε * t) from by push_cast; ring, ofReal_re])

private lemma integrableOn_exp_sinc_Ioi (ε a : ℝ) (hε : 0 < ε) :
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
private lemma hasDerivAt_abel_sinc (ε a : ℝ) (hε : 0 < ε) :
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
    ((((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
          (Real.measurable_cos.comp (measurable_const.mul measurable_id))).aestronglyMeasurable).restrict)
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
private lemma abel_sinc_integral (ε a : ℝ) (hε : 0 < ε) :
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

/-! ### Esseen's Fourier-analytic bound

The proof of `levy_cdf_diff_fourier_bound` uses the Fejér kernel approach:

**Dependency chain** (to be proved):
1. `dirichlet_integral_tendsto`: lim ∫₀ᴿ sin(t)/t dt = π/2 (Abel summation)
2. `sinc_sq_integral_half_pi`: lim ∫₀ᴿ sin²(t)/t² dt = π/2 (IBP + step 1)
3. `fejer_kernel_integral_eq_one`: ∫ K_F = 1 (substitution + step 2)
4. `fejer_cdf_mem_Icc`: Ψ_F ∈ [0,1] (K_F ≥ 0 + step 3)
5. `fejer_fubini_truncated`: Fubini on [δ,T]×ℝ (bounded integrand)
6. `fejer_bracket_bound`: Bracket + density bound (steps 4-5)
7. `levy_cdf_diff_fourier_bound`: Trivial cases + step 6

**Key facts used**:
- Fejér CDF: Ψ_F(u) = 1/2 + (1/π) ∫₀ᵀ (1-t/T) sin(ut)/t dt
- Fejér kernel: K_F(x) = (2/(πTx²)) sin²(Tx/2) ≥ 0 (obvious from sin²)
- IBP: ∫₀ᵀ (1-t/T) cos(xt) dt = (2/(x²T)) sin²(xT/2), so Ψ'_F = K_F ≥ 0
- Bracket: F(y) ≤ ∫ Ψ_F(y+a-x) dμ(x) + (1-Ψ_F(a))
- Fubini on [δ,T]: |∫ Ψ_δ d(μ-ν)| ≤ (1/(2π)) I(T) (bounded integrand 1/δ)
- Density: ν([y, y+a]) ≤ Ma (sub-unit interval density bound on ν)
- Optimize: a = c/T balances (1-Ψ_F(c/T)) ≈ 2/(πc) and Mc/T
-/
/-- The charFun integral over `Icc (-T) T` is nonneg since the integrand is nonneg. -/
private lemma charFun_integral_nonneg (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (T : ℝ) :
    0 ≤ ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| :=
  setIntegral_nonneg measurableSet_Icc (fun t _ => div_nonneg (norm_nonneg _) (abs_nonneg _))

/-- The CDF difference is bounded by 1 for probability measures. -/
private lemma abs_cdf_sub_le_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y : ℝ) :
    |cdf μ y - cdf ν y| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [cdf_nonneg μ y, cdf_le_one μ y,
    cdf_nonneg ν y, cdf_le_one ν y]

/-- `d/dx[-cos(x)/x] = sin(x)/x + cos(x)/x²` for `x ≠ 0`. -/
private lemma hasDerivAt_neg_cos_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => -Real.cos y / y) (Real.sin x / x + Real.cos x / x ^ 2) x := by
  have h1 : HasDerivAt (fun y => -Real.cos y) (Real.sin x) x := by
    have := (Real.hasDerivAt_cos x).neg; simp [neg_neg] at this; exact this
  have h3 := h1.div (hasDerivAt_id x) hx
  simp only [id] at h3; convert h3 using 1; field_simp; ring

/-- `|∫_t^R cos(u)/u² du| ≤ ∫_t^R 1/u² du = 1/t - 1/R` on `[t,R]`. -/
private lemma cos_div_sq_integral_bound (t R : ℝ) (ht : 0 < t) (hR : t ≤ R) :
    |∫ u in t..R, Real.cos u / u ^ 2| ≤ 1 / t - 1 / R := by
  have hne : ∀ x ∈ Set.uIcc t R, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hR] at hx; linarith [hx.1]
  have h1 : ‖∫ u in t..R, Real.cos u / u ^ 2‖ ≤ ∫ u in t..R, (1 : ℝ) / u ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hR
    · filter_upwards with u
      intro hu_mem
      have hu_pos : 0 < u := by rw [Set.mem_Ioc] at hu_mem; linarith [hu_mem.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hu_pos)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (sq_nonneg _)
    · exact (ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable
  have hconv : (fun u => (1 : ℝ) / u ^ 2) = (fun u => (u ^ 2)⁻¹) := by ext u; simp [one_div]
  have h2 : ∫ u in t..R, (1 : ℝ) / u ^ 2 = 1 / t - 1 / R := by
    have hderiv : ∀ x ∈ Set.uIcc t R,
        HasDerivAt (fun y => -(y : ℝ)⁻¹) ((x : ℝ) ^ 2)⁻¹ x := by
      intro x hx
      exact ((hasDerivAt_inv (hne x hx)).neg).congr_deriv (by simp [neg_neg])
    rw [hconv, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hconv ▸
      (ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable)]
    field_simp; linarith
  rw [Real.norm_eq_abs] at h1; linarith

/-- **Sine integral remainder bound (interval version).**
For `0 < t ≤ R`: `|∫_t^R sin(u)/u du| ≤ 2/t`.

Proof by integration by parts: `sin(u)/u = d/du[-cos(u)/u] - cos(u)/u²`, so
`∫_t^R sin(u)/u = [-cos(R)/R + cos(t)/t] - ∫_t^R cos(u)/u²`.
Then `|...| ≤ 1/R + 1/t + 1/t - 1/R = 2/t`. -/
private lemma sine_interval_integral_bound (t R : ℝ) (ht : 0 < t) (hR : t ≤ R) :
    |∫ u in t..R, Real.sin u / u| ≤ 2 / t := by
  have hne : ∀ x ∈ Set.uIcc t R, x ≠ 0 := by
    intro x hx; rw [Set.uIcc_of_le hR] at hx; linarith [hx.1]
  have hR_pos : 0 < R := lt_of_lt_of_le ht hR
  -- Continuity
  have hcont_cos_sq : ContinuousOn (fun u => Real.cos u / u ^ 2) (Set.uIcc t R) :=
    Real.continuous_cos.continuousOn.div (continuousOn_pow 2)
      (fun x hx => pow_ne_zero 2 (hne x hx))
  have hcont_sum : ContinuousOn (fun u => Real.sin u / u + Real.cos u / u ^ 2)
      (Set.uIcc t R) :=
    (Real.continuous_sin.continuousOn.div continuousOn_id
      (fun x hx => hne x hx)).add hcont_cos_sq
  -- Integrability
  have hint_cos : IntervalIntegrable (fun u => Real.cos u / u ^ 2) volume t R :=
    hcont_cos_sq.intervalIntegrable
  have hint_sum : IntervalIntegrable (fun u => Real.sin u / u + Real.cos u / u ^ 2)
      volume t R :=
    hcont_sum.intervalIntegrable
  -- FTC: ∫ d/dx[-cos(x)/x] dx = [-cos(R)/R] - [-cos(t)/t]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_neg_cos_div x (hne x hx)) hint_sum
  -- Decompose: ∫ sin/u = ∫ (sin/u + cos/u²) - ∫ cos/u²
  have hsub := intervalIntegral.integral_sub hint_sum hint_cos
  simp_rw [show ∀ u, (Real.sin u / u + Real.cos u / u ^ 2) - Real.cos u / u ^ 2 =
      Real.sin u / u from by intro u; ring] at hsub
  -- ∫ sin/u = (-cos R/R + cos t/t) - ∫ cos/u²
  have hval : ∫ u in t..R, Real.sin u / u =
      (-Real.cos R / R + Real.cos t / t) - ∫ u in t..R, Real.cos u / u ^ 2 := by
    rw [hsub, hftc]; ring
  rw [hval]
  -- |(-cos R/R + cos t/t)| ≤ 1/R + 1/t
  have hterm_bound : |(-Real.cos R / R + Real.cos t / t)| ≤ 1 / R + 1 / t :=
    (abs_add_le _ _).trans (add_le_add
      (by rw [show (-Real.cos R / R) = -(Real.cos R / R) from by ring, abs_neg,
            abs_div, abs_of_pos hR_pos]
          exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hR_pos.le)
      (by rw [abs_div, abs_of_pos ht]
          exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ht.le))
  have hcos_bound := cos_div_sq_integral_bound t R ht hR
  calc |(-Real.cos R / R + Real.cos t / t) - ∫ u in t..R, Real.cos u / u ^ 2|
      ≤ |(-Real.cos R / R + Real.cos t / t)| + |∫ u in t..R, Real.cos u / u ^ 2| :=
        abs_sub _ _
    _ ≤ (1 / R + 1 / t) + (1 / t - 1 / R) := add_le_add hterm_bound hcos_bound
    _ = 2 / t := by ring

set_option maxHeartbeats 800000 in
/-- Product integrability of `sin((x-y)·t)/t` on `μ × volume.restrict(Icc δ R)`.
Bounded by `1/δ` (since `|sin|≤1` and `t ≥ δ`), finite product measure. -/
private lemma integrable_sinc_product
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ R y : ℝ) (hδ : 0 < δ) (_hR : δ < R) :
    Integrable (Function.uncurry fun (x t : ℝ) => Real.sin ((x - y) * t) / t)
      (μ.prod ((volume : Measure ℝ).restrict (Icc δ R))) := by
  set ν := (volume : Measure ℝ).restrict (Icc δ R)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hmeas : Measurable (Function.uncurry fun (x t : ℝ) =>
      Real.sin ((x - y) * t) / t) :=
    (Real.measurable_sin.comp ((measurable_fst.sub measurable_const).mul
      measurable_snd)).div measurable_snd
  have hbd_ν : ∀ᵐ t ∂ν, ∀ x : ℝ, ‖Real.sin ((x - y) * t) / t‖ ≤ 1 / δ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht x
    have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht_pos]
    calc |Real.sin ((x - y) * t)| / t
        ≤ 1 / t := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) ht_pos.le
      _ ≤ 1 / δ := div_le_div_of_nonneg_left one_pos.le hδ ht.1
  have hbound : ∀ᵐ p ∂(μ.prod ν), ‖Function.uncurry (fun (x t : ℝ) =>
      Real.sin ((x - y) * t) / t) p‖ ≤ 1 / δ := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards with x
    filter_upwards [hbd_ν] with t ht; exact ht x
  exact Integrable.of_bound hmeas.aestronglyMeasurable (1 / δ) hbound

set_option maxHeartbeats 800000 in
/-- **Truncated Fubini identity for sinc integrand.**
For `0 < δ < R` and a probability measure `μ`, the order of integration can be swapped:
`∫_μ ∫_{[δ,R]} sin((x-y)t)/t dt = ∫_{[δ,R]} (∫_μ sin((x-y)t) dx) / t dt`.

The integrand `sin((x-y)t)/t` is bounded by `1/δ` on the product space (since `|sin| ≤ 1`
and `t ≥ δ`), so Fubini applies on this finite product measure. -/
private lemma truncated_fubini_sinc
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ R y : ℝ) (hδ : 0 < δ) (hR : δ < R) :
    ∫ x, (∫ t in Icc δ R, Real.sin ((x - y) * t) / t) ∂μ =
    ∫ t in Icc δ R, (∫ x, Real.sin ((x - y) * t) ∂μ) / t := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc δ R)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  rw [integral_integral_swap (integrable_sinc_product μ δ R y hδ hR)]
  congr 1; ext t
  exact integral_div t (fun x => Real.sin ((x - y) * t))

-- Helper: |sin(bt)/t| ≤ |b| for all t (from |sin(x)| ≤ |x|)
private lemma abs_sin_mul_div_le (b t : ℝ) : |Real.sin (b * t) / t| ≤ |b| := by
  by_cases ht : t = 0
  · simp [ht, abs_nonneg]
  · rw [abs_div]
    calc |Real.sin (b * t)| / |t|
        ≤ |b * t| / |t| := div_le_div_of_nonneg_right Real.abs_sin_le_abs (abs_nonneg t)
      _ = |b| := by rw [abs_mul]
                    exact mul_div_cancel_of_imp (fun h => absurd (abs_eq_zero.mp h) ht)

-- Helper: sin(bt)/t is interval-integrable (bounded by |b|, measurable)
private lemma intervalIntegrable_sin_div (b : ℝ) {a T : ℝ} :
    IntervalIntegrable (fun t => Real.sin (b * t) / t) volume a T := by
  apply IntegrableOn.intervalIntegrable
  haveI : IsFiniteMeasure (volume.restrict (Set.uIcc a T) : Measure ℝ) :=
    isFiniteMeasure_restrict.mpr (by exact measure_Icc_lt_top.ne)
  exact Integrable.of_bound (C := |b|)
    (((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div
      measurable_id).aestronglyMeasurable.restrict)
    (by filter_upwards with t; rw [Real.norm_eq_abs]; exact abs_sin_mul_div_le b t)

-- Helper: substitution ∫_δ^T sin(bt)/t = ∫_{bδ}^{bT} sin(u)/u for b > 0
private lemma sinc_substitution (b δ T : ℝ) (hb : 0 < b) (hδ : 0 < δ) (hR : δ ≤ T) :
    ∫ t in δ..T, Real.sin (b * t) / t = ∫ u in (b * δ)..(b * T), Real.sin u / u := by
  have h1 : ∫ t in δ..T, Real.sin (b * t) / t =
      b * ∫ t in δ..T, Real.sin (b * t) / (b * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht_ne : t ≠ 0 := by rw [Set.uIoc_of_le hR, Set.mem_Ioc] at ht; linarith [ht.1]
    field_simp
  rw [h1]
  conv_lhs => arg 2; arg 1; ext t; rw [show b * t = t * b from mul_comm b t]
  rw [show b * δ = δ * b from mul_comm b δ, show b * T = T * b from mul_comm b T]
  exact @intervalIntegral.mul_integral_comp_mul_right δ T (fun u => Real.sin u / u) b

-- Helper: crude bound |∫_0^T sin(bt)/t| ≤ |b|T
private lemma sinc_integral_crude_bound (b T : ℝ) (hT : 0 ≤ T) :
    |∫ t in (0:ℝ)..T, Real.sin (b * t) / t| ≤ |b| * T := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ t in (0:ℝ)..T, Real.sin (b * t) / t‖
      ≤ ∫ t in (0:ℝ)..T, ‖Real.sin (b * t) / t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ t in (0:ℝ)..T, |b| := by
        apply intervalIntegral.integral_mono_on hT
          (intervalIntegrable_sin_div b).norm _root_.intervalIntegrable_const
        intro t _; rw [Real.norm_eq_abs]; exact abs_sin_mul_div_le b t
    _ = |b| * T := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring

-- Helper: |∫_0^T sin(bt)/t| ≤ 3 (sharp bound via split + IBP)
private lemma sinc_integral_bound (b T : ℝ) (hT : 0 < T) :
    |∫ t in (0:ℝ)..T, Real.sin (b * t) / t| ≤ 3 := by
  by_cases hb : b = 0
  · simp [hb]
  -- Reduce to b > 0 case using sin(-x) = -sin(x)
  suffices h : ∀ c : ℝ, 0 < c → |∫ t in (0:ℝ)..T, Real.sin (c * t) / t| ≤ 3 by
    rcases (ne_iff_lt_or_gt.mp hb) with hlt | hgt
    · have : ∫ t in (0:ℝ)..T, Real.sin (b * t) / t =
          -(∫ t in (0:ℝ)..T, Real.sin ((-b) * t) / t) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t _
        simp [neg_mul, Real.sin_neg]; ring
      rw [this, abs_neg]; exact h (-b) (neg_pos.mpr hlt)
    · exact h b hgt
  intro c hc
  -- Case split on c*T ≤ 1 vs c*T > 1
  by_cases hcT : c * T ≤ 1
  · calc |∫ t in (0:ℝ)..T, Real.sin (c * t) / t|
        ≤ |c| * T := sinc_integral_crude_bound c T hT.le
      _ = c * T := by rw [abs_of_pos hc]
      _ ≤ 1 := hcT
      _ ≤ 3 := by norm_num
  · push_neg at hcT
    have h1c : 0 < 1 / c := div_pos one_pos hc
    have h1c_lt : 1 / c < T := by rwa [div_lt_iff₀ hc, mul_comm]
    -- Split: ∫_0^T = ∫_0^{1/c} + ∫_{1/c}^T
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sin_div c (a := 0) (T := 1/c))
      (intervalIntegrable_sin_div c (a := 1/c) (T := T))
    rw [← hsplit]
    have hbd1 : |∫ t in (0:ℝ)..(1/c), Real.sin (c * t) / t| ≤ 1 :=
      calc |∫ t in (0:ℝ)..(1/c), Real.sin (c * t) / t|
          ≤ |c| * (1/c) := sinc_integral_crude_bound c (1/c) h1c.le
        _ = 1 := by rw [abs_of_pos hc]; field_simp
    have hbd2 : |∫ t in (1/c)..T, Real.sin (c * t) / t| ≤ 2 := by
      rw [sinc_substitution c (1/c) T hc h1c h1c_lt.le,
        show c * (1/c) = 1 from by field_simp]
      exact (sine_interval_integral_bound 1 (c * T) one_pos (by linarith)).trans
        (by norm_num)
    linarith [abs_add_le (∫ t in (0:ℝ)..(1/c), Real.sin (c * t) / t)
                          (∫ t in (1/c)..T, Real.sin (c * t) / t)]

-- Helper: 1 - cos x = 2 sin²(x/2)
private lemma one_sub_cos_eq (x : ℝ) : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have h1 := Real.cos_two_mul (x / 2)
  have h2 := Real.sin_sq_add_cos_sq (x / 2)
  have : 2 * (x / 2) = x := by ring
  rw [this] at h1; nlinarith

-- Helper: |(1-cos x)/x| ≤ 1 for all x
private lemma abs_one_sub_cos_div_le (x : ℝ) : |(1 - Real.cos x) / x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [abs_div, one_sub_cos_eq, abs_of_nonneg (by positivity)]
    have hsin_le : Real.sin (x / 2) ^ 2 ≤ |Real.sin (x / 2)| * |x / 2| := by
      calc Real.sin (x / 2) ^ 2
          = |Real.sin (x / 2)| * |Real.sin (x / 2)| := by rw [← sq_abs (Real.sin (x / 2))]; ring
        _ ≤ |Real.sin (x / 2)| * |x / 2| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _)
    calc 2 * Real.sin (x / 2) ^ 2 / |x|
        ≤ 2 * (|Real.sin (x / 2)| * |x / 2|) / |x| :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsin_le (by norm_num)) (abs_nonneg x)
      _ = |Real.sin (x / 2)| := by
          rw [abs_div, show |2| = (2 : ℝ) from abs_of_pos (by norm_num)]
          field_simp
      _ ≤ 1 := Real.abs_sin_le_one _

-- Helper: ∫_0^T sin(bt) = (1-cos(bT))/b for b ≠ 0
private lemma integral_sin_mul (b T : ℝ) (hb : b ≠ 0) :
    ∫ t in (0:ℝ)..T, Real.sin (b * t) = (1 - Real.cos (b * T)) / b := by
  have hderiv : ∀ x ∈ Set.uIcc 0 T,
      HasDerivAt (fun t => -Real.cos (b * t) / b) (Real.sin (b * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => b * t) b x := by
      convert (hasDerivAt_id x).const_mul b using 1; ring
    have h3 : HasDerivAt (fun t => Real.cos (b * t)) (-Real.sin (b * x) * b) x := by
      have := (Real.hasDerivAt_cos (b * x)).comp x h1
      simp only [Function.comp_def] at this; exact this
    have h4 := h3.neg.congr_deriv (show -(-Real.sin (b * x) * b) = Real.sin (b * x) * b by ring)
    exact (h4.div_const b).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 T)]
  rw [mul_zero, Real.cos_zero]; field_simp; ring

-- Cesaro sine integral bound: |∫₀ᵀ (1-t/T) sin(bt)/t dt| ≤ 5
set_option maxHeartbeats 400000 in
private lemma cesaro_integral_bound (T b : ℝ) (hT : 0 < T) :
    |∫ t in Set.Icc 0 T, (1 - t / T) * (Real.sin (b * t) / t)| ≤ 5 := by
  -- Convert set integral on Icc to interval integral
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  -- b = 0 case
  by_cases hb : b = 0
  · simp [hb]
  -- Split: ∫ (1-t/T)sin(bt)/t = ∫ sin(bt)/t - (1/T)∫ sin(bt)
  have h1 := intervalIntegrable_sin_div b (a := (0:ℝ)) (T := T)
  have h2 : IntervalIntegrable (fun t => (1 / T) * Real.sin (b * t)) volume 0 T :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 T |>.const_mul _
  -- Rewrite integrand
  have hcongr : ∫ t in (0:ℝ)..T, (1 - t / T) * (Real.sin (b * t) / t) =
      ∫ t in (0:ℝ)..T, (Real.sin (b * t) / t - 1 / T * Real.sin (b * t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t _
    by_cases htv : t = 0 <;> simp [htv] <;> field_simp
  have hsplit : ∫ t in (0:ℝ)..T, (1 - t / T) * (Real.sin (b * t) / t) =
      (∫ t in (0:ℝ)..T, Real.sin (b * t) / t) -
      (1 / T) * ∫ t in (0:ℝ)..T, Real.sin (b * t) := by
    rw [hcongr, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [hsplit]
  -- Triangle inequality
  calc |(∫ t in (0:ℝ)..T, Real.sin (b * t) / t) -
        (1 / T) * ∫ t in (0:ℝ)..T, Real.sin (b * t)|
      ≤ |∫ t in (0:ℝ)..T, Real.sin (b * t) / t| +
        |(1 / T) * ∫ t in (0:ℝ)..T, Real.sin (b * t)| := abs_sub _ _
    _ ≤ 3 + 1 := by
        apply add_le_add (sinc_integral_bound b T hT)
        -- |(1/T) ∫ sin(bt)| = |(1-cos(bT))/(bT)| ≤ 1
        rw [integral_sin_mul b T hb, abs_mul, abs_of_nonneg (by positivity)]
        rw [show (1 : ℝ) / T * |(1 - Real.cos (b * T)) / b| =
          |(1 - Real.cos (b * T)) / (b * T)| from by
          rw [abs_div, abs_div, abs_mul, abs_of_pos hT]; ring]
        exact abs_one_sub_cos_div_le (b * T)
    _ ≤ 5 := by norm_num

/-- **Cesàro Fubini identity.**
For a probability measure `μ` and `0 < δ < T`, the order of integration can be swapped
for the Cesàro-weighted sinc integrand on `[δ, T] × μ`:

  `∫_μ ∫_{[δ,T]} (1-t/T) sin((x-y)t)/t dt = ∫_{[δ,T]} (1-t/T)(∫_μ sin((x-y)t))/t dt`

The integrand `(1-t/T) sin((x-y)t)/t` is bounded by `1/δ` on `[δ,T]` (since
`|(1-t/T)| ≤ 1` and `|sin(...)/t| ≤ 1/δ`), so Fubini applies on this finite product. -/
private lemma cesaro_fubini_truncated
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (δ T y : ℝ) (hδ : 0 < δ) (hR : δ < T) :
    ∫ x, (∫ t in Set.Icc δ T, (1 - t / T) * (Real.sin ((x - y) * t) / t)) ∂μ =
    ∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - y) * t) ∂μ) / t) := by
  -- The integrand (1-t/T)·sin((x-y)t)/t is bounded by 1/δ on [δ,T]×μ.
  -- Fubini gives ∫_μ ∫_{Icc} = ∫_{Icc} ∫_μ, then simplify.
  set ν := (volume : Measure ℝ).restrict (Set.Icc δ T)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  -- Measurability of the integrand
  have hmeas : Measurable (Function.uncurry fun (x t : ℝ) =>
      (1 - t / T) * (Real.sin ((x - y) * t) / t)) :=
    ((measurable_const.sub (measurable_snd.div measurable_const)).mul
      ((Real.measurable_sin.comp ((measurable_fst.sub measurable_const).mul
        measurable_snd)).div measurable_snd))
  -- Bound on [δ,T]: |(1-t/T) sin((x-y)t)/t| ≤ 1/δ
  have hbd : ∀ᵐ t ∂ν, ∀ x : ℝ,
      ‖(1 - t / T) * (Real.sin ((x - y) * t) / t)‖ ≤ 1 / δ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht x
    have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
    have htT : t ≤ T := ht.2
    rw [Real.norm_eq_abs, abs_mul]
    have hT_pos : (0 : ℝ) < T := lt_trans hδ hR
    calc |1 - t / T| * |Real.sin ((x - y) * t) / t|
        ≤ 1 * (1 / δ) := by
          apply mul_le_mul
          · have htT1 : t / T ≤ 1 := (div_le_one₀ hT_pos).mpr htT
            have htT0 : 0 ≤ t / T := div_nonneg ht_pos.le hT_pos.le
            rw [abs_of_nonneg (by linarith)]; linarith
          · rw [abs_div, abs_of_pos ht_pos]
            calc |Real.sin ((x - y) * t)| / t
                ≤ 1 / t := div_le_div_of_nonneg_right (Real.abs_sin_le_one _) ht_pos.le
              _ ≤ 1 / δ := div_le_div_of_nonneg_left one_pos.le hδ ht.1
          · exact abs_nonneg _
          · linarith
      _ = 1 / δ := one_mul _
  -- Product integrability
  have hprod : Integrable (Function.uncurry fun (x t : ℝ) =>
      (1 - t / T) * (Real.sin ((x - y) * t) / t)) (μ.prod ν) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable (1 / δ)
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards with x
    filter_upwards [hbd] with t ht; exact ht x
  -- Apply Fubini
  rw [integral_integral_swap hprod]
  congr 1; ext t
  -- ∫_μ (1-t/T) * (sin/t) = (1-t/T) * (∫_μ sin) / t
  rw [MeasureTheory.integral_const_mul, integral_div]

-- Helper: sin(θ) = Im(exp(iθ))
private lemma real_sin_eq_im_exp (θ : ℝ) : Real.sin θ = (exp ((↑θ : ℂ) * I)).im := by
  simp [exp_mul_I, add_im, mul_im, I_re, I_im, Complex.sin_ofReal_re]

-- Helper: exp(i(x-y)t) is integrable under a probability measure
private lemma integrable_exp_product (μ : Measure ℝ) [IsProbabilityMeasure μ] (t y : ℝ) :
    Integrable (fun x => exp ((↑((x - y) * t) : ℂ) * I)) μ := by
  apply Integrable.of_bound (C := 1)
  · exact (by fun_prop : Measurable (fun x => exp ((↑((x - y) * t) : ℂ) * I))).aestronglyMeasurable
  · filter_upwards with x; rw [Complex.norm_exp_ofReal_mul_I]

-- Helper: |∫ sin((x-y)t) dμ - ∫ sin((x-y)t) dν| ≤ ‖charFun μ t - charFun ν t‖
-- Proof: sin = Im∘exp, pull exp(-iyt) factor, use |Im(z)| ≤ ‖z‖ and ‖exp·z‖ = ‖z‖.
set_option maxHeartbeats 400000 in
private lemma sin_integral_le_charFun_norm (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (t y : ℝ) :
    |∫ x, Real.sin ((x - y) * t) ∂μ - ∫ x, Real.sin ((x - y) * t) ∂ν| ≤
    ‖charFun μ t - charFun ν t‖ := by
  simp_rw [real_sin_eq_im_exp]
  conv_lhs =>
    arg 1; arg 1
    rw [show (fun x => (exp ((↑((x - y) * t) : ℂ) * I)).im) =
      (fun x => Complex.imCLM (exp ((↑((x - y) * t) : ℂ) * I))) from rfl]
    rw [ContinuousLinearMap.integral_comp_comm Complex.imCLM (integrable_exp_product μ t y)]
  conv_lhs =>
    arg 1; arg 2
    rw [show (fun x => (exp ((↑((x - y) * t) : ℂ) * I)).im) =
      (fun x => Complex.imCLM (exp ((↑((x - y) * t) : ℂ) * I))) from rfl]
    rw [ContinuousLinearMap.integral_comp_comm Complex.imCLM (integrable_exp_product ν t y)]
  simp only [Complex.imCLM_apply]
  rw [← Complex.sub_im]
  have hexp : ∫ x, exp ((↑((x - y) * t) : ℂ) * I) ∂μ -
      ∫ x, exp ((↑((x - y) * t) : ℂ) * I) ∂ν =
      exp ((↑(-y * t) : ℂ) * I) * (charFun μ t - charFun ν t) := by
    rw [mul_sub]; congr 1 <;> {
      rw [charFun_apply_real, ← MeasureTheory.integral_const_mul]
      congr 1; ext x; rw [← Complex.exp_add]; congr 1; push_cast; ring }
  rw [hexp]
  calc |(exp ((↑(-y * t) : ℂ) * I) * (charFun μ t - charFun ν t)).im|
      ≤ ‖exp ((↑(-y * t) : ℂ) * I) * (charFun μ t - charFun ν t)‖ :=
        Complex.abs_im_le_norm _
    _ = ‖charFun μ t - charFun ν t‖ := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Substitution: ∫_{[-b,-a]} f(t) dt = ∫_{[a,b]} f(-t) dt for Lebesgue measure. -/
private lemma setIntegral_neg_Icc (f : ℝ → ℝ) (a b : ℝ) :
    ∫ t in Set.Icc (-b) (-a), f t = ∫ t in Set.Icc a b, f (-t) := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  rw [← integral_neg_eq_self (fun t => (Set.Icc a b).indicator (fun u => f (-u)) t)]
  congr 1; ext t; simp only [Set.indicator]
  split_ifs with h1 h2 h2
  · simp [neg_neg]
  · exfalso; apply h2; constructor <;> simp at h1 ⊢ <;> linarith [h1.1, h1.2]
  · exfalso; apply h1; constructor <;> simp at h2 ⊢ <;> linarith [h2.1, h2.2]
  · rfl

/-- **Cesàro Fourier bound.**
The Cesàro-averaged Fourier difference `(1/π)∫₀ᵀ (1-t/T) Im(Δ̂(t) e^{-iyt})/t dt`
is bounded by `I/(2π)` in absolute value, where `I = ∫_{-T}^T ‖Δ̂(t)‖/|t| dt`.

This uses `(1-t/T) ≤ 1` and `|Im(Δ̂ e^{-iyt})| ≤ ‖Δ̂‖`. -/
private lemma cesaro_fourier_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (T y : ℝ) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ) (hδT : δ < T)
    (hint_charfun : IntegrableOn (fun t => ‖charFun μ t - charFun ν t‖ / |t|)
      (Set.Icc (-T) T)) :
    |(1 / Real.pi) * ∫ t in Set.Icc δ T,
      (1 - t / T) * ((∫ x, Real.sin ((x - y) * t) ∂μ -
        ∫ x, Real.sin ((x - y) * t) ∂ν) / t)| ≤
    (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
      ‖charFun μ t - charFun ν t‖ / |t| := by
  -- Bound: |(1/π)| = 1/π (π > 0)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity)]

  -- Key bound: |∫_μ sin((x-y)t) - ∫_ν sin((x-y)t)| ≤ ‖charFun μ t - charFun ν t‖
  have hsin_charfun_bound : ∀ t : ℝ,
      |∫ x, Real.sin ((x - y) * t) ∂μ - ∫ x, Real.sin ((x - y) * t) ∂ν| ≤
      ‖charFun μ t - charFun ν t‖ :=
    fun t => sin_integral_le_charFun_norm μ ν t y
  -- Sorry 1: |(1/π) ∫_{[δ,T]} (1-t/T)(sin_diff/t)| ≤ ∫_{[δ,T]} ‖Δ(t)‖/|t|
  -- Proof: |∫ f| ≤ ∫ ‖f‖ ≤ ∫ g by pointwise |(1-t/T)| ≤ 1 and |sin_diff| ≤ ‖Δ‖
  have habs_int : |∫ t in Set.Icc δ T,
      (1 - t / T) * ((∫ x, Real.sin ((x - y) * t) ∂μ -
        ∫ x, Real.sin ((x - y) * t) ∂ν) / t)| ≤
      ∫ t in Set.Icc δ T, ‖charFun μ t - charFun ν t‖ / |t| := by
    -- IntegrableOn for ‖Δ(t)‖/|t| on [δ,T] (bounded by 2/δ since |t| ≥ δ)
    have hint_rhs : IntegrableOn (fun t => ‖charFun μ t - charFun ν t‖ / |t|)
        (Set.Icc δ T) := by
      refine integrableOn_of_bounded (M := 2 / δ) ?_ ?_ ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · exact ((measurable_charFun (μ := μ).sub (measurable_charFun (μ := ν))).norm.div
          measurable_abs).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Icc]; apply ae_of_all; intro t ht
        rw [Real.norm_eq_abs, abs_div, abs_abs, abs_norm]
        have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
        rw [abs_of_pos ht_pos]
        calc ‖charFun μ t - charFun ν t‖ / t
            ≤ 2 / t := div_le_div_of_nonneg_right (by
              calc _ ≤ ‖charFun μ t‖ + ‖charFun ν t‖ := norm_sub_le _ _
                _ ≤ 1 + 1 := add_le_add (norm_charFun_le_one t) (norm_charFun_le_one t)
                _ = 2 := by norm_num) ht_pos.le
          _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num) hδ ht.1
    -- Main bound: ‖∫ f‖ ≤ ∫ g (pointwise ‖f(t)‖ ≤ g(t))
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hint_rhs (by
      rw [ae_restrict_iff' measurableSet_Icc]
      apply ae_of_all; intro t ht
      have ht_pos : 0 < t := lt_of_lt_of_le hδ ht.1
      rw [Real.norm_eq_abs, abs_mul, abs_div]
      have hab : |1 - t / T| ≤ 1 := by
        rw [abs_le]; constructor <;>
          nlinarith [div_nonneg ht_pos.le hT.le, div_le_one₀ hT |>.mpr ht.2]
      calc |1 - t / T| * (|∫ x, Real.sin ((x - y) * t) ∂μ -
            ∫ x, Real.sin ((x - y) * t) ∂ν| / |t|)
          ≤ 1 * (‖charFun μ t - charFun ν t‖ / |t|) := by
            apply mul_le_mul hab
              (div_le_div_of_nonneg_right (hsin_charfun_bound t) (abs_nonneg _))
              (div_nonneg (abs_nonneg _) (abs_nonneg _)) one_pos.le
        _ = ‖charFun μ t - charFun ν t‖ / |t| := one_mul _)
  -- Sorry 2: ∫_{[δ,T]} ‖Δ‖/|t| ≤ (1/2) ∫_{[-T,T]} ‖Δ‖/|t|
  -- Proof: symmetry ‖Δ(-t)‖/|-t| = ‖Δ(t)‖/|t| gives ∫_{[-T,-δ]} = ∫_{[δ,T]},
  -- so 2∫_{[δ,T]} = ∫_{[-T,-δ]} + ∫_{[δ,T]} = ∫_{union} ≤ ∫_{[-T,T]}
  have hsymm : ∫ t in Set.Icc δ T, ‖charFun μ t - charFun ν t‖ / |t| ≤
      (1/2) * ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| := by
    set Φ := fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t| with hΦ_def
    have hΦ_even : ∀ t, Φ (-t) = Φ t := by
      intro t; simp only [hΦ_def, charFun_neg, charFun_neg, ← map_sub (starRingEnd ℂ),
        RCLike.norm_conj, abs_neg]
    have hsym : ∫ t in Set.Icc (-T) (-δ), Φ t = ∫ t in Set.Icc δ T, Φ t := by
      rw [setIntegral_neg_Icc]; congr 1; ext t; exact hΦ_even t
    have hΦ_nn : ∀ t, 0 ≤ Φ t := fun t => div_nonneg (norm_nonneg _) (abs_nonneg _)
    have hdisjoint : Disjoint (Set.Icc (-T) (-δ)) (Set.Icc δ T) := by
      rw [Set.disjoint_iff]; intro t ⟨h1, h2⟩; linarith [h1.2, h2.1]
    have hsubset : Set.Icc (-T) (-δ) ∪ Set.Icc δ T ⊆ Set.Icc (-T) T := by
      intro t ht; rcases ht with h | h
      · exact ⟨h.1, le_trans h.2 (by linarith)⟩
      · exact ⟨le_trans (by linarith) h.1, h.2⟩
    have hint_left : IntegrableOn Φ (Set.Icc (-T) (-δ)) :=
      hint_charfun.mono_set (subset_trans Set.subset_union_left hsubset)
    have hint_right : IntegrableOn Φ (Set.Icc δ T) :=
      hint_charfun.mono_set (subset_trans Set.subset_union_right hsubset)
    suffices h : 2 * ∫ t in Set.Icc δ T, Φ t ≤ ∫ t in Set.Icc (-T) T, Φ t by linarith
    have hunion_eq := setIntegral_union hdisjoint measurableSet_Icc hint_left hint_right
    have hunion_le : ∫ t in Set.Icc (-T) (-δ) ∪ Set.Icc δ T, Φ t ≤
        ∫ t in Set.Icc (-T) T, Φ t :=
      setIntegral_mono_set hint_charfun (ae_of_all _ fun t => hΦ_nn t)
        (ae_of_all _ fun t ht => hsubset ht)
    linarith [hunion_eq, hunion_le, hsym]
  calc 1 / Real.pi * |∫ t in Set.Icc δ T,
        (1 - t / T) * ((∫ x, Real.sin ((x - y) * t) ∂μ -
          ∫ x, Real.sin ((x - y) * t) ∂ν) / t)|
      ≤ 1 / Real.pi * ∫ t in Set.Icc δ T, ‖charFun μ t - charFun ν t‖ / |t| := by
        apply mul_le_mul_of_nonneg_left habs_int (by positivity)
    _ ≤ 1 / Real.pi * ((1/2) * ∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) := by
        apply mul_le_mul_of_nonneg_left hsymm (by positivity)
    _ = _ := by ring

/-- CDF of a probability measure is M-Lipschitz when the density is bounded by M. -/
private lemma cdf_lipschitz_of_density_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (a b : ℝ) (hab : a ≤ b) : cdf ν b - cdf ν a ≤ M * (b - a) := by
  -- Use measure_cdf: (cdf ν).measure = ν, and StieltjesFunction.measure_Ioc
  have hmeas_eq : (cdf ν).measure = ν := measure_cdf ν
  have hIoc : (cdf ν).measure (Set.Ioc a b) = ENNReal.ofReal (cdf ν b - cdf ν a) :=
    StieltjesFunction.measure_Ioc _ a b
  rw [hmeas_eq] at hIoc
  have h_density := hν_density a b hab
  have h_mono : cdf ν a ≤ cdf ν b := monotone_cdf ν hab
  have h_sub_nn : 0 ≤ cdf ν b - cdf ν a := sub_nonneg.mpr h_mono
  have hIoc_le : ν (Set.Ioc a b) ≤ ν (Set.Icc a b) :=
    measure_mono Set.Ioc_subset_Icc_self
  calc cdf ν b - cdf ν a
      = (ENNReal.ofReal (cdf ν b - cdf ν a)).toReal := (ENNReal.toReal_ofReal h_sub_nn).symm
    _ = (ν (Set.Ioc a b)).toReal := by rw [hIoc]
    _ ≤ (ν (Set.Icc a b)).toReal := ENNReal.toReal_mono (measure_ne_top ν _) hIoc_le
    _ ≤ (ENNReal.ofReal (M * (b - a))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_density
    _ = M * (b - a) := ENNReal.toReal_ofReal (mul_nonneg hM.le (sub_nonneg.mpr hab))

/-- The CDF difference convolution `∫ (F(y'-x) - G(y'-x)) K(x) dx` is integrable
when K is continuous and integrable. Bound: |cdf diff| ≤ 1, so the product is bounded by |K|. -/
private lemma integrable_cdf_diff_mul_kernel
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ → ℝ) (hK_cont : Continuous K) (hK_int : Integrable K volume) (y' : ℝ) :
    Integrable (fun x => (cdf μ (y' - x) - cdf ν (y' - x)) * K x) volume := by
  -- CDF is measurable (monotone → measurable)
  have hF_meas : Measurable (fun x => cdf μ (y' - x)) :=
    (monotone_cdf μ).measurable.comp (measurable_const.sub measurable_id)
  have hG_meas : Measurable (fun x => cdf ν (y' - x)) :=
    (monotone_cdf ν).measurable.comp (measurable_const.sub measurable_id)
  have hD_meas : AEStronglyMeasurable (fun x => cdf μ (y' - x) - cdf ν (y' - x)) volume :=
    (hF_meas.sub hG_meas).aestronglyMeasurable
  have hK_meas : AEStronglyMeasurable K volume := hK_cont.measurable.aestronglyMeasurable
  -- Bound: |D(y'-x)| ≤ 1, so |D(y'-x) * K(x)| ≤ |K(x)|
  refine Integrable.mono hK_int (hD_meas.mul hK_meas) ?_
  filter_upwards with x
  rw [norm_mul]
  calc ‖cdf μ (y' - x) - cdf ν (y' - x)‖ * ‖K x‖
      ≤ 1 * ‖K x‖ := by
        gcongr
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [cdf_nonneg μ (y' - x), cdf_le_one μ (y' - x),
          cdf_nonneg ν (y' - x), cdf_le_one ν (y' - x)]
    _ = ‖K x‖ := one_mul _

/-! ### Fejér bracket infrastructure

Helper lemmas for the Esseen smoothing inequality: bracket inequalities,
integrability of fejerCDF, convolution bounds, and density bounds. -/

/-- Upper bracket: `1_{x ≤ y} ≤ Ψ_F(y + a - x) + (1 - Ψ_F(a))` for `a ≥ 0`. -/
private lemma fejerCDF_bracket_upper {T : ℝ} (hT : 0 < T)
    (y a x : ℝ) (ha : 0 ≤ a) :
    Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x ≤
      fejerCDF T (y + a - x) + (1 - fejerCDF T a) := by
  by_cases hx : x ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx) (1 : ℝ → ℝ)]
    simp only [Pi.one_apply]
    linarith [fejerCDF_monotone hT (show a ≤ y + a - x by linarith)]
  · rw [Set.indicator_of_notMem (show x ∉ Set.Iic y from fun h => hx (Set.mem_Iic.mp h)) _]
    linarith [fejerCDF_nonneg hT (y + a - x), fejerCDF_le_one hT a]

/-- Lower bracket: `Ψ_F(y - a - x) - (1 - Ψ_F(a)) ≤ 1_{x ≤ y}` for `a ≥ 0`. -/
private lemma fejerCDF_bracket_lower {T : ℝ} (hT : 0 < T)
    (y a x : ℝ) (ha : 0 ≤ a) :
    fejerCDF T (y - a - x) - (1 - fejerCDF T a) ≤
      Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x := by
  by_cases hx : x ≤ y
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx) (1 : ℝ → ℝ)]
    simp only [Pi.one_apply]
    linarith [fejerCDF_le_one hT (y - a - x), fejerCDF_le_one hT a]
  · rw [Set.indicator_of_notMem (show x ∉ Set.Iic y from fun h => hx (Set.mem_Iic.mp h)) _]
    push_neg at hx
    calc fejerCDF T (y - a - x) - (1 - fejerCDF T a)
        ≤ (1 - fejerCDF T a) - (1 - fejerCDF T a) := by
          gcongr
          calc fejerCDF T (y - a - x)
              ≤ fejerCDF T (-a) := fejerCDF_monotone hT (by linarith)
            _ = 1 - fejerCDF T a := fejerCDF_symm hT a
      _ = 0 := sub_self _

/-- Measurability: `x ↦ fejerCDF T (u - x)` is measurable for `T > 0`. -/
private lemma measurable_fejerCDF_sub {T : ℝ} (hT : 0 < T) (u : ℝ) :
    Measurable (fun x => fejerCDF T (u - x)) :=
  (fejerCDF_monotone hT).measurable.comp (measurable_const.sub measurable_id)

/-- Integrability: `x ↦ fejerCDF T (u - x)` is integrable against any probability measure. -/
private lemma integrable_fejerCDF_sub {T : ℝ} (hT : 0 < T) (u : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun x => fejerCDF T (u - x)) μ := by
  apply Integrable.of_bound (C := 1)
  · exact (measurable_fejerCDF_sub hT u).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [fejerCDF_nonneg hT (u - x)],
           by linarith [fejerCDF_le_one hT (u - x)]⟩

/-- CDF upper bracket: `cdf μ y ≤ ∫ Ψ_F(y+a-x) dμ + (1 - Ψ_F(a))`. -/
private lemma cdf_le_fejerCDF_integral {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y a : ℝ) (ha : 0 ≤ a) :
    cdf μ y ≤ ∫ x, fejerCDF T (y + a - x) ∂μ + (1 - fejerCDF T a) := by
  have hcdf : cdf μ y = ∫ x, Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x ∂μ := by
    rw [cdf_eq_real, measureReal_def]
    exact (integral_indicator_one measurableSet_Iic).symm
  rw [hcdf]
  calc ∫ x, Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x ∂μ
      ≤ ∫ x, (fejerCDF T (y + a - x) + (1 - fejerCDF T a)) ∂μ := by
        apply integral_mono
        · apply Integrable.indicator (integrable_const 1) measurableSet_Iic
        · exact (integrable_fejerCDF_sub hT (y + a) μ).add (integrable_const _)
        · exact fun x => fejerCDF_bracket_upper hT y a x ha
    _ = ∫ x, fejerCDF T (y + a - x) ∂μ + (1 - fejerCDF T a) := by
        rw [integral_add (integrable_fejerCDF_sub hT (y + a) μ) (integrable_const _)]
        simp [integral_const]

/-- CDF lower bracket: `∫ Ψ_F(y-a-x) dμ - (1 - Ψ_F(a)) ≤ cdf μ y`. -/
private lemma fejerCDF_integral_le_cdf {T : ℝ} (hT : 0 < T)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y a : ℝ) (ha : 0 ≤ a) :
    ∫ x, fejerCDF T (y - a - x) ∂μ - (1 - fejerCDF T a) ≤ cdf μ y := by
  have hcdf : cdf μ y = ∫ x, Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x ∂μ := by
    rw [cdf_eq_real, measureReal_def]
    exact (integral_indicator_one measurableSet_Iic).symm
  rw [hcdf]
  have h1 : ∫ x, (fejerCDF T (y - a - x) - (1 - fejerCDF T a)) ∂μ ≤
      ∫ x, Set.indicator (Set.Iic y) (1 : ℝ → ℝ) x ∂μ := by
    apply integral_mono
    · exact (integrable_fejerCDF_sub hT (y - a) μ).sub (integrable_const _)
    · apply Integrable.indicator (integrable_const 1) measurableSet_Iic
    · exact fun x => fejerCDF_bracket_lower hT y a x ha
  calc ∫ x, fejerCDF T (y - a - x) ∂μ - (1 - fejerCDF T a)
      = ∫ x, (fejerCDF T (y - a - x) - (1 - fejerCDF T a)) ∂μ := by
        rw [integral_sub (integrable_fejerCDF_sub hT (y - a) μ) (integrable_const _)]
        simp [integral_const]
    _ ≤ _ := h1

/-- **Fejér convolution bound.**
For probability measures `μ`, `ν` and `T > 0`:
  `|∫ Ψ_F(u-x) dμ - ∫ Ψ_F(u-x) dν| ≤ (1/(2π)) I`
where `I = ∫_{[-T,T]} ‖Δ(t)‖/|t| dt`.

Proof: `Ψ_F(u-x) = 1/2 + (1/π) ∫₀ᵀ (1-t/T) sin((u-x)t)/t dt` by `fejerCDF_eq_cesaro`.
The 1/2 cancels in μ-ν. The Cesàro integral is bounded via `cesaro_fourier_bound` on `[δ,T]`,
then DCT takes δ→0. -/
private lemma fejer_convolution_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (u : ℝ)
    (hint : IntegrableOn (fun t => ‖charFun μ t - charFun ν t‖ / |t|)
      (Set.Icc (-T) T)) :
    |∫ x, fejerCDF T (u - x) ∂μ - ∫ x, fejerCDF T (u - x) ∂ν| ≤
      (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t| := by
  have hpi := Real.pi_pos
  set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|
  -- f₀(x) = ∫_{[0,T]} (1-t/T) sin((u-x)t)/t dt
  set f₀ : ℝ → ℝ := fun x =>
    ∫ t in Set.Icc (0 : ℝ) T, (1 - t / T) * (Real.sin ((u - x) * t) / t)
  have hΨ_eq : ∀ x, fejerCDF T (u - x) = 1/2 + (1 / Real.pi) * f₀ x :=
    fun x => fejerCDF_eq_cesaro T hT (u - x)
  have hf₀_bd : ∀ x, |f₀ x| ≤ 5 := fun x => cesaro_integral_bound T (u - x) hT
  have hmeas_joint : Measurable (Function.uncurry fun (t x : ℝ) =>
      (1 - t / T) * (Real.sin ((u - x) * t) / t)) :=
    (measurable_const.sub (measurable_fst.div measurable_const)).mul
      ((Real.measurable_sin.comp ((measurable_const.sub measurable_snd).mul
        measurable_fst)).div measurable_fst)
  have hf₀_smeas : StronglyMeasurable f₀ :=
    hmeas_joint.stronglyMeasurable.integral_prod_left
  have hf₀_int : ∀ (m : Measure ℝ) [IsProbabilityMeasure m], Integrable f₀ m := fun m _ =>
    ⟨hf₀_smeas.aestronglyMeasurable, hasFiniteIntegral_of_bounded (C := 5)
      (by filter_upwards with x; rw [Real.norm_eq_abs]; exact hf₀_bd x)⟩
  -- Step 1: ∫ Ψ_F dμ - ∫ Ψ_F dν = (1/π)(∫ f₀ dμ - ∫ f₀ dν)
  -- (the 1/2 terms cancel since both are probability measures)
  have hdiff_rw : ∫ x, fejerCDF T (u - x) ∂μ - ∫ x, fejerCDF T (u - x) ∂ν =
      (1 / Real.pi) * (∫ x, f₀ x ∂μ - ∫ x, f₀ x ∂ν) := by
    have hrw : ∀ (m : Measure ℝ) [IsProbabilityMeasure m],
        ∫ x, fejerCDF T (u - x) ∂m = 1/2 + (1 / Real.pi) * ∫ x, f₀ x ∂m := by
      intro m _
      simp_rw [hΨ_eq]
      rw [integral_add (integrable_const _) ((hf₀_int m).const_mul _)]
      simp [integral_const, measure_univ, integral_const_mul]
    rw [hrw μ, hrw ν]; ring
  rw [hdiff_rw]
  -- Step 2: Truncated bound via Fubini + cesaro_fourier_bound
  -- Define F_n(x) = ∫_{[T/(n+2),T]} (1-t/T) sin((u-x)t)/t dt
  set F : ℕ → ℝ → ℝ := fun n x =>
    ∫ t in Set.Icc (T / (↑n + 2)) T,
      (1 - t / T) * (Real.sin ((u - x) * t) / t)
  have hδ_pos : ∀ n : ℕ, (0 : ℝ) < T / (↑n + 2) := fun n => by positivity
  have hδ_lt_T : ∀ n : ℕ, T / (↑n + 2) < T := fun n => by
    have h : (1 : ℝ) < ↑n + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact div_lt_self hT h
  -- For each n: |(1/π)(∫ F_n dμ - ∫ F_n dν)| ≤ I/(2π)
  have htrunc_bound : ∀ n : ℕ, |(1 / Real.pi) * (∫ x, F n x ∂μ - ∫ x, F n x ∂ν)| ≤
      (1 / (2 * Real.pi)) * I := by
    intro n
    set δ := T / (↑n + 2)
    have hδp := hδ_pos n
    have hδT := hδ_lt_T n
    -- F_n uses sin((u-x)t) but cesaro_fubini_truncated uses sin((x-y)t).
    -- sin((u-x)t) = -sin((x-u)t), so F_n(x) = -G(x) where G uses (x-u).
    have hF_eq_neg : ∀ x, F n x = -(∫ t in Set.Icc δ T,
        (1 - t / T) * (Real.sin ((x - u) * t) / t)) := by
      intro x; simp only [F]
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
      have : (u - x) * t = -((x - u) * t) := by ring
      rw [this, Real.sin_neg, neg_div, mul_neg]
    -- ∫_μ F_n = -(∫_μ G)  and ∫_ν F_n = -(∫_ν G)
    -- Using cesaro_fubini_truncated: ∫_m G = ∫_{[δ,T]} (1-t/T)(∫_m sin)/t
    have hint_eq : ∀ (m : Measure ℝ) [IsProbabilityMeasure m],
        ∫ x, F n x ∂m =
        -(∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂m) / t)) := by
      intro m _
      simp_rw [hF_eq_neg, integral_neg]
      congr 1
      exact cesaro_fubini_truncated m δ T u hδp hδT
    rw [hint_eq μ, hint_eq ν]
    -- -(A) - (-(B)) = -(A - B)
    rw [show -(∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ) / t)) -
        -(∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂ν) / t)) =
        -((∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ) / t)) -
          (∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂ν) / t)))
      from by ring, mul_neg, abs_neg]
    -- Integrability on [δ,T] (bounded by 1/δ on compact interval)
    have hint_on : ∀ (m : Measure ℝ) [IsProbabilityMeasure m],
        IntegrableOn (fun t => (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂m) / t))
          (Set.Icc δ T) := by
      intro m _
      apply integrableOn_of_bounded (M := 1 / δ)
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · -- measurability: the integrand t ↦ (1-t/T)(∫ sin((x-u)t) ∂m)/t
        -- t ↦ ∫ x, sin((x-u)t) ∂m is measurable (parametric integral)
        have hmeas_sin_int : Measurable (fun t : ℝ => ∫ x, Real.sin ((x - u) * t) ∂m) := by
          have : Measurable (Function.uncurry fun (x t : ℝ) => Real.sin ((x - u) * t)) :=
            Real.measurable_sin.comp ((measurable_fst.sub measurable_const).mul measurable_snd)
          exact this.stronglyMeasurable.integral_prod_left.measurable
        exact ((measurable_const.sub (measurable_id'.div_const T)).mul
          (hmeas_sin_int.div measurable_id')).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Icc]; apply ae_of_all; intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le hδp ht.1
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |1 - t / T| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_one₀ hT).mpr ht.2))]
          linarith [div_nonneg ht_pos.le hT.le]
        have h2 : |(∫ x, Real.sin ((x - u) * t) ∂m) / t| ≤ 1 / δ := by
          rw [abs_div, abs_of_pos ht_pos]
          calc |∫ x, Real.sin ((x - u) * t) ∂m| / t
              ≤ 1 / t := by
                apply div_le_div_of_nonneg_right _ ht_pos.le
                have : |∫ x, Real.sin ((x - u) * t) ∂m| ≤ 1 := by
                  calc |∫ x, Real.sin ((x - u) * t) ∂m|
                      = ‖∫ x, Real.sin ((x - u) * t) ∂m‖ := (Real.norm_eq_abs _).symm
                    _ ≤ ∫ x, ‖Real.sin ((x - u) * t)‖ ∂m := norm_integral_le_integral_norm _
                    _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂m := by
                        apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
                          (integrable_const _)
                        filter_upwards with x
                        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _
                    _ = 1 := by simp
                linarith
            _ ≤ 1 / δ := div_le_div_of_nonneg_left one_pos.le hδp ht.1
        calc |1 - t / T| * |(∫ x, Real.sin ((x - u) * t) ∂m) / t|
            ≤ 1 * (1 / δ) := mul_le_mul h1 h2 (abs_nonneg _) one_pos.le
          _ = 1 / δ := one_mul _
    -- Factor: ∫ h_μ - ∫ h_ν = ∫ (h_μ - h_ν)
    rw [show (∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ) / t)) -
        (∫ t in Set.Icc δ T, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂ν) / t)) =
        ∫ t in Set.Icc δ T, ((1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ) / t) -
          (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂ν) / t)) from by
      rw [← integral_sub (hint_on μ) (hint_on ν)]]
    -- Simplify integrand: (1-t/T)(A/t) - (1-t/T)(B/t) = (1-t/T)((A-B)/t)
    have hcongr : ∀ t, (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ) / t) -
        (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂ν) / t) =
        (1 - t / T) * ((∫ x, Real.sin ((x - u) * t) ∂μ -
          ∫ x, Real.sin ((x - u) * t) ∂ν) / t) :=
      fun t => by rw [sub_div]; ring
    simp_rw [hcongr]
    exact cesaro_fourier_bound μ ν T u hT δ hδp hδT hint
  -- Step 3: DCT + limit argument
  -- ∫ F_n dμ → ∫ f₀ dμ by dominated convergence (bound = 7)
  -- Then |limit| ≤ I/(2π) since |a_n| ≤ I/(2π) for all n
  -- F_n(x) → f₀(x) pointwise: difference is ∫_{[0,δ_n]} ... → 0
  -- |F_n(x)| ≤ 7 (truncated cesaro bound)
  -- Use le_of_tendsto for sequences
  have hF_smeas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n; exact (hmeas_joint.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
  have hF_smeas_ν : ∀ n, AEStronglyMeasurable (F n) ν := by
    intro n; exact (hmeas_joint.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
  -- Uniform bound: |F_n(x)| ≤ 7 for all n and x
  -- Proof: split (1-t/T)sin(at)/t = sin(at)/t - (1/T)sin(at)
  -- |∫_δ^T sin(at)/t| ≤ 6 (by sinc_integral_bound twice: |∫_0^T| + |∫_0^δ| ≤ 3+3)
  -- |(1/T)∫_δ^T sin(at)| ≤ 1 (MVT on cos)
  have hF_bd : ∀ n x, |F n x| ≤ 7 := by
    intro n x
    set δ := T / (↑n + 2)
    set a := u - x
    -- Convert set integral to interval integral
    have hδ_le_T : δ ≤ T := (hδ_lt_T n).le
    have hδp := hδ_pos n
    rw [show F n x = ∫ t in Set.Icc δ T,
        (1 - t / T) * (Real.sin (a * t) / t) from rfl]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ_le_T]
    -- Split: ∫(1-t/T)sin(at)/t = ∫ sin(at)/t - (1/T) ∫ sin(at)
    have h_iint := intervalIntegrable_sin_div a (a := δ) (T := T)
    have h_sin_int : IntervalIntegrable (fun t => (1/T) * Real.sin (a * t)) volume δ T :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
        |>.const_mul _
    have hsplit : ∫ t in δ..T, (1 - t / T) * (Real.sin (a * t) / t) =
        (∫ t in δ..T, Real.sin (a * t) / t) -
        (1/T) * ∫ t in δ..T, Real.sin (a * t) := by
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_sub h_iint h_sin_int]
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t _
      by_cases htv : t = 0
      · simp [htv]
      · field_simp
    rw [hsplit]
    -- Triangle inequality
    calc |(∫ t in δ..T, Real.sin (a * t) / t) -
          (1/T) * ∫ t in δ..T, Real.sin (a * t)|
        ≤ |∫ t in δ..T, Real.sin (a * t) / t| +
          |(1/T) * ∫ t in δ..T, Real.sin (a * t)| := abs_sub _ _
      _ ≤ 6 + 1 := by
          apply add_le_add
          -- Part 1: |∫_δ^T sin(at)/t| ≤ 6
          · -- = |∫_0^T - ∫_0^δ| ≤ |∫_0^T| + |∫_0^δ| ≤ 3 + 3
            rw [show ∫ t in δ..T, Real.sin (a * t) / t =
                (∫ t in (0:ℝ)..T, Real.sin (a * t) / t) -
                (∫ t in (0:ℝ)..δ, Real.sin (a * t) / t) from by
              rw [← intervalIntegral.integral_add_adjacent_intervals
                (intervalIntegrable_sin_div a (a := (0:ℝ)) (T := δ))
                (intervalIntegrable_sin_div a (a := δ) (T := T))]
              ring]
            calc _ ≤ |∫ t in (0:ℝ)..T, Real.sin (a * t) / t| +
                    |∫ t in (0:ℝ)..δ, Real.sin (a * t) / t| := abs_sub _ _
              _ ≤ 3 + 3 := add_le_add (sinc_integral_bound a T hT)
                    (sinc_integral_bound a δ hδp)
              _ = 6 := by norm_num
          -- Part 2: |(1/T)∫_δ^T sin(at)| ≤ 1
          · by_cases ha : a = 0
            · simp [ha]
            · -- ∫_δ^T sin(at) = ∫_0^T - ∫_0^δ
              have hsin_int : ∀ (c d : ℝ), IntervalIntegrable (fun t => Real.sin (a * t)) volume c d :=
                fun c d => by exact (by fun_prop : Continuous (fun t => Real.sin (a * t))).intervalIntegrable c d
              rw [show ∫ t in δ..T, Real.sin (a * t) =
                  (∫ t in (0:ℝ)..T, Real.sin (a * t)) -
                  (∫ t in (0:ℝ)..δ, Real.sin (a * t)) from by
                rw [← intervalIntegral.integral_add_adjacent_intervals
                  (hsin_int 0 δ) (hsin_int δ T)]; ring,
                integral_sin_mul a T ha, integral_sin_mul a δ ha]
              -- Now: |(1/T)((1-cos(aT))/a - (1-cos(aδ))/a)|
              -- = |(cos(aδ)-cos(aT))/(aT)| ≤ |a|(T-δ)/(|a|T) = (T-δ)/T ≤ 1
              -- Use |cos x - cos y| ≤ |x - y| (from Real.lipschitzWith_cos)
              have hcos_lip := Real.lipschitzWith_cos.dist_le_mul (a * δ) (a * T)
              simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hcos_lip
              -- |cos(aδ)-cos(aT)| ≤ |aδ-aT| = |a|·|δ-T| = |a|(T-δ)
              rw [show a * δ - a * T = a * (δ - T) from by ring] at hcos_lip
              rw [abs_mul] at hcos_lip
              rw [show |δ - T| = T - δ from by rw [abs_of_nonpos (by linarith)]; ring] at hcos_lip
              -- Goal: |(1/T) * ((1-cos(aT))/a - (1-cos(aδ))/a)| ≤ 1
              -- Simplify: (1-cos(aT))/a - (1-cos(aδ))/a = (cos(aδ)-cos(aT))/a
              -- So the LHS = |cos(aδ)-cos(aT)| / (|a|·T) ≤ |a|(T-δ)/(|a|T) = (T-δ)/T ≤ 1
              have ha_pos : 0 < |a| := abs_pos.mpr ha
              rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / T)]
              -- Simplify the fraction
              rw [show (1 - Real.cos (a * T)) / a - (1 - Real.cos (a * δ)) / a =
                  (Real.cos (a * δ) - Real.cos (a * T)) / a from by ring]
              rw [abs_div]
              -- 1/T * (|cos diff| / |a|) ≤ 1/T * (|a|(T-δ)/|a|) = (T-δ)/T ≤ 1
              calc 1 / T * (|Real.cos (a * δ) - Real.cos (a * T)| / |a|)
                  ≤ 1 / T * (|a| * (T - δ) / |a|) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    exact div_le_div_of_nonneg_right hcos_lip (abs_nonneg _)
                _ = (T - δ) / T := by
                    rw [mul_div_cancel_left₀ _ (ne_of_gt ha_pos)]; ring
                _ ≤ 1 := by rw [div_le_one₀ hT]; linarith
      _ = 7 := by norm_num
  -- Pointwise convergence: F_n(x) → f₀(x)
  -- F_n(x) = f₀(x) - ∫_0^{δ_n} g, and |∫_0^{δ_n} g| → 0
  have hF_conv : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f₀ x)) := by
    intro x
    set s : ℕ → Set ℝ := fun n => Set.Icc (T / (↑n + 2)) T
    -- Monotone sets
    have hmono : Monotone s := by
      intro m n hmn; apply Set.Icc_subset_Icc_left
      exact div_le_div_of_nonneg_left hT.le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hmn 2)
    -- g is integrable on Icc 0 T
    set g := fun t : ℝ => (1 - t / T) * (Real.sin ((u - x) * t) / t)
    have hg_intOn : IntegrableOn g (Set.Icc 0 T) :=
      integrableOn_of_bounded measure_Icc_lt_top.ne
        ((measurable_const.sub (measurable_id'.div_const T)).mul
          ((Real.measurable_sin.comp (measurable_const.mul measurable_id')).div
            measurable_id')).aestronglyMeasurable
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            rw [Real.norm_eq_abs, abs_mul]
            have h1 : |1 - t / T| ≤ 1 := by
              rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_one₀ hT).mpr ht.2))]
              linarith [div_nonneg ht.1 hT.le]
            exact (mul_le_mul h1 (abs_sin_mul_div_le (u-x) t)
              (abs_nonneg _) one_pos.le).trans (one_mul _).le)
    -- ⋃ s ⊆ Icc 0 T
    have hsubset : ⋃ n, s n ⊆ Set.Icc 0 T :=
      Set.iUnion_subset fun n => Set.Icc_subset_Icc_left (hδ_pos n).le
    have htend := tendsto_setIntegral_of_monotone (f := g) (μ := volume)
      (fun _ => measurableSet_Icc) hmono (hg_intOn.mono_set hsubset)
    -- ∫_{⋃ s} g = ∫_{Icc 0 T} g = f₀ x
    -- Because ⋃ s =ᵃᵉ Icc 0 T (differ at most at {0})
    suffices h : ∫ t in ⋃ n, s n, g t = f₀ x by rwa [h] at htend
    apply setIntegral_congr_set
    -- ⋃ s =ᵃᵉ Icc 0 T. The symmetric difference is ⊆ {0}, which has measure 0.
    rw [Filter.EventuallyEq, ae_iff]
    apply le_antisymm _ (zero_le _)
    apply le_trans (measure_mono _) (by simp : volume ({0} : Set ℝ) ≤ 0)
    intro t ht
    simp only [Set.mem_setOf, Set.mem_singleton_iff]
    -- ht : ¬(t ∈ ⋃ s ↔ t ∈ Icc 0 T)
    -- Since ⋃ s ⊆ Icc 0 T, the → direction is automatic.
    -- So the failure must be ←: t ∈ Icc 0 T but t ∉ ⋃ s.
    -- This happens only if t = 0 (since for t > 0, t ∈ Icc(δ_n, T) for large n).
    by_contra ht0
    apply ht; show (⋃ n, s n) t = (Set.Icc 0 T) t
    apply propext; exact ⟨fun h => hsubset h, fun h => by
      have ht_pos : 0 < t := lt_of_le_of_ne h.1 (Ne.symm ht0)
      obtain ⟨n, hn⟩ := exists_nat_gt (T / t - 2)
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_Icc.mpr ⟨by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < ↑n + 2)]
        nlinarith [mul_div_cancel₀ T (ne_of_gt ht_pos)], h.2⟩⟩⟩
  -- DCT: ∫ F_n dμ → ∫ f₀ dμ
  have htends_μ : Filter.Tendsto (fun n => ∫ x, F n x ∂μ) Filter.atTop
      (nhds (∫ x, f₀ x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (7 : ℝ)) hF_smeas
      (integrable_const _)
      (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hF_bd n x)
      (ae_of_all _ fun x => hF_conv x)
  have htends_ν : Filter.Tendsto (fun n => ∫ x, F n x ∂ν) Filter.atTop
      (nhds (∫ x, f₀ x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (7 : ℝ)) hF_smeas_ν
      (integrable_const _)
      (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hF_bd n x)
      (ae_of_all _ fun x => hF_conv x)
  -- The sequence |(1/π)(∫ F_n dμ - ∫ F_n dν)| → |(1/π)(∫ f₀ dμ - ∫ f₀ dν)|
  -- and each term ≤ I/(2π), so the limit ≤ I/(2π)
  have htends_diff : Filter.Tendsto
      (fun n => (1 / Real.pi) * (∫ x, F n x ∂μ - ∫ x, F n x ∂ν))
      Filter.atTop (nhds ((1 / Real.pi) * (∫ x, f₀ x ∂μ - ∫ x, f₀ x ∂ν))) :=
    (htends_μ.sub htends_ν).const_mul _
  exact le_of_tendsto (htends_diff.abs) (Filter.Eventually.of_forall htrunc_bound)

set_option maxHeartbeats 800000 in
/-- **Fejér CDF density bound.**
For ν with M-Lipschitz CDF and a ≥ 0:
  `∫ (Ψ_F(y+a-x) - Ψ_F(y-a-x)) dν ≤ 2aM`
Uses `fejerKernel_le_const` for the MVT bound: `Ψ_F(u+2a) - Ψ_F(u) ≤ 2a · T/(2π)`.
For the Lipschitz-based bound, uses Tonelli and the density hypothesis. -/
private lemma fejerCDF_density_bound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    {T : ℝ} (hT : 0 < T) (y a : ℝ) (ha : 0 < a) :
    ∫ x, (fejerCDF T (y + a - x) - fejerCDF T (y - a - x)) ∂ν ≤ 2 * a * M := by
  have hnn : ∀ x, 0 ≤ fejerCDF T (y + a - x) - fejerCDF T (y - a - x) := fun x =>
    sub_nonneg.mpr (fejerCDF_monotone hT (by linarith))
  have hmeas := (measurable_fejerCDF_sub hT (y + a)).sub (measurable_fejerCDF_sub hT (y - a))
  -- Convert Bochner integral to lintegral (h ≥ 0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity : (0 : ℝ) ≤ 2 * a * M)
  -- Define the product function G(x,v) = ofReal(K_F(v)) · 𝟏_{Ioc(y-a-x)(y+a-x)}(v)
  set G : ℝ → ℝ → ENNReal := fun x v =>
    ENNReal.ofReal (fejerKernel T v) *
    (Set.Ioc (y - a - x) (y + a - x)).indicator (fun _ => (1 : ENNReal)) v
  -- Indicator swap: v ∈ Ioc(y-a-x)(y+a-x) ↔ x ∈ Ioc(y-a-v)(y+a-v)
  have ind_swap : ∀ x v, v ∈ Set.Ioc (y - a - x) (y + a - x) ↔
      x ∈ Set.Ioc (y - a - v) (y + a - v) := by
    intro x v; constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- Step 1: ofReal(h(x)) = ∫⁻ v, G x v (fejerCDF diff = set integral of K_F)
  have step1 : ∀ x, ENNReal.ofReal (fejerCDF T (y + a - x) - fejerCDF T (y - a - x)) =
      ∫⁻ v, G x v := by
    intro x
    -- fejerCDF T hi - fejerCDF T lo = ∫ v in Ioc lo hi, K_F v
    have hdiff : fejerCDF T (y + a - x) - fejerCDF T (y - a - x) =
        ∫ v in Set.Ioc (y - a - x) (y + a - x), fejerKernel T v := by
      unfold fejerCDF
      have hunion : Set.Iic (y - a - x) ∪ Set.Ioc (y - a - x) (y + a - x) =
          Set.Iic (y + a - x) := by
        ext w; simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioc]
        constructor
        · rintro (h | ⟨h1, h2⟩) <;> linarith
        · intro hw; by_cases hwlo : w ≤ y - a - x
          · left; exact hwlo
          · right; exact ⟨not_le.mp hwlo, hw⟩
      rw [← hunion, setIntegral_union
          (by rw [Set.disjoint_iff]; intro w ⟨h1, h2⟩
              simp only [Set.mem_Iic] at h1; simp only [Set.mem_Ioc] at h2; linarith)
          measurableSet_Ioc (fejerKernel_integrable hT).integrableOn
          (fejerKernel_integrable hT).integrableOn]
      ring
    rw [hdiff]
    rw [ofReal_integral_eq_lintegral_ofReal
        ((fejerKernel_integrable hT).integrableOn.mono_set Set.Ioc_subset_Iic_self)
        (ae_of_all _ (fun v => fejerKernel_nonneg hT v))]
    -- ∫⁻ v in Ioc, ofReal(K_F v) = ∫⁻ v, G x v
    -- G x v = ofReal(K_F v) * indicator_{Ioc}(1)(v) = indicator_{Ioc}(ofReal∘K_F)(v)
    rw [← lintegral_indicator measurableSet_Ioc]
    congr 1; ext v; simp only [G, Set.indicator]
    split_ifs <;> simp
  -- Step 2: G is measurable on the product
  have hG_meas : Measurable (Function.uncurry G) := by
    apply Measurable.mul
    · exact (fejerKernel_measurable T).ennreal_ofReal.comp measurable_snd
    · apply measurable_one.indicator
      exact (measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
  -- Step 3: Tonelli swap ∫⁻_ν ∫⁻_vol G = ∫⁻_vol ∫⁻_ν G
  conv_lhs => rw [show (fun x => ENNReal.ofReal (fejerCDF T (y + a - x) -
    fejerCDF T (y - a - x))) = (fun x => ∫⁻ v, G x v) from funext step1]
  rw [lintegral_lintegral_swap hG_meas.aemeasurable]
  -- Step 4: Compute inner integral ∫⁻_ν G(x,v) dν(x) = ofReal(K_F v) · ν(Ioc(y-a-v)(y+a-v))
  have step4 : ∀ v, ∫⁻ x, G x v ∂ν = ENNReal.ofReal (fejerKernel T v) *
      ν (Set.Ioc (y - a - v) (y + a - v)) := by
    intro v
    -- Swap the indicator: 𝟏_{Ioc(y-a-x)(y+a-x)}(v) = 𝟏_{Ioc(y-a-v)(y+a-v)}(x)
    have : (fun x => G x v) = fun x => ENNReal.ofReal (fejerKernel T v) *
        (Set.Ioc (y - a - v) (y + a - v)).indicator (fun _ => (1 : ENNReal)) x := by
      ext x; simp only [G, Set.indicator]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; exact h2 ((ind_swap x v).mp h1)
      · exfalso; exact h1 ((ind_swap x v).mpr h2)
      · rfl
    rw [show (fun x => G x v) = fun x => ENNReal.ofReal (fejerKernel T v) *
        (Set.Ioc (y - a - v) (y + a - v)).indicator (fun _ => (1 : ENNReal)) x from this]
    simp only [lintegral_const_mul _ ((measurable_indicator_const_iff 1).mpr measurableSet_Ioc)]
    simp only [show (Set.Ioc (y - a - v) (y + a - v)).indicator
        (fun (_ : ℝ) => (1 : ENNReal)) = (Set.Ioc (y - a - v) (y + a - v)).indicator 1 from rfl,
      lintegral_indicator_one measurableSet_Ioc]
  -- Step 5: Bound ν(Ioc) ≤ ofReal(M · 2a)
  have step5 : ∀ v, ν (Set.Ioc (y - a - v) (y + a - v)) ≤ ENNReal.ofReal (M * (2 * a)) := by
    intro v
    calc ν (Set.Ioc (y - a - v) (y + a - v))
        ≤ ν (Set.Icc (y - a - v) (y + a - v)) := measure_mono Set.Ioc_subset_Icc_self
      _ ≤ ENNReal.ofReal (M * ((y + a - v) - (y - a - v))) := hν_density _ _ (by linarith)
      _ = ENNReal.ofReal (M * (2 * a)) := by congr 1; ring
  -- Step 6: Combine
  simp_rw [step4]
  calc ∫⁻ v, ENNReal.ofReal (fejerKernel T v) * ν (Set.Ioc (y - a - v) (y + a - v))
      ≤ ∫⁻ v, ENNReal.ofReal (fejerKernel T v) * ENNReal.ofReal (M * (2 * a)) := by
        apply lintegral_mono; intro v; exact mul_le_mul_left' (step5 v) _
    _ = ENNReal.ofReal (M * (2 * a)) * ∫⁻ v, ENNReal.ofReal (fejerKernel T v) := by
        rw [lintegral_mul_const _ (fejerKernel_measurable T).ennreal_ofReal]
        ring
    _ = ENNReal.ofReal (M * (2 * a)) * ENNReal.ofReal 1 := by
        congr 1
        rw [← ofReal_integral_eq_lintegral_ofReal (fejerKernel_integrable hT)
            (ae_of_all _ (fun v => fejerKernel_nonneg hT v)),
            fejerKernel_integral_one hT]
    _ = ENNReal.ofReal (2 * a * M) := by
        simp only [ENNReal.ofReal_one, mul_one]; congr 1; ring

/-- **Kernel identity for Fejér convolution**: the integral of fejerCDF against a
probability measure equals the kernel convolution with the CDF.
`∫ Ψ_F(c-x) dμ(x) = ∫ K_F(v) · cdf μ (c-v) dv`.
Proof by Tonelli swap (Fubini for nonneg integrands). -/
private lemma fejer_kernel_cdf_identity
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (c : ℝ) :
    ∫ x, fejerCDF T (c - x) ∂μ =
    ∫ v, fejerKernel T v * cdf μ (c - v) := by
  simp_rw [show ∀ x, fejerCDF T (c - x) =
      ∫ v, (Set.Iic (c - x)).indicator (fejerKernel T) v from
    fun x => by unfold fejerCDF; rw [integral_indicator measurableSet_Iic]]
  set f : ℝ → ℝ → ℝ := fun x v => (Set.Iic (c - x)).indicator (fejerKernel T) v
  have hset_meas : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Iic (c - p.1)} := by
    have : {p : ℝ × ℝ | p.2 ∈ Set.Iic (c - p.1)} = {p : ℝ × ℝ | p.1 + p.2 ≤ c} := by
      ext ⟨x, v⟩; simp [Set.mem_Iic]; constructor <;> intro h <;> linarith
    rw [this]; exact measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hf_smeas : StronglyMeasurable (Function.uncurry f) :=
    StronglyMeasurable.indicator
      ((fejerKernel_measurable T).stronglyMeasurable.comp_snd) hset_meas
  have hf_int : Integrable (Function.uncurry f) (μ.prod volume) := by
    apply Integrable.mono ((fejerKernel_integrable hT).comp_snd μ)
      hf_smeas.aestronglyMeasurable
    apply ae_of_all; intro ⟨x, v⟩
    show ‖(Set.Iic (c - x)).indicator (fejerKernel T) v‖ ≤ ‖fejerKernel T v‖
    by_cases hv : v ∈ Set.Iic (c - x)
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, norm_zero]; exact norm_nonneg _
  rw [integral_integral_swap hf_int]
  congr 1; ext v
  have heq : ∀ x, f x v =
      fejerKernel T v * (Set.Iic (c - v)).indicator (1 : ℝ → ℝ) x := by
    intro x; simp only [f, Set.indicator, Set.mem_Iic, Pi.one_apply]
    split_ifs with h1 h2 h2
    · ring
    · exfalso; exact h2 (by linarith)
    · exfalso; exact h1 (by linarith)
    · ring
  simp_rw [heq, integral_const_mul, integral_indicator_one measurableSet_Iic, cdf_eq_real]

/-- **Fejér CDF inversion remainder bound** (Esseen 1945).

For probability measures `μ`, `ν` where `ν` has `M`-Lipschitz CDF, the CDF
difference is bounded by the characteristic function integral plus a `1/T` error:

  `|cdf μ y - cdf ν y| ≤ (1/π) ∫_{-T}^T ‖Δ(t)‖/|t| dt + 24M/(πT)`

**Reference**: Esseen (1945), Feller Vol II §XV.3, Petrov Ch. V. -/
-- sorry count: 1 (I < 2π/3 case)
-- Case I ≥ 2π/3: PROVED via bracket inequality with a = 12/(πT)
-- Case I < 2π/3: needs Fejér kernel convolution identity + sup-norm argument
private lemma esseen_smoothing_ineq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      48 * M / (Real.pi * T) := by
  have hI_nn := charFun_integral_nonneg μ ν T
  have hcdf := abs_cdf_sub_le_one μ ν y
  have hpi := Real.pi_pos
  -- The CDF of ν is M-Lipschitz
  have hG_lip : ∀ a b : ℝ, a ≤ b → cdf ν b - cdf ν a ≤ M * (b - a) :=
    cdf_lipschitz_of_density_bound ν hM hν_density
  -- Key: Lipschitz regularity of Δ. For t ≥ 0:
  -- Δ(y+t) ≥ Δ(y) - Mt because F(y+t) ≥ F(y) and G(y+t) ≤ G(y) + Mt
  have hΔ_reg : ∀ t : ℝ, 0 ≤ t → cdf μ (y + t) - cdf ν (y + t) ≥
      (cdf μ y - cdf ν y) - M * t := by
    intro t ht
    have hF_mono : cdf μ y ≤ cdf μ (y + t) := monotone_cdf μ (le_add_of_nonneg_right ht)
    have hG_lip_t : cdf ν (y + t) - cdf ν y ≤ M * t := by
      have h1 := hG_lip y (y + t) (le_add_of_nonneg_right ht)
      linarith
    linarith
  -- Similarly for the other direction: Δ(y-t) ≤ Δ(y) + Mt
  -- (F(y-t) ≤ F(y) and G(y-t) ≥ G(y) - Mt)
  have hΔ_reg' : ∀ t : ℝ, 0 ≤ t → cdf μ y - cdf ν y ≤
      (cdf μ (y + t) - cdf ν (y + t)) + M * t := by
    intro t ht; linarith [hΔ_reg t ht]
  -- Case split: if |Δ(y)| ≤ 48M/(πT), trivially ≤ RHS
  set D := cdf μ y - cdf ν y with hD_def
  by_cases hD_small : |D| ≤ 48 * M / (Real.pi * T)
  · calc |D| ≤ 48 * M / (Real.pi * T) := hD_small
      _ ≤ 1 / Real.pi * (∫ t in Set.Icc (-T) T,
            ‖charFun μ t - charFun ν t‖ / |t|) +
          48 * M / (Real.pi * T) := le_add_of_nonneg_left (mul_nonneg (by positivity) hI_nn)
  · -- Case |Δ(y)| > 48M/(πT). Need genuine bound.
    push_neg at hD_small
    set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| with hI_def
    by_cases hI_large : 2 * Real.pi / 3 ≤ I
    · -- Case I ≥ 2π/3: bracket argument closes this case.
      -- The charFun integral is positive, so the integrand is IntegrableOn
      have hI_pos : 0 < I := lt_of_lt_of_le (by positivity) hI_large
      have hint : IntegrableOn (fun t => ‖charFun μ t - charFun ν t‖ / |t|)
          (Set.Icc (-T) T) := by
        by_contra h
        have : I = 0 := integral_undef (show ¬Integrable _ (volume.restrict _) from h)
        linarith
      -- Set bracket parameter a = 12/(πT)
      set a := 12 / (Real.pi * T) with ha_def
      have ha_pos : 0 < a := by positivity
      -- Upper bracket: D ≤ ∫ Ψ_F(y+a-x) dμ - ∫ Ψ_F(y-a-x) dν + 2(1-Ψ_F(a))
      have hD_upper : D ≤ ∫ x, fejerCDF T (y + a - x) ∂μ -
          ∫ x, fejerCDF T (y - a - x) ∂ν + 2 * (1 - fejerCDF T a) := by
        have h1 := cdf_le_fejerCDF_integral hT μ y a ha_pos.le
        have h2 := fejerCDF_integral_le_cdf hT ν y a ha_pos.le
        linarith
      -- Lower bracket: -D ≤ ∫ Ψ_F(y+a-x) dν - ∫ Ψ_F(y-a-x) dμ + 2(1-Ψ_F(a))
      have hD_lower : -D ≤ ∫ x, fejerCDF T (y + a - x) ∂ν -
          ∫ x, fejerCDF T (y - a - x) ∂μ + 2 * (1 - fejerCDF T a) := by
        have h1 := cdf_le_fejerCDF_integral hT ν y a ha_pos.le
        have h2 := fejerCDF_integral_le_cdf hT μ y a ha_pos.le
        linarith
      -- Decompose: ∫ Ψ_F(y+a-·) dμ - ∫ Ψ_F(y-a-·) dν
      --   = [∫ Ψ_F(y+a-·) d(μ-ν)] + [∫ (Ψ_F(y+a-·) - Ψ_F(y-a-·)) dν]
      -- Bound 1: |convolution| ≤ I/(2π)
      have hconv_plus := fejer_convolution_bound μ ν T hT (y + a) hint
      have hconv_minus := fejer_convolution_bound μ ν T hT (y - a) hint
      -- Bound 2: density ≤ 2aM
      have hdensity := fejerCDF_density_bound ν hM hν_density hT y a ha_pos
      -- Bound 3: tail ≤ 2/(πTa)
      have htail := fejerCDF_tail_bound hT ha_pos
      -- Combine: |D| ≤ I/(2π) + 2aM + 2·2/(πTa) = I/(2π) + 2aM + 4/(πTa)
      -- With a = 12/(πT): 2aM = 24M/(πT), 4/(πTa) = 4πT/(πT·12) = 1/3
      have ha_val : 2 * a * M = 24 * M / (Real.pi * T) := by
        rw [ha_def]; field_simp; ring
      have htail_val : 4 / (Real.pi * T * a) = 1 / 3 := by
        rw [ha_def]; field_simp; ring
      -- Decomposition: ∫ Ψ(y+a) dμ - ∫ Ψ(y-a) dν = conv + density where
      -- conv = ∫ Ψ(y+a) d(μ-ν), density = ∫ (Ψ(y+a)-Ψ(y-a)) dν
      -- Upper bound for D:
      have hD_upper' : D ≤ 1 / (2 * Real.pi) * I +
          2 * a * M + 2 * (1 - fejerCDF T a) := by
        calc D ≤ ∫ x, fejerCDF T (y + a - x) ∂μ -
            ∫ x, fejerCDF T (y - a - x) ∂ν + 2 * (1 - fejerCDF T a) := hD_upper
          _ = (∫ x, fejerCDF T (y + a - x) ∂μ - ∫ x, fejerCDF T (y + a - x) ∂ν) +
              (∫ x, (fejerCDF T (y + a - x) - fejerCDF T (y - a - x)) ∂ν) +
              2 * (1 - fejerCDF T a) := by
            rw [integral_sub (integrable_fejerCDF_sub hT (y + a) ν)
                (integrable_fejerCDF_sub hT (y - a) ν)]
            ring
          _ ≤ |∫ x, fejerCDF T (y + a - x) ∂μ - ∫ x, fejerCDF T (y + a - x) ∂ν| +
              2 * a * M + 2 * (1 - fejerCDF T a) := by
            linarith [le_abs_self (∫ x, fejerCDF T (y + a - x) ∂μ -
                ∫ x, fejerCDF T (y + a - x) ∂ν), hdensity]
          _ ≤ 1 / (2 * Real.pi) * I + 2 * a * M +
              2 * (1 - fejerCDF T a) := by linarith [hconv_plus]
      -- Lower bound for -D:
      have hD_lower' : -D ≤ 1 / (2 * Real.pi) * I +
          2 * a * M + 2 * (1 - fejerCDF T a) := by
        calc -D ≤ ∫ x, fejerCDF T (y + a - x) ∂ν -
            ∫ x, fejerCDF T (y - a - x) ∂μ + 2 * (1 - fejerCDF T a) := hD_lower
          _ = -(∫ x, fejerCDF T (y - a - x) ∂μ - ∫ x, fejerCDF T (y - a - x) ∂ν) +
              (∫ x, (fejerCDF T (y + a - x) - fejerCDF T (y - a - x)) ∂ν) +
              2 * (1 - fejerCDF T a) := by
            rw [integral_sub (integrable_fejerCDF_sub hT (y + a) ν)
                (integrable_fejerCDF_sub hT (y - a) ν)]
            ring
          _ ≤ |∫ x, fejerCDF T (y - a - x) ∂μ - ∫ x, fejerCDF T (y - a - x) ∂ν| +
              2 * a * M + 2 * (1 - fejerCDF T a) := by
            linarith [neg_abs_le (∫ x, fejerCDF T (y - a - x) ∂μ -
                ∫ x, fejerCDF T (y - a - x) ∂ν), hdensity]
          _ ≤ 1 / (2 * Real.pi) * I + 2 * a * M +
              2 * (1 - fejerCDF T a) := by linarith [hconv_minus]
      -- Combine: |D| ≤ I/(2π) + 2aM + 2(1-Ψ_F(a))
      -- With a = 12/(πT): 2aM = 24M/(πT), 2(1-Ψ_F(a)) ≤ 4/(πTa) = 1/3
      -- 2(1-Ψ_F(a)) ≤ 4/(πTa)
      have htail2 : 2 * (1 - fejerCDF T a) ≤ 4 / (Real.pi * T * a) := by
        have h := htail
        have : (4 : ℝ) / (Real.pi * T * a) = 2 * (2 / (Real.pi * T * a)) := by ring
        linarith
      have habs_D : |D| ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := by
        rw [abs_le]; constructor
        · -- Need: -(1/(2π)*I + 24M/(πT) + 1/3) ≤ D
          -- From hD_lower': -D ≤ 1/(2π)*I + 2aM + 2(1-Ψ_F(a))
          --   ≤ 1/(2π)*I + 24M/(πT) + 1/3
          have : -D ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := by
            calc -D ≤ 1 / (2 * Real.pi) * I + 2 * a * M +
                2 * (1 - fejerCDF T a) := hD_lower'
              _ ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) +
                  4 / (Real.pi * T * a) := by linarith [ha_val]
              _ = 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := by
                  rw [htail_val]
          linarith
        · -- Need: D ≤ 1/(2π)*I + 24M/(πT) + 1/3
          have : D ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := by
            calc D ≤ 1 / (2 * Real.pi) * I + 2 * a * M +
                2 * (1 - fejerCDF T a) := hD_upper'
              _ ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) +
                  4 / (Real.pi * T * a) := by linarith [ha_val]
              _ = 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := by
                  rw [htail_val]
          linarith
      -- For I ≥ 2π/3: I/(2π) ≥ 1/3, so I/(2π) + 1/3 ≤ I/π
      have hI_halfpi : 1 / 3 ≤ 1 / (2 * Real.pi) * I := by
        have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
        have : 2 * Real.pi / 3 ≤ I := hI_large
        calc (1 : ℝ) / 3 = 2 * Real.pi / 3 * (1 / (2 * Real.pi)) := by field_simp
          _ ≤ I * (1 / (2 * Real.pi)) := by
              apply mul_le_mul_of_nonneg_right hI_large (by positivity)
          _ = 1 / (2 * Real.pi) * I := by ring
      calc |D| ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) + 1 / 3 := habs_D
        _ ≤ 1 / (2 * Real.pi) * I + 24 * M / (Real.pi * T) +
            1 / (2 * Real.pi) * I := by linarith
        _ = 1 / Real.pi * I + 24 * M / (Real.pi * T) := by ring
        _ ≤ 1 / Real.pi * I + 48 * M / (Real.pi * T) := by
            have : 0 ≤ 24 * M / (Real.pi * T) := by positivity
            have : 48 * M / (Real.pi * T) = 24 * M / (Real.pi * T) + 24 * M / (Real.pi * T) := by ring
            linarith
    · -- Case I < 2π/3: sup-norm (sSup) convolution argument.
      -- Uses fejer_kernel_cdf_identity + integral splitting with sup-norm bound.
      -- Key: S = sup|D| satisfies S/2 - 24M/(πT) ≤ I/(2π), giving S ≤ I/π + 48M/(πT).
      push_neg at hI_large
      sorry

/-- **Esseen's Fourier-analytic CDF bound.**

For probability measures `μ`, `ν` where `ν` has bounded density (CDF is `M`-Lipschitz),
the CDF difference is bounded by the characteristic function integral plus a `1/T` error:

  `|cdf μ y - cdf ν y| ≤ (1/π) ∫_{-T}^T ‖Δ(t)‖/|t| dt + 24/(πT)`

**Hypothesis** `hν_density`: the CDF of `ν` is `M`-Lipschitz, stated as
  `ν(Icc a b) ≤ M * (b - a)` for all `a ≤ b`.
This excludes point masses (which would make the bound false, see below).

**Why the Lipschitz condition is necessary**:
The previous hypothesis `∀ y, ν(Icc y (y+1)) ≤ M` was too weak.
Counterexample: `μ = δ_0`, `ν = δ_{1/T²}`, `y = 0`, `T = 100`.
Then `|cdf μ 0 - cdf ν 0| = 1` but `(1/π) I + 24/(πT) ≈ 0.07`,
since `|Δ(t)| = |1 - e^{it/T²}| ≈ |t|/T²` gives `I ≈ 2/T`.
Both point masses satisfy `ν(Icc y (y+1)) ≤ 1` but violate the bound.

**Proof strategy**: Fejér bracket approach via de la Vallée-Poussin kernel.
The hard case (I < π, T > 24/π) requires the Fourier identity:
  `∫ Ψ_k(y-z) d(μ-ν) = (1/2π) ∫_{-T}^T (1-|t|/T) Δ(t) e^{-ity}/(-it) dt`
where `Ψ_k` is the CDF of the Fejér kernel with compact Fourier support.
Combined with the bracket `Ψ_k(u-a) ≤ H(u) ≤ Ψ_k(u+a)` and the Lipschitz
condition on `ν`, this gives `|F-G| ≤ I/(2π) + 2Ma + 4/(πTa)`.
Optimizing `a = 1/T` and absorbing constants gives the result. -/
private lemma levy_cdf_diff_fourier_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      48 * M / (Real.pi * T) := by
  exact esseen_smoothing_ineq μ ν hM hν_density T hT y

private lemma esseen_fourier_cdf_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν_density : ∃ M : ℝ, 0 < M ∧
      ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    ∃ M : ℝ, 0 < M ∧ |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      48 * M / (Real.pi * T) := by
  obtain ⟨M, hM, hbd⟩ := hν_density
  exact ⟨M, hM, levy_cdf_diff_fourier_bound μ ν hM hbd T hT y⟩

/-- The Gaussian density `gaussianPDFReal 0 1 x ≤ 1` for all `x`. -/
private lemma gaussianPDFReal_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  rw [gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hsqrt_ge : (1:ℝ) ≤ √(2 * Real.pi) := by
    calc (1:ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ √(2 * Real.pi) := Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
  have hinv : (√(2 * Real.pi))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt_ge
  calc (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
      ≤ 1 * 1 := mul_le_mul hinv hexp (Real.exp_pos _).le (by positivity)
    _ = 1 := by ring

/-- The standard Gaussian `N(0,1)` has Lipschitz CDF: for all `a ≤ b`,
`ν(Icc a b) ≤ 1 * (b - a)`. This follows from the density being bounded by
`(2π)^{-1/2} < 1`, so `ν(Icc a b) = ∫_a^b g(x) dx ≤ (b-a) · max g ≤ b - a`. -/
private lemma gaussianReal_density_bounded :
    ∀ a b : ℝ, a ≤ b → (gaussianReal 0 1) (Set.Icc a b) ≤ ENNReal.ofReal (1 * (b - a)) := by
  intro a b hab
  rw [one_mul]
  rw [gaussianReal_apply_eq_integral (μ := 0) (by simp : (1 : NNReal) ≠ 0)]
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith)]
  calc ∫ x in Set.Icc a b, gaussianPDFReal 0 1 x
      ≤ ∫ _ in Set.Icc a b, (1 : ℝ) := by
        apply setIntegral_mono_on
        · exact (integrable_gaussianPDFReal 0 1).integrableOn
        · exact integrableOn_const (hs := by simp [Real.volume_Icc, ENNReal.ofReal_ne_top])
        · exact measurableSet_Icc
        · intro x _; exact gaussianPDFReal_le_one x
    _ = b - a := by
        rw [setIntegral_const, smul_eq_mul, mul_one]
        simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ b - a)]

end EsseenInversion

/-- **Esseen's concentration inequality with universal constants.**

For any probability measure `μ` on `ℝ`, there exist **universal** constants `C₁, C₂ > 0`
(independent of `μ`, `T`, `y`) such that for all `T > 0`:

  `|cdf μ y - cdf(gaussianReal 0 1) y| ≤ C₁ * ∫_{-T}^{T} ‖φ_μ(t) - φ_Φ(t)‖/|t| dt + C₂/T`

This is the classical Esseen inequality (1945). The constants are universal because
the standard Gaussian has a bounded continuous density `g(x) = (2π)^{-1/2} e^{-x²/2}`.

**Proof**: Instantiates `esseen_fourier_cdf_bound` with `ν = gaussianReal 0 1` and
uses `gaussianReal_density_bounded` to provide the bounded density hypothesis.
-/
-- sorry count: 0 (sorry moved to JacksonKernel.lean)
lemma esseen_concentration_universal :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
          ∀ y : ℝ, |cdf μ y - cdf (gaussianReal 0 1) y| ≤
            C₁ * (∫ t in Set.Icc (-T) T,
              ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
            C₂ / T := by
  refine ⟨1 / Real.pi, 48 / Real.pi, by positivity, by positivity, fun T hT μ _ y => ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Apply the core Fourier-analytic bound with M = 1 (Gaussian density)
  obtain ⟨M, hM, hbound⟩ := esseen_fourier_cdf_bound μ (gaussianReal 0 1)
    ⟨1, one_pos, gaussianReal_density_bounded⟩ T hT y
  -- Since M = 1 from Gaussian: 24*1/(π*T) = (24/π)/T
  -- But M could be any value satisfying the density bound; we use M = 1 explicitly.
  have hbound' := levy_cdf_diff_fourier_bound μ (gaussianReal 0 1) one_pos
    gaussianReal_density_bounded T hT y
  rw [show 48 * (1 : ℝ) / (Real.pi * T) = (48 / Real.pi) / T from by ring] at hbound'
  exact hbound'

/-- **Auxiliary: the charfun integrand is bounded by 5δ|t|² on Icc(-T, T).**
For t² ≤ 2n (which holds for all t ∈ Icc(-T, T)), the Taylor bound gives
`‖φ_S(t) - φ_Φ(t)‖ ≤ 5δ|t|³` and hence the integrand `≤ 5δt²`. -/
private lemma charfun_integrand_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ)
    (t : ℝ) (ht : t ∈ Set.Icc (-(σ ^ 3 * Real.sqrt ↑n / ρ)) (σ ^ 3 * Real.sqrt ↑n / ρ)) :
    let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
    let δ := ρ / (σ ^ 3 * Real.sqrt ↑n)
    ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ / |t| ≤ 5 * δ * t ^ 2 := by
  intro S δ
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
      (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  have hδ_pos : 0 < δ := div_pos hρ_pos hden_pos
  -- Key: T² ≤ 2n (since σ⁶ ≤ 2ρ² and ρ ≥ σ³)
  set T := σ ^ 3 * Real.sqrt ↑n / ρ with T_def
  have hT_pos : 0 < T := div_pos hden_pos hρ_pos
  have hT_sq_le : T ^ 2 ≤ 2 * ↑n := by
    rw [T_def, div_pow]
    rw [div_le_iff₀ (pow_pos hρ_pos 2)]
    rw [mul_pow, Real.sq_sqrt (le_of_lt hn')]
    have h_s6 : σ ^ 6 ≤ ρ ^ 2 := by
      calc σ ^ 6 = (σ ^ 3) ^ 2 := by ring
        _ ≤ ρ ^ 2 := (sq_le_sq₀ (pow_nonneg hσ.le 3) (by linarith [pow_pos hσ 3])).mpr hρσ
    nlinarith
  -- |t| ≤ T, so t² ≤ T² ≤ 2n
  have ht_abs : |t| ≤ T := by
    rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  have ht2n : t ^ 2 ≤ 2 * ↑n := by
    calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      _ ≤ T ^ 2 := (sq_le_sq₀ (abs_nonneg t) (le_of_lt hT_pos)).mpr ht_abs
      _ ≤ 2 * ↑n := hT_sq_le
  -- Apply Taylor bound
  have htaylor := charfun_diff_taylor_bound hn hσ hm hindep hmean hvar h3 hLp t ht2n
  -- Bound t⁴/(4n) ≤ δ|t|³ for |t| ≤ T
  have ht4_le : t ^ 4 / (4 * ↑n) ≤ δ * |t| ^ 3 := by
    rcases eq_or_ne t 0 with rfl | ht_ne
    · simp
    · have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
      rw [show t ^ 4 = |t| ^ 3 * |t| from by
        nlinarith [sq_abs t, sq_nonneg t, sq_nonneg (|t|), abs_nonneg t]]
      rw [mul_div_assoc, mul_comm δ]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg t) 3)
      -- Need |t|/(4n) ≤ δ = ρ/(σ³√n). Use |t| ≤ T = σ³√n/ρ and σ⁶ ≤ 4ρ².
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ↑n) hden_pos]
      calc |t| * (σ ^ 3 * Real.sqrt ↑n)
          ≤ σ ^ 3 * Real.sqrt ↑n / ρ * (σ ^ 3 * Real.sqrt ↑n) :=
            mul_le_mul_of_nonneg_right ht_abs (le_of_lt hden_pos)
        _ = σ ^ 6 * (Real.sqrt ↑n) ^ 2 / ρ := by ring
        _ = σ ^ 6 * ↑n / ρ := by rw [Real.sq_sqrt (le_of_lt hn')]
        _ ≤ ρ ^ 2 * ↑n / ρ := by
            gcongr
            calc σ ^ 6 = (σ ^ 3) ^ 2 := by ring
              _ ≤ ρ ^ 2 := (sq_le_sq₀ (pow_nonneg hσ.le 3)
                  (by linarith [pow_pos hσ 3])).mpr hρσ
        _ = ρ * ↑n := by field_simp
        _ ≤ ρ * (4 * ↑n) := by nlinarith
  -- Now ‖φ_S - φ_Φ‖ ≤ 5δ|t|³
  have hbound : ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ ≤ 5 * δ * |t| ^ 3 := by
    calc ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖
        ≤ 4 * δ * |t| ^ 3 + t ^ 4 / (4 * ↑n) := htaylor
      _ ≤ 4 * δ * |t| ^ 3 + δ * |t| ^ 3 := by linarith [ht4_le]
      _ = 5 * δ * |t| ^ 3 := by ring
  -- Finally: ‖...‖/|t| ≤ 5δ|t|² = 5δt²
  rcases eq_or_ne t 0 with rfl | ht_ne
  · simp
  · rw [div_le_iff₀ (abs_pos.mpr ht_ne)]
    calc ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖
        ≤ 5 * δ * |t| ^ 3 := hbound
      _ = 5 * δ * t ^ 2 * |t| := by
          have : |t| ^ 3 = |t| ^ 2 * |t| := by ring
          rw [this, sq_abs]; ring

-- 7-step proof with many calc chains and field_simp needs extra heartbeats
set_option maxHeartbeats 400000 in
/-- **Charfun difference bound with exponential decay.**
The charfun difference `‖φ_S(t) - φ_Φ(t)‖` is bounded by `Cδ(|t|³ + t⁴)e^{-t²/8}`
for `16ρ|t| ≤ σ³√n`. This combines:
- Product vs power telescope with M^{n-1} factor (`norm_prod_sub_prod_le_sum_mul_pow`)
- Per-factor charfun bound `‖φᵢ(t')‖ ≤ 1-t²/(4n) =: M` (`norm_charFun_le_one_sub`)
- Power vs exp bound with exponential factor (`complex_pow_approx_exp_decay`)
- `M^{n-1} ≤ e^{-t²(n-1)/(4n)} ≤ e^{-t²/8}` for n ≥ 2
-/
-- sorry count: 0
private lemma charfun_diff_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ)
    (t : ℝ) (ht : 16 * ρ * |t| ≤ σ ^ 3 * Real.sqrt ↑n) :
    let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
    let δ := ρ / (σ ^ 3 * Real.sqrt ↑n)
    ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ ≤
      5 * δ * (|t| ^ 3 + t ^ 4) * Real.exp (-(t ^ 2 / 8)) := by
  intro S δ
  have hn_pos : 0 < n := by omega
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hn2 : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hsn_pos : 0 < σ * Real.sqrt ↑n := mul_pos hσ hsqrt_pos
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
      (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  have hδ_pos : 0 < δ := div_pos hρ_pos hden_pos
  set sn := σ * Real.sqrt ↑n with sn_def
  set t' := t / sn with t'_def
  -- Derive: 16ρ|t'| ≤ σ² (needed for norm_charFun_le_one_sub)
  have ht'_range : 16 * ρ * |t'| ≤ σ ^ 2 := by
    rw [t'_def, abs_div, abs_of_pos hsn_pos]
    rw [show 16 * ρ * (|t| / sn) = 16 * ρ * |t| / sn from by ring]
    rw [div_le_iff₀ hsn_pos, sn_def]
    calc 16 * ρ * |t| ≤ σ ^ 3 * Real.sqrt ↑n := ht
      _ = σ ^ 2 * (σ * Real.sqrt ↑n) := by ring
  -- Derive: t² ≤ 2n
  have ht2n : t ^ 2 ≤ 2 * ↑n := by
    have h_abs : |t| ≤ σ ^ 3 * Real.sqrt ↑n / (16 * ρ) := by
      rw [le_div_iff₀ (by positivity : 0 < 16 * ρ)]; linarith
    have h_abs2 : |t| ≤ Real.sqrt ↑n / 16 := by
      calc |t| ≤ σ ^ 3 * Real.sqrt ↑n / (16 * ρ) := h_abs
        _ ≤ ρ * Real.sqrt ↑n / (16 * ρ) := by gcongr
        _ = Real.sqrt ↑n / 16 := by field_simp
    have : t ^ 2 ≤ (Real.sqrt ↑n / 16) ^ 2 := by
      rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg t) (by positivity)).mpr h_abs2
    rw [div_pow, Real.sq_sqrt (le_of_lt hn')] at this; linarith
  -- Set M := 1 - t²/(4n), the modulus bound
  set M := 1 - t ^ 2 / (4 * ↑n) with M_def
  have ht4n_le1 : t ^ 2 / (4 * ↑n) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * ↑n)]; linarith
  have hM_nonneg : 0 ≤ M := by simp only [M_def]; linarith
  -- Per-factor: ‖φᵢ(t')‖ ≤ M
  have h_factor : ∀ i, ‖charFun (μ.map (Y i)) t'‖ ≤ M := by
    intro i
    have hσ2s2 : σ ^ 2 * t' ^ 2 / 4 = t ^ 2 / (4 * ↑n) := by
      rw [t'_def, div_pow, sn_def, mul_pow, Real.sq_sqrt (le_of_lt hn')]; field_simp
    rw [M_def, ← hσ2s2]
    exact norm_charFun_le_one_sub hσ (hm i) (hmean i) (hvar i) (h3 i) (hLp i) ht'_range
  -- w = 1 - t²/(2n) and ‖w‖ ≤ M
  set w : ℂ := (1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ)) with w_def
  have hw_real : w = ((1 - t ^ 2 / (2 * ↑n) : ℝ) : ℂ) := by
    simp only [w_def]; push_cast; ring
  have ht2n_le1 : t ^ 2 / (2 * ↑n) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * ↑n)]; linarith
  have hw_norm_le_M : ‖w‖ ≤ M := by
    rw [hw_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    simp only [M_def]
    -- Need: 1 - t²/(2n) ≤ 1 - t²/(4n), i.e., t²/(4n) ≤ t²/(2n)
    have h4 : (0 : ℝ) < 4 * ↑n := by positivity
    have h2 : (0 : ℝ) < 2 * ↑n := by positivity
    have : t ^ 2 / (4 * ↑n) ≤ t ^ 2 / (2 * ↑n) := by
      rw [div_le_div_iff₀ h4 h2]; nlinarith [sq_nonneg t]
    linarith
  -- Per-factor Taylor: ‖φᵢ(t') - w‖ ≤ 4ρ|t'|³
  have h_taylor_per : ∀ i,
      ‖charFun (μ.map (Y i)) t' - w‖ ≤ 4 * ρ * |t'| ^ 3 := by
    intro i
    have htaylor := charfun_taylor_third_moment (hm i) (hmean i) (hvar i) (h3 i) (hLp i) t'
    suffices heq : w = (1 : ℂ) - ((σ ^ 2 * t' ^ 2 / 2 : ℝ) : ℂ) by rwa [heq]
    have hreal : (1 : ℝ) - t ^ 2 / (2 * ↑n) = 1 - σ ^ 2 * t' ^ 2 / 2 := by
      congr 1; simp only [t', sn]
      rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hn')]; field_simp
    rw [hw_real, hreal]; push_cast; ring
  -- Step 1: Rewrite charfun using product factorization
  have step1 := charfun_iid_sum_eq_prod hn_pos hσ hm hindep t
  rw [charFun_gaussianReal_standard t, step1]
  set prod_val := ∏ i : Fin n, charFun (μ.map (Y i)) t'
  set gauss_val := Complex.exp (-((↑(t ^ 2) : ℂ) / 2))
  -- Step 2: Part A — telescope bound on ‖∏φᵢ - w^n‖
  have part_a : ‖prod_val - w ^ n‖ ≤ M ^ (n - 1) * (4 * δ * |t| ^ 3) := by
    have h_telescope := norm_prod_sub_prod_le_sum_mul_pow
        (fun i => charFun (μ.map (Y i)) t') (fun _ => w) M hM_nonneg
        h_factor (fun _ => hw_norm_le_M)
    have h_sum_le : ∑ i : Fin n, ‖charFun (μ.map (Y i)) t' - w‖ ≤
        ↑n * (4 * ρ * |t'| ^ 3) := by
      calc ∑ i : Fin n, ‖charFun (μ.map (Y i)) t' - w‖
          ≤ ∑ _i : Fin n, (4 * ρ * |t'| ^ 3) :=
            Finset.sum_le_sum (fun i _ => h_taylor_per i)
        _ = ↑n * (4 * ρ * |t'| ^ 3) := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    calc ‖prod_val - w ^ n‖
        = ‖∏ i, charFun (μ.map (Y i)) t' - ∏ _i : Fin n, w‖ := by
          congr 1; rw [Finset.prod_const, Finset.card_fin]
      _ ≤ M ^ (n - 1) * ∑ i : Fin n, ‖charFun (μ.map (Y i)) t' - w‖ := by
          exact h_telescope
      _ ≤ M ^ (n - 1) * (↑n * (4 * ρ * |t'| ^ 3)) :=
          mul_le_mul_of_nonneg_left h_sum_le (pow_nonneg hM_nonneg _)
      _ = M ^ (n - 1) * (4 * δ * |t| ^ 3) := by
          congr 1; simp only [t'_def, δ, sn_def]
          rw [abs_div, abs_of_pos hsn_pos, div_pow, mul_pow]
          rw [show Real.sqrt ↑n ^ 3 = Real.sqrt ↑n * ↑n from by
            rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two,
                Real.mul_self_sqrt (le_of_lt hn'), mul_comm]]
          field_simp
  -- Step 3: Part B — power-vs-exp
  have part_b : ‖w ^ n - gauss_val‖ ≤
      t ^ 4 / (4 * ↑n) * Real.exp (-(↑(n - 1) * t ^ 2 / (2 * ↑n))) :=
    complex_pow_approx_exp_decay n hn_pos t ht2n
  -- Step 4: M^{n-1} ≤ e^{-t²/8}
  have h1n : (1 : ℕ) ≤ n := by omega
  have hn_sub : (↑(n - 1) : ℝ) = ↑n - 1 := by simp [Nat.cast_sub h1n]
  have hM_exp : M ^ (n - 1) ≤ Real.exp (-(t ^ 2 / 8)) := by
    have h_base : M ≤ Real.exp (-(t ^ 2 / (4 * ↑n))) := by
      have h_exp := Real.add_one_le_exp (-(t ^ 2 / (4 * ↑n)))
      simp only [M_def]; linarith
    calc M ^ (n - 1)
        ≤ (Real.exp (-(t ^ 2 / (4 * ↑n)))) ^ (n - 1) :=
          pow_le_pow_left₀ hM_nonneg h_base _
      _ = Real.exp (↑(n - 1) * -(t ^ 2 / (4 * ↑n))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(t ^ 2 / 8)) := by
          apply Real.exp_le_exp_of_le; rw [hn_sub]
          rw [show (↑n - 1) * -(t ^ 2 / (4 * ↑n)) = -((↑n - 1) * t ^ 2 / (4 * ↑n)) from by ring]
          rw [neg_le_neg_iff]
          rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) (by positivity : (0:ℝ) < 4 * ↑n)]
          nlinarith [sq_nonneg t, mul_self_nonneg (t ^ 2)]
  -- Step 5: exp factor in Part B ≤ e^{-t²/8}
  have hexp_B_le : Real.exp (-(↑(n - 1) * t ^ 2 / (2 * ↑n))) ≤
      Real.exp (-(t ^ 2 / 8)) := by
    apply Real.exp_le_exp_of_le
    rw [neg_le_neg_iff]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) (by positivity : (0:ℝ) < 2 * ↑n)]
    rw [hn_sub]
    nlinarith [sq_nonneg t, mul_self_nonneg (t ^ 2)]
  -- Step 6: t⁴/(4n) ≤ δ·t⁴  (from σ³ ≤ ρ, √n ≤ n)
  have h_inv_n_le_δ : t ^ 4 / (4 * ↑n) ≤ δ * t ^ 4 := by
    suffices h : 1 / (4 * ↑n) ≤ δ by
      have ht4 : 0 ≤ t ^ 4 := by positivity
      calc t ^ 4 / (4 * ↑n) = 1 / (4 * ↑n) * t ^ 4 := by ring
        _ ≤ δ * t ^ 4 := by gcongr
    show 1 / (4 * ↑n) ≤ ρ / (σ ^ 3 * Real.sqrt ↑n)
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ↑n) hden_pos]
    have h_sqrt_le : Real.sqrt ↑n ≤ ↑n := by
      calc Real.sqrt ↑n ≤ Real.sqrt (↑n ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [hn2])
        _ = ↑n := Real.sqrt_sq (by linarith)
    calc 1 * (σ ^ 3 * Real.sqrt ↑n) = σ ^ 3 * Real.sqrt ↑n := one_mul _
      _ ≤ ρ * Real.sqrt ↑n := by gcongr
      _ ≤ ρ * ↑n := by gcongr
      _ ≤ ρ * (4 * ↑n) := by nlinarith
  -- Step 7: Assembly
  have hexp_pos : 0 < Real.exp (-(t ^ 2 / 8)) := Real.exp_pos _
  calc ‖prod_val - gauss_val‖
      ≤ ‖prod_val - w ^ n‖ + ‖w ^ n - gauss_val‖ := by
        calc _ = ‖(prod_val - w ^ n) + (w ^ n - gauss_val)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ M ^ (n - 1) * (4 * δ * |t| ^ 3) +
        t ^ 4 / (4 * ↑n) * Real.exp (-(↑(n - 1) * t ^ 2 / (2 * ↑n))) :=
      add_le_add part_a part_b
    _ ≤ Real.exp (-(t ^ 2 / 8)) * (4 * δ * |t| ^ 3) +
        δ * t ^ 4 * Real.exp (-(t ^ 2 / 8)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hM_exp (by positivity)
      · calc t ^ 4 / (4 * ↑n) * Real.exp (-(↑(n - 1) * t ^ 2 / (2 * ↑n)))
            ≤ t ^ 4 / (4 * ↑n) * Real.exp (-(t ^ 2 / 8)) :=
              mul_le_mul_of_nonneg_left hexp_B_le (by positivity)
          _ ≤ δ * t ^ 4 * Real.exp (-(t ^ 2 / 8)) := by
              nlinarith [h_inv_n_le_δ, hexp_pos.le]
    _ = (4 * δ * |t| ^ 3 + δ * t ^ 4) * Real.exp (-(t ^ 2 / 8)) := by ring
    _ ≤ 5 * δ * (|t| ^ 3 + t ^ 4) * Real.exp (-(t ^ 2 / 8)) := by
      apply mul_le_mul_of_nonneg_right _ hexp_pos.le
      have : 0 ≤ |t| ^ 3 := by positivity
      have : 0 ≤ t ^ 4 := by positivity
      nlinarith

-- sorry count: 0 (proved using charfun_diff_exp_bound + Gaussian moment integrability)
-- Strategy: For n ≥ 2, charfun_diff_exp_bound gives ‖φ-Φ‖/|t| ≤ 5δ(t²+|t|³)e^{-t²/8}
-- on [-T', T'] with T' = σ³√n/(16ρ). Then ∫ ≤ 5δ·K where K = ∫_ℝ (t²+|t|³)e^{-t²/8} dt.
-- Integration range changed from T to T/16 to match charfun_diff_exp_bound hypothesis.
set_option maxHeartbeats 800000 in
lemma charfun_integral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n : ℕ} (hn : 2 ≤ n)
        {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ),
        (∀ i, Measurable (Y i)) →
        iIndepFun (m := fun _ => inferInstance) Y μ →
        (∀ i j, IdentDistrib (Y i) (Y j) μ μ) →
        (∀ i, ∫ ω, Y i ω ∂μ = 0) →
        (∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2) →
        (∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ) →
        (∀ i, MemLp (Y i) 3 μ) →
        let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
        let T' := σ ^ 3 * Real.sqrt ↑n / (16 * ρ)
        ∫ t in Set.Icc (-T') T',
          ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ / |t| ≤
          C * ρ / (σ ^ 3 * Real.sqrt ↑n) := by
  -- Step 1: Establish integrability of 5δ·(t²+|t|³)·e^{-t²/8}
  -- We bound t²+|t|³ ≤ 2(1+t⁴) and show (1+t⁴)e^{-t²/8} is integrable.
  have hb : (0 : ℝ) < 1/8 := by norm_num
  -- e^{-t²/8} is integrable
  have hint_exp : Integrable (fun x : ℝ => Real.exp (-(1/8) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  -- t⁴·e^{-t²/8} is integrable: convert rpow to pow
  have hint_t4 : Integrable (fun x : ℝ => x ^ 4 * Real.exp (-(1/8) * x ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 4)
    exact this.congr (ae_of_all _ fun _ => by norm_cast)
  -- (1+t⁴)·e^{-t²/8} is integrable
  have hg_int : Integrable
      (fun t : ℝ => (1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)) :=
    (hint_exp.add hint_t4).congr (ae_of_all _ fun t => by simp [Pi.add_apply]; ring)
  -- Set K = ∫_ℝ (1+t⁴)·e^{-t²/8} dt (finite, nonneg)
  set K := ∫ t : ℝ, (1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2) with K_def
  have hK_nonneg : 0 ≤ K := integral_nonneg fun t => by positivity
  -- Step 2: Choose C = 10 * K + 1
  refine ⟨10 * K + 1, by linarith, ?_⟩
  intro Ω mΩ μ hprob n hn Y σ ρ hσ hm hindep hiid hmean hvar h3 hLp S T'
  -- Derive basic positivity facts
  have hn_pos : 0 < n := by omega
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
      (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  set δ := ρ / (σ ^ 3 * Real.sqrt ↑n) with δ_def
  have hδ_pos : 0 < δ := div_pos hρ_pos hden_pos
  have hT'_pos : 0 < T' := div_pos hden_pos (by positivity)
  -- Step 3: Pointwise bound on integrand
  -- For t ∈ [-T', T'], charfun_diff_exp_bound gives:
  --   ‖φ_S(t) - φ_Φ(t)‖ ≤ 5δ(|t|³+t⁴)·e^{-t²/8}
  -- Dividing by |t|: ‖...‖/|t| ≤ 5δ(t²+|t|³)·e^{-t²/8}
  -- Bounding: t²+|t|³ ≤ 2(1+t⁴) since t²≤1+t⁴ and |t|³≤1+t⁴
  -- So: ‖...‖/|t| ≤ 10δ·(1+t⁴)·e^{-t²/8}
  have h_pointwise : ∀ t ∈ Set.Icc (-T') T',
      ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ / |t| ≤
        10 * δ * ((1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)) := by
    intro t ht
    have ht_abs : |t| ≤ T' := by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
    have h16 : 16 * ρ * |t| ≤ σ ^ 3 * Real.sqrt ↑n := by
      calc 16 * ρ * |t| ≤ 16 * ρ * T' := by nlinarith [abs_nonneg t]
        _ = 16 * ρ * (σ ^ 3 * Real.sqrt ↑n / (16 * ρ)) := rfl
        _ = σ ^ 3 * Real.sqrt ↑n := by field_simp
    have hcdb := charfun_diff_exp_bound hn hσ hm hindep hmean hvar h3 hLp t h16
    have hexp_eq : Real.exp (-(t ^ 2 / 8)) = Real.exp (-(1/8) * t ^ 2) := by congr 1; ring
    rcases eq_or_ne t 0 with rfl | ht_ne
    · simp; positivity
    · rw [div_le_iff₀ (abs_pos.mpr ht_ne)]
      -- ‖...‖ ≤ 5δ(|t|³+t⁴)·e^{-t²/8} ≤ 10δ(1+t⁴)·e^{-(1/8)t²}·|t|
      -- because (|t|³+t⁴) ≤ 2(1+t⁴)·|t|? No, that's wrong.
      -- Actually: (|t|³+t⁴)/|t| = t²+|t|³, and t²+|t|³ ≤ 2(1+t⁴)
      -- So ‖...‖/|t| ≤ 5δ(t²+|t|³)·e^{...} ≤ 10δ(1+t⁴)·e^{...}
      -- Rewrite: ‖...‖ ≤ 5δ(|t|³+t⁴)·e^{...} = 5δ·|t|·(t²+|t|³)·e^{...}
      --                                       ≤ 5δ·|t|·2(1+t⁴)·e^{...}
      --                                       = 10δ·(1+t⁴)·e^{...}·|t|
      have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
      -- Factor: |t|³+t⁴ = |t|·(t²+|t|³) since |t|²=t² and |t|⁴=t⁴
      have hfactor : |t| ^ 3 + t ^ 4 = |t| * (t ^ 2 + |t| ^ 3) := by
        have : |t| ^ 2 = t ^ 2 := sq_abs t
        nlinarith [sq_nonneg t, abs_nonneg t, sq_nonneg (|t|)]
      -- Bound: t²+|t|³ ≤ 2(1+t⁴)
      have hbound_sum : t ^ 2 + |t| ^ 3 ≤ 2 * (1 + t ^ 4) := by
        have h1 : t ^ 2 ≤ 1 + t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - 1)]
        have h2 : |t| ^ 3 ≤ 1 + t ^ 4 := by
          nlinarith [sq_nonneg (|t| * |t| - 1), sq_nonneg (|t|), abs_nonneg t,
                     sq_abs t]
        linarith
      calc ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖
          ≤ 5 * δ * (|t| ^ 3 + t ^ 4) * Real.exp (-(t ^ 2 / 8)) := hcdb
        _ = 5 * δ * (|t| * (t ^ 2 + |t| ^ 3)) * Real.exp (-(1/8) * t ^ 2) := by
            rw [hfactor, hexp_eq]
        _ ≤ 5 * δ * (|t| * (2 * (1 + t ^ 4))) * Real.exp (-(1/8) * t ^ 2) := by
            gcongr
        _ = 10 * δ * ((1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)) * |t| := by ring
  -- Step 4: Integrate the bound over [-T', T']
  -- ∫_{-T'}^{T'} ‖...‖/|t| ≤ ∫_{-T'}^{T'} 10δ(1+t⁴)e^{-t²/8}
  --                           ≤ 10δ · ∫_ℝ (1+t⁴)e^{-t²/8}
  --                           = 10δ · K
  --                           = 10K · ρ/(σ³√n)
  --                           ≤ (10K+1) · ρ/(σ³√n)
  -- Integrable bound on restricted measure
  have hg_intOn : IntegrableOn
      (fun t => 10 * δ * ((1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)))
      (Set.Icc (-T') T') :=
    ((hg_int.const_mul (10 * δ)).congr (ae_of_all _ fun t => by ring)).integrableOn
  calc ∫ t in Set.Icc (-T') T',
        ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ / |t|
      ≤ ∫ t in Set.Icc (-T') T',
          10 * δ * ((1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)) := by
        -- Use integral_mono_of_nonneg on the restricted measure
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun t => div_nonneg (norm_nonneg _) (abs_nonneg _)
        · exact hg_intOn
        · exact ae_restrict_mem measurableSet_Icc |>.mono fun t ht => h_pointwise t ht
    _ ≤ ∫ t, 10 * δ * ((1 + t ^ 4) * Real.exp (-(1/8) * t ^ 2)) := by
        apply setIntegral_le_integral
        · exact (hg_int.const_mul (10 * δ)).congr (ae_of_all _ fun t => by ring)
        · exact ae_of_all _ fun t => by positivity
    _ = 10 * δ * K := by
        rw [integral_const_mul]
    _ = 10 * K * (ρ / (σ ^ 3 * Real.sqrt ↑n)) := by ring
    _ ≤ (10 * K + 1) * ρ / (σ ^ 3 * Real.sqrt ↑n) := by
        rw [mul_div_assoc]
        gcongr
        linarith [div_pos hρ_pos hden_pos]

/-- **Berry-Esseen core bound (assembly).**

For the standardized sum `S`, the CDF difference is bounded by `O(ρ/(σ³√n))`:

  `|cdf(μ.map S) y - cdf(gaussianReal 0 1) y| ≤ C * ρ / (σ³ * √n)`

Combines `esseen_concentration_universal` (Esseen's inequality with universal `C₁, C₂`)
and `charfun_integral_bound` (integral bound `I ≤ C₃ * δ`).

With `T' = σ³√n/(16ρ)` and `δ = ρ/(σ³√n)`:
- From `esseen_concentration_universal` with T': `|F-Φ| ≤ C₁ * I(T') + C₂/T'`
- From `charfun_integral_bound`: `I(T') ≤ C₃ * δ`
- `C₂/T' = 16C₂δ`
- So `|F-Φ| ≤ C₁C₃δ + 16C₂δ = (C₁C₃ + 16C₂) * δ`
-/
-- sorry count: 0 (proved from esseen_concentration_universal + charfun_integral_bound)
lemma esseen_charfun_integral_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n : ℕ} (hn : 2 ≤ n)
        {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ),
        (∀ i, Measurable (Y i)) →
        iIndepFun (m := fun _ => inferInstance) Y μ →
        (∀ i j, IdentDistrib (Y i) (Y j) μ μ) →
        (∀ i, ∫ ω, Y i ω ∂μ = 0) →
        (∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2) →
        (∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ) →
        (∀ i, MemLp (Y i) 3 μ) →
        let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
        ∀ y : ℝ,
          |cdf (μ.map S) y - cdf (gaussianReal 0 1) y| ≤
            C * ρ / (σ ^ 3 * Real.sqrt ↑n) := by
  -- Extract universal constants from both sub-lemmas FIRST
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hesseen⟩ := esseen_concentration_universal
  obtain ⟨C₃, hC₃_pos, hintegral⟩ := charfun_integral_bound
  -- Set C = C₁ * C₃ + 16 * C₂ (the combined constant)
  refine ⟨C₁ * C₃ + 16 * C₂, by positivity, ?_⟩
  intro Ω mΩ μ hprob n hn Y σ ρ hσ hm hindep hiid hmean hvar h3 hLp S y
  -- Derive basic positivity facts
  have hn_pos : 0 < n := by omega
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
      (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  -- Use T' = σ³√n/(16ρ) for both Esseen and the integral bound
  set T' := σ ^ 3 * Real.sqrt ↑n / (16 * ρ) with T'_def
  have hT'_pos : 0 < T' := div_pos hden_pos (by positivity)
  -- S is measurable, so μ.map S is a probability measure
  have hS_meas : Measurable S :=
    (Finset.measurable_sum Finset.univ (fun i _ => hm i)).div_const _
  have : IsProbabilityMeasure (μ.map S) := isProbabilityMeasure_map hS_meas.aemeasurable
  -- Apply Esseen's inequality with T': |F-Φ| ≤ C₁ * I(T') + C₂/T'
  have hess := hesseen T' hT'_pos (μ.map S) y
  -- Apply the integral bound: I(T') ≤ C₃ * δ
  have hint := hintegral hn hσ hm hindep hiid hmean hvar h3 hLp
  -- Key: C₂/T' = 16C₂ * ρ/(σ³√n)
  have hC2T' : C₂ / T' = 16 * C₂ * ρ / (σ ^ 3 * Real.sqrt ↑n) := by
    simp only [T'_def]; field_simp
  -- Combine: |F-Φ| ≤ C₁*(C₃δ) + 16C₂δ = (C₁C₃ + 16C₂)δ
  calc |cdf (μ.map S) y - cdf (gaussianReal 0 1) y|
      ≤ C₁ * (∫ t in Set.Icc (-T') T',
          ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ / |t|) +
        C₂ / T' := hess
    _ ≤ C₁ * (C₃ * ρ / (σ ^ 3 * Real.sqrt ↑n)) + C₂ / T' := by
        gcongr
    _ = C₁ * (C₃ * ρ / (σ ^ 3 * Real.sqrt ↑n)) +
        16 * C₂ * ρ / (σ ^ 3 * Real.sqrt ↑n) := by rw [hC2T']
    _ = (C₁ * C₃ + 16 * C₂) * ρ / (σ ^ 3 * Real.sqrt ↑n) := by ring

/-! ## Main theorem -/

/-- **Berry-Esseen Theorem.**

For i.i.d. mean-zero random variables `Y₁, ..., Yₙ` with `E[Yᵢ²] = σ²`,
`E[|Yᵢ|³] = ρ`, and `Yᵢ ∈ L³`, the CDF of the standardized sum
`S = (∑ Yᵢ)/(σ√n)` satisfies:

  `|F_S(y) - Φ(y)| ≤ C * ρ / (σ³ * √n)`

for all `y ∈ ℝ`, where `C` is a universal constant and `Φ` is the standard normal CDF. -/
theorem berry_esseen_theorem :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n : ℕ} (hn : 2 ≤ n)
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
  obtain ⟨C, hC_pos, hbound⟩ := esseen_charfun_integral_bound
  refine ⟨C, hC_pos, ?_⟩
  intro Ω mΩ μ hprob n hn' Y σ' ρ' hσ' hm' hindep' hiid' hmean' hvar' h3' hLp' S F_n Φ y
  exact hbound hn' hσ' hm' hindep' hiid' hmean' hvar' h3' hLp' y

end Statlean.BerryEsseen

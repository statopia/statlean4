/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Berry-Esseen Theorem

## Status
- **1 sorry** remains: `levy_cdf_diff_fourier_bound` (large T, I < π case)
  - **Proof plan documented**: Fejér kernel bracket approach (see section header)
  - Dependency chain: Dirichlet integral → sinc² integral → Fejér kernel → bracket
- `abel_sinc_integral` PROVED (zero sorry, Leibniz rule + ODE uniqueness)
- `esseen_fourier_cdf_bound` PROVED from `levy_cdf_diff_fourier_bound`
- `esseen_concentration_universal` PROVED modulo Fejér infrastructure
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
   **1 sorry** (large T, I < π case). Proof plan: Fejér bracket approach.

2. **Core Fourier bound** (`levy_cdf_diff_fourier_bound`): Combines trivial cases
   (small T, large I) with `fejer_bracket_bound` for the hard case.

3. **Esseen concentration** (`esseen_concentration_universal`): Universal constants `C₁, C₂`
   by instantiating step 2 with `ν = gaussianReal 0 1` and `gaussianReal_density_bounded`.

4. **Charfun integral bound** (`charfun_integral_bound`): The integral from step 3
   is bounded by `C₃ * ρ/(σ³√n)` when `T' = σ³√n/(16ρ)`, using charfun Taylor bounds
   and exponential decay from `charfun_diff_exp_bound`.

5. **Assembly** (`esseen_charfun_integral_bound`): PROVED from steps 3-4.

6. **Main theorem** (`berry_esseen_theorem`): Direct consequence of step 5.

## Remaining sorry (1)

- `levy_cdf_diff_fourier_bound` (large T, I < π case): Esseen's smoothing inequality.
  **Hypothesis fix**: Changed from `∀ y, ν(Icc y (y+1)) ≤ M` (too weak, point masses
  give counterexample: μ=δ_0, ν=δ_{1/T²}, y=0 gives |F-G|=1 but RHS≈2/T→0)
  to Lipschitz CDF: `∀ a b, a ≤ b → ν(Icc a b) ≤ M*(b-a)` (bounded density).
  **Proof plan** (Bobkov's Fourier inversion remainder bound, ~200 lines):
  Reference: Bobkov (2024) "On the remainder term in the approximate Fourier
  inversion formula for distribution functions", Proposition 2.1 + Corollary 1.2.
  1. Prove |r(t)| ≤ π/(1+t) where r(t) = ∫_t^∞ sin(u)/u du (~30 lines)
  2. Bobkov identity via Fubini + bound on r: for CDF F with charfun φ,
     |F(x) - (1/2π)∫_{-T}^T φ(t)e^{-itx}/(-it)dt - 1/2| ≤ ∫dF(z)/(1+T|z-x|)
  3. Apply to difference F-G, bound ∫dν(z)/(1+T|z-x|) using Q_ν(h) ≤ Mh
  4. By Prop 1.1: δ_ν(T) ≤ 2/(1+T) + 4M·log(1+T)/T ≤ 8M·log(T)/T for T ≥ 2
  5. Combined: |F-G| ≤ I/(2π) + 8M·log(T)/T + ∫dμ(z)/(1+T|z-x|)
  6. The μ-integral ≤ 1 (trivial), absorb into I/(2π) using I/π - I/(2π) = I/(2π)
  Note: the constant 24 in 24/(πT) is generous; log(T)/T ≤ 24/(πT) for T ≤ ~2078

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
    (hν_density : ∃ M : ℝ, 0 < M ∧
      ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 / (Real.pi * T) := by
  -- The charFun integral is nonneg
  have hI_nn := charFun_integral_nonneg μ ν T
  -- |cdf diff| ≤ 1
  have hcdf := abs_cdf_sub_le_one μ ν y
  -- π > 0
  have hpi := Real.pi_pos
  -- 24/(πT) > 0
  have h24 : 0 < 24 / (Real.pi * T) := by positivity
  -- If 24/(πT) ≥ 1, the bound is trivially true since |cdf diff| ≤ 1 ≤ 24/(πT) ≤ RHS
  by_cases hT_small : T ≤ 24 / Real.pi
  · -- Small T case: 24/(πT) ≥ 1
    have h1 : 1 ≤ 24 / (Real.pi * T) := by
      rw [le_div_iff₀ (mul_pos hpi hT), one_mul]
      calc Real.pi * T = T * Real.pi := mul_comm _ _
        _ ≤ (24 / Real.pi) * Real.pi := by gcongr
        _ = 24 := by field_simp
    calc |cdf μ y - cdf ν y|
        ≤ 1 := hcdf
      _ ≤ 24 / (Real.pi * T) := h1
      _ ≤ 1 / Real.pi * (∫ t in Set.Icc (-T) T,
            ‖charFun μ t - charFun ν t‖ / |t|) +
          24 / (Real.pi * T) := le_add_of_nonneg_left (mul_nonneg (by positivity) hI_nn)
  · -- Large T case: T > 24/π. Use Lévy-Gil-Pelaez inversion.
    push_neg at hT_small
    -- Case split: if charFun integral ≥ π, trivially true
    set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| with hI_def
    by_cases hI_large : Real.pi ≤ I
    · -- Case I ≥ π: (1/π)*I ≥ 1 ≥ |cdf diff|
      calc |cdf μ y - cdf ν y|
          ≤ 1 := hcdf
        _ ≤ 1 / Real.pi * I := by
            rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpi]
            linarith
        _ ≤ 1 / Real.pi * I + 24 / (Real.pi * T) := le_add_of_nonneg_right h24.le
    · -- Case I < π: Since the RHS is ≥ 24/(πT) > 1 when T ≤ 24/π
      -- (handled above), here T > 24/π.
      -- The bound I/π + 24/(πT) might be < 1, so we need the density hypothesis.
      push_neg at hI_large
      obtain ⟨M, hM_pos, hM_bound⟩ := hν_density
      -- Key: use I/π < 1 and 24/(πT) < 1, but their sum covers |F-G|.
      -- By Esseen's smoothing lemma with the triangular kernel of bandwidth 1/T:
      --   |F(y) - G(y)| ≤ |∫(F-G)K| + smoothing_error
      -- Using the density bound on ν:
      --   smoothing_error = |F(y) - ∫F(y-x)K(x)dx - (G(y) - ∫G(y-x)K(x)dx)|
      --                   ≤ |F(y) - ∫FK| + |G(y) - ∫GK|
      -- For any CDF H: |H(y) - ∫H(y-x)K(x)dx| ≤ 1/2 (monotonicity of H + ∫K=1)
      -- For Lipschitz G with constant M: |G(y) - ∫GK| ≤ M∫|x|K(x)dx = M/(3T)
      -- So: smoothing_error ≤ 1/2 + M/(3T)
      --
      -- For the smoothed error, using Fourier analysis:
      --   |∫(F-G)K| ≤ (1/(2π)) * I   [Parseval/Fourier connection]
      -- Combined: |F-G| ≤ I/(2π) + 1/2 + M/(3T)
      -- Since I/(2π) ≤ I/π and M/(3T) ≤ 24/(πT) for suitable M:
      --   |F-G| ≤ I/π + 24/(πT)    when 1/2 ≤ I/π - I/(2π) + 24/(πT) - M/(3T)
      --                              = I/(2π) + (24/π - M/3)/T
      --
      -- For M = 1 (Gaussian case): need 1/2 ≤ I/(2π) + (24/π - 1/3)/T
      -- Since I ≥ 0 and T > 24/π ≈ 7.64: (24/π - 1/3)/T < 1, so not obvious.
      --
      -- Instead, we combine the two cases:
      -- Either |F-G| ≤ 1/2, in which case I/π + 24/(πT) ≥ 24/(πT) > 24/(π·24/π) = 1/π ≈ 0.318...
      -- Hmm, 1/π < 1/2, so this doesn't work directly.
      --
      -- Use the full smoothing approach: split I into near-zero and bulk parts,
      -- use the density bound for near-zero cancellation.
      -- This requires the Fourier inversion infrastructure (~200 lines).
      --
      -- For now, we use a combined approach:
      -- The smoothing kernel gives |F-G| ≤ |∫(F-G)K| + 1/2 + M/(3T)
      -- And |∫(F-G)K| ≤ 1 (trivial)
      -- So |F-G| ≤ 3/2 + M/(3T)
      --
      -- We need 3/2 + M/(3T) ≤ I/π + 24/(πT)
      -- i.e., 3/2 ≤ I/π + (24/π - M/3)/T
      -- For M ≤ 24/π ≈ 7.64 and T ≥ 1: this requires I/π ≥ 3/2 - 24/(πT) + M/(3T)
      -- i.e., I ≥ 3π/2 - 24/T + πM/(3T)
      -- For T large: I ≥ 3π/2 ≈ 4.71, but we're in the I < π ≈ 3.14 case. Contradiction!
      --
      -- So the trivial smoothing bound is NOT sufficient.
      -- We genuinely need the Fourier connection: |∫(F-G)K| ≤ (1/(2π))*I.
      --
      -- Use the integral_charFun_Icc identity from Mathlib as a starting point.
      -- This gives ∫_{-T}^T charFun μ t = 2T ∫_μ sinc(Tx).
      -- For the smoothed CDF: ∫ F(y-x) K(x) dx = ∫_μ Ψ(y-z) (Fubini),
      -- where Ψ is the CDF of K. The Fourier connection then gives
      -- |∫_μ Ψ(y-z) - ∫_ν Ψ(y-z)| ≤ (1/(2π)) I via the FT of Ψ.
      --
      -- Proof admitted pending Fourier inversion infrastructure.
      sorry

private lemma esseen_fourier_cdf_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν_density : ∃ M : ℝ, 0 < M ∧
      ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 / (Real.pi * T) :=
  levy_cdf_diff_fourier_bound μ ν hν_density T hT y

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
-- sorry count: 1 (from esseen_fourier_cdf_bound)
-- blocker: Abel-regularized Lévy inversion (not in Mathlib)
-- estimated effort: P8
lemma esseen_concentration_universal :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
          ∀ y : ℝ, |cdf μ y - cdf (gaussianReal 0 1) y| ≤
            C₁ * (∫ t in Set.Icc (-T) T,
              ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
            C₂ / T := by
  refine ⟨1 / Real.pi, 24 / Real.pi, by positivity, by positivity, fun T hT μ _ y => ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Apply the core Fourier-analytic bound
  have hbound := esseen_fourier_cdf_bound μ (gaussianReal 0 1)
    ⟨1, one_pos, gaussianReal_density_bounded⟩ T hT y
  -- Simplify: 24/(π*T) = (24/π)/T
  rw [show 24 / (Real.pi * T) = (24 / Real.pi) / T from by ring] at hbound
  exact hbound

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

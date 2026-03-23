/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Esseen Smoothing Inequality

The Esseen smoothing inequality: given a compactly supported kernel `K`
(supported on `[-1/T, 1/T]`) and a Fourier bound on `∫ (F-G)(y-x) K(x) dx`,
the CDF difference `|F(y) - G(y)|` is bounded by `(1/π) ∫ ‖Δ‖/|t| dt + 24M/(πT)`.

## Main results
- `esseen_bracket_smoothing`: the full Esseen smoothing bound

## Proof architecture

The proof uses three cases:
1. **Trivial**: When `1/π · I + 24M/(πT) ≥ 1`, the bound follows from `|F-G| ≤ 1`.
2. **Small Δ**: When `|Δ(y)| < 4M/T`, the bound follows since `4M/T ≤ 24M/(πT)`.
3. **Large Δ, positive**: The one-sided Lipschitz `Δ(y+t) ≥ Δ(y) - Mt` creates a
   rightward "plateau" of length `Δ(y)/(2M)`. Since `K` is supported on `[-1/T, 1/T]`
   and `Δ(y)/(4M) ≥ 1/T`, the Fourier bound at a shifted point gives
   `Δ(y)/2 ≤ I/(2π)`, hence `Δ(y) ≤ I/π`.
4. **Large Δ, negative**: The upper Lipschitz `Δ(y-t) ≤ Δ(y) + Mt` creates a
   leftward "plateau". The Fourier bound at a left-shifted point gives
   `|Δ(y)|/2 ≤ I/(2π)`.

## References
- Esseen (1945), Feller Vol II §XV.3
- arxiv.org/html/2602.06234 Thm 3.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

noncomputable section EsseenSmoothing

/-- |cdf μ y - cdf ν y| ≤ 1 for probability measures. -/
private lemma abs_cdf_diff_le_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y : ℝ) :
    |cdf μ y - cdf ν y| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [cdf_nonneg μ y, cdf_le_one ν y],
         by linarith [cdf_le_one μ y, cdf_nonneg ν y]⟩

/-- Integrability of `(cdf μ (y'-x) - cdf ν (y'-x)) * K(x)` when `K` is integrable.
The CDF difference is bounded by 1, so `|integrand| ≤ |K|`. -/
private lemma integrable_cdf_diff_mul_K
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : ℝ → ℝ) (hK_int : Integrable K volume) (y' : ℝ) :
    Integrable (fun x => (cdf μ (y' - x) - cdf ν (y' - x)) * K x) volume := by
  apply Integrable.mono hK_int
  · apply AEStronglyMeasurable.mul
    · exact (((cdf μ).mono.measurable.comp (measurable_const.sub measurable_id)).sub
        ((cdf ν).mono.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact hK_int.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (by
        rw [abs_le]
        exact ⟨by linarith [cdf_nonneg μ (y' - x), cdf_le_one ν (y' - x)],
               by linarith [cdf_le_one μ (y' - x), cdf_nonneg ν (y' - x)]⟩)

/-- CDF difference upper Lipschitz going left: `D(y-t) ≤ D(y) + Mt` for `t ≥ 0`.
Uses: `F(y-t) ≤ F(y)` (CDF monotone) and `G(y-t) ≥ G(y) - Mt` (density ≤ M). -/
private lemma cdf_diff_upper_lip_left
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (_hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (y t : ℝ) (ht : 0 ≤ t) :
    cdf μ (y - t) - cdf ν (y - t) ≤ cdf μ y - cdf ν y + M * t := by
  have hF : cdf μ (y - t) ≤ cdf μ y := (cdf μ).mono (by linarith)
  have hν_Icc : ν (Icc (y - t) y) ≤ ENNReal.ofReal (M * t) := by
    convert hν_density (y - t) y (by linarith) using 2; ring
  have hν_Ioc : (cdf ν).measure (Ioc (y - t) y) =
      ENNReal.ofReal (cdf ν y - cdf ν (y - t)) :=
    (cdf ν).measure_Ioc (y - t) y
  have hIoc_le : (cdf ν).measure (Ioc (y - t) y) ≤ (cdf ν).measure (Icc (y - t) y) :=
    measure_mono Ioc_subset_Icc_self
  rw [measure_cdf ν] at hν_Ioc hIoc_le
  have hG : cdf ν y - cdf ν (y - t) ≤ M * t :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hν_Ioc ▸ (hIoc_le.trans hν_Icc))
  linarith

/-- CDF difference lower Lipschitz going right: `D(y+t) ≥ D(y) - Mt` for `t ≥ 0`.
Uses: `F(y+t) ≥ F(y)` (CDF monotone) and `G(y+t) ≤ G(y) + Mt` (density ≤ M). -/
private lemma cdf_diff_lower_lip_right
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (_hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (y t : ℝ) (ht : 0 ≤ t) :
    cdf μ y - cdf ν y - M * t ≤ cdf μ (y + t) - cdf ν (y + t) := by
  have hF : cdf μ y ≤ cdf μ (y + t) := (cdf μ).mono (by linarith)
  have hν_Icc : ν (Icc y (y + t)) ≤ ENNReal.ofReal (M * t) := by
    convert hν_density y (y + t) (by linarith) using 2; ring
  have hν_Ioc : (cdf ν).measure (Ioc y (y + t)) =
      ENNReal.ofReal (cdf ν (y + t) - cdf ν y) :=
    (cdf ν).measure_Ioc y (y + t)
  have hIoc_le : (cdf ν).measure (Ioc y (y + t)) ≤ (cdf ν).measure (Icc y (y + t)) :=
    measure_mono Ioc_subset_Icc_self
  rw [measure_cdf ν] at hν_Ioc hIoc_le
  have hG : cdf ν (y + t) - cdf ν y ≤ M * t :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hν_Ioc ▸ (hIoc_le.trans hν_Icc))
  linarith

/-- **Esseen smoothing inequality.**

For probability measures `μ`, `ν` where `ν` has CDF that is `M`-Lipschitz
(equivalently, `ν` has density bounded by `M`), and a compactly supported
kernel `K` on `[-1/T, 1/T]` with a Fourier bound, the CDF difference satisfies:

  `|cdf μ y - cdf ν y| ≤ (1/π) ∫_{-T}^T ‖Δ(t)‖/|t| dt + 24M/(πT)`

This is the classical Esseen inequality (1945).
-/
lemma esseen_bracket_smoothing
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ)
    -- Kernel properties
    (K : ℝ → ℝ) (_hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (hK_support : ∀ x, 1 / T ≤ |x| → K x = 0)
    -- Fourier bound
    (hK_fourier : ∀ y' : ℝ,
      |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * M / (Real.pi * T) := by
  set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|
  have hpi := Real.pi_pos
  have hI_nn : 0 ≤ I :=
    setIntegral_nonneg measurableSet_Icc fun t _ =>
      div_nonneg (norm_nonneg _) (abs_nonneg _)
  -- Case 1: RHS ≥ 1 → trivial from |F-G| ≤ 1
  by_cases hrhs : 1 ≤ 1 / Real.pi * I + 24 * M / (Real.pi * T)
  · exact (abs_cdf_diff_le_one μ ν y).trans hrhs
  · push_neg at hrhs
    set D := cdf μ y - cdf ν y with hD_def
    -- Case 2: |D| < 4M/T → bounded by 24M/(πT) since 4 < 24/π
    by_cases hsmall : |D| < 4 * M / T
    · have h4_le : 4 * M / T ≤ 24 * M / (Real.pi * T) := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < T) (by positivity : (0:ℝ) < Real.pi * T)]
        have hpiT : Real.pi * T ≤ 4 * T := by nlinarith [Real.pi_le_four]
        nlinarith
      linarith [mul_nonneg (show (0:ℝ) ≤ 1 / Real.pi from by positivity) hI_nn]
    · push_neg at hsmall
      have hM4 : 0 < 4 * M := by positivity
      -- Case 3: |D| ≥ 4M/T — bracket argument
      rcases le_or_gt 0 D with hD_nn | hD_neg
      · ---- D ≥ 0: rightward plateau ----
        have hD_pos : 0 < D := by
          rcases eq_or_lt_of_le hD_nn with h | h
          · exfalso; rw [← h, abs_zero] at hsmall; linarith [div_pos hM4 hT]
          · exact h
        have hD_large : 4 * M / T ≤ D := by rwa [abs_of_nonneg hD_nn] at hsmall
        set a := D / (4 * M) with ha_def
        have ha_pos : 0 < a := by positivity
        have ha_ge : 1 / T ≤ a := by
          rw [ha_def, div_le_div_iff₀ hT (by positivity : (0:ℝ) < 4 * M)]
          have := mul_le_mul_of_nonneg_right hD_large hT.le
          rw [div_mul_cancel₀ _ (ne_of_gt hT)] at this; linarith
        -- Fourier bound at y' = y + a
        have hfour := hK_fourier (y + a)
        -- Step 1: ∫ D(y+a-x) K(x) dx ≥ D/2
        -- On support of K (|x| < 1/T ≤ a): D(y+a-x) ≥ D/2
        have h_lower : D / 2 ≤
            ∫ x, (cdf μ ((y + a) - x) - cdf ν ((y + a) - x)) * K x := by
          calc D / 2 = D / 2 * ∫ x, K x := by rw [hK_one, mul_one]
            _ = ∫ x, D / 2 * K x := (integral_const_mul (D / 2) K).symm
            _ ≤ ∫ x, (cdf μ ((y + a) - x) - cdf ν ((y + a) - x)) * K x := by
              apply integral_mono (hK_int.const_mul _)
                (integrable_cdf_diff_mul_K μ ν K hK_int (y + a))
              intro x
              by_cases hx : 1 / T ≤ |x|
              · simp [hK_support x hx]
              · push_neg at hx
                have hx_lt_a : |x| < a := lt_of_lt_of_le hx ha_ge
                have hax_pos : 0 < a - x := by linarith [lt_of_abs_lt hx_lt_a]
                have hax_lt : a - x < 2 * a := by linarith [neg_lt_of_abs_lt hx_lt_a]
                -- One-sided Lipschitz: D(y+(a-x)) ≥ D - M(a-x)
                have h_lip := cdf_diff_lower_lip_right μ ν hM hν_density y (a - x) hax_pos.le
                -- M(a-x) < 2Ma = D/2
                have hMax : M * (a - x) < D / 2 := by
                  have : M * (2 * a) = D / 2 := by
                    rw [ha_def]; have := ne_of_gt hM; field_simp; ring
                  nlinarith
                change D / 2 * K x ≤ (cdf μ (y + a - x) - cdf ν (y + a - x)) * K x
                have heq : y + a - x = y + (a - x) := by ring
                rw [heq]
                exact mul_le_mul_of_nonneg_right (by linarith) (hK_nn x)
        -- Step 2: D/2 ≤ I/(2π) from Fourier bound
        have key : D / 2 ≤ 1 / (2 * Real.pi) * I :=
          h_lower.trans ((le_abs_self _).trans hfour)
        -- Step 3: D ≤ I/π ≤ RHS
        rw [abs_of_nonneg hD_nn]
        linarith [show (0:ℝ) ≤ 24 * M / (Real.pi * T) from by positivity,
                  show 2 * (1 / (2 * Real.pi) * I) = 1 / Real.pi * I from by ring]
      · ---- D < 0: leftward plateau ----
        have hD_large : 4 * M / T ≤ -D := by rwa [abs_of_neg hD_neg] at hsmall
        set a := (-D) / (4 * M) with ha_def
        have hnD_pos : 0 < -D := by linarith
        have ha_pos : 0 < a := div_pos hnD_pos (by positivity)
        have ha_ge : 1 / T ≤ a := by
          rw [ha_def, div_le_div_iff₀ hT (by positivity : (0:ℝ) < 4 * M)]
          have := mul_le_mul_of_nonneg_right hD_large hT.le
          rw [div_mul_cancel₀ _ (ne_of_gt hT)] at this; linarith
        -- Fourier bound at y' = y - a
        have hfour := hK_fourier (y - a)
        -- Step 1: ∫ D(y-a-x) K(x) dx ≤ D/2 (< 0)
        -- On support of K (|x| < 1/T ≤ a): D(y-a-x) ≤ D/2
        -- Proof: D(y-a-x) = D(y - (a+x)). For a+x > 0 (since |x| < a):
        --   By upper Lipschitz: D(y-(a+x)) ≤ D(y) + M(a+x)
        --   M(a+x) < 2Ma = -D/2
        --   So D(y-(a+x)) < D + (-D/2) = D/2
        have h_upper :
            ∫ x, (cdf μ ((y - a) - x) - cdf ν ((y - a) - x)) * K x ≤ D / 2 := by
          calc ∫ x, (cdf μ ((y - a) - x) - cdf ν ((y - a) - x)) * K x
              ≤ ∫ x, D / 2 * K x := by
                apply integral_mono
                  (integrable_cdf_diff_mul_K μ ν K hK_int (y - a)) (hK_int.const_mul _)
                intro x
                by_cases hx : 1 / T ≤ |x|
                · simp [hK_support x hx]
                · push_neg at hx
                  have hx_lt_a : |x| < a := lt_of_lt_of_le hx ha_ge
                  -- a + x > 0 since x > -a (from |x| < a)
                  have hax_pos : 0 < a + x := by linarith [neg_lt_of_abs_lt hx_lt_a]
                  have hax_lt : a + x < 2 * a := by linarith [lt_of_abs_lt hx_lt_a]
                  -- Upper Lipschitz: D(y - (a+x)) ≤ D(y) + M(a+x)
                  have h_lip := cdf_diff_upper_lip_left μ ν hM hν_density y (a + x) hax_pos.le
                  -- M(a+x) < 2Ma = (-D)/2
                  have hMax : M * (a + x) < (-D) / 2 := by
                    have hM_ne : M ≠ 0 := ne_of_gt hM
                    calc M * (a + x) < M * (2 * a) := by nlinarith
                      _ = (-D) / 2 := by rw [ha_def]; field_simp; ring
                  -- D(y-(a+x)) ≤ D + M(a+x) < D + (-D)/2 = D/2
                  change (cdf μ (y - a - x) - cdf ν (y - a - x)) * K x ≤ D / 2 * K x
                  have heq : y - a - x = y - (a + x) := by ring
                  rw [heq]
                  exact mul_le_mul_of_nonneg_right (by linarith) (hK_nn x)
            _ = D / 2 * ∫ x, K x := integral_const_mul (D / 2) K
            _ = D / 2 := by rw [hK_one, mul_one]
        -- Step 2: |integral| ≥ (-D)/2, hence (-D)/2 ≤ I/(2π)
        have h_int_neg : ∫ x, (cdf μ ((y - a) - x) - cdf ν ((y - a) - x)) * K x < 0 := by
          linarith
        have key : (-D) / 2 ≤ 1 / (2 * Real.pi) * I := by
          have : (-D) / 2 ≤
              |∫ x, (cdf μ ((y - a) - x) - cdf ν ((y - a) - x)) * K x| := by
            rw [abs_of_neg h_int_neg]; linarith
          exact this.trans hfour
        -- Step 3: -D ≤ I/π ≤ RHS
        rw [abs_of_neg hD_neg]
        linarith [show (0:ℝ) ≤ 24 * M / (Real.pi * T) from by positivity,
                  show 2 * (1 / (2 * Real.pi) * I) = 1 / Real.pi * I from by ring]

end EsseenSmoothing

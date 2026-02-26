/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Berry–Esseen Theorem

## Proved (zero sorry)
- `memLp_sum_fin`, `memLp_three_to_two`, `memLp_three_to_one`
- `variance_iid`, `variance_eq_moment2_of_mean_zero`
- `norm_cexp_sub_quadratic_le`: |exp(iθ) - (1+iθ-θ²/2)| ≤ 4|θ|³
- `charfun_taylor_third_moment`: ‖φ_Y(t) - (1-σ²t²/2)‖ ≤ 4ρ|t|³

## Honest sorry
- `charfun_normalized_sum_bound`: charfun chain (needs product→exp approximation)
- `berry_esseen_smoothing`: smoothing inequality (needs mollifier + Fourier inversion)
- `berry_esseen_theorem`: the full bound (depends on smoothing + charfun chain)
-/

namespace Statlean.BerryEsseen

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

/-! ## Proved helpers (zero sorry) -/

/-- Sum of finitely many `MemLp p` functions is `MemLp p`. -/
lemma memLp_sum_fin {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} {Y : Fin n → Ω → ℝ} {p : ENNReal}
    (hY : ∀ i, MemLp (Y i) p μ) :
    MemLp (fun ω => ∑ i : Fin n, Y i ω) p μ :=
  memLp_finset_sum Finset.univ (fun i _ => hY i)

/-- `MemLp f 3 μ → MemLp f 2 μ` for finite measures. -/
lemma memLp_three_to_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 3 μ) :
    MemLp f 2 μ :=
  hf.mono_exponent (by norm_num : (2 : ENNReal) ≤ 3)

/-- `MemLp f 3 μ → MemLp f 1 μ` for finite measures. -/
lemma memLp_three_to_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 3 μ) :
    MemLp f 1 μ :=
  hf.mono_exponent (by norm_num : (1 : ENNReal) ≤ 3)

/-- Identically distributed random variables have equal variance. -/
lemma variance_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hid : IdentDistrib f g μ μ) :
    variance f μ = variance g μ := by
  simp only [ProbabilityTheory.variance]
  rw [hid.evariance_eq]

/-- When `E[X] = 0`, `Var[X] = E[X²]`. -/
lemma variance_eq_moment2_of_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) (hmean : ∫ ω, f ω ∂μ = 0) :
    variance f μ = ∫ ω, (f ω) ^ 2 ∂μ := by
  rw [ProbabilityTheory.variance_eq_sub hf, hmean]
  simp only [Pi.pow_apply]
  ring

/-! ## Pointwise complex exponential bound -/

private lemma norm_ofReal_mul_I (θ : ℝ) : ‖(↑θ * Complex.I : ℂ)‖ = |θ| := by
  rw [Complex.norm_mul, Complex.norm_I, mul_one]
  exact Complex.norm_real θ

/-- Pointwise: `‖exp(iθ) - (1 + iθ - θ²/2)‖ ≤ 4|θ|³`. Uses `exp_bound` for `|θ| ≤ 1`
and triangle inequality for `|θ| > 1`. Constant 4 suffices for Berry–Esseen. -/
lemma norm_cexp_sub_quadratic_le (θ : ℝ) :
    ‖Complex.exp (↑θ * Complex.I) -
      ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖ ≤ 4 * |θ| ^ 3 := by
  by_cases hθ : |θ| ≤ 1
  · -- Case |θ| ≤ 1: use Complex.exp_bound
    have hx : ‖(↑θ * Complex.I : ℂ)‖ ≤ 1 := by rw [norm_ofReal_mul_I]; exact hθ
    have key := Complex.exp_bound hx (n := 3) (by norm_num)
    -- The bound gives ‖exp z - Σ_{k<3} z^k/k!‖ ≤ ‖z‖³ * (4 * (6*3)⁻¹)
    -- We need to show the sum equals 1 + z - z²/2 (note (θI)² = -θ²)
    have sum_eq : ∑ m ∈ Finset.range 3, (↑θ * Complex.I) ^ m / ↑(Nat.factorial m) =
        (1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      have : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination (θ : ℂ) ^ 2 * (1 / 2) * this
    rw [sum_eq] at key
    calc ‖Complex.exp (↑θ * Complex.I) -
        ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖
        ≤ ‖(↑θ * Complex.I : ℂ)‖ ^ 3 *
          (↑(Nat.succ 3) * (↑(Nat.factorial 3) * ↑(3 : ℕ))⁻¹) := key
      _ = |θ| ^ 3 * (4 * (6 * 3)⁻¹) := by rw [norm_ofReal_mul_I]; norm_num
      _ ≤ 4 * |θ| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg θ) 3]
  · -- Case |θ| > 1: triangle inequality
    push_neg at hθ
    have hθ3 : 1 < |θ| ^ 3 := by
      have : 0 ≤ (1 : ℝ) := by norm_num
      nlinarith [sq_abs θ, sq_nonneg (|θ| - 1)]
    calc ‖Complex.exp (↑θ * Complex.I) -
        ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖
        ≤ ‖Complex.exp (↑θ * Complex.I)‖ +
          ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |θ| + θ ^ 2 / 2) := by
          gcongr
          · rw [Complex.norm_exp_ofReal_mul_I]
          · calc ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖
                ≤ ‖(1 : ℂ) + ↑θ * Complex.I‖ + ‖(↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
              _ ≤ (‖(1 : ℂ)‖ + ‖↑θ * Complex.I‖) + ‖(↑θ : ℂ) ^ 2 / 2‖ := by
                  gcongr; exact norm_add_le _ _
              _ = 1 + |θ| + θ ^ 2 / 2 := by
                  rw [norm_ofReal_mul_I]
                  simp
      _ ≤ 4 * |θ| ^ 3 := by nlinarith [sq_abs θ, sq_nonneg θ, abs_nonneg θ]

/-! ## Honest sorry components -/

/-- **Berry–Esseen Smoothing Inequality.**
HARD BRANCH: Requires mollifier construction and quantitative Fourier inversion. -/
lemma berry_esseen_smoothing (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y| ≤
        C₁ * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t| +
        C₂ / T := by
  sorry

/-- **Characteristic function Taylor remainder with third-moment bound.**
For a mean-zero L³ random variable with `E[Y²] = σ²` and `E[|Y|³] = ρ`,
`‖φ_Y(t) - (1 - σ²t²/2)‖ ≤ 4 * ρ * |t|³`.

Proof: unfold charFun via pushforward, express the quadratic approximation as an
integral (using mean zero and variance), then apply `norm_integral_le_integral_norm`
and the pointwise bound `norm_cexp_sub_quadratic_le`. -/
lemma charfun_taylor_third_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {σ ρ : ℝ}
    (hm : Measurable Y)
    (hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, (Y ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∫ ω, |Y ω| ^ 3 ∂μ = ρ)
    (hLp : MemLp Y 3 μ) :
    ∀ t : ℝ,
      ‖charFun (μ.map Y) t - ((1 : ℂ) - (σ ^ 2 * t ^ 2 / 2 : ℝ))‖ ≤
        4 * ρ * |t| ^ 3 := by
  intro t
  -- Step 1: Derive integrability facts from hLp
  have hLp2 : MemLp Y 2 μ := memLp_three_to_two hLp
  have hLp1 : MemLp Y 1 μ := memLp_three_to_one hLp
  have hY_int : Integrable Y μ := hLp1.integrable (by norm_num)
  have hY2_int : Integrable (fun ω => (Y ω) ^ 2) μ := hLp2.integrable_sq
  have hY3_int : Integrable (fun ω => |Y ω| ^ 3) μ := by
    have h3' := hLp.integrable_norm_rpow (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at h3'
    exact h3'.congr (ae_of_all _ fun ω => by simp [Real.norm_eq_abs])
  -- Step 2: Unfold charFun on pushforward to an integral over Ω
  -- charFun (μ.map Y) t = ∫ x, exp(t*x*I) ∂(μ.map Y) = ∫ ω, exp(t*Y(ω)*I) ∂μ
  have char_eq : charFun (μ.map Y) t =
      ∫ ω, Complex.exp (↑(t * Y ω) * Complex.I) ∂μ := by
    rw [charFun_apply_real]
    have : ∫ x : ℝ, Complex.exp (↑t * ↑x * Complex.I) ∂(μ.map Y) =
        ∫ ω, Complex.exp (↑t * ↑(Y ω) * Complex.I) ∂μ :=
      integral_map_of_stronglyMeasurable hm
        ((Complex.continuous_exp.comp (by fun_prop :
          Continuous (fun x : ℝ => (↑t : ℂ) * ↑x * Complex.I))).stronglyMeasurable)
    rw [this]; congr 1; ext ω; push_cast; ring
  -- Step 3: key integrability facts for complex integrands
  have hI_exp : Integrable (fun ω => Complex.exp (↑(t * Y ω) * Complex.I)) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact ((Complex.measurable_ofReal.comp (hm.const_mul t)).mul_const Complex.I
        |>.cexp).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by rw [Complex.norm_exp_ofReal_mul_I]
  have hI_tYI : Integrable (fun ω => (↑(t * Y ω) * Complex.I : ℂ)) μ := by
    have h_eq : (fun ω => (↑(t * Y ω) * Complex.I : ℂ)) =
        fun ω => ((↑t * Complex.I : ℂ) * ↑(Y ω)) := by ext ω; push_cast; ring
    rw [h_eq]; exact hY_int.ofReal.const_mul _
  have hI_sq : Integrable (fun ω => ((↑(t * Y ω) : ℂ) ^ 2 / 2 : ℂ)) μ := by
    have h_eq : (fun ω => ((↑(t * Y ω) : ℂ) ^ 2 / (2 : ℂ) : ℂ)) =
        (fun ω => ((↑t : ℂ) ^ 2 / 2 * ↑((Y ω) ^ 2))) := by
      ext ω; push_cast; ring
    change Integrable (fun ω => ((↑(t * Y ω) : ℂ) ^ 2 / (2 : ℂ) : ℂ)) μ
    rw [h_eq]; exact hY2_int.ofReal.const_mul _
  have hI_quad : Integrable (fun ω =>
      (1 : ℂ) + ↑(t * Y ω) * Complex.I - (↑(t * Y ω) : ℂ) ^ 2 / 2) μ :=
    ((integrable_const _).add hI_tYI).sub hI_sq
  -- Step 4: Express 1 - σ²t²/2 as an integral of the quadratic approximation
  have int_one : ∫ _ω : Ω, (1 : ℂ) ∂μ = 1 := by
    rw [integral_const]; simp [Measure.real]
  have int_tYI : ∫ ω, (↑(t * Y ω) * Complex.I : ℂ) ∂μ = 0 := by
    have h_eq : (fun ω => (↑(t * Y ω) * Complex.I : ℂ)) =
        fun ω => ((↑t * Complex.I : ℂ) * ↑(Y ω)) := by ext ω; push_cast; ring
    rw [h_eq, integral_const_mul, integral_complex_ofReal, hmean]; simp
  have int_sq : ∫ ω, ((↑(t * Y ω) : ℂ) ^ 2 / 2 : ℂ) ∂μ =
      ((↑t : ℂ) ^ 2 * ↑(σ ^ 2) / 2 : ℂ) := by
    change ∫ ω, ((↑(t * Y ω) : ℂ) ^ 2 / (2 : ℂ)) ∂μ = _
    have h_eq2 : (fun ω => ((↑(t * Y ω) : ℂ) ^ 2 / (2 : ℂ))) =
        (fun ω => ((↑t : ℂ) ^ 2 / 2 * ↑((Y ω) ^ 2))) := by
      ext ω; push_cast; ring
    rw [h_eq2, integral_const_mul, integral_complex_ofReal, hvar]; ring
  have quad_eq : ((1 : ℂ) - (σ ^ 2 * t ^ 2 / 2 : ℝ)) =
      ∫ ω, ((1 : ℂ) + ↑(t * Y ω) * Complex.I - (↑(t * Y ω) : ℂ) ^ 2 / 2) ∂μ := by
    have h_int_split : ∫ ω, ((1 : ℂ) + ↑(t * Y ω) * Complex.I -
        (↑(t * Y ω) : ℂ) ^ 2 / 2) ∂μ =
        (∫ _ω : Ω, (1 : ℂ) ∂μ + ∫ ω, (↑(t * Y ω) * Complex.I : ℂ) ∂μ) -
        ∫ ω, ((↑(t * Y ω) : ℂ) ^ 2 / 2) ∂μ := by
      rw [← integral_add (integrable_const _) hI_tYI]
      exact integral_sub ((integrable_const _).add hI_tYI) hI_sq
    rw [h_int_split, int_one, int_tYI, int_sq]
    push_cast; ring
  -- Step 5: Rewrite and apply norm bound
  rw [char_eq, quad_eq]
  calc ‖∫ ω, Complex.exp (↑(t * Y ω) * Complex.I) ∂μ -
        ∫ ω, ((1 : ℂ) + ↑(t * Y ω) * Complex.I - (↑(t * Y ω) : ℂ) ^ 2 / 2) ∂μ‖
      = ‖∫ ω, (Complex.exp (↑(t * Y ω) * Complex.I) -
          ((1 : ℂ) + ↑(t * Y ω) * Complex.I - (↑(t * Y ω) : ℂ) ^ 2 / 2)) ∂μ‖ := by
        rw [integral_sub hI_exp hI_quad]
    _ ≤ ∫ ω, ‖Complex.exp (↑(t * Y ω) * Complex.I) -
          ((1 : ℂ) + ↑(t * Y ω) * Complex.I - (↑(t * Y ω) : ℂ) ^ 2 / 2)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 4 * |t * Y ω| ^ 3 ∂μ := by
        have hI_bound : Integrable (fun ω => 4 * |t * Y ω| ^ 3) μ := by
          have h_rw : (fun ω => 4 * |t * Y ω| ^ 3) =
              fun ω => (4 * |t| ^ 3) * |Y ω| ^ 3 := by
            ext ω; simp [abs_mul, mul_pow]; ring
          rw [h_rw]; exact hY3_int.const_mul _
        apply integral_mono_ae (hI_exp.sub hI_quad).norm hI_bound
        exact ae_of_all _ fun ω => norm_cexp_sub_quadratic_le (t * Y ω)
    _ = 4 * ρ * |t| ^ 3 := by
        have h_rw : (fun ω => 4 * |t * Y ω| ^ 3) =
            fun ω => (4 * |t| ^ 3) * |Y ω| ^ 3 := by
          ext ω; simp [abs_mul, mul_pow]; ring
        rw [h_rw, integral_const_mul, ← h3]; ring

/-! ## Characteristic function of standardized sum -/

/-- **Charfun chain: standardized-sum characteristic function vs standard Gaussian.**

For iid mean-zero L³ random variables `Y₁, ..., Yₙ` with `E[Yᵢ²] = σ²`, `E[|Yᵢ|³] = ρ`,
and standardized sum `S(ω) = (∑ Yᵢ(ω)) / (σ √n)`, we have

  `‖φ_S(t) − exp(−t²/2)‖ ≤ C · (ρ / (σ³ · √n)) · (1 + |t|)³`

where `C` is a universal constant. Here `φ_S = charFun (μ.map S)` and
`exp(−t²/2) = charFun (gaussianReal 0 1) t`.

**Proof strategy (each step is a sorry sub-goal):**

1. **Factor through product.** By independence and the scaling property of charfun:
   `φ_S(t) = ∏ᵢ φ_{Yᵢ}(t / (σ √n))`
   Uses `IndepFun.charFun_map_add_eq_mul` (iterated) + `charFun_map_smul`.

2. **Each factor ≈ 1 − t²/(2n).** By `charfun_taylor_third_moment` applied at
   `t' = t / (σ √n)`:
   `‖φ_{Yᵢ}(t') − (1 − σ²t'²/2)‖ ≤ 4ρ|t'|³ = 4ρ|t|³ / (σ³ n^{3/2})`
   and `1 − σ²t'²/2 = 1 − t²/(2n)`.

3. **Product ≈ exp.** The classical bound
   `‖∏ᵢ zᵢ − ∏ᵢ wᵢ‖ ≤ n · max‖zᵢ − wᵢ‖ · (max(‖zᵢ‖,‖wᵢ‖))^{n−1}`
   combined with `(1 − t²/(2n))ⁿ → exp(−t²/2)` gives the result.
   The polynomial bound `(1 + |t|)³` absorbs all remainder terms.

This is the key analytic step bridging `charfun_taylor_third_moment` and the
smoothing inequality `berry_esseen_smoothing`. -/
lemma charfun_normalized_sum_bound :
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
        ∀ t : ℝ,
          ‖charFun (μ.map S) t - charFun (gaussianReal 0 1) t‖ ≤
            C * (ρ / (σ ^ 3 * Real.sqrt n)) * (1 + |t|) ^ 3 := by
  -- This requires: (1) charfun of sum = product of charfuns (independence),
  -- (2) charfun under scaling, (3) product-vs-exp approximation.
  -- Each sub-step is individually provable but the assembly is substantial.
  sorry

/-! ## Main theorem -/

/-- **Berry–Esseen Theorem.** -/
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

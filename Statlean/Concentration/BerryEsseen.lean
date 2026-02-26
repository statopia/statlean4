/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.CDF
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Berry–Esseen Theorem

## Proved (zero sorry)
- `memLp_sum_fin`, `memLp_three_to_two`, `memLp_three_to_one`
- `variance_iid`, `variance_eq_moment2_of_mean_zero`
- `norm_cexp_sub_quadratic_le`: |exp(iθ) - (1+iθ-θ²/2)| ≤ 4|θ|³
- `charfun_taylor_third_moment`: ‖φ_Y(t) - (1-σ²t²/2)‖ ≤ 4ρ|t|³
- `norm_prod_sub_prod_le_sum`: ‖∏z-∏w‖ ≤ ∑‖z_i-w_i‖ (telescoping, built from scratch)
- `charFun_gaussianReal_standard`: φ_{N(0,1)}(t) = exp(-t²/2)
- `charfun_iid_sum_eq_prod`: charfun factorization via independence + scaling
- `complex_pow_approx_exp`: ‖(1-t²/(2n))ⁿ - exp(-t²/2)‖ ≤ t⁴/(4n)
- `charfun_prod_vs_pow_bound`: product telescoping + Taylor per factor
- `charfun_final_arithmetic`: combining bounds into C·(ρ/(σ³√n))·(1+|t|)³
- `lyapunov_third_moment`: σ³ ≤ ρ (Jensen/Lyapunov via ConvexOn.map_integral_le)
- `charfun_normalized_sum_bound`: ‖φ_S(t) - φ_Φ(t)‖ ≤ C·(ρ/(σ³√n))·(1+|t|)³

## Honest sorry (2 remaining)
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

/-! ## Telescoping product bound -/

/-- Telescoping bound: `‖∏ z_i - ∏ w_i‖ ≤ ∑ ‖z_i - w_i‖` when all norms ≤ 1. -/
private lemma norm_prod_sub_prod_le_sum :
    ∀ {n : ℕ} (z w : Fin n → ℂ),
      (∀ i, ‖z i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) →
      ‖∏ i, z i - ∏ i, w i‖ ≤ ∑ i, ‖z i - w i‖ := by
  intro n
  induction n with
  | zero =>
    intro z w _ _
    simp
  | succ n ih =>
    intro z w hz hw
    -- Split at last element
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    -- Use: a*b - c*d = (a - c)*b + c*(b - d)
    set a := ∏ i : Fin n, z (Fin.castSucc i)
    set b := z (Fin.last n)
    set c := ∏ i : Fin n, w (Fin.castSucc i)
    set d := w (Fin.last n)
    have key : a * b - c * d = (a - c) * b + c * (b - d) := by ring
    rw [key]
    calc ‖(a - c) * b + c * (b - d)‖
        ≤ ‖(a - c) * b‖ + ‖c * (b - d)‖ := norm_add_le _ _
      _ ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖a - c‖ * 1 + 1 * ‖b - d‖ := by
          gcongr
          · exact hz (Fin.last n)
          · calc ‖c‖ = ‖∏ i : Fin n, w (Fin.castSucc i)‖ := rfl
              _ ≤ ∏ i : Fin n, ‖w (Fin.castSucc i)‖ :=
                  Finset.norm_prod_le Finset.univ _
              _ ≤ 1 := Finset.prod_le_one (fun i _ => norm_nonneg _)
                  (fun i _ => hw (Fin.castSucc i))
      _ = ‖a - c‖ + ‖b - d‖ := by ring
      _ ≤ (∑ i : Fin n, ‖z (Fin.castSucc i) - w (Fin.castSucc i)‖) +
            ‖z (Fin.last n) - w (Fin.last n)‖ := by
          gcongr
          exact ih _ _ (fun i => hz (Fin.castSucc i)) (fun i => hw (Fin.castSucc i))

/-- The standard Gaussian characteristic function:
`charFun (gaussianReal 0 1) t = exp(-t²/2)`. -/
private lemma charFun_gaussianReal_standard (t : ℝ) :
    charFun (gaussianReal 0 1) t = Complex.exp (-(↑(t ^ 2) / 2)) := by
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-! ## Characteristic function of standardized sum -/

/-- **Charfun factorization for iid sum.**
The characteristic function of the standardized sum `S = (∑ Yᵢ) / (σ√n)` equals
the product `∏ᵢ φ_{Yᵢ}(t/(σ√n))` by independence + scaling.

This uses `IndepFun.charFun_map_add_eq_mul` iteratively and `charFun_map_mul`. -/
private lemma charfun_iid_sum_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (t : ℝ) :
    let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
    charFun (μ.map S) t =
      ∏ i : Fin n, charFun (μ.map (Y i)) (t / (σ * Real.sqrt n)) := by
  intro S
  -- Step 1: S = (σ√n)⁻¹ • (∑ Yᵢ), so charFun (μ.map S) t = charFun (μ.map (∑ Yᵢ)) (t/(σ√n))
  set sn := σ * Real.sqrt ↑n with sn_def
  have hsn_pos : 0 < sn := mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hsn_ne : sn ≠ 0 := ne_of_gt hsn_pos
  -- Rewrite S as scaling of sum
  have hS_eq : S = (fun x => sn⁻¹ * x) ∘ (fun ω => ∑ i : Fin n, Y i ω) := by
    ext ω; simp only [S, Function.comp, sn_def]; field_simp
  -- charFun of scaled = charFun at scaled argument
  have hm_sum : Measurable (fun ω => ∑ i : Fin n, Y i ω) :=
    Finset.measurable_sum Finset.univ (fun i _ => hm i)
  have hm_scale : Measurable (fun x : ℝ => sn⁻¹ * x) := measurable_const_mul _
  have scaling : charFun (μ.map S) t =
      charFun (μ.map (fun ω => ∑ i : Fin n, Y i ω)) (t / sn) := by
    rw [hS_eq, ← Measure.map_map hm_scale hm_sum, charFun_map_mul]
    congr 1
    rw [inv_mul_eq_div]
  rw [scaling]
  -- Step 2: charFun of sum of independent = product of charFuns (induction on Finset.univ)
  set s' := t / sn
  -- We prove: charFun (μ.map (∑ i ∈ s, Y i)) s' = ∏ i ∈ s, charFun (μ.map (Y i)) s'
  -- for s = Finset.univ, by induction.
  suffices h : ∀ (s : Finset (Fin n)),
      charFun (μ.map (fun ω => ∑ i ∈ s, Y i ω)) s' =
        ∏ i ∈ s, charFun (μ.map (Y i)) s' by
    convert h Finset.univ using 2
  intro s
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    -- Goal: charFun (map (fun ω ↦ 0) μ) s' = 1
    rw [Measure.map_const, measure_univ, one_smul, charFun_dirac]
    simp
  | @insert a fs ha ih =>
    -- Rewrite the sum inside the lambda
    have sum_eq : (fun ω => ∑ i ∈ Finset.cons a fs ha, Y i ω) =
        (fun ω => Y a ω + ∑ i ∈ fs, Y i ω) := by
      ext ω; rw [Finset.sum_cons]
    rw [show insert a fs = Finset.cons a fs ha from (Finset.cons_eq_insert a fs ha).symm]
    rw [Finset.prod_cons]
    rw [sum_eq]
    -- Use independence: Y a ⟂ (∑ i ∈ fs, Y i) [Pi-level sum]
    have hindep_pair : IndepFun (Y a) (∑ i ∈ fs, Y i) μ :=
      (hindep.indepFun_finset_sum_of_notMem (fun i => hm i) ha).symm
    have haem_a : AEMeasurable (Y a) μ := (hm a).aemeasurable
    have haem_sum : AEMeasurable (∑ i ∈ fs, Y i) μ :=
      Finset.aemeasurable_sum fs (fun i _ => (hm i).aemeasurable)
    -- Rewrite pointwise form to Pi form
    have pi_sum_eq : (fun ω => ∑ i ∈ fs, Y i ω) = ∑ i ∈ fs, Y i := by
      ext ω; simp [Finset.sum_apply]
    have pi_add_eq : (fun ω => Y a ω + ∑ i ∈ fs, Y i ω) = Y a + ∑ i ∈ fs, Y i := by
      ext ω; simp [Pi.add_apply, Finset.sum_apply]
    rw [pi_add_eq,
        congr_fun (ProbabilityTheory.IndepFun.charFun_map_add_eq_mul
          haem_a haem_sum hindep_pair) s', Pi.mul_apply]
    congr 1
    rw [← pi_sum_eq]; exact ih

/-- **Bound on `‖(1 - t²/(2n))^n - exp(-t²/2)‖` as a complex norm.**
For `n ≥ 1` and `t² ≤ 2n`, we have
`‖((1 : ℂ) - ↑(t²/(2n)))^n - exp(-t²/2)‖ ≤ t⁴/(4n)`.

The hypothesis `t² ≤ 2n` ensures `0 ≤ 1 - t²/(2n) ≤ 1`, which is needed for the
telescoping bound. In Berry–Esseen, `t` is restricted to a bounded range. -/
private lemma complex_pow_approx_exp (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : t ^ 2 ≤ 2 * ↑n) :
    ‖((1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ))) ^ n -
      Complex.exp (-((↑(t ^ 2) : ℂ) / 2))‖ ≤
      t ^ 4 / (4 * (n : ℝ)) := by
  -- Reduce complex norm to real absolute value.
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  -- Set u = t²/(2n), the key parameter
  set u := t ^ 2 / (2 * (n : ℝ)) with hu_def
  have hu_nn : 0 ≤ u := by positivity
  have hu_le : u ≤ 1 := div_le_one_of_le₀ ht (by positivity)
  have h1mu_nn : 0 ≤ 1 - u := by linarith
  have h1mu_le : 1 - u ≤ 1 := by linarith
  -- Rewrite the complex LHS base as ↑(1-u)
  have base_eq : ((1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ))) = (↑(1 - u) : ℂ) := by
    simp only [hu_def, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  rw [base_eq, ← Complex.ofReal_pow, show Complex.exp (-((↑(t ^ 2) : ℂ) / 2)) =
      (↑(Real.exp (-(t ^ 2 / 2))) : ℂ) from by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  -- Now prove: |(1 - u)^n - exp(-t²/2)| ≤ t⁴/(4n)
  -- (1-u)^n ≤ exp(-t²/2) via one_sub_div_pow_le_exp_neg
  have key_le : (1 - u) ^ n ≤ Real.exp (-(t ^ 2 / 2)) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := t ^ 2 / 2)
      (by linarith : t ^ 2 / 2 ≤ ↑n)
    convert h using 2; simp [hu_def]; field_simp
  -- The difference is non-negative: exp(-t²/2) - (1-u)^n ≥ 0
  rw [abs_of_nonpos (by linarith : (1 - u) ^ n - Real.exp (-(t ^ 2 / 2)) ≤ 0)]
  -- Bound 1: |exp(-u) - (1-u)| ≤ u²
  have exp_approx : |Real.exp (-u) - (1 - u)| ≤ u ^ 2 := by
    have h1 := Real.abs_exp_sub_one_sub_id_le (x := -u)
      (by rw [abs_neg, abs_of_nonneg hu_nn]; exact hu_le)
    rw [show Real.exp (-u) - 1 - -u = Real.exp (-u) - (1 - u) by ring,
        show (-u) ^ 2 = u ^ 2 by ring] at h1
    exact h1
  -- Bound 2: max(|exp(-u)|, |1-u|) ≤ 1
  have exp_bound : |Real.exp (-u)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (by linarith)
  have sub_bound : |1 - u| ≤ 1 := by rw [abs_of_nonneg h1mu_nn]; exact h1mu_le
  -- exp(-u)^n = exp(-t²/2)
  have exp_pow : Real.exp (-u) ^ n = Real.exp (-(t ^ 2 / 2)) := by
    rw [← Real.exp_nat_mul]; congr 1; simp [hu_def]; field_simp
  -- n * u² = t⁴/(4n)
  have nu2_eq : u ^ 2 * ↑n = t ^ 4 / (4 * ↑n) := by
    simp [hu_def]; field_simp; ring
  -- Combine via abs_pow_sub_pow_le telescoping
  calc -(((1 - u) ^ n) - Real.exp (-(t ^ 2 / 2)))
      = Real.exp (-(t ^ 2 / 2)) - (1 - u) ^ n := by ring
    _ ≤ |Real.exp (-(t ^ 2 / 2)) - (1 - u) ^ n| := le_abs_self _
    _ = |Real.exp (-u) ^ n - (1 - u) ^ n| := by rw [exp_pow]
    _ ≤ |Real.exp (-u) - (1 - u)| * ↑n *
          max |Real.exp (-u)| |1 - u| ^ (n - 1) := abs_pow_sub_pow_le ..
    _ ≤ u ^ 2 * ↑n * 1 ^ (n - 1) := by
        gcongr
        exact max_le exp_bound sub_bound
    _ = u ^ 2 * ↑n := by ring
    _ = t ^ 4 / (4 * ↑n) := nu2_eq

/-- **Product vs power bound.** The product of charfun values minus the power of
the quadratic approximation is bounded by `4ρn|t'|³`. -/
private lemma charfun_prod_vs_pow_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ)
    (t : ℝ) (ht : t ^ 2 ≤ 4 * ↑n) :
    let sn := σ * Real.sqrt ↑n
    let t' := t / sn
    let w : ℂ := (1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ))
    ‖∏ i : Fin n, charFun (μ.map (Y i)) t' - w ^ n‖ ≤
      4 * ρ * (↑n : ℝ) * |t'| ^ 3 := by
  intro sn t' w
  -- Useful positivity facts
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hsn_pos : 0 < sn := mul_pos hσ hsqrt_pos
  have hsn_ne : sn ≠ 0 := ne_of_gt hsn_pos
  -- Step 0: Each μ.map (Y i) is a probability measure
  have hprob : ∀ i, IsProbabilityMeasure (μ.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hm i).aemeasurable
  -- Step 1: Key algebraic identity: σ² * t'² / 2 = t² / (2n)
  have hreal_eq : σ ^ 2 * t' ^ 2 / 2 = t ^ 2 / (2 * (n : ℝ)) := by
    simp only [t', sn]
    rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hn')]
    field_simp
  -- Therefore w = 1 - ↑(σ² * t'² / 2) as complex
  have hw_eq : (w : ℂ) = (1 : ℂ) - (σ ^ 2 * t' ^ 2 / 2 : ℝ) := by
    -- Rewrite w as 1 - ↑(t²/(2n)) using ofReal lemmas
    have w_alt : w = (1 : ℂ) - (t ^ 2 / (2 * (n : ℝ)) : ℝ) := by
      simp only [w]
      push_cast
      ring
    rw [w_alt, hreal_eq.symm]
  -- Step 2: Per-factor Taylor bound
  have hfactor : ∀ i, ‖charFun (μ.map (Y i)) t' - w‖ ≤ 4 * ρ * |t'| ^ 3 := by
    intro i
    rw [hw_eq]
    exact charfun_taylor_third_moment (hm i) (hmean i) (hvar i) (h3 i) (hLp i) t'
  -- Step 3: Norm bounds for charFun factors
  have hz : ∀ i, ‖charFun (μ.map (Y i)) t'‖ ≤ 1 := fun i =>
    norm_charFun_le_one t'
  -- Step 4: ‖w‖ ≤ 1 using ht : t² ≤ 4n, so t²/(2n) ≤ 2, hence w ∈ [-1,1]
  have hw_norm : ∀ (_i : Fin n), ‖w‖ ≤ 1 := by
    intro _
    -- w = ↑(1 - t²/(2n)) as a real coercion
    set u := t ^ 2 / (2 * (n : ℝ)) with hu_def
    have hw_real : w = (↑(1 - u) : ℂ) := by
      simp only [w, hu_def]
      push_cast; ring
    rw [hw_real, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hu_le : u ≤ 2 := by
      simp only [hu_def]
      have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
      exact div_le_of_le_mul₀ (le_of_lt h2n_pos) (by norm_num) (by linarith)
    have hu_nn : 0 ≤ u := by positivity
    constructor <;> linarith
  -- Step 5: Apply norm_prod_sub_prod_le_sum and sum the per-factor bounds
  calc ‖∏ i : Fin n, charFun (μ.map (Y i)) t' - w ^ n‖
      = ‖∏ i : Fin n, charFun (μ.map (Y i)) t' -
          ∏ _i : Fin n, w‖ := by rw [Finset.prod_const, Finset.card_fin]
    _ ≤ ∑ i : Fin n, ‖charFun (μ.map (Y i)) t' - w‖ :=
        norm_prod_sub_prod_le_sum _ _ hz hw_norm
    _ ≤ ∑ _i : Fin n, (4 * ρ * |t'| ^ 3) :=
        Finset.sum_le_sum fun i _ => hfactor i
    _ = 4 * ρ * ↑n * |t'| ^ 3 := by
        simp [Finset.sum_const]; ring

/-- Auxiliary: purely multiplicative inequality (no fractions).
Given `σ3 ≤ ρ`, `a·ρ ≤ σ3·s`, and `s² = nn`, we have
`16·ρ·nn·a³ + a⁴·σ3·s ≤ 32·ρ·nn·(1+a)³`. -/
private lemma charfun_arith_aux {a s σ3 ρ nn : ℝ}
    (ha : 0 ≤ a) (_hs : 0 < s) (_hσ3 : 0 < σ3) (hρ : 0 < ρ) (hnn : 0 < nn)
    (hρσ : σ3 ≤ ρ) (ht : a * ρ ≤ σ3 * s) (hsq : s ^ 2 = nn) :
    16 * ρ * nn * a ^ 3 + a ^ 4 * σ3 * s ≤ 32 * ρ * nn * (1 + a) ^ 3 := by
  -- Key: a·(σ3·s) ≤ ρ·nn
  have hss : 0 ≤ σ3 * s := by positivity
  have h_as : a * (σ3 * s) ≤ ρ * nn := by
    -- From ht: a·ρ ≤ σ3·s, multiplying both sides by σ3·s ≥ 0:
    -- a·ρ·(σ3·s) ≤ (σ3·s)²
    have hab : a * ρ * (σ3 * s) ≤ (σ3 * s) ^ 2 := by nlinarith
    -- (σ3·s)² = σ3²·s² = σ3²·nn
    have heq : (σ3 * s) ^ 2 = σ3 ^ 2 * nn := by nlinarith [hsq]
    -- σ3² ≤ ρ²
    have hle : σ3 ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ - σ3)]
    -- a·ρ·(σ3·s) ≤ σ3²·nn ≤ ρ²·nn = (ρ·nn)·ρ
    -- hence a·(σ3·s) ≤ ρ·nn (dividing by ρ > 0)
    have h1 : a * (σ3 * s) * ρ ≤ ρ * nn * ρ := by nlinarith
    exact le_of_mul_le_mul_right h1 hρ
  -- a⁴·σ3·s = a³·(a·σ3·s) ≤ a³·(ρ·nn)
  have key : a ^ 4 * σ3 * s ≤ a ^ 3 * (ρ * nn) := by
    have : a ^ 4 * σ3 * s = a ^ 3 * (a * (σ3 * s)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left h_as (pow_nonneg ha 3)
  -- a³ ≤ (1+a)³
  have h_cube : a ^ 3 ≤ (1 + a) ^ 3 := by nlinarith [sq_nonneg a]
  -- Combine: 16ρnn·a³ + a⁴σ3s ≤ 16ρnn·a³ + a³(ρnn) = (16+1)ρnn·a³
  -- ≤ 17ρnn(1+a)³ ≤ 32ρnn(1+a)³
  have step1 : 16 * ρ * nn * a ^ 3 + a ^ 4 * σ3 * s ≤
      16 * ρ * nn * a ^ 3 + a ^ 3 * (ρ * nn) := by linarith
  have step2 : 16 * ρ * nn * a ^ 3 + a ^ 3 * (ρ * nn) = 17 * (ρ * nn) * a ^ 3 := by ring
  have step3 : (ρ * nn) * a ^ 3 ≤ (ρ * nn) * (1 + a) ^ 3 :=
    mul_le_mul_of_nonneg_left h_cube (by positivity)
  have step4 : 0 ≤ (ρ * nn) * (1 + a) ^ 3 := by positivity
  linarith

/-- **Final arithmetic.** Combine the product-vs-power and power-vs-exp bounds
into the overall `8 · (ρ/(σ³√n)) · (1+|t|)³` bound.

Requires `σ³ ≤ ρ` (Jensen: `E[|Y|³] ≥ (E[Y²])^{3/2}`) and
`|t| · ρ ≤ σ³ · √n` (Berry–Esseen truncation: `|t| ≤ σ³√n/ρ`). -/
private lemma charfun_final_arithmetic
    {n : ℕ} (hn : 0 < n)
    {σ ρ t : ℝ} (hσ : 0 < σ) (hρσ : σ ^ 3 ≤ ρ) (ht : |t| * ρ ≤ σ ^ 3 * Real.sqrt ↑n)
    {prod_val w gauss_val : ℂ}
    (part_a : ‖prod_val - w ^ n‖ ≤ 4 * ρ * (↑n : ℝ) * |t / (σ * Real.sqrt ↑n)| ^ 3)
    (part_b : ‖w ^ n - gauss_val‖ ≤ t ^ 4 / (4 * (n : ℝ)))
    (triangle : ‖prod_val - gauss_val‖ ≤
      ‖prod_val - w ^ n‖ + ‖w ^ n - gauss_val‖) :
    ‖prod_val - gauss_val‖ ≤
      8 * (ρ / (σ ^ 3 * Real.sqrt ↑n)) * (1 + |t|) ^ 3 := by
  -- Positivity setup
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  have hsn_pos : 0 < σ * Real.sqrt ↑n := mul_pos hσ hsqrt_pos
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  -- Simplify |t/(σ√n)| = |t|/(σ√n)
  have hab : |t / (σ * Real.sqrt ↑n)| = |t| / (σ * Real.sqrt ↑n) := by
    rw [abs_div, abs_of_pos hsn_pos]
  -- Simplify Part A: 4ρn·(|t|/(σ√n))³ = 4ρ|t|³/(σ³√n)
  have part_a_eq : 4 * ρ * ↑n * (|t| / (σ * Real.sqrt ↑n)) ^ 3 =
      4 * ρ * |t| ^ 3 / (σ ^ 3 * Real.sqrt ↑n) := by
    rw [div_pow, mul_pow]
    have : (Real.sqrt ↑n) ^ 3 = Real.sqrt ↑n * (Real.sqrt ↑n) ^ 2 := by ring
    rw [this, Real.sq_sqrt (le_of_lt hn')]
    field_simp
  -- Chain triangle with part_a + part_b
  have combined : ‖prod_val - gauss_val‖ ≤
      4 * ρ * |t| ^ 3 / (σ ^ 3 * Real.sqrt ↑n) + t ^ 4 / (4 * ↑n) := by
    calc ‖prod_val - gauss_val‖
        ≤ ‖prod_val - w ^ n‖ + ‖w ^ n - gauss_val‖ := triangle
      _ ≤ 4 * ρ * ↑n * |t / (σ * Real.sqrt ↑n)| ^ 3 + t ^ 4 / (4 * ↑n) :=
          by linarith [part_a, part_b]
      _ = 4 * ρ * |t| ^ 3 / (σ ^ 3 * Real.sqrt ↑n) + t ^ 4 / (4 * ↑n) :=
          by rw [hab, part_a_eq]
  -- Suffices to show the algebraic bound
  suffices hsuff : 4 * ρ * |t| ^ 3 / (σ ^ 3 * Real.sqrt ↑n) + t ^ 4 / (4 * ↑n) ≤
      8 * (ρ / (σ ^ 3 * Real.sqrt ↑n)) * (1 + |t|) ^ 3 by linarith [combined]
  -- Multiply everything by (σ³√n · 4n) > 0 to work with integers
  -- We'll show: LHS * D ≤ RHS * D where D = σ³√n · 4n
  set D := σ ^ 3 * Real.sqrt ↑n * (4 * ↑n) with hD_def
  have hD_pos : 0 < D := by positivity
  rw [div_add_div _ _ (ne_of_gt hden_pos) (ne_of_gt (show (0:ℝ) < 4 * ↑n by positivity))]
  rw [div_le_iff₀ (mul_pos hden_pos (show (0:ℝ) < 4 * ↑n by positivity))]
  -- RHS * D = 8·(ρ/(σ³√n))·(1+|t|)³ · (σ³√n · 4n) = 32ρn(1+|t|)³
  have hrhs : 8 * (ρ / (σ ^ 3 * Real.sqrt ↑n)) * (1 + |t|) ^ 3 *
      (σ ^ 3 * Real.sqrt ↑n * (4 * ↑n)) = 32 * ρ * ↑n * (1 + |t|) ^ 3 := by
    field_simp; ring
  rw [hrhs]
  -- LHS numerator: 4ρ|t|³·(4n) + t⁴·(σ³√n)
  -- Note: t⁴ ≥ 0 and t⁴ = (t²)² while |t|⁴ = (|t|²)² = (t²)² = t⁴
  -- So we can write t⁴ = |t|⁴
  -- The LHS after clearing denominators is:
  -- 4ρ|t|³·4n + t⁴·σ³√n = 16ρn|t|³ + t⁴·σ³√n
  -- Since t⁴ = |t|⁴ (even power), this equals 16ρn|t|³ + |t|⁴·σ³√n
  -- which matches charfun_arith_aux
  have ht4 : t ^ 4 = |t| ^ 4 := by
    have : t ^ 4 = (t ^ 2) ^ 2 := by ring
    have : |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
    nlinarith [sq_abs t]
  have hsq : (Real.sqrt ↑n) ^ 2 = (↑n : ℝ) := Real.sq_sqrt (le_of_lt hn')
  have aux := charfun_arith_aux (abs_nonneg t) hsqrt_pos hσ3_pos hρ_pos hn' hρσ ht hsq
  -- aux: 16ρn|t|³ + |t|⁴·σ³·√n ≤ 32ρn(1+|t|)³
  -- Goal: 4ρ|t|³·(4n) + t⁴·(σ³√n) ≤ 32ρn(1+|t|)³
  -- = 16ρn|t|³ + t⁴·σ³√n ≤ 32ρn(1+|t|)³
  nlinarith


/-- **Lyapunov inequality:** `σ³ ≤ ρ` when `E[Y²] = σ²` and `E[|Y|³] = ρ`.
By Jensen's inequality (`ConvexOn.map_integral_le`) applied to the convex function
`x ↦ x ^ (3/2 : ℝ)` on `[0, ∞)` with `f(ω) = (Y ω)²`:
`(E[Y²])^{3/2} ≤ E[(Y²)^{3/2}] = E[|Y|³]`, i.e., `σ³ ≤ ρ`.

Proved via `ConvexOn.map_integral_le` (Jensen) for `x ↦ x ^ (3/2)` on `[0,∞)`,
with `rpow_natCast_mul` bridging between `rpow (3/2)` and `pow 3`. -/
private lemma lyapunov_third_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (_hm : Measurable Y)
    (_hmean : ∫ ω, Y ω ∂μ = 0)
    (hvar : ∫ ω, (Y ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∫ ω, |Y ω| ^ 3 ∂μ = ρ)
    (hLp : MemLp Y 3 μ) :
    σ ^ 3 ≤ ρ := by
  -- Use Jensen's inequality: for convex g(x)=x^(3/2) on [0,∞),
  -- g(E[Y²]) ≤ E[g(Y²)] = E[|Y|³], i.e., (σ²)^(3/2) = σ³ ≤ ρ.
  have hLp2 : MemLp Y 2 μ := hLp.mono_exponent (by norm_num)
  -- σ³ = (σ²)^(3/2)
  have hσ3 : σ ^ 3 = (σ ^ 2) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast σ 3, ← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ.le]
    norm_num
  -- ((Y ω)²)^(3/2) = |Y ω|³ pointwise
  have hrw : ∀ ω : Ω, ((Y ω) ^ 2) ^ ((3 : ℝ) / 2) = |Y ω| ^ 3 := by
    intro ω
    -- Y ω ^ 2 = |Y ω| ^ 2
    rw [← sq_abs (Y ω)]
    -- (|Y ω| ^ 2) ^ (3/2) = |Y ω| ^ (2 * (3/2)) = |Y ω| ^ 3
    rw [← Real.rpow_natCast_mul (abs_nonneg (Y ω)) 2 ((3 : ℝ) / 2)]
    simp [show (2 : ℝ) * (3 / 2) = 3 by ring]
  -- Integrability
  have hfi : Integrable (fun ω => (Y ω) ^ 2) μ := hLp2.integrable_sq
  have h_abs3_int : Integrable (fun ω => |Y ω| ^ 3) μ := by
    have := hLp.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
    simp only [Real.norm_eq_abs] at this; exact this
  have hgi : Integrable ((fun x : ℝ => x ^ ((3 : ℝ) / 2)) ∘ (fun ω => (Y ω) ^ 2)) μ := by
    change Integrable (fun ω => ((Y ω) ^ 2) ^ ((3 : ℝ) / 2)) μ
    refine h_abs3_int.congr (ae_of_all _ (fun ω => ?_))
    exact (hrw ω).symm
  -- Jensen: g(E[f]) ≤ E[g∘f]
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ ((3 : ℝ) / 2)) :=
    convexOn_rpow (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hcont : ContinuousOn (fun x : ℝ => x ^ ((3 : ℝ) / 2)) (Set.Ici 0) :=
    continuousOn_id.rpow_const (fun _ _ => Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
  have hfs : ∀ᵐ ω ∂μ, (Y ω) ^ 2 ∈ Set.Ici (0 : ℝ) :=
    ae_of_all _ (fun ω => Set.mem_Ici.mpr (sq_nonneg _))
  have hJ := ConvexOn.map_integral_le hconv hcont isClosed_Ici hfs hfi hgi
  -- hJ : (∫ Y²)^(3/2) ≤ ∫ (Y²)^(3/2)
  -- Finish: σ³ = (σ²)^(3/2) = (∫ Y²)^(3/2) ≤ ∫ (Y²)^(3/2) = ∫ |Y|³ = ρ
  rw [hσ3, ← hvar]
  calc (∫ ω, (Y ω) ^ 2 ∂μ) ^ ((3 : ℝ) / 2)
      ≤ ∫ ω, ((Y ω) ^ 2) ^ ((3 : ℝ) / 2) ∂μ := by convert hJ using 1
    _ = ∫ ω, |Y ω| ^ 3 ∂μ := integral_congr_ae (ae_of_all _ hrw)
    _ = ρ := h3

/-- **Charfun chain: standardized-sum characteristic function vs standard Gaussian.**

For iid mean-zero L³ random variables `Y₁, ..., Yₙ` with `E[Yᵢ²] = σ²`, `E[|Yᵢ|³] = ρ`,
and standardized sum `S(ω) = (∑ Yᵢ(ω)) / (σ √n)`, we have

  `‖φ_S(t) − exp(−t²/2)‖ ≤ C · (ρ / (σ³ · √n)) · (1 + |t|)³`

where `C` is a universal constant. -/
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
  -- We choose C = 8 (any sufficiently large constant works).
  refine ⟨8, by norm_num, ?_⟩
  intro Ω mΩ μ inst n hn Y σ ρ hσ hm hindep hiid hmean hvar h3 hLp S t
  -- Positivity setup
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn'
  set sn := σ * Real.sqrt ↑n with sn_def
  set t' := t / sn with t'_def
  have hsn_pos : 0 < sn := mul_pos hσ hsqrt_pos
  have hσ3_pos : 0 < σ ^ 3 := pow_pos hσ 3
  have hden_pos : 0 < σ ^ 3 * Real.sqrt ↑n := mul_pos hσ3_pos hsqrt_pos
  -- Step 0: σ³ ≤ ρ (Lyapunov inequality: (E[Y²])^{3/2} ≤ E[|Y|³])
  have hρσ : σ ^ 3 ≤ ρ :=
    lyapunov_third_moment hσ (hm ⟨0, by omega⟩) (hmean ⟨0, by omega⟩)
      (hvar ⟨0, by omega⟩) (h3 ⟨0, by omega⟩) (hLp ⟨0, by omega⟩)
  -- Step 1: Factor φ_S(t) = ∏ φ_{Yi}(t')  via independence + scaling
  have step1 := charfun_iid_sum_eq_prod hn hσ hm hindep t
  -- Step 2: Gaussian charfun: φ_N(0,1)(t) = exp(-t²/2)
  have step2 := charFun_gaussianReal_standard t
  -- Assembly: rewrite Gaussian side
  rw [step2]
  -- Define intermediates
  set w : ℂ := (1 : ℂ) - (↑(t ^ 2) : ℂ) / (2 * (↑n : ℂ))
  set gauss_val : ℂ := Complex.exp (-((↑(t ^ 2) : ℂ) / 2))
  set prod_val : ℂ := ∏ i : Fin n, charFun (μ.map (Y i)) t'
  -- Connect charFun (map S μ) t with prod_val
  have charfun_eq_prod : charFun (μ.map S) t = prod_val := step1
  rw [charfun_eq_prod]
  -- Case split: either |t| is small enough for the detailed chain, or use crude bound
  by_cases ht_small : t ^ 2 ≤ 2 * ↑n ∧ |t| * ρ ≤ σ ^ 3 * Real.sqrt ↑n
  · -- CASE 1: |t| is small — use the detailed sub-lemma chain
    obtain ⟨ht2, htrunc⟩ := ht_small
    -- t² ≤ 2n implies t² ≤ 4n (needed for charfun_prod_vs_pow_bound)
    have ht4 : t ^ 2 ≤ 4 * ↑n := by linarith
    -- Part A: product vs w^n
    have part_a : ‖prod_val - w ^ n‖ ≤ 4 * ρ * (↑n : ℝ) * |t'| ^ 3 :=
      charfun_prod_vs_pow_bound hn hσ hm hmean hvar h3 hLp t ht4
    -- Part B: w^n vs Gaussian
    have part_b : ‖w ^ n - gauss_val‖ ≤ t ^ 4 / (4 * (n : ℝ)) :=
      complex_pow_approx_exp n hn t ht2
    -- Triangle inequality
    have triangle : ‖prod_val - gauss_val‖ ≤
        ‖prod_val - w ^ n‖ + ‖w ^ n - gauss_val‖ := by
      calc ‖prod_val - gauss_val‖
          = ‖(prod_val - w ^ n) + (w ^ n - gauss_val)‖ := by ring_nf
        _ ≤ ‖prod_val - w ^ n‖ + ‖w ^ n - gauss_val‖ := norm_add_le _ _
    -- Final arithmetic
    exact charfun_final_arithmetic hn hσ hρσ htrunc part_a part_b triangle
  · -- CASE 2: |t| is large — use crude bound ‖φ_S(t) - φ_Φ(t)‖ ≤ 2
    push_neg at ht_small
    -- ht_small : t ^ 2 ≤ 2 * ↑n → σ ^ 3 * Real.sqrt ↑n < |t| * ρ
    have hρ_pos : 0 < ρ := lt_of_lt_of_le hσ3_pos hρσ
    -- Derive σ³√n < |t|ρ unconditionally
    -- If t² ≤ 2n, ht_small gives it directly.
    -- If t² > 2n, then |t| > √(2n) > √n, and since σ³ ≤ ρ:
    --   |t|ρ > √n · ρ ≥ √n · σ³ = σ³√n
    have h_trunc : σ ^ 3 * Real.sqrt ↑n < |t| * ρ := by
      by_cases h2n : t ^ 2 ≤ 2 * ↑n
      · exact ht_small h2n
      · push_neg at h2n
        -- |t|² > 2n, so |t| > √(2n)
        have h_abs_sq : |t| ^ 2 > 2 * ↑n := by rwa [sq_abs]
        have h_abs_gt : |t| > Real.sqrt (2 * ↑n) := by
          rw [← Real.sqrt_sq (abs_nonneg t)]
          exact Real.sqrt_lt_sqrt (by positivity) h_abs_sq
        have h_sqrt_lt : Real.sqrt ↑n < |t| := by
          calc Real.sqrt ↑n < Real.sqrt (2 * ↑n) :=
                Real.sqrt_lt_sqrt (le_of_lt hn') (by linarith)
            _ < |t| := h_abs_gt
        calc σ ^ 3 * Real.sqrt ↑n
            ≤ ρ * Real.sqrt ↑n := by nlinarith
          _ < ρ * |t| := by nlinarith
          _ = |t| * ρ := by ring
    -- Crude bound: both charfun norms ≤ 1, so difference ≤ 2
    have crude : ‖prod_val - gauss_val‖ ≤ 2 := by
      calc ‖prod_val - gauss_val‖ ≤ ‖prod_val‖ + ‖gauss_val‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
          gcongr
          · -- ‖∏ charFun‖ ≤ 1 via product bound and charfun norm ≤ 1
            calc ‖prod_val‖ = ‖∏ i : Fin n, charFun (μ.map (Y i)) t'‖ := rfl
              _ ≤ ∏ i : Fin n, ‖charFun (μ.map (Y i)) t'‖ :=
                  Finset.norm_prod_le Finset.univ _
              _ ≤ 1 := Finset.prod_le_one (fun i _ => norm_nonneg _)
                  (fun i _ => by
                    haveI : IsProbabilityMeasure (μ.map (Y i)) :=
                      isProbabilityMeasure_map (hm i).aemeasurable
                    exact norm_charFun_le_one t')
          · -- ‖exp(z)‖ = exp(re(z)) and re(z) ≤ 0 when z = -(t²/2)
            change ‖Complex.exp (-((↑(t ^ 2) : ℂ) / 2))‖ ≤ 1
            rw [Complex.norm_exp]
            apply Real.exp_le_one_iff.mpr
            -- The real part of -(↑(t²)/2) is -(t²/2)
            -- ↑(t²) has re = t², im = 0, so ↑(t²)/2 has re = t²/2
            show (-((↑(t ^ 2) : ℂ) / 2)).re ≤ 0
            simp only [Complex.neg_re, Complex.div_ofNat,
              Complex.ofReal_re, Complex.ofReal_im]
            nlinarith [sq_nonneg t]
        _ = 2 := by ring
    -- Show 2 ≤ 8 * (ρ/(σ³√n)) * (1+|t|)³
    -- Key: since σ³√n < |t|ρ, we have |t| * R > 1 where R = ρ/(σ³√n)
    -- Then 8R(1+|t|)³ ≥ 8R(1+|t|) ≥ 8R|t| > 8 ≥ 2
    suffices hsuff : 2 ≤ 8 * (ρ / (σ ^ 3 * Real.sqrt ↑n)) * (1 + |t|) ^ 3 by
      linarith
    have h_ratio_pos : 0 < ρ / (σ ^ 3 * Real.sqrt ↑n) := div_pos hρ_pos hden_pos
    have h_one_lt : 1 < |t| * (ρ / (σ ^ 3 * Real.sqrt ↑n)) := by
      rw [show |t| * (ρ / (σ ^ 3 * Real.sqrt ↑n)) = |t| * ρ / (σ ^ 3 * Real.sqrt ↑n)
        from by ring]
      rw [one_lt_div hden_pos]
      exact h_trunc
    -- (1+|t|)³ ≥ (1+|t|) ≥ |t| since 1+|t| ≥ 1
    -- So R(1+|t|)³ ≥ R(1+|t|) ≥ R|t| > 1, hence 8R(1+|t|)³ > 8 > 2
    have h_1t_ge1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have h_cube_ge : (1 + |t|) ^ 3 ≥ 1 + |t| := by
      nlinarith [sq_nonneg (1 + |t|)]
    nlinarith [abs_nonneg t]

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

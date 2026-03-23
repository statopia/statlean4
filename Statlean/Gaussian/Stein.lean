import Statlean.Gaussian.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.BoundedVariation

/-! # Stein's Identity for Standard Gaussian

`E_γ[x·h(x)] = E_γ[h'(x)]` for `h, h' ∈ L²(γ)`.

## Main results

- `stein_identity`: Stein's identity for C¹ functions with L² bounds.
- `stein_identity_of_lipschitz`: Stein's identity for Lipschitz functions
  (only ae differentiable, proved via Steklov approximation).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

lemma stein_identity
    (h h' : ℝ → ℝ)
    (hh : MemLp h 2 stdGaussian)
    (hh' : MemLp h' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt h (h' x) x) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, h' x ∂stdGaussian := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  change ∫ x, x * h x ∂gaussianReal 0 1 = ∫ x, h' x ∂gaussianReal 0 1
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv,
      integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv]
  simp only [smul_eq_mul]
  have hφ_deriv : ∀ x, HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := hasDerivAt_gaussianPDFReal_std
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    hderiv hφ_deriv
    (by have := integrable_id_mul_mul_gaussianPDFReal_of_memLp hh
        change Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) volume
        have : Integrable (fun x => -(x * h x * gaussianPDFReal 0 1 x)) volume :=
          this.neg
        convert this using 1; ext x; ring)
    (integrable_mul_gaussianPDFReal_of_memLp hh')
    (integrable_mul_gaussianPDFReal_of_memLp hh)
  have key : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]; congr 1; ext x; ring
  have key2 : ∫ x, h' x * gaussianPDFReal 0 1 x =
      ∫ x, gaussianPDFReal 0 1 x * h' x := by
    congr 1; ext x; ring
  linarith

/-! ## Stein identity for Lipschitz functions -/

section Lipschitz

open intervalIntegral

/-- The Steklov average `x ↦ (2δ)⁻¹ ∫_{x-δ}^{x+δ} h` is C¹ for continuous h,
with derivative `(2δ)⁻¹ (h(x+δ) - h(x-δ))` (the symmetric difference quotient). -/
private lemma steklov_hasDerivAt (h : ℝ → ℝ) (hc : Continuous h) (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    HasDerivAt (fun x => (2 * δ)⁻¹ * ∫ t in (x - δ)..(x + δ), h t)
      ((2 * δ)⁻¹ * (h (x + δ) - h (x - δ))) x := by
  set F : ℝ → ℝ := fun a => ∫ t in (0 : ℝ)..a, h t
  have hF : ∀ a, HasDerivAt F (h a) a := fun a =>
    integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter volume (𝓝 a)) hc.continuousAt
  have hG : HasDerivAt (fun x' => ∫ t in (x' - δ)..(x' + δ), h t) (h (x + δ) - h (x - δ)) x := by
    have h_eq : ∀ x', ∫ t in (x' - δ)..(x' + δ), h t = F (x' + δ) - F (x' - δ) := by
      intro x'
      have := integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := x' - δ) (c := x' + δ) (μ := volume)
        (hc.intervalIntegrable 0 (x' - δ)) (hc.intervalIntegrable (x' - δ) (x' + δ))
      linarith
    simp_rw [h_eq]
    have h1 := (hF (x + δ)).comp x ((hasDerivAt_id x).add (hasDerivAt_const x δ))
    have h2 := (hF (x - δ)).comp x ((hasDerivAt_id x).sub (hasDerivAt_const x δ))
    simp only [Function.comp_def] at h1 h2
    convert h1.sub h2 using 1; ring
  exact ((hasDerivAt_const x ((2 * δ)⁻¹)).mul hG).congr_deriv (by ring)

/-- Lipschitz functions satisfy MemLp p for stdGaussian (probability measure,
Lipschitz gives linear growth, Gaussian has all moments finite). -/
private lemma lipschitz_memLp_gaussianReal (h : ℝ → ℝ) (C : ℝ≥0) (hLip : LipschitzWith C h)
    (p : NNReal) : MemLp h p stdGaussian := by
  -- Bound: |h(x)| ≤ |h(0)| + C|x|
  -- Both |h(0)| (constant) and C|x| (id scaled) are in Lᵖ(γ)
  -- Use MemLp.of_bound after showing a suitable constant bound doesn't work (growth is linear)
  -- Instead: h = (h - h(0)) + h(0), where h-h(0) is Lip with h(0)=0, so |h-h(0)| ≤ C|x|
  have h1 : MemLp (fun _ : ℝ => h 0) p stdGaussian := memLp_const _
  have h2 : MemLp (fun x => h x - h 0) p stdGaussian := by
    have hLip2 : LipschitzWith C (fun x => h x - h 0) :=
      hLip.sub (LipschitzWith.const _) |>.weaken (by simp)
    -- |h(x) - h(0)| ≤ C|x|, and C|x| ∈ Lᵖ(γ)
    exact ((memLp_id_gaussianReal p (μ := 0) (v := 1)).const_mul C).mono
      hLip2.continuous.aestronglyMeasurable (.of_forall fun x => by
        calc ‖h x - h 0‖ ≤ C * dist x 0 := by
              rw [← dist_eq_norm]; exact hLip.dist_le_mul x 0
          _ = C * |x| := by rw [dist_zero_right, Real.norm_eq_abs]
          _ = ‖(C : ℝ) * x‖ := by rw [norm_mul, norm_of_nonneg (NNReal.coe_nonneg C), Real.norm_eq_abs])
  convert h1.add h2 using 1; ext x; simp

/-- Forward difference quotient converges to derivative along δ_n → 0⁺. -/
private lemma forward_diff_tendsto {f : ℝ → ℝ} {a x : ℝ} (hf : HasDerivAt f a x)
    {δ : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ n) (hδ_lim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => (f (x + δ n) - f x) / δ n) atTop (𝓝 a) := by
  convert (hasDerivAt_iff_tendsto_slope.mp hf).comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by have := (tendsto_const_nhds (x := x)).add hδ_lim; simp only [add_zero] at this; exact this)
      (by filter_upwards with n; simp; linarith [hδ_pos n])) using 1
  ext n; simp [slope, Function.comp_def, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Backward difference quotient converges to derivative along δ_n → 0⁺. -/
private lemma backward_diff_tendsto {f : ℝ → ℝ} {a x : ℝ} (hf : HasDerivAt f a x)
    {δ : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ n) (hδ_lim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => (f x - f (x - δ n)) / δ n) atTop (𝓝 a) := by
  suffices key : (fun n => (f x - f (x - δ n)) / δ n) = (slope f x) ∘ (fun n => x - δ n) from
    key ▸ (hasDerivAt_iff_tendsto_slope.mp hf).comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by convert tendsto_const_nhds.sub hδ_lim using 1; simp)
        (by filter_upwards with n; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            linarith [hδ_pos n]))
  ext n; simp only [slope, Function.comp_def, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv]; ring

/-- Symmetric difference quotient converges to derivative along δ_n → 0⁺. -/
private lemma symm_diff_quotient_tendsto {f : ℝ → ℝ} {a x : ℝ} (hf : HasDerivAt f a x)
    {δ : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ n) (hδ_lim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => (2 * δ n)⁻¹ * (f (x + δ n) - f (x - δ n))) atTop (𝓝 a) := by
  rw [show (fun n => (2 * δ n)⁻¹ * (f (x + δ n) - f (x - δ n))) =
      fun n => ((f (x + δ n) - f x) / δ n + (f x - f (x - δ n)) / δ n) / 2 from by
    ext n; have := (hδ_pos n).ne'; field_simp; ring]
  rw [show a = (a + a) / 2 from by ring]
  exact ((forward_diff_tendsto hf hδ_pos hδ_lim).add
    (backward_diff_tendsto hf hδ_pos hδ_lim)).div_const 2

/-- Steklov average ‖(2δ)⁻¹ · ∫ h(t) dt - h(x)‖ ≤ C * δ for C-Lipschitz h. -/
private lemma steklov_sub_norm_le {h : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C h)
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ‖(2 * δ)⁻¹ * (∫ t in (x - δ)..(x + δ), h t) - h x‖ ≤ C * δ := by
  have h2δ_ne : (2 * δ) ≠ 0 := by positivity
  have h2δ_pos : (0 : ℝ) < 2 * δ := by positivity
  have hab : x - δ ≤ x + δ := by linarith
  -- Write ∫ (h t - h x) in terms of ∫ h t
  have hint_sub : ∫ t in (x - δ)..(x + δ), (h t - h x) =
      (∫ t in (x - δ)..(x + δ), h t) - 2 * δ * h x := by
    rw [intervalIntegral.integral_sub (hLip.continuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_const, show x + δ - (x - δ) = 2 * δ from by ring,
        smul_eq_mul]
  -- Rewrite the LHS to use ∫ (h t - h x)
  have key : (2 * δ)⁻¹ * (∫ t in (x - δ)..(x + δ), h t) - h x =
      (2 * δ)⁻¹ * ∫ t in (x - δ)..(x + δ), (h t - h x) := by
    rw [hint_sub]; field_simp
  rw [key, norm_mul, norm_inv, norm_of_nonneg h2δ_pos.le]
  calc (2 * δ)⁻¹ * ‖∫ t in (x - δ)..(x + δ), (h t - h x)‖
      ≤ (2 * δ)⁻¹ * ∫ t in (x - δ)..(x + δ), ↑C * δ := by
        gcongr
        apply norm_integral_le_of_norm_le hab
        · apply ae_of_all; intro t ht
          calc ‖h t - h x‖ = dist (h t) (h x) := (dist_eq_norm _ _).symm
            _ ≤ C * dist t x := hLip.dist_le_mul _ _
            _ ≤ C * δ := by
                gcongr; rw [Real.dist_eq, abs_le]
                exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · exact continuous_const.intervalIntegrable _ _
    _ = (C : ℝ) * δ := by
        rw [intervalIntegral.integral_const,
            show x + δ - (x - δ) = 2 * δ from by ring, smul_eq_mul]
        field_simp

/-- Steklov average S_δ(x) → h(x) pointwise as δ → 0 for Lipschitz h. -/
private lemma steklov_tendsto_pointwise {h : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C h) (x : ℝ)
    {δ : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ n) (hδ_lim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => (2 * δ n)⁻¹ * ∫ t in (x - δ n)..(x + δ n), h t) atTop (𝓝 (h x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC1 : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hδ_lim (ε / ((C : ℝ) + 1)) (div_pos hε hC1)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, dist_eq_norm]
  -- Goal: ‖h x - (2δ)⁻¹ * ∫ h t‖ = ‖(2δ)⁻¹ * ∫ h t - h x‖ by norm_sub_rev
  rw [norm_sub_rev]
  calc ‖(2 * δ n)⁻¹ * (∫ t in (x - δ n)..(x + δ n), h t) - h x‖
      ≤ C * δ n := steklov_sub_norm_le hLip (hδ_pos n) x
    _ < ε := by
        have hδn := hN n hn
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hδ_pos n).le] at hδn
        calc (C : ℝ) * δ n ≤ ((C : ℝ) + 1) * δ n := by
              apply mul_le_mul_of_nonneg_right _ (hδ_pos n).le
              linarith [NNReal.coe_nonneg C]
          _ < ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
              exact mul_lt_mul_of_pos_left hδn hC1
          _ = ε := mul_div_cancel₀ ε hC1.ne'

/-- Stein identity for Lipschitz functions. Same as `stein_identity` but only requires
Lipschitz (which gives ae differentiability) instead of everywhere HasDerivAt.
Proof: approximate h by Steklov averages h_δ (C¹), apply `stein_identity` to h_δ,
take δ → 0 using DCT with uniform Lipschitz bound. -/
lemma stein_identity_of_lipschitz
    (h : ℝ → ℝ) (C : ℝ≥0) (hLip : LipschitzWith C h)
    (hInt : Integrable h stdGaussian) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, deriv h x ∂stdGaussian := by
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ_pos : ∀ k, 0 < δ k := fun k => by positivity
  have hδ_lim : Tendsto δ atTop (𝓝 0) := by
    simp only [δ, one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  set S : ℕ → ℝ → ℝ := fun k x => (2 * δ k)⁻¹ * ∫ t in (x - δ k)..(x + δ k), h t
  set S' : ℕ → ℝ → ℝ := fun k x => (2 * δ k)⁻¹ * (h (x + δ k) - h (x - δ k))
  -- S' k is bounded by C (symmetric difference quotient of Lip function)
  have hS'_bound : ∀ k x, ‖S' k x‖ ≤ C := by
    intro k x
    show ‖(2 * δ k)⁻¹ * (h (x + δ k) - h (x - δ k))‖ ≤ C
    rw [norm_mul, norm_inv]
    calc ‖(2 * δ k)‖⁻¹ * ‖h (x + δ k) - h (x - δ k)‖
        ≤ ‖(2 * δ k)‖⁻¹ * (↑C * (2 * δ k)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
          calc ‖h (x + δ k) - h (x - δ k)‖
              ≤ C * dist (x + δ k) (x - δ k) := hLip.norm_sub_le _ _
            _ = C * (2 * δ k) := by
                congr 1; rw [dist_eq_norm]; simp; rw [abs_of_pos (by positivity)]; ring
      _ = ↑C := by
          rw [norm_of_nonneg (show (0 : ℝ) ≤ 2 * δ k from by positivity),
              show ↑C * (2 * δ k) = (2 * δ k) * ↑C from by ring,
              inv_mul_cancel_left₀ (show (2 * δ k) ≠ 0 from by positivity)]
  -- S' k is measurable
  have hS'_asm : ∀ k, AEStronglyMeasurable (S' k) stdGaussian := fun k =>
    AEStronglyMeasurable.const_mul
      ((hLip.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable.sub
        (hLip.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable) _
  -- S k is C-Lipschitz (Steklov of C-Lip is C-Lip)
  have hS_lip : ∀ k, LipschitzWith C (S k) := by
    intro k
    intro x y
    have h2δ_ne : (2 * δ k) ≠ 0 := by positivity
    have h2δ_pos : (0 : ℝ) < 2 * δ k := by positivity
    suffices hdist : dist (S k x) (S k y) ≤ ↑C * dist x y by
      calc edist _ _ = ENNReal.ofReal (dist _ _) := edist_dist _ _
        _ ≤ ENNReal.ofReal (↑C * dist x y) := ENNReal.ofReal_le_ofReal hdist
        _ = ENNReal.ofReal ↑C * ENNReal.ofReal (dist x y) :=
            ENNReal.ofReal_mul (NNReal.coe_nonneg C)
        _ = ↑C * edist x y := by rw [ENNReal.ofReal_coe_nnreal, edist_dist]
    have hIx : IntervalIntegrable (fun u => h (u + x)) volume (-δ k) (δ k) :=
      (hLip.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    have hIy : IntervalIntegrable (fun u => h (u + y)) volume (-δ k) (δ k) :=
      (hLip.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    show dist ((2 * δ k)⁻¹ * ∫ t in (x - δ k)..(x + δ k), h t)
        ((2 * δ k)⁻¹ * ∫ t in (y - δ k)..(y + δ k), h t) ≤ ↑C * dist x y
    rw [dist_eq_norm, dist_eq_norm]
    have hx_shift : ∫ t in (x - δ k)..(x + δ k), h t = ∫ u in (-δ k)..(δ k), h (u + x) := by
      conv_lhs => rw [show x - δ k = -δ k + x from by ring, show x + δ k = δ k + x from by ring]
      rw [← integral_comp_add_right]
    have hy_shift : ∫ t in (y - δ k)..(y + δ k), h t = ∫ u in (-δ k)..(δ k), h (u + y) := by
      conv_lhs => rw [show y - δ k = -δ k + y from by ring, show y + δ k = δ k + y from by ring]
      rw [← integral_comp_add_right]
    have key : ((2 * δ k)⁻¹ * ∫ t in (x - δ k)..(x + δ k), h t) -
        (2 * δ k)⁻¹ * ∫ t in (y - δ k)..(y + δ k), h t =
        (2 * δ k)⁻¹ * ∫ u in (-δ k)..(δ k), (h (u + x) - h (u + y)) := by
      rw [← mul_sub, hx_shift, hy_shift, ← intervalIntegral.integral_sub hIx hIy]
    rw [key, norm_mul, norm_inv, norm_of_nonneg h2δ_pos.le]
    calc (2 * δ k)⁻¹ * ‖∫ u in (-δ k)..(δ k), (h (u + x) - h (u + y))‖
        ≤ (2 * δ k)⁻¹ * ∫ u in (-δ k)..(δ k), (↑C * ‖x - y‖) := by
          gcongr
          apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          · exact ae_of_all _ fun t _ht => by
              calc ‖h (t + x) - h (t + y)‖ ≤ ↑C * dist (t + x) (t + y) := hLip.norm_sub_le _ _
                _ = ↑C * ‖x - y‖ := by rw [dist_eq_norm]; congr 1; ring
          · exact _root_.intervalIntegrable_const
      _ = ↑C * ‖x - y‖ := by
          rw [intervalIntegral.integral_const, smul_eq_mul,
            show δ k - -δ k = 2 * δ k from by ring, inv_mul_cancel_left₀ h2δ_ne]
  -- Stein identity for each S k
  have hstein : ∀ k, ∫ x, x * S k x ∂stdGaussian = ∫ x, S' k x ∂stdGaussian := fun k =>
    stein_identity _ _
      (lipschitz_memLp_gaussianReal _ C (hS_lip k) 2)
      (MemLp.of_bound (hS'_asm k) C (ae_of_all _ (hS'_bound k)))
      (fun x => steklov_hasDerivAt h hLip.continuous (δ k) (hδ_pos k) x)
  -- RHS: ∫ S'_k(x) → ∫ deriv h x by DCT (bounded dominator + ae pointwise convergence)
  have hRHS : Tendsto (fun k => ∫ x, S' k x ∂stdGaussian) atTop
      (𝓝 (∫ x, deriv h x ∂stdGaussian)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (C : ℝ))
    · exact hS'_asm
    · exact integrable_const _
    · exact fun k => ae_of_all _ (hS'_bound k)
    · -- S'_k(x) → deriv h x ae (Rademacher + symmetric diff quotient convergence)
      filter_upwards [(gaussianReal_absolutelyContinuous 0 one_ne_zero).ae_le
        hLip.ae_differentiableAt_real] with x hx
      exact symm_diff_quotient_tendsto hx.hasDerivAt hδ_pos hδ_lim
  -- LHS: ∫ x * S_k(x) → ∫ x * h(x) by DCT
  have hLHS : Tendsto (fun k => ∫ x, x * S k x ∂stdGaussian) atTop
      (𝓝 (∫ x, x * h x ∂stdGaussian)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => |h 0| * |x| + ↑C * x ^ 2 + ↑C * |x|)
    · -- AEStronglyMeasurable for x * S_k(x)
      intro k; exact aestronglyMeasurable_id.mul ((hS_lip k).continuous.aestronglyMeasurable)
    · -- Dominator integrable: |h(0)|·|x| + C·x² + C·|x| under Gaussian
      exact ((((memLp_id_gaussianReal (1 : ℝ≥0)).integrable le_rfl).norm.const_mul |h 0|).add
        (((memLp_id_gaussianReal (2 : ℝ≥0)).integrable_sq).const_mul ↑C)).add
        (((memLp_id_gaussianReal (1 : ℝ≥0)).integrable le_rfl).norm.const_mul ↑C)
    · -- Bound: ‖x * S_k(x)‖ ≤ dominator
      intro k; apply ae_of_all; intro x
      -- ‖S_k(x)‖ ≤ |h(0)| + C|x| + C  (Lip bound on h + Steklov closeness)
      have hSx : ‖S k x‖ ≤ |h 0| + ↑C * |x| + ↑C := by
        calc ‖S k x‖ = ‖h x + (S k x - h x)‖ := by ring_nf
          _ ≤ ‖h x‖ + ‖S k x - h x‖ := norm_add_le _ _
          _ ≤ (|h 0| + ↑C * |x|) + ↑C := by
              gcongr
              · calc ‖h x‖ = |h x| := Real.norm_eq_abs _
                  _ ≤ |h 0| + |h x - h 0| := by linarith [abs_sub_abs_le_abs_sub (h x) (h 0)]
                  _ ≤ |h 0| + ↑C * |x| := by
                      gcongr
                      calc |h x - h 0| = dist (h x) (h 0) := by rw [Real.dist_eq]
                        _ ≤ ↑C * dist x 0 := hLip.dist_le_mul _ _
                        _ = ↑C * |x| := by rw [dist_zero_right, Real.norm_eq_abs]
              · -- ‖S_k(x) - h(x)‖ ≤ C * δ_k ≤ C * 1 ≤ C
                have hδ_le1 : δ k ≤ 1 := by
                  show 1 / ((k : ℝ) + 1) ≤ 1
                  exact div_le_one_of_le₀
                    (by linarith [Nat.cast_nonneg (α := ℝ) k])
                    (by linarith [Nat.cast_nonneg (α := ℝ) k])
                -- ‖S_k(x) - h(x)‖ ≤ C * δ ≤ C
                have : ‖S k x - h x‖ ≤ ↑C * δ k := by
                  show ‖(2 * δ k)⁻¹ * (∫ t in (x - δ k)..(x + δ k), h t) - h x‖ ≤ _
                  exact steklov_sub_norm_le hLip (hδ_pos k) x
                calc ‖S k x - h x‖ ≤ ↑C * δ k := this
                  _ ≤ ↑C * 1 := by
                      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg C)
                      exact div_le_one_of_le₀
                        (by linarith [Nat.cast_nonneg (α := ℝ) k])
                        (by linarith [Nat.cast_nonneg (α := ℝ) k])
                  _ = ↑C := mul_one _
      calc ‖x * S k x‖ = ‖x‖ * ‖S k x‖ := norm_mul x (S k x)
        _ ≤ |x| * (|h 0| + ↑C * |x| + ↑C) := by
            rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hSx (abs_nonneg x)
        _ = |h 0| * |x| + ↑C * x ^ 2 + ↑C * |x| := by
            rw [(sq_abs x).symm]; ring
    · -- Pointwise: x * S_k(x) → x * h(x)
      apply ae_of_all; intro x
      exact tendsto_const_nhds.mul (steklov_tendsto_pointwise hLip x hδ_pos hδ_lim)
  -- Conclude by limit uniqueness
  exact tendsto_nhds_unique hLHS (by rwa [funext hstein])

end Lipschitz

section GaussianIBP

open Function

set_option synthInstance.maxHeartbeats 80000

/-- lineDeriv in coordinate direction eⱼ = deriv of the j-th coordinate slice. -/
private lemma lineDeriv_eq_deriv_coord {n : ℕ} (j : Fin n) (g : (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) :
    lineDeriv ℝ g y (Pi.single j 1 : Fin n → ℝ) =
    deriv (fun s => g (update y j s)) (y j) := by
  show deriv (fun t => g (y + t • (Pi.single j (1 : ℝ) : Fin n → ℝ))) 0 =
    deriv (fun s => g (update y j s)) (y j)
  conv_lhs => arg 1; ext t; rw [show y + t • (Pi.single j (1 : ℝ) : Fin n → ℝ) =
    update y j (y j + t) from by
      ext i; simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, update_apply]
      split_ifs with h <;> simp_all]
  rw [show deriv (fun t => g (update y j (y j + t))) 0 =
      deriv (fun s => g (update y j s)) (y j + 0) from
    deriv_comp_const_add (fun s => g (update y j s)) (y j) 0, add_zero]

/-- update (insertNth j s z) j s' = insertNth j s' z -/
private lemma update_insertNth_eq {m : ℕ} (j : Fin (m + 1)) (s s' : ℝ)
    (z : Fin m → ℝ) :
    update (Fin.insertNth (α := fun _ => ℝ) j s z) j s' =
    Fin.insertNth (α := fun _ => ℝ) j s' z := by
  rw [← Fin.insertNth_removeNth (α := fun _ => ℝ) j s'
      (Fin.insertNth (α := fun _ => ℝ) j s z)]
  congr 1; ext k; simp [Fin.removeNth, Fin.insertNth_apply_succAbove]

/-- s ↦ insertNth j s z is 1-Lipschitz. -/
private lemma lipschitz_insertNth {m : ℕ} (j : Fin (m + 1)) (z : Fin m → ℝ) :
    LipschitzWith 1 (fun s : ℝ => Fin.insertNth (α := fun _ => ℝ) j s z) := by
  intro a b
  simp only [edist_pi_def, ENNReal.coe_one, one_mul]
  apply Finset.sup_le; intro i _
  by_cases h : i = j
  · subst h; simp [Fin.insertNth_apply_same]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    rw [show (Fin.insertNth (α := fun _ => ℝ) j a z) i = z k from by
          rw [← hk]; exact Fin.insertNth_apply_succAbove _ _ _ _,
        show (Fin.insertNth (α := fun _ => ℝ) j b z) i = z k from by
          rw [← hk]; exact Fin.insertNth_apply_succAbove _ _ _ _]
    simp [edist_self]

/-- Multi-dimensional Gaussian integration by parts in coordinate j:
for Lipschitz g on ℝⁿ, `∫ (∂ⱼg)(y) dγⁿ(y) = ∫ g(y)·yⱼ dγⁿ(y)`.
This is the score function identity for product Gaussians.
Proof uses Fubini decomposition into the j-th coordinate and applies 1D Stein. -/
lemma gaussian_ibp_coord {n : ℕ} (j : Fin n) (g : (Fin n → ℝ) → ℝ) (C : ℝ≥0)
    (hLip : LipschitzWith C g) :
    ∫ y, lineDeriv ℝ g y (Pi.single j 1) ∂stdGaussianPi n =
    ∫ y, g y * (y j) ∂stdGaussianPi n := by
  -- Step 1: Rewrite lineDeriv as deriv of coordinate slice
  simp_rw [lineDeriv_eq_deriv_coord j g]
  -- Step 2: n = m + 1 since j : Fin n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos j)).symm⟩
  -- Step 3: piFinSuccAbove decomposition
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
  set gamma := stdGaussian
  set mu_rest : Measure (Fin m → ℝ) := Measure.pi (fun _ : Fin m => stdGaussian)
  have hmp : MeasurePreserving e (stdGaussianPi (m + 1)) (gamma.prod mu_rest) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => stdGaussian) j
  have hmp_s := hmp.symm e
  have he_symm : ∀ (s : ℝ) (z : Fin m → ℝ),
      e.symm (s, z) = Fin.insertNth (α := fun _ => ℝ) j s z := by
    intro s z; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  -- Step 4: Define slice function h_z(s) = g(insertNth j s z)
  set h_z : (Fin m → ℝ) → ℝ → ℝ := fun z s => g (Fin.insertNth (α := fun _ => ℝ) j s z)
  -- Slice is C-Lipschitz
  have h_lip : ∀ z, LipschitzWith C (h_z z) := fun z => by
    have := hLip.comp (lipschitz_insertNth j z)
    simpa [mul_one] using this
  -- Slice is integrable against stdGaussian
  have h_int : ∀ z, Integrable (h_z z) gamma := fun z =>
    (lipschitz_memLp_gaussianReal (h_z z) C (h_lip z) 1).integrable le_rfl
  -- 1D Stein identity per fiber
  have h_stein : ∀ z,
      ∫ s, s * h_z z s ∂gamma = ∫ s, deriv (h_z z) s ∂gamma :=
    fun z => stein_identity_of_lipschitz (h_z z) C (h_lip z) (h_int z)
  -- Step 5: Transform both integrals to product form via MeasurePreserving
  have lhs_eq : ∫ y, deriv (fun s => g (update y j s)) (y j) ∂stdGaussianPi (m + 1) =
      ∫ p : ℝ × (Fin m → ℝ), deriv (h_z p.2) p.1 ∂(gamma.prod mu_rest) := by
    rw [← hmp_s.integral_comp e.symm.measurableEmbedding]
    congr 1; ext ⟨s, z⟩
    simp only [comp_def, e.apply_symm_apply, h_z, he_symm,
      Fin.insertNth_apply_same (α := fun _ => ℝ)]
    congr 1; ext s'; rw [update_insertNth_eq]
  have rhs_eq : ∫ y, g y * (y j) ∂stdGaussianPi (m + 1) =
      ∫ p : ℝ × (Fin m → ℝ), h_z p.2 p.1 * p.1 ∂(gamma.prod mu_rest) := by
    rw [← hmp_s.integral_comp e.symm.measurableEmbedding]
    congr 1; ext ⟨s, z⟩
    simp only [comp_def, e.apply_symm_apply, h_z, he_symm,
      Fin.insertNth_apply_same (α := fun _ => ℝ)]
  rw [lhs_eq, rhs_eq]
  -- Step 6: Fubini decomposition + fiber Stein identity
  haveI : SFinite gamma := inferInstance
  haveI : SFinite mu_rest := by
    change SFinite (Measure.pi (fun _ : Fin m => stdGaussian))
    exact inferInstance
  -- Define curried functions for Fubini
  set F : ℝ → (Fin m → ℝ) → ℝ := fun s z => deriv (h_z z) s
  set G : ℝ → (Fin m → ℝ) → ℝ := fun s z => h_z z s * s
  -- Integrability on product (for Fubini)
  have hF_int : Integrable (uncurry F) (gamma.prod mu_rest) := by
    -- |deriv(h_z z)(s)| ≤ C everywhere (0 when not diff, ≤ C when diff)
    refine (MemLp.of_bound (C := (C : ℝ)) sorry (ae_of_all _ fun ⟨s, z⟩ => ?_)).integrable le_rfl
    show ‖deriv (h_z z) s‖ ≤ C
    by_cases hd : DifferentiableAt ℝ (h_z z) s
    · exact norm_deriv_le_of_lipschitz (h_lip z)
    · simp [deriv_zero_of_not_differentiableAt hd, NNReal.coe_nonneg]
  have hG_int : Integrable (uncurry G) (gamma.prod mu_rest) := by
    -- g(y)*y_j integrable on γⁿ, transport to product via e.symm
    suffices h : Integrable (fun y => g y * y j) (stdGaussianPi (m + 1)) by
      rw [show uncurry G = (fun y => g y * y j) ∘ e.symm from by
        ext ⟨s, z⟩; simp [G, h_z, he_symm, Fin.insertNth_apply_same (α := fun _ => ℝ)]]
      exact (hmp_s.integrable_comp_emb e.symm.measurableEmbedding).mpr h
    -- g is Lipschitz ⇒ |g(y)| ≤ |g(0)| + C*‖y‖, |y_j| ≤ ‖y‖
    -- So |g(y)*y_j| ≤ (|g(0)| + C*‖y‖)*‖y‖ ≤ |g(0)|*‖y‖ + C*‖y‖²
    apply Integrable.mono
      (g := fun y => (|g 0| + ↑C * ‖y‖) * ‖y‖)
    · -- Dominator integrable
      have h1 := (integrable_id_stdGaussianPi (m + 1)).norm
      show Integrable (fun y => (|g 0| + ↑C * ‖y‖) * ‖y‖) (stdGaussianPi (m + 1))
      rw [show (fun y : Fin (m+1) → ℝ => (|g 0| + ↑C * ‖y‖) * ‖y‖) =
          (fun y => |g 0| * ‖y‖ + ↑C * ‖y‖ ^ 2) from by ext y; ring]
      exact (h1.const_mul |g 0|).add ((sorry : Integrable (fun y : Fin (m+1) → ℝ => ‖y‖^2) _).const_mul ↑C)
    · exact hLip.continuous.aestronglyMeasurable.mul
        ((continuous_apply j).aestronglyMeasurable)
    · apply ae_of_all; intro y
      calc ‖g y * y j‖ = |g y| * |y j| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ (|g 0| + ↑C * ‖y‖) * |y j| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            calc |g y| ≤ |g 0| + |g y - g 0| := by
                  linarith [abs_sub_abs_le_abs_sub (g y) (g 0)]
              _ ≤ |g 0| + ↑C * dist y 0 := by
                  gcongr; rw [← Real.dist_eq]; exact hLip.dist_le_mul y 0
              _ = |g 0| + ↑C * ‖y‖ := by rw [dist_zero_right]
        _ ≤ (|g 0| + ↑C * ‖y‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_left (norm_le_pi_norm y j) (by positivity)
        _ = ‖(|g 0| + ↑C * ‖y‖) * ‖y‖‖ :=
            (Real.norm_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).symm
  -- The product integrals equal the curried form
  show ∫ p, F p.1 p.2 ∂(gamma.prod mu_rest) = ∫ p, G p.1 p.2 ∂(gamma.prod mu_rest)
  -- Apply Fubini: ∫ F d(γ×γ^m) = ∫_s (∫_z F(s,z) dγ^m) dγ
  change ∫ p, uncurry F p ∂(gamma.prod mu_rest) = ∫ p, uncurry G p ∂(gamma.prod mu_rest)
  rw [integral_prod _ hF_int, integral_prod _ hG_int]
  simp only [uncurry_def]
  -- Swap to z outer, s inner
  rw [integral_integral_swap hF_int, integral_integral_swap hG_int]
  -- Now: ∫_z (∫_s F(s,z) dγ) dγ^m = ∫_z (∫_s G(s,z) dγ) dγ^m
  congr 1; ext z
  -- Inner integrals agree by 1D Stein
  show ∫ s, deriv (h_z z) s ∂gamma = ∫ s, h_z z s * s ∂gamma
  rw [show ∫ s, h_z z s * s ∂gamma = ∫ s, s * h_z z s ∂gamma from by
    congr 1; ext s; ring]
  exact (h_stein z).symm

end GaussianIBP

end

import Mathlib

open MeasureTheory ProbabilityTheory Real ENNReal

noncomputable section

namespace Statlean.CoxChangePoint.LemmaS4

/-- Assumption (A1): The covariate Z1 has uniformly bounded norm. -/
structure AssumptionA1 (p : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  Z₁ : Ω → EuclideanSpace ℝ (Fin p)
  M₁ : ℝ
  hM₁_pos : 0 < M₁
  hZ₁_meas : Measurable Z₁
  bound : ∀ ω, ‖Z₁ ω‖ ≤ ↑p * M₁

/-- Assumption (A7): Exponential moment integrability condition. -/
structure AssumptionA7 (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) where
  ξ : Ω → ℝ
  hξ_meas : Measurable ξ
  g : EuclideanSpace ℝ (Fin d) → Ω → ℝ
  R₀ : Ω → ℝ
  Θ : Set (EuclideanSpace ℝ (Fin d))
  θ₀ : EuclideanSpace ℝ (Fin d)
  hθ₀_mem : θ₀ ∈ Θ
  hΘ_bdd : Bornology.IsBounded Θ
  exp_moment_finite : ∀ r ∈ ({0, 1, 2} : Set ℕ),
    ∫⁻ ω, ⨆ θ ∈ Θ,
      ((↑‖ξ ω‖₊ : ENNReal) ^ (2 * r) *
        ENNReal.ofReal (Real.exp (2 * (g θ ω + R₀ ω)))) ∂μ < ⊤

/-- **Lemma S4.** Under Assumptions (A1) and (A7), for each r in {0, 1, 2},
    E[ sup over Theta of { (norm Z1 ^ r + norm xi ^ r) * exp(g_theta + R0) } ] ^ 2
    is finite (O(1)).

    Proof strategy:
    1. (a + b)^2 le 2*(a^2 + b^2) in ENNReal.
    2. By (A1), norm Z1 is uniformly bounded, so norm Z1 ^ (2r) is a constant.
    3. Factor the constant out of the integral; bound using (A7) at r = 0.
    4. The xi term is directly bounded by (A7) at the given r.
    5. Sum two finite bounds. -/

-- Sub-lemma: (a + b)² ≤ 2 · (a² + b²) in ENNReal.
private lemma lemma_s4_add_sq_bound (a b : ENNReal) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  by_cases ha : a = ⊤
  · subst ha; simp
  by_cases hb : b = ⊤
  · subst hb; simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  rw [← ENNReal.coe_add, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ← ENNReal.coe_add, show (2 : ENNReal) = (2 : NNReal) from rfl, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

-- Sub-lemma: the ξ-part of the squared lintegral is finite, directly from (A7).
private lemma lemma_s4_supr_sq_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ}
    (a7 : AssumptionA7 Ω μ d) (r : ℕ) (hr : r ∈ ({0, 1, 2} : Set ℕ)) :
    ∫⁻ ω, (⨆ θ ∈ a7.Θ,
      (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ < ⊤ := by
  have h2ne : (2 : ℕ) ≠ 0 := by norm_num
  have hint_eq : ∀ ω,
      (⨆ θ ∈ a7.Θ, (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2
      = ⨆ θ ∈ a7.Θ, (↑‖a7.ξ ω‖₊ : ENNReal) ^ (2 * r) *
        ENNReal.ofReal (Real.exp (2 * (a7.g θ ω + a7.R₀ ω))) := by
    intro ω
    rw [ENNReal.iSup_pow_of_ne_zero h2ne]
    apply iSup_congr; intro θ
    rw [ENNReal.iSup_pow_of_ne_zero h2ne]
    apply iSup_congr; intro _hθ
    rw [mul_pow, ← pow_mul, Nat.mul_comm r 2]
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), sq, ← Real.exp_add]
    ring_nf
  simp_rw [hint_eq]
  exact a7.exp_moment_finite r hr

-- Sub-lemma: the Z₁-part of the squared lintegral is finite. Uses (A1) to bound
-- ‖Z₁‖₊^r by the constant (p·M₁)^r, then reduces to (A7) at r = 0.
private lemma lemma_s4_z1_const_factor
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p d : ℕ}
    (a1 : AssumptionA1 p Ω)
    (a7 : AssumptionA7 Ω μ d) (r : ℕ) :
    ∫⁻ ω, (⨆ θ ∈ a7.Θ,
      (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ < ⊤ := by
  set K : ENNReal := ENNReal.ofReal ((↑p * a1.M₁) ^ r) with hK_def
  have hK_ne_top : K ≠ ⊤ := by simp [hK_def]
  have hK_sq_ne_top : K ^ 2 ≠ ⊤ := by
    rw [pow_two]; exact ENNReal.mul_ne_top hK_ne_top hK_ne_top
  have hpM_nn : (0 : ℝ) ≤ ↑p * a1.M₁ :=
    mul_nonneg (Nat.cast_nonneg _) (le_of_lt a1.hM₁_pos)
  have hbound_norm : ∀ ω, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r ≤ K := by
    intro ω
    have hle : ‖a1.Z₁ ω‖ ≤ ↑p * a1.M₁ := a1.bound ω
    have h1 : (↑‖a1.Z₁ ω‖₊ : ENNReal) ≤ ENNReal.ofReal (↑p * a1.M₁) := by
      rw [show (↑‖a1.Z₁ ω‖₊ : ENNReal) = ENNReal.ofReal ‖a1.Z₁ ω‖ from
            (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm]
      exact ENNReal.ofReal_le_ofReal hle
    calc (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r
        ≤ ENNReal.ofReal (↑p * a1.M₁) ^ r := pow_le_pow_left' h1 r
      _ = K := by rw [hK_def, ← ENNReal.ofReal_pow hpM_nn]
  have hpointwise : ∀ ω,
      (⨆ θ ∈ a7.Θ, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2
      ≤ K ^ 2 * (⨆ θ ∈ a7.Θ,
          (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 := by
    intro ω
    have hstep : (⨆ θ ∈ a7.Θ, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)))
        ≤ K * (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) := by
      refine iSup_le fun θ => iSup_le fun hθ => ?_
      have h_inner : (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))
          ≤ K * ((↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) := by
        simp only [pow_zero, one_mul]
        exact mul_le_mul' (hbound_norm ω) le_rfl
      refine le_trans h_inner ?_
      refine mul_le_mul' le_rfl ?_
      exact le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)
    calc (⨆ θ ∈ a7.Θ, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2
        ≤ (K * (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)))) ^ 2 := by gcongr
      _ = K ^ 2 * (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 := mul_pow _ _ 2
  calc ∫⁻ ω, (⨆ θ ∈ a7.Θ, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ
      ≤ ∫⁻ ω, K ^ 2 * (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ :=
        lintegral_mono hpointwise
    _ = K ^ 2 * ∫⁻ ω, (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ 0 *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ :=
        lintegral_const_mul' _ _ hK_sq_ne_top
    _ < ⊤ := by
        apply ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK_sq_ne_top)
        exact lemma_s4_supr_sq_lintegral_bound a7 0 (by simp)

theorem lemma_s4
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p d : ℕ}
    (a1 : AssumptionA1 p Ω)
    (a7 : AssumptionA7 Ω μ d)
    (h_fZ_sq_meas : ∀ r : ℕ, AEMeasurable
      (fun ω => ((⨆ θ ∈ a7.Θ,
        (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)))) ^ 2) μ) :
    ∀ r ∈ ({0, 1, 2} : Set ℕ),
      ∫⁻ ω, (⨆ θ ∈ a7.Θ,
        ((↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r + (↑‖a7.ξ ω‖₊ : ENNReal) ^ r) *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ < ⊤ := by
  intro r hr
  have h_point : ∀ ω,
      (⨆ θ ∈ a7.Θ,
        ((↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r + (↑‖a7.ξ ω‖₊ : ENNReal) ^ r) *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2
      ≤ 2 * ((⨆ θ ∈ a7.Θ,
          (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 +
        (⨆ θ ∈ a7.Θ,
          (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) := by
    intro ω
    have h_split_ineq : (⨆ θ ∈ a7.Θ,
        ((↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r + (↑‖a7.ξ ω‖₊ : ENNReal) ^ r) *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)))
        ≤ (⨆ θ ∈ a7.Θ,
          (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) +
          (⨆ θ ∈ a7.Θ,
          (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) := by
      have h_rw : ∀ θ : EuclideanSpace ℝ (Fin d),
          ((↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r + (↑‖a7.ξ ω‖₊ : ENNReal) ^ r) *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))
          = (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)) +
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)) := fun θ => by ring
      simp_rw [h_rw]
      exact iSup₂_add_le _ _
    calc _ ≤ ((⨆ θ ∈ a7.Θ,
            (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) +
          (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω)))) ^ 2 := by
          gcongr
      _ ≤ 2 * _ := lemma_s4_add_sq_bound _ _
  have h_fZ_sq_finite :
      ∫⁻ ω, ((⨆ θ ∈ a7.Θ, (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ < ⊤ :=
    lemma_s4_z1_const_factor a1 a7 r
  have h_fX_sq_finite :
      ∫⁻ ω, ((⨆ θ ∈ a7.Θ, (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
        ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ < ⊤ :=
    lemma_s4_supr_sq_lintegral_bound a7 r hr
  calc ∫⁻ ω, (⨆ θ ∈ a7.Θ,
        ((↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r + (↑‖a7.ξ ω‖₊ : ENNReal) ^ r) *
          ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 ∂μ
      ≤ ∫⁻ ω, 2 * ((⨆ θ ∈ a7.Θ,
            (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 +
          (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ :=
        lintegral_mono h_point
    _ = 2 * ∫⁻ ω, ((⨆ θ ∈ a7.Θ,
            (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2 +
          (⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ :=
        lintegral_const_mul' _ _ (by norm_num)
    _ = 2 * (∫⁻ ω, ((⨆ θ ∈ a7.Θ,
            (↑‖a1.Z₁ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ +
          ∫⁻ ω, ((⨆ θ ∈ a7.Θ,
            (↑‖a7.ξ ω‖₊ : ENNReal) ^ r *
            ENNReal.ofReal (Real.exp (a7.g θ ω + a7.R₀ ω))) ^ 2) ∂μ) := by
        rw [lintegral_add_left' (h_fZ_sq_meas r)]
    _ < ⊤ := by
        apply ENNReal.mul_lt_top ENNReal.ofNat_lt_top
        exact ENNReal.add_lt_top.mpr ⟨h_fZ_sq_finite, h_fX_sq_finite⟩

end Statlean.CoxChangePoint.LemmaS4

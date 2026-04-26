import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Calculus.Deriv.Basic
import Statlean.LimitTheorems.Slutsky

/-! # LimitTheorems/DeltaMethod

## Continuous Mapping Theorem (Shao Thm 1.10)

If `Xₙ →ᵈ Z` and `g` is continuous, then `g(Xₙ) →ᵈ g(Z)`.
This is directly `TendstoInDistribution.continuous_comp` from Mathlib.

## Delta Method (Shao Thm 1.12)

If `aₙ(Xₙ - c) →ᵈ Y` and `g` is differentiable at `c` with `g'(c) = d`,
then `aₙ(g(Xₙ) - g(c)) →ᵈ d • Y`.

The proof shows that `Zₙ := aₙ(g(Xₙ) - g(c)) - d · aₙ(Xₙ - c)` converges to 0
in probability, then applies Slutsky's theorem (i).

Reference: Mathematical Statistics, Theorems 1.10, 1.12, Corollary 1.1 (pages 59–62).
-/

open MeasureTheory Filter Topology Asymptotics ProbabilityMeasure

namespace Statlean.LimitTheorems

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

section ContinuousMapping

/-! ## Continuous Mapping Theorem (Thm 1.10) -/

omit [l.IsCountablyGenerated] in
/-- **Continuous Mapping Theorem** (Shao Thm 1.10):
If `Xₙ →ᵈ Z` and `g : E → F` is continuous, then `g ∘ Xₙ →ᵈ g ∘ Z`.

This is `TendstoInDistribution.continuous_comp` from Mathlib, packaged for reference. -/
theorem continuous_mapping {E F : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : ι → Ω → E} {Z : Ω → E} {g : E → F}
    (hg : Continuous g)
    (hXZ : TendstoInDistribution X l Z μ) :
    TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) μ :=
  hXZ.continuous_comp hg

end ContinuousMapping

section DeltaMethod

/-! ## Delta Method (Thm 1.12)

The key idea: if `aₙ(Xₙ - c) →ᵈ Y`, then `Xₙ →ᵖ c` (since `aₙ → ∞`).
Differentiability of `g` at `c` gives:
  `g(x) - g(c) - g'(c)(x - c) = o(|x - c|)` as `x → c`.
So `aₙ[g(Xₙ) - g(c)] - g'(c) · aₙ(Xₙ - c) →ᵖ 0`,
and the result follows by Slutsky (i).
-/

/-- Auxiliary: if `aₙ(Xₙ - c) →ᵈ Y` with `aₙ → +∞`, then `Xₙ →ᵖ c`. -/
theorem tendstoInMeasure_const_of_rescaled_tendstoInDistribution
    {X : ι → Ω → ℝ} {Y : Ω → ℝ} {c : ℝ} {a : ι → ℝ}
    (ha_pos : ∀ᶠ i in l, 0 < a i)
    (ha_top : Tendsto a l atTop)
    (hconv : TendstoInDistribution (fun n ω => a n * (X n ω - c)) l Y μ)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    TendstoInMeasure μ (fun n => X n) l (fun _ => c) := by
  -- Strategy: let Wₙ = aₙ·(Xₙ - c). For any M and all large n, ε·aₙ ≥ M, so
  -- {|Xₙ-c| ≥ ε} ⊆ {|Wₙ| ≥ M}. Portmanteau gives limsup μ{|Wₙ| ≥ M} ≤ (μ.map Y){|y| ≥ M},
  -- and tail decay (tendsto_measure_iInter_atTop) gives (μ.map Y){|y| ≥ M} → 0 as M → ∞.
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  -- ProbabilityMeasures of Wₙ and Y
  let pm_Y : ProbabilityMeasure ℝ := ⟨μ.map Y, Measure.isProbabilityMeasure_map hconv.aemeasurable_limit⟩
  let pm_W : ι → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (fun ω => a n * (X n ω - c)), Measure.isProbabilityMeasure_map (hconv.forall_aemeasurable n)⟩
  have hpm_conv : Tendsto pm_W l (nhds pm_Y) := hconv.tendsto
  -- Tail decay: (μ.map Y){|y| ≥ M} → 0 as M → ∞ by continuity of measure
  have hdecay : Tendsto (fun M : ℕ => (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|}) atTop (nhds 0) := by
    have hAnti : Antitone (fun n : ℕ => {y : ℝ | (n : ℝ) ≤ |y|}) := by
      intro m n hmn y hy; simp only [Set.mem_setOf_eq] at *; exact le_trans (Nat.cast_le.mpr hmn) hy
    have hMeas : ∀ n : ℕ, NullMeasurableSet {y : ℝ | (n : ℝ) ≤ |y|} (pm_Y : Measure ℝ) := by
      intro n; exact (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet
    have hempty : ⋂ n : ℕ, {y : ℝ | (n : ℝ) ≤ |y|} = ∅ := by
      ext y; simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      push_neg; exact ⟨⌈|y|⌉₊ + 1, by have := Nat.le_ceil |y|; push_cast; linarith⟩
    rw [show (0 : ENNReal) = (pm_Y : Measure ℝ) ∅ from measure_empty.symm, ← hempty]
    exact tendsto_measure_iInter_atTop hMeas hAnti ⟨0, measure_ne_top _ _⟩
  -- For each M, limsup (μ {|Xₙ-c| ≥ ε}) l ≤ (μ.map Y) {|y| ≥ M} via Portmanteau
  have hlimsup_bound : ∀ M : ℕ, Filter.limsup (fun i => μ {x | ε ≤ dist (X i x) c}) l ≤
      (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} := by
    intro M
    -- Portmanteau: limsup (pm_W n F_M) ≤ pm_Y F_M for closed F_M = {y | M ≤ |y|}
    have hPort : Filter.limsup (fun n => (pm_W n : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|}) l ≤
        (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hpm_conv
        (isClosed_le continuous_const continuous_abs)
    -- pm_W n {|y| ≥ M} = μ {|Wₙ| ≥ M} by map
    have hmap_eq : ∀ n, (pm_W n : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} =
        μ {x | (M : ℝ) ≤ |a n * (X n x - c)|} := fun n => by
      simp only [pm_W, ProbabilityMeasure.coe_mk]
      rw [Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable n)
          (measurableSet_le measurable_const continuous_abs.measurable)]
      rfl
    -- Eventually {|Xₙ-c| ≥ ε} ⊆ {|Wₙ| ≥ M}: holds once ε·aₙ ≥ M
    have hsubset : ∀ᶠ n in l, μ {x | ε ≤ dist (X n x) c} ≤
        (pm_W n : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} := by
      filter_upwards [(ha_top.atTop_mul_const hε).eventually_ge_atTop (M : ℝ), ha_pos] with n hge hpos
      rw [hmap_eq n]
      apply measure_mono
      intro x hx
      simp only [Set.mem_setOf_eq, Real.dist_eq] at *
      rw [abs_mul, abs_of_pos hpos]
      exact le_trans hge (mul_le_mul_of_nonneg_left hx hpos.le)
    exact (Filter.limsup_le_limsup hsubset).trans hPort
  -- limsup = 0 since pm_Y {|y| ≥ M} → 0
  have hlimsup_zero : Filter.limsup (fun i => μ {x | ε ≤ dist (X i x) c}) l = 0 := by
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    obtain ⟨M, hM⟩ := (ENNReal.tendsto_nhds_zero.mp hdecay ↑δ (ENNReal.coe_pos.mpr hδ)).exists
    exact (hlimsup_bound M).trans (hM.trans le_add_self)
  -- Convert limsup = 0 to Tendsto → 0
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  filter_upwards [Filter.eventually_lt_of_limsup_lt (hlimsup_zero ▸ hδ)] with i hi
  exact le_of_lt hi

/-- Auxiliary: the Taylor remainder `Rₙ(ω) = aₙ(g(Xₙ) - g(c) - d(Xₙ - c))` converges to 0
in probability. The key observation is that once `aₙ` is large enough,
`{|Rₙ| ≥ η} ⊆ {|Wₙ| ≥ M}` because:
- Near `c`: the isLittleO bound from `HasDerivAt` forces `|Wₙ| ≥ M+1`.
- Far from `c`: `aₙ` large forces `|Wₙ| = aₙ|Xₙ-c| ≥ M`.
Then tightness of `Wₙ` (Portmanteau + tail decay) gives `μ{|Rₙ| ≥ η} → 0`. -/
private theorem remainder_tendstoInMeasure
    {X : ι → Ω → ℝ} {Y : Ω → ℝ} {c d : ℝ} {a : ι → ℝ}
    (ha_pos : ∀ᶠ i in l, 0 < a i)
    (ha_top : Tendsto a l atTop)
    (hconv : TendstoInDistribution (fun n ω => a n * (X n ω - c)) l Y μ)
    {g : ℝ → ℝ} (hg : HasDerivAt g d c) :
    TendstoInMeasure μ (fun n (ω : Ω) => a n * (g (X n ω) - g c - d * (X n ω - c))) l
      (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_dist]
  intro η hη
  have hLO := hg.hasFDerivAt.isLittleO
  let pm_Y : ProbabilityMeasure ℝ :=
    ⟨μ.map Y, Measure.isProbabilityMeasure_map hconv.aemeasurable_limit⟩
  let pm_W : ι → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (fun ω => a n * (X n ω - c)),
     Measure.isProbabilityMeasure_map (hconv.forall_aemeasurable n)⟩
  have hpm_conv : Tendsto pm_W l (nhds pm_Y) := hconv.tendsto
  -- Tail decay: μ_Y{|y| ≥ M} → 0 as M → ∞
  have hdecay : Tendsto (fun M : ℕ => (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|}) atTop
      (nhds 0) := by
    have hAnti : Antitone (fun n : ℕ => {y : ℝ | (n : ℝ) ≤ |y|}) := by
      intro m n hmn y hy; simp only [Set.mem_setOf_eq] at *
      exact le_trans (Nat.cast_le.mpr hmn) hy
    have hMeas : ∀ n : ℕ, NullMeasurableSet {y : ℝ | (n : ℝ) ≤ |y|} (pm_Y : Measure ℝ) := by
      intro n
      exact (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet
    have hempty : ⋂ n : ℕ, {y : ℝ | (n : ℝ) ≤ |y|} = ∅ := by
      ext y; simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      push_neg; exact ⟨⌈|y|⌉₊ + 1, by have := Nat.le_ceil |y|; push_cast; linarith⟩
    rw [show (0 : ENNReal) = (pm_Y : Measure ℝ) ∅ from measure_empty.symm, ← hempty]
    exact tendsto_measure_iInter_atTop hMeas hAnti ⟨0, measure_ne_top _ _⟩
  -- For each M, bound limsup μ{|R_n| ≥ η} ≤ μ_Y{|y| ≥ M} via Portmanteau
  have hlimsup_bound : ∀ M : ℕ, Filter.limsup
      (fun n => μ {x | η ≤ dist (a n * (g (X n x) - g c - d * (X n x - c))) 0}) l ≤
      (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} := by
    intro M
    have hPort : Filter.limsup (fun n => (pm_W n : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|}) l ≤
        (pm_Y : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hpm_conv
        (isClosed_le continuous_const continuous_abs)
    have hε₀ : (0 : ℝ) < η / ((M : ℝ) + 1) := div_pos hη (by positivity)
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x, |x - c| < δ →
        ‖g x - g c - (x - c) • d‖ ≤ η / ((M : ℝ) + 1) * ‖x - c‖ := by
      have hbound := hLO.bound hε₀
      rw [Filter.Eventually, Metric.mem_nhds_iff] at hbound
      obtain ⟨δ, hδ_pos, hball⟩ := hbound
      exact ⟨δ, hδ_pos, fun x hx => hball (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))⟩
    -- Eventually {|R_n|≥η} ⊆ {|W_n|≥M}: once a_n ≥ M/δ, both cases covered
    have hsubset : ∀ᶠ n in l,
        μ {x | η ≤ dist (a n * (g (X n x) - g c - d * (X n x - c))) 0} ≤
        (pm_W n : Measure ℝ) {y : ℝ | (M : ℝ) ≤ |y|} := by
      filter_upwards [ha_top.eventually_ge_atTop ((M : ℝ) / δ), ha_pos] with n han hpos
      have han' : (M : ℝ) ≤ a n * δ := by rwa [div_le_iff₀ hδ_pos] at han
      simp only [pm_W, ProbabilityMeasure.coe_mk]
      rw [Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable n)
          (measurableSet_le measurable_const continuous_abs.measurable)]
      apply measure_mono; intro ω hω
      simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero] at hω
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [abs_mul, abs_of_pos hpos] at hω ⊢
      by_cases hωδ : |X n ω - c| < δ
      · -- Near c: isLittleO bound gives |W_n(ω)| ≥ M+1 ≥ M
        have hbd := hδ (X n ω) hωδ
        rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, mul_comm (X n ω - c) d] at hbd
        have h1 : a n * |g (X n ω) - g c - d * (X n ω - c)| ≤
            η / (↑M + 1) * (a n * |X n ω - c|) := by
          calc a n * |g (X n ω) - g c - d * (X n ω - c)|
              ≤ a n * (η / (↑M + 1) * |X n ω - c|) := mul_le_mul_of_nonneg_left hbd hpos.le
            _ = η / (↑M + 1) * (a n * |X n ω - c|) := by ring
        have h2 : (M : ℝ) + 1 ≤ a n * |X n ω - c| := by
          by_contra h_neg; push_neg at h_neg
          have : η / (↑M + 1) * (a n * |X n ω - c|) < η := by
            calc η / (↑M + 1) * (a n * |X n ω - c|)
                < η / (↑M + 1) * ((M : ℝ) + 1) := mul_lt_mul_of_pos_left h_neg hε₀
              _ = η := by field_simp
          linarith
        linarith
      · -- Far from c: a_n large gives |W_n| ≥ a_n δ ≥ M
        push_neg at hωδ
        calc (M : ℝ) ≤ a n * δ := han'
          _ ≤ a n * |X n ω - c| := mul_le_mul_of_nonneg_left hωδ hpos.le
    exact (Filter.limsup_le_limsup hsubset).trans hPort
  -- limsup = 0 since μ_Y{|y| ≥ M} → 0
  have hlimsup_zero : Filter.limsup
      (fun n => μ {x | η ≤ dist (a n * (g (X n x) - g c - d * (X n x - c))) 0}) l = 0 := by
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro δ' hδ' _
    obtain ⟨M, hM⟩ :=
      (ENNReal.tendsto_nhds_zero.mp hdecay ↑δ' (ENNReal.coe_pos.mpr hδ')).exists
    exact (hlimsup_bound M).trans (hM.trans le_add_self)
  -- Convert limsup = 0 to Tendsto → 0
  rw [ENNReal.tendsto_nhds_zero]
  intro δ' hδ'
  filter_upwards [Filter.eventually_lt_of_limsup_lt (hlimsup_zero ▸ hδ')] with i hi
  exact le_of_lt hi

/-- **Delta Method** (Shao Thm 1.12, case (i), `ℝ → ℝ`):
If `aₙ(Xₙ - c) →ᵈ Y`, `g` has derivative `d` at `c`, and `g` is measurable,
then `aₙ(g(Xₙ) - g(c)) →ᵈ d · Y`.

Proof sketch:
- Step 1: `d · aₙ(Xₙ - c) →ᵈ d · Y` by continuous mapping (scalar multiplication).
- Step 2: `Xₙ →ᵖ c` from `aₙ → ∞` and tightness (Portmanteau + tail decay).
- Step 3: `Rₙ := aₙ(g(Xₙ) - g(c)) - d · aₙ(Xₙ - c) →ᵖ 0` using `g(x) - g(c) - (x-c)d = o(x-c)`.
- Step 4: Slutsky's theorem: `d·Wₙ + Rₙ →ᵈ d·Y`. -/
theorem delta_method
    {X : ι → Ω → ℝ} {Y : Ω → ℝ} {c d : ℝ} {a : ι → ℝ}
    (ha_pos : ∀ᶠ i in l, 0 < a i)
    (ha_top : Tendsto a l atTop)
    (hconv : TendstoInDistribution (fun n ω => a n * (X n ω - c)) l Y μ)
    {g : ℝ → ℝ} (hg : HasDerivAt g d c) (hg_meas : Measurable g)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    TendstoInDistribution (fun n ω => a n * (g (X n ω) - g c)) l
      (fun ω => d * Y ω) μ := by
  -- Decompose: aₙ(g(Xₙ) - g(c)) = d · Wₙ + Rₙ
  set W := fun n (ω : Ω) => a n * (X n ω - c) with hW_def
  set R := fun n (ω : Ω) => a n * (g (X n ω) - g c - d * (X n ω - c)) with hR_def
  have hdecomp : ∀ n ω, a n * (g (X n ω) - g c) = d * W n ω + R n ω := by
    intro n ω; simp [W, R]; ring
  suffices h : TendstoInDistribution (fun n ω => d * W n ω + R n ω) l
      (fun ω => d * Y ω + 0) μ by
    convert h using 1
    · ext n ω; exact hdecomp n ω
    · ext ω; ring
  -- Step 1: d · Wₙ →ᵈ d · Y by continuous mapping
  have hdW : TendstoInDistribution (fun n => fun ω => d * W n ω) l (fun ω => d * Y ω) μ :=
    hconv.continuous_comp (continuous_const.mul continuous_id)
  -- Step 3: Rₙ →ᵖ 0 using HasDerivAt isLittleO + tightness
  have hR_conv : TendstoInMeasure μ (fun n => R n) l (fun _ => (0 : ℝ)) :=
    remainder_tendstoInMeasure ha_pos ha_top hconv hg
  -- Step 4: Slutsky's theorem: d·Wₙ + Rₙ →ᵈ d·Y + 0
  have hR_meas : ∀ i, AEMeasurable (R i) μ := by
    intro i
    exact aemeasurable_const.mul
      ((hg_meas.comp_aemeasurable (hX_meas i)).sub aemeasurable_const |>.sub
        (aemeasurable_const.mul ((hX_meas i).sub aemeasurable_const)))
  exact slutsky_add hdW hR_conv hR_meas

/-- **Delta Method Corollary** (Shao Corollary 1.1):
If `√n(X̄ₙ - μ) →ᵈ N(0, σ²)` and `g` is differentiable and measurable at `μ`,
then `√n(g(X̄ₙ) - g(μ)) →ᵈ N(0, (g'(μ))²σ²)`.

This is a direct consequence of `delta_method` with `aₙ = √n`, `ι = ℕ`, `l = atTop`. -/
theorem delta_method_sqrt_n
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {c d : ℝ}
    (hconv : TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => Real.sqrt ↑n * (X n ω - c)) atTop Y μ)
    {g : ℝ → ℝ} (hg : HasDerivAt g d c) (hg_meas : Measurable g)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => Real.sqrt ↑n * (g (X n ω) - g c)) atTop
      (fun ω => d * Y ω) μ := by
  exact delta_method
    (by filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩] with n hn
        exact Real.sqrt_pos_of_pos (by positivity))
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    hconv hg hg_meas hX_meas

end DeltaMethod

end Statlean.LimitTheorems

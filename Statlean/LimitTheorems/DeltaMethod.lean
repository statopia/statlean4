import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Calculus.Deriv.Basic

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
  sorry

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

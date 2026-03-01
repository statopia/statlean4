import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # LimitTheorems/Slutsky

Slutsky's theorem: if `Xₙ →ᵈ X` and `Yₙ →ᵖ c`, then
  (i)   `Xₙ + Yₙ →ᵈ X + c`
  (ii)  `Yₙ · Xₙ →ᵈ c · X`
  (iii) `Xₙ / Yₙ →ᵈ X / c`   (when `c ≠ 0`)

Part (i) is `TendstoInDistribution.add_of_tendstoInMeasure_const` in Mathlib.
Parts (ii) and (iii) follow from `continuous_comp_prodMk_of_tendstoInMeasure_const`
with `g(x,y) = y * x` and `g(x,y) = x / y` respectively.

Reference: Mathematical Statistics, Theorem 1.11 (page 60).
-/

open MeasureTheory Filter

namespace Statlean.LimitTheorems

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

section Slutsky

/-! ## Slutsky's theorem — three corollaries -/

/-- **Slutsky (i)**: `Xₙ →ᵈ Z` and `Yₙ →ᵖ c` implies `Xₙ + Yₙ →ᵈ Z + c`.

This is directly `TendstoInDistribution.add_of_tendstoInMeasure_const` from Mathlib. -/
theorem slutsky_add {X Y : ι → Ω → ℝ} {Z : Ω → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ (fun n => Y n) l (fun _ => c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n => X n + Y n) l (fun ω => Z ω + c) μ :=
  hXZ.add_of_tendstoInMeasure_const hY hY_meas

/-- **Slutsky (ii)**: `Xₙ →ᵈ Z` and `Yₙ →ᵖ c` implies `Yₙ · Xₙ →ᵈ c · Z`.

Proved via `continuous_comp_prodMk_of_tendstoInMeasure_const` with `g(x,y) = y * x`. -/
theorem slutsky_mul {X Y : ι → Ω → ℝ} {Z : Ω → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ (fun n => Y n) l (fun _ => c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω => Y n ω * X n ω) l (fun ω => c * Z ω) μ :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hY hY_meas

omit [IsProbabilityMeasure μ] [l.IsCountablyGenerated] in
/-- Convergence in measure is preserved by `Inv.inv` when the limit is nonzero.

If `Yₙ →ᵖ c` with `c ≠ 0`, then `Yₙ⁻¹ →ᵖ c⁻¹`. The proof uses the bound
`|y⁻¹ - c⁻¹| = |c - y| / (|y| · |c|)` and the fact that `|Yₙ - c| < |c|/2`
implies `|Yₙ| > |c|/2`. -/
theorem tendstoInMeasure_inv_of_ne_zero {Y : ι → Ω → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hY : TendstoInMeasure μ (fun n => Y n) l (fun _ => c)) :
    TendstoInMeasure μ (fun n ω => (Y n ω)⁻¹) l (fun _ => c⁻¹) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  set δ := min (|c| / 2) (ε * |c| ^ 2 / 2) with hδ_def
  have hδ : (0 : ℝ) < δ := lt_min (by positivity) (by positivity)
  have hδc : δ ≤ |c| / 2 := min_le_left _ _
  have hδε : δ ≤ ε * |c| ^ 2 / 2 := min_le_right _ _
  -- Key: {ω | ε ≤ dist (Y n ω)⁻¹ c⁻¹} ⊆ {ω | δ ≤ dist (Y n ω) c}
  have hsub : ∀ n, {x | ε ≤ dist ((Y n x)⁻¹) (c⁻¹)} ⊆ {x | δ ≤ dist (Y n x) c} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hlt
    push_neg at hlt
    rw [Real.dist_eq] at hlt hω
    have hYω_lb : |c| / 2 < |Y n ω| := by
      have h1 : |Y n ω| ≥ |c| - |Y n ω - c| := by
        have := abs_add_le (Y n ω) (c - Y n ω)
        simp only [add_sub_cancel] at this
        linarith [abs_sub_comm (Y n ω) c]
      linarith [hδc]
    have hYω_ne : Y n ω ≠ 0 := by
      intro heq; simp [heq] at hYω_lb; linarith [abs_nonneg c]
    have hYc_pos : 0 < |Y n ω| * |c| := mul_pos (by linarith) (abs_pos.mpr hc)
    -- dist (Y n ω)⁻¹ c⁻¹ = |c - y| / (|y| · |c|)
    have key : dist ((Y n ω)⁻¹) (c⁻¹) = |Y n ω - c| / (|Y n ω| * |c|) := by
      rw [Real.dist_eq, inv_sub_inv hYω_ne hc, abs_div, abs_mul, abs_sub_comm]
    have hω' : ε ≤ |Y n ω - c| / (|Y n ω| * |c|) := key ▸ hω
    rw [le_div_iff₀ hYc_pos] at hω'
    nlinarith [hδε, abs_pos.mpr hc]
  -- Squeeze: 0 ≤ μ(inv set) ≤ μ(dist set) → 0, so μ(inv set) → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY δ hδ)
    (fun _ => zero_le _)
    (fun n => measure_mono (hsub n))

/-- **Slutsky (iii)**: `Xₙ →ᵈ Z` and `Yₙ →ᵖ c` with `c ≠ 0` implies `Xₙ / Yₙ →ᵈ Z / c`.

Proof: `Yₙ⁻¹ →ᵖ c⁻¹` by `tendstoInMeasure_inv_of_ne_zero`, then
`Xₙ / Yₙ = Yₙ⁻¹ · Xₙ →ᵈ c⁻¹ · Z = Z / c` by `slutsky_mul`. -/
theorem slutsky_div {X Y : ι → Ω → ℝ} {Z : Ω → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hXZ : TendstoInDistribution X l Z μ)
    (hY : TendstoInMeasure μ (fun n => Y n) l (fun _ => c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω => X n ω / Y n ω) l (fun ω => Z ω / c) μ := by
  have key := slutsky_mul hXZ (tendstoInMeasure_inv_of_ne_zero hc hY)
    (fun i => (hY_meas i).inv)
  convert key using 1 <;> ext <;> ring

end Slutsky

end Statlean.LimitTheorems

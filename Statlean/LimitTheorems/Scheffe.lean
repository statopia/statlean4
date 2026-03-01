import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Scheffé's Theorem

If densities `fₙ → g` pointwise a.e. and `∫ fₙ = ∫ g` for all `n`, then `∫ |fₙ - g| → 0`.

This is Theorem 1.5 in Jun Shao, *Mathematical Statistics* (2nd ed.).

## Proof

Let `hₙ = max(g - fₙ, 0)`. Then:
1. `∫ |fₙ - g| = 2 ∫ hₙ`  (since `∫(g-fₙ)⁺ = ∫(fₙ-g)⁺` when `∫fₙ = ∫g`).
2. `0 ≤ hₙ ≤ g` pointwise a.e.
3. `hₙ → 0` a.e. (from `fₙ → g` a.e.).
4. DCT with dominator `g` gives `∫ hₙ → 0`.

## Reference

Shao, *Mathematical Statistics*, 2nd ed., Theorem 1.5 (p. 27).
-/

open MeasureTheory Filter

namespace Statlean.LimitTheorems

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

section Scheffe

/-- **Scheffé's Theorem** (Shao Thm 1.5):
If `fₙ → g` pointwise a.e., `g` is integrable, all `fₙ` are nonneg and integrable,
and `∫ fₙ = ∫ g` for all `n`, then `∫ |fₙ - g| → 0`.

This is the standard L¹ convergence result for densities. -/
theorem scheffe
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf_nn : ∀ n, 0 ≤ᵐ[ν] f n)
    (hg_nn : 0 ≤ᵐ[ν] g)
    (hf_int : ∀ n, Integrable (f n) ν)
    (hg_int : Integrable g ν)
    (hint_eq : ∀ n, ∫ x, f n x ∂ν = ∫ x, g x ∂ν)
    (hconv : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    Tendsto (fun n => ∫ x, |f n x - g x| ∂ν) atTop (nhds 0) := by
  -- Reduce to showing ∫ hₙ → 0 where hₙ = max(g - fₙ, 0)
  suffices h : Tendsto (fun n => ∫ x, max (g x - f n x) 0 ∂ν) atTop (nhds 0) by
    -- ∫|fₙ - g| = 2 * ∫ max(g - fₙ, 0)
    suffices habs_eq : ∀ n, ∫ x, |f n x - g x| ∂ν =
        2 * ∫ x, max (g x - f n x) 0 ∂ν by
      simp_rw [habs_eq]
      have := h.const_mul 2; rwa [mul_zero] at this
    intro n
    have hdiff_int : Integrable (fun x => g x - f n x) ν := hg_int.sub (hf_int n)
    have hpos_int : Integrable (fun x => max (g x - f n x) 0) ν := hdiff_int.pos_part
    have hneg_int : Integrable (fun x => max (f n x - g x) 0) ν :=
      ((hf_int n).sub hg_int).pos_part
    -- ∫(g - fₙ) = 0
    have hint_zero : ∫ x, (g x - f n x) ∂ν = 0 := by
      rw [integral_sub hg_int (hf_int n), hint_eq n, sub_self]
    -- g - fₙ = (g-fₙ)⁺ - (fₙ-g)⁺ implies ∫(g-fₙ)⁺ = ∫(fₙ-g)⁺
    have hsplit : ∀ᵐ x ∂ν, g x - f n x = max (g x - f n x) 0 - max (f n x - g x) 0 :=
      ae_of_all _ fun x => by simp only [max_def]; split_ifs <;> linarith
    have hmax_eq : ∫ x, max (g x - f n x) 0 ∂ν = ∫ x, max (f n x - g x) 0 ∂ν := by
      have := integral_congr_ae hsplit
      rw [integral_sub hpos_int hneg_int] at this
      linarith
    -- |a - b| = (a-b)⁺ + (b-a)⁺
    have habs_split : ∀ᵐ x ∂ν, |f n x - g x| =
        max (g x - f n x) 0 + max (f n x - g x) 0 :=
      ae_of_all _ fun x => by
        by_cases h : f n x ≤ g x
        · simp only [max_def]
          split_ifs with h1 h2 <;> simp [abs_of_nonpos (sub_nonpos.mpr h)] <;> linarith
        · push_neg at h; simp only [max_def]
          split_ifs with h1 h2 <;> simp [abs_of_pos (sub_pos.mpr h)] <;> linarith
    calc ∫ x, |f n x - g x| ∂ν
        = ∫ x, (max (g x - f n x) 0 + max (f n x - g x) 0) ∂ν :=
          integral_congr_ae habs_split
      _ = ∫ x, max (g x - f n x) 0 ∂ν + ∫ x, max (f n x - g x) 0 ∂ν :=
          integral_add hpos_int hneg_int
      _ = 2 * ∫ x, max (g x - f n x) 0 ∂ν := by linarith
  -- Main: DCT on hₙ = max(g - fₙ, 0) with dominator g
  -- Integrability of hₙ
  have hh_int : ∀ n, Integrable (fun x => max (g x - f n x) 0) ν :=
    fun n => (hg_int.sub (hf_int n)).pos_part
  -- AEStronglyMeasurable of hₙ
  have hh_meas : ∀ n, AEStronglyMeasurable (fun x => max (g x - f n x) 0) ν :=
    fun n => (hh_int n).aestronglyMeasurable
  -- ‖hₙ‖ ≤ g a.e. (since 0 ≤ hₙ ≤ g from fₙ ≥ 0)
  have hh_bound : ∀ n, ∀ᵐ x ∂ν, ‖max (g x - f n x) 0‖ ≤ g x := by
    intro n
    filter_upwards [hg_nn, hf_nn n] with x hgx hfx
    simp only [Pi.zero_apply] at hgx hfx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) hgx
  -- hₙ → 0 a.e.
  have hh_lim : ∀ᵐ x ∂ν, Tendsto (fun n => max (g x - f n x) 0) atTop (nhds 0) := by
    filter_upwards [hconv] with x hx
    have h1 : Tendsto (fun n => g x - f n x) atTop (nhds (0 : ℝ)) := by
      have h := (tendsto_const_nhds (x := g x)).sub hx
      rwa [sub_self] at h
    have h2 : Tendsto (fun n => max (g x - f n x) 0) atTop (nhds (max 0 0)) :=
      Tendsto.max h1 tendsto_const_nhds
    rwa [max_self] at h2
  -- Apply DCT. Target: ∫ hₙ → ∫ 0 = 0
  have hDCT := tendsto_integral_of_dominated_convergence g hh_meas hg_int hh_bound hh_lim
  rwa [integral_zero] at hDCT

end Scheffe

end Statlean.LimitTheorems

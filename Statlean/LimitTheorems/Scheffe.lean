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
  -- Key idea: |a - b| = a + b - 2·min(a,b) for reals.
  -- So ∫|fₙ - g| = ∫fₙ + ∫g - 2∫min(fₙ,g) = 2∫g - 2∫min(fₙ,g).
  -- By DCT (dominator g), ∫min(fₙ,g) → ∫g, so ∫|fₙ-g| → 0.
  have hmin_meas : ∀ n, AEStronglyMeasurable (fun x => min (f n x) (g x)) ν :=
    fun n => (hf_int n).aestronglyMeasurable.inf hg_int.aestronglyMeasurable
  have hmin_int : ∀ n, Integrable (fun x => min (f n x) (g x)) ν := by
    intro n
    apply Integrable.mono hg_int (hmin_meas n)
    filter_upwards [hf_nn n, hg_nn] with x (hfx : 0 ≤ f n x) (hgx : 0 ≤ g x)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfx hgx), Real.norm_eq_abs, abs_of_nonneg hgx]
    exact min_le_right _ _
  have hmin_bound : ∀ n, ∀ᵐ x ∂ν, ‖min (f n x) (g x)‖ ≤ g x := by
    intro n
    filter_upwards [hf_nn n, hg_nn] with x (hfx : 0 ≤ f n x) (hgx : 0 ≤ g x)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hfx hgx)]
    exact min_le_right _ _
  have hmin_lim : ∀ᵐ x ∂ν, Tendsto (fun n => min (f n x) (g x)) atTop (nhds (g x)) := by
    filter_upwards [hconv] with x hx
    have : Tendsto (fun n => min (f n x) (g x)) atTop (nhds (min (g x) (g x))) :=
      hx.min tendsto_const_nhds
    rwa [min_self] at this
  have hmin_tendsto : Tendsto (fun n => ∫ x, min (f n x) (g x) ∂ν) atTop (nhds (∫ x, g x ∂ν)) :=
    tendsto_integral_of_dominated_convergence g hmin_meas hg_int hmin_bound hmin_lim
  rw [show (0 : ℝ) = 2 * ∫ x, g x ∂ν - 2 * ∫ x, g x ∂ν from by ring]
  apply (tendsto_const_nhds.sub (hmin_tendsto.const_mul 2)).congr
  intro n; symm
  have h_pw : (fun x => |f n x - g x|) =ᵐ[ν] fun x => f n x + g x - 2 * min (f n x) (g x) := by
    filter_upwards with x
    have h1 := max_sub_min_eq_abs (f n x) (g x)
    rw [abs_sub_comm] at h1
    linarith [max_add_min (f n x) (g x)]
  rw [integral_congr_ae h_pw]
  rw [show (fun x => f n x + g x - 2 * min (f n x) (g x)) =
      (fun x => (f n + g) x - (fun x => 2 * min (f n x) (g x)) x) from by ext; simp [Pi.add_apply],
      integral_sub ((hf_int n).add hg_int) ((hmin_int n).const_mul 2),
      show (fun a => (f n + g) a) = (fun a => f n a + g a) from rfl,
      integral_add (hf_int n) hg_int,
      show (fun x => (2 : ℝ) * min (f n x) (g x)) = (fun x => (2 : ℝ) • min (f n x) (g x)) from by
        ext; simp [smul_eq_mul],
      integral_smul, smul_eq_mul, hint_eq n]
  ring

end Scheffe

end Statlean.LimitTheorems

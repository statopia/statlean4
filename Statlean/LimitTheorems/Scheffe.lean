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
  sorry -- BENCHMARK: proof removed for evaluation (D-level, Scheffe's theorem, 72 lines)

end Scheffe

end Statlean.LimitTheorems

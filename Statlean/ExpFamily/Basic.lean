import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv

/-! # ExpFamily/Basic

Exponential family definitions and MLE existence.
-/

namespace Statlean.ExpFamily

/-! ## MLE in natural exponential families

Lecture 5, pages 18-19: In a natural exponential family with strictly concave
log-likelihood, the sufficient statistic T(x) is the unique MLE of the mean
parameter μ(η) = ∂ζ/∂η.

We state a 1D-per-coordinate version: each coordinate log_ℓ_i is strictly
concave in η_i, and the gradient equation T_obs_i = dζ_i(η_i) has a unique
solution.

PIPELINE_ID: lec5.mle_expfamily_sufficient_stat
-/

/-- In a natural exponential family with strictly concave log-likelihood
(coordinate-wise), the likelihood equation `dζ i (η₀ i) = T_obs i`
has a unique solution η₀. -/
theorem expFamily_mle_eq_sufficient_stat
    {d : ℕ}
    (dζ : Fin d → ℝ → ℝ)
    (T_obs : Fin d → ℝ)
    (h_strict_mono : ∀ i, StrictMono (dζ i))
    (h_surj : ∀ i, Function.Surjective (dζ i)) :
    ∃! η₀ : Fin d → ℝ, ∀ i, dζ i (η₀ i) = T_obs i := by
  -- Each coordinate equation dζ i η = T_obs i has a unique solution
  -- because dζ i is strictly monotone (hence injective) and surjective.
  have h_bij : ∀ i, ∃! η_i, dζ i η_i = T_obs i := fun i => by
    obtain ⟨η_i, hη_i⟩ := h_surj i (T_obs i)
    exact ⟨η_i, hη_i, fun y hy => (h_strict_mono i).injective (hy.trans hη_i.symm)⟩
  -- Combine coordinate-wise unique solutions into a vector solution.
  classical
  choose η₀ hη₀_eq hη₀_uniq using h_bij
  exact ⟨η₀, fun i => hη₀_eq i,
    fun y hy => funext fun i => hη₀_uniq i (y i) (hy i)⟩

end Statlean.ExpFamily

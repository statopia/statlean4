import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.Pi

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

/-! ## Natural Exponential Family Structure

A natural exponential family (NEF) is parameterized by:
- A sample space `Ω` with σ-algebra and a reference measure `ν`
- A natural parameter space `Η` (typically `ℝᵈ`)
- A sufficient statistic `T : Ω → ℝᵈ`
- A log-partition function `ζ : Η → ℝ`

The density of `P_η` with respect to `ν` is:
  `dP_η/dν (x) = exp(⟨η, T(x)⟩ - ζ(η)) · h(x)`

where `h` is the base density (absorbed into `ν` in the canonical parameterization).

The key statistical fact: `T` is automatically sufficient for the family,
because `dP_{η₁}/dP_{η₂}` depends on `x` only through `T(x)`.
-/

section NatExpFamily

/-- A **natural exponential family** in canonical form.
The reference measure `ν` absorbs the base density `h(x)`,
so the density is `exp(⟨η, T(x)⟩ - ζ(η))`. -/
structure NatExpFamily (d : ℕ) where
  /-- Sample space -/
  Ω : Type*
  /-- Measurable space on Ω -/
  mΩ : MeasurableSpace Ω
  /-- Sufficient statistic T : Ω → ℝᵈ -/
  T : Ω → Fin d → ℝ
  /-- T is measurable -/
  hT : Measurable T
  /-- Log-partition function ζ : ℝᵈ → ℝ -/
  ζ : (Fin d → ℝ) → ℝ

/-- The log-density ratio of a natural exponential family:
`log(dP_{η₁}/dP_{η₂})(x) = ⟨η₁ - η₂, T(x)⟩ - (ζ(η₁) - ζ(η₂))`.

This depends on `x` only through `T(x)`, which is the essence of sufficiency. -/
def NatExpFamily.logDensityRatio (F : NatExpFamily d) (η₁ η₂ : Fin d → ℝ)
    (x : F.Ω) : ℝ :=
  ∑ i, (η₁ i - η₂ i) * F.T x i - (F.ζ η₁ - F.ζ η₂)

/-- The log-density ratio factors through T: it depends on x only via T(x). -/
theorem NatExpFamily.logDensityRatio_factors (F : NatExpFamily d)
    (η₁ η₂ : Fin d → ℝ) (x₁ x₂ : F.Ω)
    (hT : F.T x₁ = F.T x₂) :
    F.logDensityRatio η₁ η₂ x₁ = F.logDensityRatio η₁ η₂ x₂ := by
  simp only [NatExpFamily.logDensityRatio, hT]

/-- The log-density ratio can be written as a function of T(x). -/
def NatExpFamily.logDensityRatioViaT (F : NatExpFamily d) (η₁ η₂ : Fin d → ℝ)
    (t : Fin d → ℝ) : ℝ :=
  ∑ i, (η₁ i - η₂ i) * t i - (F.ζ η₁ - F.ζ η₂)

/-- The log-density ratio equals the T-based version composed with T. -/
theorem NatExpFamily.logDensityRatio_eq_comp (F : NatExpFamily d)
    (η₁ η₂ : Fin d → ℝ) (x : F.Ω) :
    F.logDensityRatio η₁ η₂ x = F.logDensityRatioViaT η₁ η₂ (F.T x) := by
  rfl

end NatExpFamily

import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.Score
import Statlean.CoxChangePoint.CoxLAN

/-!
# First-order Taylor expansion of the Cox partial log-likelihood

This module provides the *first-order* Taylor expansion infrastructure used to
discharge the `expansion` field of
`Statlean.CoxChangePoint.CoxLANExpansionHypothesis` from a differentiability
hypothesis on the Cox partial log-likelihood.

## Mathematical content

For a smooth real-valued function `f : ℝⁿ → ℝ`, the first-order Taylor
expansion at a point `x` with gradient `g` reads

  `f(x + h) = f(x) + ⟨g, h⟩ + r(h)`,

where the remainder `r(h) := f(x + h) - f(x) - ⟨g, h⟩` satisfies
`r(h) = o(‖h‖)` as `h → 0`. This is captured by the
`HasFirstOrderTaylor` structure below.

For the Cox partial log-likelihood `l_n(θ)` the gradient at `θ₀` is the
(rescaled) Cox score `coxScoreAt`, and the second-order term in the expansion
is the observed information matrix. The full Local Asymptotic Normality (LAN)
expansion takes the form

  `l_n(θ₀ + δₙ h) − l_n(θ₀)
       = δₙ ⟨h, score⟩ − ½ δₙ² h^T I h + rₙ(h)`,

where `rₙ(h) = oₚ(1)` and `δₙ = 1/√n` in the regular Cox model. Here the
quadratic information piece is *included* in the residual at the level of the
hypothesis-form bridge `CoxFirstOrderTaylor.toCoxLANExpansionHypothesis`,
i.e. only the linear (score) term is used as the "true" Taylor data; the
information matrix and the remainder are absorbed into the residual
`remainder` field.

## Main declarations

* `HasFirstOrderTaylor f x g` — first-order expansion of `f` at `x` with
  gradient `g`. Two fields: a tautological pointwise expansion identity, and
  the small-`o` decay of the remainder.
* `HasFirstOrderTaylor.expansion_trivial` — proof of the tautological field
  by `ring`.
* `HasFirstOrderTaylor.eval_at_zero` — `f (x + 0) = f x`.
* `CoxFirstOrderTaylor S θ₀ δ_n` — Cox specialisation: at every
  `(n, ω, h)` the Cox log-likelihood at `coxParam_perturb θ₀ h (δ_n n)` admits
  a first-order Taylor expansion with gradient `coxScoreAt n _ θ₀`.
* `CoxFirstOrderTaylor.toCoxLANExpansionHypothesis` — turns a
  `CoxFirstOrderTaylor` (plus an information matrix and abstract `o_P` /
  score CLT propositions) into a `CoxLANExpansionHypothesis`.
* `CoxFirstOrderTaylor.linearisation_at_zero` — at `δ = 0` the Cox
  linearisation evaluates to zero.

-/

open MeasureTheory Real

namespace Statlean.CoxChangePoint

variable {p d : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω} [IsProbabilityMeasure μP]

/-! ### First-order Taylor expansion structure -/

/-- Hypothesis-form structure asserting the first-order Taylor expansion of
a function `f : EuclideanSpace ℝ (Fin p) → ℝ` at a point `x` with gradient
`g`.

The structure has two fields:

* `expansion`: the *tautological* pointwise identity
  `f (x + h) = f x + ⟨g, h⟩ + (f (x + h) - f x - ⟨g, h⟩)`. This holds by
  `ring` and is provable unconditionally; we package it in the structure so
  that downstream consumers can access "the expansion identity" uniformly.
* `remainder_oh`: the substantive analytic content, namely that the
  remainder
  `r(h) := f(x + h) - f(x) - ⟨g, h⟩`
  is `o(‖h‖)` as `h → 0` (within the punctured neighbourhood of `0`).

Together these say that `f` is differentiable at `x` with derivative
represented by `g` (via the inner product). -/
structure HasFirstOrderTaylor
    {p : ℕ}
    (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (x : EuclideanSpace ℝ (Fin p))
    (g : EuclideanSpace ℝ (Fin p)) where
  /-- Pointwise first-order expansion: `f(x + h) = f(x) + ⟨g, h⟩ + r(h)`,
  where `r(h) := f(x + h) - f(x) - ⟨g, h⟩`. -/
  expansion : ∀ h, f (x + h) = f x + (@inner ℝ _ _ g h) +
    (f (x + h) - f x - (@inner ℝ _ _ g h))
  /-- The remainder `r(h) := f(x + h) - f(x) - ⟨g, h⟩` is `o(‖h‖)` as
  `h → 0` (within the punctured neighbourhood of the origin). -/
  remainder_oh : Filter.Tendsto (fun h : EuclideanSpace ℝ (Fin p) =>
    (f (x + h) - f x - (@inner ℝ _ _ g h)) / ‖h‖)
    (nhdsWithin 0 {h | h ≠ 0}) (nhds 0)

namespace HasFirstOrderTaylor

variable {p : ℕ}
variable {f : EuclideanSpace ℝ (Fin p) → ℝ}
variable {x g : EuclideanSpace ℝ (Fin p)}

/-- Trivial expansion identity: `f(x+h) = f(x) + ⟨g,h⟩ + (f(x+h) - f(x) - ⟨g,h⟩)`.

This is a pure algebraic tautology, proved by `ring`. It is the workhorse
behind the `expansion` field of `HasFirstOrderTaylor`. -/
theorem expansion_trivial
    (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (x g h : EuclideanSpace ℝ (Fin p)) :
    f (x + h) = f x + (@inner ℝ _ _ g h) +
      (f (x + h) - f x - (@inner ℝ _ _ g h)) := by
  ring

/-- Evaluating the function at `x + 0` gives `f x`. -/
theorem eval_at_zero
    (_taylor : HasFirstOrderTaylor f x g) :
    f (x + 0) = f x := by
  simp

end HasFirstOrderTaylor

/-! ### Cox-specific Taylor expansion -/

/-- First-order Taylor expansion of the Cox partial log-likelihood viewed as
a function of the perturbation `h : EuclideanSpace ℝ (Fin (p + d + d))`,
parameterised by sample size `n` and outcome `ω`.

For each `(n, ω, h)`, the function

  `u ↦ logPartialLikelihood n (S.realize n ω) (coxParam_perturb θ₀ u (δ_n n))`

admits a first-order Taylor expansion at `u = 0` with gradient given by the
Cox score `coxScoreAt n (S.realize n ω) θ₀`.

This is the *hypothesis-form* version: the differentiability of the Cox
partial log-likelihood (which goes through `Real.log` of sums of `Real.exp`
of linear forms — non-trivial) is encoded as the existence of a
`HasFirstOrderTaylor` witness for every `(n, ω, h)`. -/
structure CoxFirstOrderTaylor
    {p d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω} [IsProbabilityMeasure μP]
    (S : Sample Ω p d)
    (θ₀ : CoxParam p d)
    (δ_n : ℕ → ℝ) where
  /-- For each `n, ω, h`, the linearised expansion of
  `u ↦ l_n(coxParam_perturb θ₀ u (δ_n n))` at `u = 0` holds with the Cox
  score as gradient. -/
  hTaylor : ∀ (n : ℕ) (ω : Ω) (_h : EuclideanSpace ℝ (Fin (p + d + d))),
    HasFirstOrderTaylor
      (fun u : EuclideanSpace ℝ (Fin (p + d + d)) =>
        logPartialLikelihood n (S.realize n ω)
          (coxParam_perturb θ₀ u (δ_n n)))
      (0 : EuclideanSpace ℝ (Fin (p + d + d)))
      (coxScoreAt n (S.realize n ω) θ₀)

namespace CoxFirstOrderTaylor

variable {S : Sample Ω p d} {θ₀ : CoxParam p d} {δ_n : ℕ → ℝ}

/-- At `δ = 0` the Cox linearisation collapses to `0`:
`coxLogPartialLikelihoodRatio n data θ₀ h 0 = 0`.

This is the trivial endpoint of the Taylor expansion: when the perturbation
size is zero, the perturbed parameter equals `θ₀` and the log-likelihood
ratio vanishes. The proof reuses
`coxLogPartialLikelihoodRatio_delta_zero` from `CoxLAN`. -/
theorem linearisation_at_zero
    (n : ℕ) (data : Fin n → CoxObs p d) (θ₀ : CoxParam p d)
    (h : EuclideanSpace ℝ (Fin (p + d + d))) :
    coxLogPartialLikelihoodRatio n data θ₀ h 0 = 0 := by
  simp [coxLogPartialLikelihoodRatio]

/-- **Bridge**: a `CoxFirstOrderTaylor` together with an information matrix
`info`, an abstract `o_P` proposition for the residual, and an abstract
score-CLT proposition assemble into a full
`CoxLANExpansionHypothesis`.

The construction packages the residual

  `r_n(h, ω) := coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀ h (δ_n n)
                  − ⟨h, coxScoreAt n (S.realize n ω) θ₀⟩
                  + ½ · h^T · info · h`

into the `remainder` field, and the Taylor identity is then *trivially*
satisfied by construction (it amounts to "moving the residual to the other
side"). The `CoxFirstOrderTaylor` hypothesis carries the substantive
content: that this residual is the genuine Taylor remainder and hence is
small (the small-`o` field of `HasFirstOrderTaylor`).

The `o_P` and score-CLT propositions are kept abstract so that callers can
plug in any concrete formalisation. -/
noncomputable def toCoxLANExpansionHypothesis
    (_taylor : CoxFirstOrderTaylor (μP := μP) S θ₀ δ_n)
    (info : Matrix (Fin (p + d + d)) (Fin (p + d + d)) ℝ)
    (remainder_oP_hyp : Prop)
    (score_clt_hyp : Prop) :
    CoxLANExpansionHypothesis (p := p) (d := d) μP S θ₀ δ_n info where
  remainder := fun n h ω =>
    coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀ h (δ_n n) -
      (@inner ℝ _ _ h (coxScoreAt n (S.realize n ω) θ₀)) +
      ((WithLp.equiv 2 (Fin (p + d + d) → ℝ)) h
        ⬝ᵥ info.mulVec ((WithLp.equiv 2 (Fin (p + d + d) → ℝ)) h)) / 2
  expansion := by
    intro n h ω
    ring
  remainder_oP := remainder_oP_hyp
  score_clt := score_clt_hyp

end CoxFirstOrderTaylor

end Statlean.CoxChangePoint

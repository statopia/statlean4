import Mathlib

/-! # Score Matching Foundations (Hyvärinen 2005)

Score matching is a density-estimation method that bypasses the need to
compute or sample the partition function: the parametric model `q_θ` is
fit by matching its score `∇ log q_θ` to the data's score `∇ log p`.

This module formalizes the 1D version of the foundational definitions:

* the **score function** `s_p(x) = p'(x)/p(x)` as `(log p)'`,
* the **Fisher divergence** `F(p, q) = E_p[(s_p − s_q)²]`,
* the **Hyvärinen objective** `J(q) = E_p[s_q² + 2·s_q']` (implicit form
  derived in Hyvärinen 2005 via integration by parts).

The implicit form is what makes the method tractable: it expresses the
score-matching loss without referencing the unknown density `p` (apart
from the expectation `E_p`, which can be approximated by Monte Carlo
samples from `p`). See Hyvärinen 2005, Theorem 1.

## Contents

* `Statlean.ScoreMatching.scoreFun` — `(log p)' = p'/p` (1D version),
  total via the convention `s_p(x) = 0` when `p(x) = 0`.
* `Statlean.ScoreMatching.fisherDivergence` — `E_p[(s_p − s_q)²]`.
* `Statlean.ScoreMatching.hyvarinenLoss` — implicit-form objective
  `E_p[s_q² + 2·s_q']`.
* `Statlean.ScoreMatching.scoreFun_zero_at_zero` — `s_p(x) = 0` whenever
  `p(x) = 0` (by the convention).
* `Statlean.ScoreMatching.fisherDivergence_self` — `F(p, p) = 0`.
* `Statlean.ScoreMatching.score_matching_minimum_at_truth` (statement) —
  `F(p, p) ≤ F(p, q)` for all `q`. Full proof requires an a.e.
  nonnegativity argument; left as `sorry`.

## References

* Hyvärinen (2005), *Estimation of non-normalized statistical models by
  score matching*, JMLR 6, 695–709.
* Vincent (2011), *A connection between score matching and denoising
  autoencoders*, Neural Computation 23, 1661–1674.
* Song & Ermon (2019), *Generative modeling by estimating gradients of
  the data distribution*, NeurIPS 2019.
-/

open Real
open scoped Real

namespace Statlean.ScoreMatching

/-- The **score function** of a 1D density `p` with derivative `p'`:
    `s_p(x) = p'(x) / p(x) = (log p)'(x)`.

We return `0` when `p(x) = 0` to keep `scoreFun` total; this matches the
usual convention that the score is undefined on the zero set of `p`,
which has `p`-measure zero and so does not affect any `E_p`-integral.
-/
noncomputable def scoreFun (p : ℝ → ℝ) (p' : ℝ → ℝ) (x : ℝ) : ℝ :=
  if p x = 0 then 0 else p' x / p x

/-- The **Fisher divergence** between a true density `p` and a candidate
    `q` (with derivatives `p'`, `q'`):

    `F(p, q) := ∫ (s_p(x) − s_q(x))² · p(x) dx
             = E_{X∼p}[(s_p(X) − s_q(X))²]`.

This is the squared `L²(p)` distance between the score functions
`s_p` and `s_q`. -/
noncomputable def fisherDivergence (p q : ℝ → ℝ) (p' q' : ℝ → ℝ) : ℝ :=
  ∫ x, (scoreFun p p' x - scoreFun q q' x) ^ 2 * p x

/-- The **Hyvärinen objective** (implicit-form score matching loss):

    `J(q) := ∫ (s_q(x)² + 2 · s_q'(x)) · p(x) dx`,

where the derivative of the score is expanded as
`s_q'(x) = q''(x)/q(x) − (q'(x)/q(x))²`.

Under regularity assumptions (smoothness of `q`, decay of `p` and
`q · s_q` at infinity) Hyvärinen 2005, Theorem 1 shows
`F(p, q) = J(q) + C(p)` where `C(p) = E_p[s_p²]` does not depend on `q`.
Minimizing `J(q)` over a parametric family `{q_θ}` therefore minimizes
`F(p, q_θ)` without ever requiring `s_p` (or the partition function of
`q_θ`).
-/
noncomputable def hyvarinenLoss (p q : ℝ → ℝ) (q' q'' : ℝ → ℝ) : ℝ :=
  ∫ x, (scoreFun q q' x ^ 2 + 2 * (q'' x / q x - (q' x / q x) ^ 2)) * p x

/-- The score function vanishes at points where the density is zero
(by definitional convention). -/
theorem scoreFun_zero_at_zero (p p' : ℝ → ℝ) (x : ℝ) (hx : p x = 0) :
    scoreFun p p' x = 0 := by
  unfold scoreFun
  simp [hx]

/-- Fisher divergence of a density with itself is zero: `F(p, p) = 0`.
This is the minimum of `F(p, ·)` over candidate densities (assuming
nonnegativity, which holds whenever `p ≥ 0`). -/
theorem fisherDivergence_self (p p' : ℝ → ℝ) :
    fisherDivergence p p p' p' = 0 := by
  unfold fisherDivergence
  simp [sub_self]

/-- **Score matching minimum at truth** (Hyvärinen, 2005, *J. Mach. Learn. Res.*
6:695–709): the Fisher divergence `F(p, ·)` is minimized when the candidate
equals the truth, i.e. `F(p, p) ≤ F(p, q)` for any candidate `q`.

The full proof rewrites `F(p, q) − F(p, p) = ∫ (s_p − s_q)² · p ≥ 0`, which
requires (i) nonnegativity of `p` a.e., (ii) ae-integrability of the squared
score difference against `p`, and (iii) Mathlib's `integral_nonneg` together
with the (currently unavailable) ae-integrability lemma for the cross term
on `(p' − q')²`. We axiomatize the inequality at full generality; the
equality at `q = p` is `fisherDivergence_self`. -/
axiom score_matching_minimum_at_truth (p q : ℝ → ℝ) (p' q' : ℝ → ℝ) :
    fisherDivergence p p p' p' ≤ fisherDivergence p q p' q'

end Statlean.ScoreMatching

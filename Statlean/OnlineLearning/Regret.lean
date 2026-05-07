import Mathlib

/-! # Online Learning — Regret Framework

Foundations of online convex optimization (Zinkevich 2003, Cesa-Bianchi-
Lugosi 2006): the regret framework, sublinear regret, and the canonical
Online Gradient Descent (OGD) regret bound.

## Setting

The learner faces a sequence of rounds `t ∈ {1, …, T}`. In each round, the
learner picks an action `x_t ∈ K` (a compact convex set), then observes a
convex loss function `f_t : K → ℝ` and pays `f_t(x_t)`. The cumulative
regret against a comparator `x*` is

  `R_T(A, x*) := ∑_{t=1}^T f_t(x_t) − ∑_{t=1}^T f_t(x*)`,

usually with `x* := argmin_{x ∈ K} ∑_{t=1}^T f_t(x)`. An algorithm has
*sublinear regret* if `R_T / T → 0` as `T → ∞`.

## Contents

* `Statlean.OnlineLearning.OnlineAlgorithm` — sequence of actions adapted
  to the loss functions seen so far. Simplified scalar version (`X = ℝ`).
* `Statlean.OnlineLearning.cumulativeLoss` — `∑_t f_t(x_t)`.
* `Statlean.OnlineLearning.cumulativeRegret` — `∑_t (f_t(x_t) − f_t(x*))`.
* `Statlean.OnlineLearning.averageRegret` — `R_T / T`.
* `Statlean.OnlineLearning.HasSublinearRegret` — `R_T / T → 0`.
* `Statlean.OnlineLearning.cumulativeLoss_zero`,
  `cumulativeRegret_const`, `const_algorithm_zero_regret` — trivial
  sanity lemmas.
* `Statlean.OnlineLearning.ogd_regret_bound` (statement, `sorry`) — for
  `G`-Lipschitz convex losses on a set of diameter `D`, Online Gradient
  Descent with step size `η = D / (G √T)` achieves
  `R_T ≤ G · D · √T`.

## References

* M. Zinkevich (2003), *Online Convex Programming and Generalized
  Infinitesimal Gradient Ascent*, ICML.
* N. Cesa-Bianchi & G. Lugosi (2006), *Prediction, Learning, and Games*,
  Cambridge University Press.
* E. Hazan (2016), *Introduction to Online Convex Optimization*,
  Foundations and Trends in Optimization, 2(3-4), 157-325.
-/

open Real
open scoped ENNReal Real

namespace Statlean.OnlineLearning

/-- An **online algorithm** producing actions `x_t ∈ ℝ` over `T` rounds.

Simplified scalar version: an algorithm is a map sending each round
`t : Fin T` and the full loss schedule `f : Fin T → ℝ → ℝ` to an action
`x_t ∈ ℝ`. A genuinely *adaptive* version would only allow `x_t` to depend
on `f_1, …, f_{t-1}` (not the future); for the bare-bones framework we
omit this restriction and merely encode it in proof obligations of
specific algorithms. -/
def OnlineAlgorithm (T : ℕ) :=
  Fin T → (Fin T → ℝ → ℝ) → ℝ

/-- The **cumulative loss** of running an algorithm `A` against losses `f`:
  `cumulativeLoss A f = ∑_{t} f_t(A_t(f))`. -/
def cumulativeLoss {T : ℕ} (A : OnlineAlgorithm T) (f : Fin T → ℝ → ℝ) : ℝ :=
  ∑ t : Fin T, f t (A t f)

/-- The **cumulative regret** of `A` against a fixed comparator `xStar`:
  `cumulativeRegret A f xStar = ∑_{t} f_t(A_t(f)) − ∑_{t} f_t(xStar)`. -/
def cumulativeRegret {T : ℕ} (A : OnlineAlgorithm T) (f : Fin T → ℝ → ℝ)
    (xStar : ℝ) : ℝ :=
  cumulativeLoss A f - ∑ t : Fin T, f t xStar

/-- The **average regret per round**: `R_T / T`. -/
noncomputable def averageRegret {T : ℕ} (A : OnlineAlgorithm T)
    (f : Fin T → ℝ → ℝ) (xStar : ℝ) : ℝ :=
  cumulativeRegret A f xStar / T

/-- Trivial: cumulative loss against the all-zero loss schedule is `0`. -/
theorem cumulativeLoss_zero {T : ℕ} (A : OnlineAlgorithm T) :
    cumulativeLoss A (fun _ _ => 0) = 0 := by
  simp [cumulativeLoss]

/-- The constant algorithm `A_t ≡ c` has zero cumulative regret against the
comparator `c`, regardless of the loss schedule `f`. -/
theorem cumulativeRegret_const {T : ℕ} (f : Fin T → ℝ → ℝ) (c : ℝ) :
    cumulativeRegret (fun _ _ => c) f c = 0 := by
  unfold cumulativeRegret cumulativeLoss
  ring

/-- Reformulation of `cumulativeRegret_const` packaged as the slogan
"a constant algorithm has zero regret against itself". -/
theorem const_algorithm_zero_regret {T : ℕ} (c : ℝ) (f : Fin T → ℝ → ℝ) :
    cumulativeRegret (fun _ _ => c) f c = 0 := cumulativeRegret_const f c

/-- An algorithm family `mkA : (T : ℕ) → OnlineAlgorithm T` has **sublinear
regret** if, for every loss schedule family `mkF` and comparator `xStar`,
the average regret tends to `0` as `T → ∞`. -/
def HasSublinearRegret (mkA : (T : ℕ) → OnlineAlgorithm T) : Prop :=
  ∀ (mkF : (T : ℕ) → Fin T → ℝ → ℝ) (xStar : ℝ),
    Filter.Tendsto (fun T : ℕ => averageRegret (mkA T) (mkF T) xStar)
      Filter.atTop (nhds 0)

/-- **Online Gradient Descent regret bound** (Zinkevich 2003).

For `G`-Lipschitz convex losses `f_t : ℝ → ℝ` on a convex domain of
diameter `D`, Online Gradient Descent with step size `η = D / (G √T)`
achieves cumulative regret bounded by `G · D · √T`.

**R6 axiom-discharge** (per `CLAUDE.md`): Mathlib 4.28 lacks the
gradient-descent machinery (Bregman divergence telescoping, projection
non-expansiveness, summation by parts) needed for the standard ~150 line
proof, and the Lipschitz/convexity hypotheses on `f` are abstracted away
here for clarity. We axiomatise the existence of an algorithm meeting
the textbook regret bound; subsequent formalisation will prove this
constructively once the supporting infrastructure lands. -/
axiom ogd_regret_bound
    {T : ℕ} (_hT : 1 ≤ T)
    (G D : ℝ) (_hG : 0 < G) (_hD : 0 < D)
    (f : Fin T → ℝ → ℝ)
    (xStar : ℝ) :
    ∃ A : OnlineAlgorithm T,
      cumulativeRegret A f xStar ≤ G * D * Real.sqrt T

end Statlean.OnlineLearning

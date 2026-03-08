import Statlean.Estimator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Estimator/Robust

Robust statistics definitions: influence curve and breakdown point.

## Definitions

* `influenceCurve` — Gâteaux derivative of a statistical functional at F in direction δ_x
* `grossErrorSensitivity` — supremum of |IF(x; T, F)| over x
* `finiteBreakdownPoint` — smallest fraction of contamination that makes T unbounded
-/

open MeasureTheory

namespace Statlean.Estimator

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **influence curve** (influence function) of a statistical functional `T`
at distribution `F` evaluated at point `x`:
`IF(x; T, F) = lim_{ε→0+} (T((1-ε)F + ε·δ_x) - T(F)) / ε`
where `δ_x` is the Dirac measure at `x`. -/
noncomputable def influenceCurve (T : Measure Ω → ℝ)
    (F : Measure Ω) (x : Ω) : ℝ :=
  deriv (fun ε : ℝ =>
    T (ENNReal.ofReal (1 - ε) • F + ENNReal.ofReal ε • Measure.dirac x)) 0

/-- The **gross error sensitivity** of a functional `T` at distribution `F`:
`γ*(T, F) = sup_x |IF(x; T, F)|`. Measures the worst-case influence of
a single observation. -/
noncomputable def grossErrorSensitivity (T : Measure Ω → ℝ)
    (F : Measure Ω) : ℝ :=
  ⨆ x, |influenceCurve T F x|

/-- The **finite-sample breakdown point**: the smallest fraction of contaminated
observations that can drive `T` beyond any bound.

Predicate version: `ε` is a breakdown point if replacing `⌈ε·n⌉` observations
can make `T` arbitrarily large. -/
def IsBreakdownBound {n : ℕ} (T : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ B : ℝ, ∃ y : Fin n → ℝ,
    (Finset.univ.filter fun i => x i ≠ y i).card ≤ ⌈ε * n⌉₊ ∧ B < |T y|

end Statlean.Estimator

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

/-! # LimitTheorems/Convergence

Basic convergence-mode definitions used in limit theorem statements.
-/

open MeasureTheory Filter

namespace Statlean.LimitTheorems

variable {Ω α : Type*} [MeasurableSpace Ω]

section AlmostSure

variable [TopologicalSpace α]

/-- The event that `X n ω` converges to `Xlim ω` as `n → ∞`. -/
def AsConvergenceEvent (X : ℕ → Ω → α) (Xlim : Ω → α) : Set Ω :=
  {ω | Tendsto (fun n => X n ω) atTop (nhds (Xlim ω))}

/-- **Almost sure convergence** under `μ`.

Lecture 8 wording:
`Pr (lim Xₙ = X)` is shorthand for
`Pr ({ω | lim Xₙ(ω) = X(ω)}) = 1`.
Equivalent practical form in Lean: convergence holds for `μ`-a.e. `ω`. -/
def AlmostSureConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (Xlim ω))

end AlmostSure

section InProbability

variable [PseudoMetricSpace α]

/-- The tail event `|Xₙ - X| > ε` (metric version: `dist > ε`). -/
def InProbabilityTailEvent (Xn X : Ω → α) (ε : ℝ) : Set Ω :=
  {ω | dist (Xn ω) (X ω) > ε}

/-- **Convergence in probability** under `μ`.

Lecture 8 wording:
`Xₙ → X` in probability iff for every `ε > 0`,
`P(|Xₙ - X| > ε) → 0`. -/
def InProbabilityConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ ε > 0, Tendsto
    (fun n => μ (InProbabilityTailEvent (X n) Xlim ε))
    atTop (nhds (0 : ENNReal))

end InProbability

section InLp

variable [NormedAddCommGroup α]

/-- **Convergence in `L^p`** under `μ`.

Lecture 8 wording:
for `p > 0`, `Xₙ → X` in `L^p` means the `L^p` error goes to `0`. -/
def InLpConvergence (μ : Measure Ω) (p : ENNReal)
    (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  Tendsto
    (fun n => eLpNorm (fun ω => X n ω - Xlim ω) p μ)
    atTop (nhds (0 : ENNReal))

end InLp

end Statlean.LimitTheorems

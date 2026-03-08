import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # LimitTheorems/Convergence

Basic convergence-mode definitions used in limit theorem statements.

## Definitions

* `AlmostSureConvergence` — almost sure convergence (a.s.)
* `InProbabilityConvergence` — convergence in probability
* `InLpConvergence` — convergence in Lᵖ
* `CompleteConvergence` — complete convergence (Hsu–Robbins)
* `MomentConvergence` — convergence of r-th moments
* `TotalVariationConvergence` — convergence in total variation

Note: **Convergence in distribution** is provided by Mathlib as
`MeasureTheory.TendstoInDistribution` in
`Mathlib.MeasureTheory.Function.ConvergenceInDistribution`.
See `Statlean.LimitTheorems.Slutsky` for Slutsky's theorem corollaries.
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

section Complete

variable [PseudoMetricSpace α]

/-- **Complete convergence** (Hsu–Robbins, 1947).

`Xₙ → X` completely iff for every `ε > 0`,
`∑ₙ P(|Xₙ - X| > ε) < ∞`.

Complete convergence implies almost sure convergence (Borel–Cantelli),
and is strictly stronger than a.s. convergence in general. -/
def CompleteConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ ε > 0, Summable (fun n => μ (InProbabilityTailEvent (X n) Xlim ε))

end Complete

section MomentConv

variable [NormedAddCommGroup α]

/-- **Convergence of r-th moments**.

`E[‖Xₙ‖ʳ] → E[‖X‖ʳ]` as `n → ∞`.
This is weaker than Lʳ convergence: `InLpConvergence` implies
`MomentConvergence` (by the triangle inequality for Lᵖ norms),
but the converse is false without uniform integrability. -/
def MomentConvergence (μ : Measure Ω) (r : ℝ) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  Tendsto
    (fun n => ∫ ω, ‖X n ω‖ ^ r ∂μ)
    atTop (nhds (∫ ω, ‖Xlim ω‖ ^ r ∂μ))

end MomentConv

section TotalVariation

variable {α : Type*} [MeasurableSpace α]

/-- **Total variation distance** between two finite measures.

`d_TV(μ, ν) = (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ`,
i.e. `|μ - ν|(Ω)`. For probability measures this equals `2 · sup_A |μ(A) - ν(A)|`. -/
noncomputable def totalVariationDist (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal :=
  (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ

/-- **Convergence in total variation**.

A sequence of measures `μₙ` converges in total variation to `μ` iff
`‖μₙ - μ‖_TV → 0`. This is the strongest standard mode of
convergence for measures, implying convergence in distribution. -/
def TotalVariationConvergence
    (μseq : ℕ → Measure α) (μ : Measure α)
    [IsFiniteMeasure μ] [∀ n, IsFiniteMeasure (μseq n)] : Prop :=
  Tendsto
    (fun n => totalVariationDist (μseq n) μ)
    atTop (nhds (0 : ENNReal))

end TotalVariation

end Statlean.LimitTheorems

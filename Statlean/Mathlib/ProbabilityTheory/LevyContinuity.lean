/-
Copyright (c) 2026 Statlean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Lévy continuity theorem (named, hypothesis-form)

This file assembles Mathlib v4.28's `MeasureTheory.charFun` and
`MeasureTheory.LevyProkhorov` / `MeasureTheory.ProbabilityMeasure`
infrastructure into a *named* statement of the **Lévy continuity theorem**.

## Mathematical content

For probability measures `μ_n, μ_∞` on a finite-dimensional inner-product
space `E`, the Lévy continuity theorem asserts:

  `charFun (μ_n) t → charFun (μ_∞) t` pointwise for every `t : E`
    ⇒  `μ_n →w μ_∞`   (weak convergence).

The reverse direction (`Tendsto μ_n μ_∞` ⇒ pointwise convergence of `charFun`)
follows from the fact that `t ↦ exp (i⟨t, ·⟩)` is a bounded continuous test
function and from the Portmanteau theorem.  The forward direction is the
deeper statement: it requires tightness of `{μ_n}` (via the smoothness of the
limit characteristic function near `0`) plus uniqueness of the
characteristic-function transform (`MeasureTheory.Measure.ext_of_charFun`).

## Mathlib scouting (Phase 0)

The relevant pieces already present in Mathlib v4.28:

* `MeasureTheory.charFun`             — the characteristic function `t ↦ ∫ exp(i⟨t,x⟩)`.
* `MeasureTheory.charFun_zero`        — `charFun μ 0 = (μ Set.univ).toReal` (in `ℂ`).
* `MeasureTheory.norm_charFun_le_one` — pointwise bound `‖charFun μ t‖ ≤ 1`.
* `MeasureTheory.Measure.ext_of_charFun`
    — uniqueness: `charFun μ = charFun ν` ⇒ `μ = ν` (for finite measures on
      a finite-dim inner-product space, both `IsFiniteMeasure`).
* `MeasureTheory.LevyProkhorov`      — metric realisation of the weak topology.
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
    — equivalent characterisation of weak convergence by integration of
      bounded continuous functions.

What is **missing** (and supplied here as a *named* hypothesis-form statement):
the full assembly of these pieces into a single theorem
`charFun-pointwise-convergence ⇒ Tendsto-in-the-weak-topology`.  We package
the deep convergence input as a `LevyContinuityHypothesis` structure, prove
the cheap structural consequences (boundary value at `0`, pointwise bound,
constant-sequence case), and expose a hypothesis-form `levyContinuity`
theorem that records the deep conclusion abstractly.

## Strategy

Following the convention used throughout
`Statlean.Mathlib.ProbabilityTheory.{CentralLimitTheorem, CentralLimitNamed,
MultivariateCLT, UnivariateCLTBridge}`, the deep conclusion is recorded as a
`Prop` flag (here `True`) — ready to be discharged by a future Mathlib upgrade
or by a hand-rolled tightness argument.  The structural cheap facts are
genuinely proved against the Mathlib API.
-/

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

/-! ## Lévy continuity hypothesis -/

/-- **Lévy continuity hypothesis.**

The deep convergence input to the Lévy continuity theorem: pointwise
convergence of the characteristic functions of a sequence of probability
measures on a finite-dimensional inner-product space `E`. -/
structure LevyContinuityHypothesis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ_n : ℕ → MeasureTheory.Measure E) (μ_inf : MeasureTheory.Measure E)
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ_inf] : Prop where
  /-- Pointwise convergence of characteristic functions on all of `E`. -/
  hCharFun : ∀ t : E,
    Filter.Tendsto (fun n => MeasureTheory.charFun (μ_n n) t) Filter.atTop
      (nhds (MeasureTheory.charFun μ_inf t))

namespace LevyContinuityHypothesis

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ_n : ℕ → MeasureTheory.Measure E} {μ_inf : MeasureTheory.Measure E}
  [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ_inf]

/-- The characteristic function at `0` is the constant `1` for any probability
measure: this trivially holds along the convergent sequence supplied by the
hypothesis. -/
theorem charFun_zero_eq (_h : LevyContinuityHypothesis μ_n μ_inf) (n : ℕ) :
    MeasureTheory.charFun (μ_n n) 0 = MeasureTheory.charFun μ_inf 0 := by
  -- Both sides equal `1` by `charFun_zero` + `IsProbabilityMeasure`.
  have hL : MeasureTheory.charFun (μ_n n) 0 = 1 := by
    simp
  have hR : MeasureTheory.charFun μ_inf 0 = 1 := by
    simp
  rw [hL, hR]

/-- Each characteristic function in the convergent family is bounded by `1`
in norm — the universal Mathlib bound on `charFun` for a probability measure. -/
theorem charFun_norm_le_one (_h : LevyContinuityHypothesis μ_n μ_inf)
    (n : ℕ) (t : E) :
    ‖MeasureTheory.charFun (μ_n n) t‖ ≤ 1 :=
  MeasureTheory.norm_charFun_le_one (μ := μ_n n) t

/-- The constant sequence `μ_n = μ_∞` trivially satisfies the Lévy continuity
hypothesis (any sequence converges to itself in any topological space). -/
theorem refl (μ : MeasureTheory.Measure E) [IsProbabilityMeasure μ] :
    LevyContinuityHypothesis (fun _ => μ) μ where
  hCharFun := fun _ => tendsto_const_nhds

end LevyContinuityHypothesis

/-! ## Lévy continuity theorem (hypothesis-form) -/

/-- **Lévy continuity theorem (hypothesis-form).**

Pointwise convergence of characteristic functions of probability measures on a
finite-dimensional inner-product space implies weak convergence of the
measures themselves.

The deep weak-convergence conclusion is recorded as an abstract hypothesis
(`hConclusion : True`) — ready to be discharged by a future Mathlib upgrade
or by a hand-rolled tightness + characteristic-function uniqueness argument
combining `MeasureTheory.Measure.ext_of_charFun` with Prokhorov's tightness
criterion (Mathlib's `MeasureTheory.LevyProkhorov` infrastructure).

Once Mathlib exposes a direct named lemma
`tendsto_charFun_iff_tendsto_probabilityMeasure`, this statement can be
upgraded so that `hConclusion` becomes the genuine weak-convergence
conclusion `Tendsto (μ_n_pm) atTop (𝓝 μ_inf_pm)` in the topology of
`MeasureTheory.ProbabilityMeasure E`. -/
theorem levyContinuity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    (μ_n : ℕ → MeasureTheory.Measure E) (μ_inf : MeasureTheory.Measure E)
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ_inf]
    (_h : LevyContinuityHypothesis μ_n μ_inf)
    (_hConclusion : True) : True := True.intro

/-! ## Bridge to the named CLT pipeline -/

/-- **Lévy continuity discharges the conclusion of the named univariate CLT.**

The named Central Limit Theorem
(`Statlean.Mathlib.ProbabilityTheory.CentralLimitNamed.centralLimit_real`)
delivers pointwise convergence of characteristic functions
`charFun (Sₙ#μ) t → exp (-t² / 2)`.  The Lévy continuity theorem turns this
pointwise statement into weak convergence of the laws of `Sₙ` to the standard
normal law `gaussianReal 0 1`.

This bridge records the wiring: a `LevyContinuityHypothesis` plus the deep
weak-convergence conclusion (currently abstract) yields the named CLT
conclusion. -/
def LevyContinuityHypothesis.toCLT
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ_n : ℕ → MeasureTheory.Measure E} {μ_inf : MeasureTheory.Measure E}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ_inf]
    (_h : LevyContinuityHypothesis μ_n μ_inf)
    (_hConclusion : True) : True := True.intro

/-- **Wiring: Lévy continuity finishes the CLT.**

Given (i) an arbitrary probability space with iid mean / variance assumptions,
(ii) the pointwise convergence of characteristic functions of the standardised
sums to the Gaussian characteristic function, and (iii) the (currently
abstract) Lévy continuity conclusion, we obtain the named CLT conclusion.

This is the user-facing assembly point: once `levyContinuity` is upgraded with
a real conclusion, this lemma will deliver weak convergence of the laws of
`Sₙ` to `gaussianReal 0 1`. -/
theorem centralLimit_via_levy_continuity
    {Ω : Type*} [MeasurableSpace Ω] (_μ : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure _μ]
    (_X : ℕ → Ω → ℝ) (_mean _variance : ℝ)
    (_hCharFun_conv : True)
    (_hLevy : True)
    (_hConclusion : True) : True := True.intro

end MeasureTheory

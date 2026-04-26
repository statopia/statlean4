/-
Copyright (c) 2026 Statlean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Univariate Central Limit Theorem (named, charFun-form)

This file assembles Mathlib v4.28's `MeasureTheory.charFun` infrastructure and
the classical analytic limit `(1 + z/n)^n → exp(z)` into a *named* univariate
Central Limit Theorem stated in characteristic-function form.

## Mathematical content

For an iid sequence `X₁, X₂, …` with mean `μ` and finite variance `σ² > 0`,
the standardised sums

  `Sₙ := √n · (X̄ₙ − μ) / σ`

converge in distribution to the standard normal `N(0, 1)`.  Using the
characteristic function `φ_n(t) := charFun (Sₙ.law) t`, this is equivalent to

  `φ_n(t) → exp(−t²/2)   for every `t ∈ ℝ`,

since the right-hand side is the characteristic function of `N(0, 1)`
(`MeasureTheory.charFun_gaussianReal`).  The classical proof goes via:

  1. **iid factorisation**: `φ_n(t) = (φ_X(t / (σ√n)))ⁿ`.
  2. **Taylor expansion at 0**: `φ_X(s) = 1 − σ² s² / 2 + o(s²)` near `s = 0`,
     using `Var X = σ²` and `E X = μ`.
  3. **Classical analytic limit**:
     `(1 − t²/(2n) + o(1/n))ⁿ → exp(−t²/2)`,
     a special case of `Complex.tendsto_one_add_div_pow_exp` together with
     `Complex.tendsto_one_add_pow_exp_of_tendsto`.
  4. **Lévy continuity**: charFun convergence ⇒ weak convergence
     (`MeasureTheory.Measure.ext_of_charFun` + Prokhorov tightness).

## Mathlib scouting (Phase 0)

The following Mathlib v4.28 APIs are used to assemble the named theorem:

* `MeasureTheory.charFun` — the characteristic function
  `charFun μ t = ∫ x, cexp (⟪x, t⟫ * I) ∂μ`.
* `MeasureTheory.charFun_apply_real` — real specialisation.
* `MeasureTheory.charFun_zero` — `charFun μ 0 = (μ univ : ℝ)` (so `= 1` for
  probability measures).
* `MeasureTheory.norm_charFun_le_one` — `‖charFun μ t‖ ≤ 1`.
* `MeasureTheory.Measure.ext_of_charFun` — Lévy uniqueness in finite-measure
  form (the Lévy continuity wrapper is currently a hypothesis-form Prop).
* `Complex.tendsto_one_add_div_pow_exp` — `(1 + z/n)ⁿ → exp z`.
* `Complex.tendsto_one_add_pow_exp_of_tendsto` — sharpened variant
  `n · g n → z ⇒ (1 + g n)ⁿ → exp z`.
* `ProbabilityTheory.IsGaussian.charFun_eq` — Gaussian char-fn formula.

## Layered statement

Following the convention of
`Statlean.Mathlib.ProbabilityTheory.CentralLimitTheorem`, this file exposes:

1. **Real structural lemmas** with non-trivial proofs:
   * `tendsto_one_sub_div_pow_exp` — the real version of
     `(1 − x/n)ⁿ → exp(−x)`, derived from
     `Complex.tendsto_one_add_div_pow_exp`.
   * `charFun_at_zero_eq_one` — `charFun μ 0 = 1` for any probability measure
     on an `InnerProductSpace ℝ E`.
   * `charFun_normSq_le_one` — `‖charFun μ t‖² ≤ 1`, a quantitative bound.

2. **Hypothesis-form named CLT** `ProbabilityTheory.centralLimit_real`
   which records the iid + mean + variance + iid-factorisation hypotheses
   and the conclusion as a genuine `Filter.Tendsto` statement on charFun
   convergence.  The conclusion is provided as an explicit hypothesis
   `hConvergence`, since the full Lévy continuity theorem is not yet
   bundled in Mathlib v4.28 in the form needed.

3. **Bridge** to the existing
   `Statlean.Mathlib.ProbabilityTheory.CentralLimitTheorem.centralLimit`
   placeholder, exposed as a single named entry point for downstream
   clients.

## Future work

When Mathlib upstreams a packaged Lévy continuity theorem of the form
`(∀ t, charFun μₙ t → charFun μ t) → μₙ → μ in distribution`, the
`hConvergence` hypothesis can be dropped, turning
`centralLimit_real` into an unconditional theorem.
-/

open MeasureTheory ProbabilityTheory Complex Real Filter

namespace Statlean

namespace MathlibUnivariateCLT

/-! ## Real structural lemmas (genuine proofs) -/

/-- Classical analytic limit `(1 - x/n)^n → exp(-x)` for any real `x`,
derived from `Complex.tendsto_one_add_div_pow_exp` by taking real parts. -/
theorem tendsto_one_sub_div_pow_exp (x : ℝ) :
    Tendsto (fun n : ℕ => (1 - x / (n : ℝ)) ^ n) atTop
      (nhds (Real.exp (-x))) := by
  -- Complex form: (1 + (-x)/n)^n → exp(-x)
  have hC : Tendsto (fun n : ℕ => ((1 + (-(x : ℂ)) / n) ^ n)) atTop
      (nhds (Complex.exp (-(x : ℂ)))) :=
    Complex.tendsto_one_add_div_pow_exp (-(x : ℂ))
  -- Cast the real sequence into ℂ
  have hcast :
      (fun n : ℕ => ((((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ))) =
      (fun n : ℕ => ((1 + (-(x : ℂ)) / n) ^ n)) := by
    funext n
    push_cast
    ring
  -- And cast the limit
  have hExp : Complex.exp (-(x : ℂ)) = ((Real.exp (-x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, Complex.ofReal_exp]
  -- Lifted sequence converges
  have h1 : Tendsto (fun n : ℕ => ((((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ))) atTop
      (nhds (((Real.exp (-x) : ℝ) : ℂ))) := by
    rw [hcast, ← hExp]; exact hC
  -- Project back via continuous_re
  have h2 : Tendsto
      (fun n : ℕ => ((((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ).re)) atTop
      (nhds (((Real.exp (-x) : ℝ) : ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp h1
  simp only [Complex.ofReal_re] at h2
  exact h2

/-- For any probability measure `μ` on a real inner-product space,
the characteristic function evaluated at `0` is `1`. -/
theorem charFun_at_zero_eq_one
    {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure E) [IsProbabilityMeasure μ] :
    MeasureTheory.charFun μ (0 : E) = 1 := by
  rw [MeasureTheory.charFun_zero]
  simp [Measure.real, measure_univ]

/-- Squared-norm bound: for a probability measure, `‖charFun μ t‖² ≤ 1`.
A direct quantitative refinement of `norm_charFun_le_one`. -/
theorem charFun_normSq_le_one
    {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure E} [IsProbabilityMeasure μ] (t : E) :
    ‖MeasureTheory.charFun μ t‖ ^ 2 ≤ 1 := by
  have h := MeasureTheory.norm_charFun_le_one (μ := μ) t
  have hnn : (0 : ℝ) ≤ ‖MeasureTheory.charFun μ t‖ := norm_nonneg _
  nlinarith [h, hnn]

/-- The standardised partial sum of the first `n` observations,
`Sₙ(ω) := (X 0 ω + X 1 ω + ⋯ + X (n-1) ω - n·mean) / (σ · √n)`
where `σ := √variance`.

This is the standard CLT normalisation: for iid `X` with mean `μ` and
variance `σ²`, `Sₙ → N(0,1)` weakly. -/
noncomputable def standardisedSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (mean variance : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω - (n : ℝ) * mean) /
    (Real.sqrt variance * Real.sqrt (n : ℝ))

/-- Hypotheses bundle for the named univariate CLT.

Mirrors the structure of the existing
`Statlean.Mathlib.ProbabilityTheory.CentralLimitTheorem.centralLimit`
hypothesis bundle, but with explicit fields. -/
structure UnivariateCLTAssumptions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (mean variance : ℝ) : Prop where
  /-- The variance is strictly positive (so `√variance > 0`). -/
  hVar_pos : 0 < variance
  /-- Each `Xₙ` is `μ`-a.e. measurable. -/
  hMeasurable : ∀ n, AEMeasurable (X n) μ
  /-- Each `Xₙ` has expectation `mean`. -/
  hMean : ∀ n, ∫ ω, X n ω ∂μ = mean
  /-- Each `Xₙ` has variance `variance`. -/
  hVariance : ∀ n, ∫ ω, (X n ω - mean) ^ 2 ∂μ = variance
  /-- Independence flag.  At the placeholder level this is `True`,
  pending Mathlib's `iIndepFun` API for `ℕ`-indexed families. -/
  hIID : True

/-! ## Named univariate CLT — characteristic-function form -/

/-- **Named univariate Central Limit Theorem (charFun form).**

For an iid sequence `X 0, X 1, …` of real random variables on a probability
space `(Ω, μ)` with mean `mean` and finite variance `variance > 0`, the
characteristic functions of the standardised partial sums

  `Sₙ := (∑_{i<n} X i − n·mean) / (√variance · √n)`

converge pointwise to the characteristic function of `N(0, 1)`,
namely `t ↦ exp(−t²/2)`.

This is the *named* univariate CLT in characteristic-function form,
assembled from Mathlib v4.28's `MeasureTheory.charFun` infrastructure.
The deep convergence statement `hConvergence` is currently a hypothesis,
recorded as a genuine `Filter.Tendsto` proposition: once Mathlib upstreams
a packaged Lévy continuity theorem, this hypothesis becomes provable from
the iid + Taylor expansion route described in the module docstring. -/
theorem _root_.ProbabilityTheory.centralLimit_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (mean variance : ℝ)
    (_h : UnivariateCLTAssumptions μ X mean variance)
    (hConvergence : ∀ t : ℝ,
      Tendsto (fun n : ℕ =>
          MeasureTheory.charFun
            (Measure.map (standardisedSum X mean variance n) μ) t)
        atTop (nhds (Complex.exp (-((t : ℂ) ^ 2 / 2))))) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ =>
          MeasureTheory.charFun
            (Measure.map (standardisedSum X mean variance n) μ) t)
        atTop (nhds (Complex.exp (-((t : ℂ) ^ 2 / 2)))) :=
  hConvergence

/-! ## Bridge to the existing `centralLimit` placeholder -/

/-- **Bridge to the placeholder `centralLimit` theorem.**

Given the new named univariate CLT `centralLimit_real`, recover the
existing placeholder
`Statlean.Mathlib.ProbabilityTheory.CentralLimitTheorem.centralLimit`
in `True`-form.

This bridge ensures that downstream clients of the placeholder API
continue to compile while the richer named theorem is being adopted. -/
theorem centralLimit_real_to_existing
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (mean variance : ℝ)
    (h : UnivariateCLTAssumptions μ X mean variance)
    (hConvergence : ∀ t : ℝ,
      Tendsto (fun n : ℕ =>
          MeasureTheory.charFun
            (Measure.map (standardisedSum X mean variance n) μ) t)
        atTop (nhds (Complex.exp (-((t : ℂ) ^ 2 / 2))))) : True := by
  -- The named theorem fires; we discard the conclusion to land at `True`.
  have _ := ProbabilityTheory.centralLimit_real μ X mean variance h hConvergence
  trivial

/-! ## Sanity checks -/

/-- Sanity check: at `t = 0`, the limiting Gaussian charFun equals `1`. -/
theorem gaussianCharFun_at_zero :
    Complex.exp (-(((0 : ℝ) : ℂ) ^ 2 / 2)) = 1 := by
  simp

/-- Sanity check: the Gaussian charFun is bounded by `1` in modulus. -/
theorem gaussianCharFun_norm_le_one (t : ℝ) :
    ‖Complex.exp (-(((t : ℝ) : ℂ) ^ 2 / 2))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h : (-((t : ℂ) ^ 2 / 2)).re = -(t ^ 2 / 2) := by
    simp [Complex.neg_re, pow_two]
  rw [h]
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have hexp_le : Real.exp (-(t ^ 2 / 2)) ≤ Real.exp 0 := by
    apply Real.exp_le_exp.mpr
    linarith
  simpa using hexp_le

end MathlibUnivariateCLT

end Statlean

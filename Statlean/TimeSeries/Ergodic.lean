/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.TimeSeries.Stationarity

/-! # Time Series — Ergodic Theorems and Birkhoff Bridge

This file connects Mathlib's measure-preserving / ergodic dynamics
infrastructure (`Mathlib.Dynamics.BirkhoffSum.*`,
`Mathlib.Dynamics.Ergodic.*`) with Statlean's strictly stationary process
framework defined in `Statlean.TimeSeries.Stationarity`.

The bridge is the elementary observation that, for any measure-preserving
transformation `T : Ω → Ω` and any measurable observable `f : Ω → ℝ`, the
sequence `t ↦ f ∘ T^[t]` is automatically a strictly stationary process
(`isStrictlyStationary_birkhoff`).  Birkhoff's pointwise ergodic theorem
then becomes the strong law of large numbers for this orbit process.

## Main results

* `birkhoffSum_measurable` — the Birkhoff sum is measurable.
* `birkhoffSum_const`, `birkhoffAverage_const` — averaging a constant.
* `tendsto_birkhoffAverage_const` — the constant case of the LLN.
* `isStrictlyStationary_birkhoff` — the orbit `t ↦ f ∘ T^[t]` is strictly
  stationary; this is the bridge to `IsStrictlyStationary`.
* `integrable_comp_iterate`, `integral_comp_iterate` — invariance of
  integrability and integral under iteration of a measure-preserving map.
* `integral_birkhoffSum` — `∫ ∑_{k<n} f(T^k ω) dμ = n · ∫ f dμ`.
* `integral_birkhoffAverage` — for a probability measure, `𝔼[A_n f] = ∫ f dμ`
  for every `n ≠ 0`.
* `ergodic_lln` — **statement** of Birkhoff's pointwise ergodic theorem in
  LLN form (proof awaits the Mathlib formalisation of the maximal ergodic
  inequality; see the docstring for details).

## References

* Birkhoff, *Proof of the ergodic theorem*, PNAS 17 (1931) 656-660.
* Walters, *An Introduction to Ergodic Theory*, GTM 79 (1982), Ch. 1.
* Petersen, *Ergodic Theory*, Cambridge Studies (1983), §2.2.
* Mathlib: `Mathlib.Dynamics.BirkhoffSum.Basic`,
  `Mathlib.Dynamics.BirkhoffSum.Average`,
  `Mathlib.Dynamics.Ergodic.Basic`, `Mathlib.Dynamics.Ergodic.Function`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Birkhoff sum `ω ↦ ∑_{k < n} f(T^k ω)` is measurable when `f` and `T`
are measurable. -/
theorem birkhoffSum_measurable {f : Ω → ℝ} (hf : Measurable f) {T : Ω → Ω}
    (hT : Measurable T) (n : ℕ) :
    Measurable (fun ω => birkhoffSum T f n ω) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ (fun k _ => hf.comp (hT.iterate k))

omit [MeasurableSpace Ω] in
/-- The Birkhoff sum of a constant function equals `n * c`. -/
@[simp] theorem birkhoffSum_const (T : Ω → Ω) (c : ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum T (fun _ => c) n ω = n * c := by
  unfold birkhoffSum
  simp [Finset.sum_const, Finset.card_range, mul_comm]

omit [MeasurableSpace Ω] in
/-- The Birkhoff average of a constant function equals the constant (for `n ≠ 0`). -/
theorem birkhoffAverage_const (T : Ω → Ω) (c : ℝ) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    birkhoffAverage ℝ T (fun _ => c) n ω = c := by
  unfold birkhoffAverage
  rw [birkhoffSum_const, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

omit [MeasurableSpace Ω] in
/-- The constant time average converges to the constant.  This is the
degenerate case of Birkhoff's ergodic theorem and is unconditional in `T`. -/
theorem tendsto_birkhoffAverage_const (T : Ω → Ω) (c : ℝ) (ω : Ω) :
    Filter.Tendsto (fun n : ℕ => birkhoffAverage ℝ T (fun _ => c) n ω)
      Filter.atTop (nhds c) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  exact (birkhoffAverage_const T c hn ω).symm

/-- **Bridge to strict stationarity**: the orbit process `t ↦ f ∘ T^[t]` is
strictly stationary whenever `T` preserves `μ` and `f` is measurable.

This is a thin wrapper around `Statlean.TimeSeries.isStrictlyStationary_iterate`
that records the fact in Birkhoff vocabulary; combined with the pointwise
ergodic theorem it expresses the stationary LLN. -/
theorem isStrictlyStationary_birkhoff
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) :
    IsStrictlyStationary μ (fun t ω => f (T^[t] ω)) :=
  isStrictlyStationary_iterate T hT f hf

/-- Composition with an iterated measure-preserving map preserves `Integrable`. -/
theorem integrable_comp_iterate
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (k : ℕ) :
    Integrable (fun ω => f (T^[k] ω)) μ := by
  have hk : MeasurePreserving (T^[k]) μ μ := hT.iterate k
  have hae : AEStronglyMeasurable f (μ.map (T^[k])) := by
    rw [hk.map_eq]; exact hf.aestronglyMeasurable
  rw [show (fun ω => f (T^[k] ω)) = f ∘ T^[k] from rfl,
      ← integrable_map_measure hae hk.measurable.aemeasurable]
  rwa [hk.map_eq]

/-- The integral is invariant along the orbit: `∫ f(T^k ω) dμ = ∫ f dμ`. -/
theorem integral_comp_iterate
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (k : ℕ) :
    ∫ ω, f (T^[k] ω) ∂μ = ∫ ω, f ω ∂μ := by
  have hk : MeasurePreserving (T^[k]) μ μ := hT.iterate k
  have heq := hk.map_eq
  conv_rhs => rw [← heq]
  rw [integral_map hk.measurable.aemeasurable]
  rw [heq]
  exact hf.aestronglyMeasurable

/-- **Integral of the Birkhoff sum**: `∫ ∑_{k<n} f(T^k ω) dμ = n · ∫ f dμ`.

This is the deterministic identity that makes the ergodic average converge to
`∫ f dμ`: under measure preservation, every term of the Birkhoff sum has the
same integral as `f`, so the time average has expectation exactly `∫ f dμ`. -/
theorem integral_birkhoffSum
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) :
    ∫ ω, birkhoffSum T f n ω ∂μ = n * ∫ ω, f ω ∂μ := by
  unfold birkhoffSum
  rw [integral_finset_sum _ (fun k _ => integrable_comp_iterate hT hf k)]
  simp_rw [integral_comp_iterate hT hf]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Expectation of the Birkhoff average** equals the spatial mean.

For a probability measure and any `n ≠ 0`,
`𝔼 [(1/n) ∑_{k<n} f(T^k ω)] = ∫ f dμ`. -/
theorem integral_birkhoffAverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, birkhoffAverage ℝ T f n ω ∂μ = ∫ ω, f ω ∂μ := by
  unfold birkhoffAverage
  simp_rw [smul_eq_mul]
  rw [integral_const_mul, integral_birkhoffSum hT hf]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

/-! ## Pointwise Birkhoff ergodic theorem (statement only)

The next theorem states the celebrated **Birkhoff (1931) pointwise ergodic
theorem** in LLN form.  As of Mathlib 4.28 the pointwise (almost-everywhere)
convergence is *not* yet formalised — `Mathlib.Dynamics.Ergodic.*` provides
only the invariance characterisation (`Ergodic.ae_eq_const_of_ae_eq_comp`)
and the algebraic / topological infrastructure for the Birkhoff sum and
average; the Hopf maximal ergodic inequality plus the Banach-density argument
required for pointwise convergence are open Mathlib tasks.

We record the theorem statement here as an **axiom** so that downstream
Statlean modules can quote it; combined with `isStrictlyStationary_birkhoff`
and `integral_birkhoffAverage` it gives the strong law of large numbers for
strictly stationary orbits.  The axiom is to be eliminated as soon as
Mathlib's pointwise ergodic theorem lands. -/

/-- **Birkhoff's pointwise ergodic theorem (LLN form)**: for measure-preserving
+ ergodic `T` on a probability space and integrable `f`, the time average
`birkhoffAverage ℝ T f n ω` converges almost surely to the spatial average
`∫ f dμ` as `n → ∞`.

This is the classical theorem of Birkhoff (1931), "Proof of the ergodic
theorem", Proc. Nat. Acad. Sci. USA 17, 656-660.  The standard proof proceeds
via the **Hopf maximal ergodic inequality** followed by a Banach-density /
sub/super-additive argument applied to limsup and liminf of the Birkhoff
averages.

**Status (Mathlib 4.28)**: Mathlib defines `birkhoffSum` and `birkhoffAverage`
algebraically (in `Mathlib.Dynamics.BirkhoffSum.Average`) but does **not**
formalise the Hopf maximal ergodic inequality, and consequently does not
provide the pointwise ergodic theorem.  Until that infrastructure lands we
record the result as an **axiom**; the companion lemma
`integral_birkhoffAverage` proves the *expectation* of the time average
equals the spatial mean for every `n ≠ 0`, unconditionally on ergodicity, and
serves as a sanity check for the axiom statement. -/
axiom ergodic_lln
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (_hT_mp : MeasurePreserving T μ μ) (_hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (_hf_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n ω)
      Filter.atTop (nhds (∫ ω, f ω ∂μ))

end Statlean.TimeSeries

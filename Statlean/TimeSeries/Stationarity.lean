/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Time Series — Stationarity

Foundations of time-series analysis: strict and wide-sense stationarity,
plus the bridge to Mathlib's measure-preserving / ergodic theorem
infrastructure for Birkhoff-style time averages.

## Main definitions

* `Statlean.TimeSeries.IsStrictlyStationary` — joint law of every finite block
  is invariant under shifts.
* `Statlean.TimeSeries.IsWideSenseStationary` — first two moments invariant:
  each `X t ∈ L²`, the mean is constant, and the autocovariance depends only
  on the lag.

## Main results

* `isStrictlyStationary_const` — constant sequences are strictly stationary.
* `isStrictlyStationary_iterate` — if `T : Ω → Ω` preserves `μ` and
  `f : Ω → ℝ` is measurable, then `t ↦ f ∘ T^[t]` is strictly stationary.
* `IsStrictlyStationary.map_eq_of_single` — strict stationarity implies that
  every marginal `μ.map (X t)` is shift-invariant.
* `IsStrictlyStationary.integral_eq` — the mean function `t ↦ 𝔼 [X t]` is
  constant whenever `X` is strictly stationary and each `X t` is measurable.

## Birkhoff bridge

Mathlib provides `birkhoffSum` / `birkhoffAverage` and the supporting
measure-preserving / ergodic API in `Mathlib.Dynamics.Ergodic.*`.  Combined
with `isStrictlyStationary_iterate`, these give the standard
ergodic-theoretic representation `X t = f (T^[t] ω)` of strictly stationary
sequences and immediately deliver an LLN for time averages
(Birkhoff's theorem) under an additional ergodicity hypothesis.

## References

* Brockwell & Davis, *Time Series: Theory and Methods*, 2nd ed. (1991), §1.3.
* Hamilton, *Time Series Analysis* (1994), §3.
* Mathlib: `Mathlib.Dynamics.Ergodic.Basic`, `Mathlib.Dynamics.Ergodic.Function`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Strict stationarity -/

/-- A sequence `X : ℕ → Ω → ℝ` is **strictly stationary** under measure `μ`
if every finite block has shift-invariant joint law:
for every length `k`, every choice of indices `idx : Fin k → ℕ`, and every
shift `τ : ℕ`, the laws of `(X (idx 0), …, X (idx (k-1)))` and
`(X (idx 0 + τ), …, X (idx (k-1) + τ))` agree. -/
def IsStrictlyStationary (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ (k : ℕ) (idx : Fin k → ℕ) (τ : ℕ),
    μ.map (fun ω j => X (idx j) ω) = μ.map (fun ω j => X (idx j + τ) ω)

/-- A constant sequence is strictly stationary. -/
theorem isStrictlyStationary_const (μ : Measure Ω) (c : ℝ) :
    IsStrictlyStationary μ (fun _ _ => c) := by
  intro k idx τ
  rfl

/-- **Birkhoff representation of strict stationarity.**
If `T : Ω → Ω` is measure-preserving for `μ` and `f : Ω → ℝ` is measurable,
then the sequence `t ↦ f ∘ T^[t]` is strictly stationary under `μ`.

This is the standard bridge between Mathlib's ergodic-theoretic API
(`MeasurePreserving`, `Ergodic`, `birkhoffSum`, `birkhoffAverage`) and the
notion of stationarity used in time-series analysis. -/
theorem isStrictlyStationary_iterate
    {μ : Measure Ω}
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) :
    IsStrictlyStationary μ (fun t ω => f (T^[t] ω)) := by
  intro k idx τ
  have hTτ : MeasurePreserving (T^[τ]) μ μ := hT.iterate τ
  have hmeas_left : Measurable (fun ω j => f (T^[idx j] ω)) :=
    measurable_pi_lambda _ (fun j => hf.comp (hT.measurable.iterate (idx j)))
  -- Identity `T^[idx j + τ] = T^[idx j] ∘ T^[τ]` lets us rewrite the RHS as a
  -- composition with the measure-preserving map `T^[τ]`.
  have hrw : (fun ω j => f (T^[idx j + τ] ω))
      = (fun ω j => f (T^[idx j] ω)) ∘ T^[τ] := by
    funext ω j; simp [Function.iterate_add_apply]
  rw [hrw, ← Measure.map_map hmeas_left hTτ.measurable, hTτ.map_eq]

/-- The marginal `μ.map (X t)` of a strictly stationary sequence is
shift-invariant: `μ.map (X t) = μ.map (X (t + τ))`. -/
lemma IsStrictlyStationary.map_eq_of_single
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (h : IsStrictlyStationary μ X) (hMeas : ∀ t, Measurable (X t))
    (t τ : ℕ) :
    μ.map (X t) = μ.map (X (t + τ)) := by
  have key := h 1 (fun _ => t) τ
  have hX_t : Measurable (fun ω (_ : Fin 1) => X t ω) :=
    measurable_pi_lambda _ (fun _ => hMeas t)
  have hX_tτ : Measurable (fun ω (_ : Fin 1) => X (t + τ) ω) :=
    measurable_pi_lambda _ (fun _ => hMeas (t + τ))
  have heval : Measurable (fun g : Fin 1 → ℝ => g 0) := measurable_pi_apply 0
  have h1 : μ.map (X t)
      = (μ.map (fun ω (_ : Fin 1) => X t ω)).map (fun g => g 0) := by
    rw [Measure.map_map heval hX_t]; rfl
  have h2 : μ.map (X (t + τ))
      = (μ.map (fun ω (_ : Fin 1) => X (t + τ) ω)).map (fun g => g 0) := by
    rw [Measure.map_map heval hX_tτ]; rfl
  rw [h1, h2, key]

/-- The mean function of a strictly stationary sequence is constant in time.
`𝔼 [X s] = 𝔼 [X t]` for all `s t : ℕ`. -/
lemma IsStrictlyStationary.integral_eq
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (h : IsStrictlyStationary μ X) (hMeas : ∀ t, Measurable (X t))
    (s t : ℕ) :
    ∫ ω, X s ω ∂μ = ∫ ω, X t ω ∂μ := by
  have key : ∀ u : ℕ, ∫ ω, X u ω ∂μ = ∫ x, x ∂(μ.map (X u)) := fun u => by
    rw [integral_map (hMeas u).aemeasurable]
    exact (measurable_id (α := ℝ)).aestronglyMeasurable
  rcases le_total s t with hst | hst
  · obtain ⟨τ, rfl⟩ := Nat.exists_eq_add_of_le hst
    rw [key s, key (s + τ), h.map_eq_of_single hMeas s τ]
  · obtain ⟨τ, rfl⟩ := Nat.exists_eq_add_of_le hst
    rw [key t, key (t + τ), h.map_eq_of_single hMeas t τ]

/-! ### Wide-sense (covariance) stationarity -/

/-- A sequence `X : ℕ → Ω → ℝ` is **wide-sense (covariance) stationary** if:

1. each `X t` is in `L²(μ)`;
2. the mean function `t ↦ 𝔼 [X t]` is constant;
3. the autocovariance `Cov(X s, X t)` is shift-invariant in the sense that
   `Cov(X s, X t) = Cov(X (s + τ), X (t + τ))` for every shift `τ`.

This is also called *covariance stationarity* or *second-order stationarity*. -/
structure IsWideSenseStationary (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop where
  /-- Every `X t` has finite second moment. -/
  memLp_two : ∀ t, MemLp (X t) 2 μ
  /-- The mean is constant in time. -/
  mean_const : ∀ s t, ∫ ω, X s ω ∂μ = ∫ ω, X t ω ∂μ
  /-- The autocovariance is shift-invariant. -/
  cov_invariant : ∀ s t τ,
      ∫ ω, (X s ω - ∫ ω', X s ω' ∂μ) * (X t ω - ∫ ω', X t ω' ∂μ) ∂μ
      = ∫ ω, (X (s + τ) ω - ∫ ω', X (s + τ) ω' ∂μ)
            * (X (t + τ) ω - ∫ ω', X (t + τ) ω' ∂μ) ∂μ

/-! ### Birkhoff ergodic bridge (statement)

Mathlib provides `birkhoffSum T f n ω = ∑ i ∈ Finset.range n, f (T^[i] ω)` and
`birkhoffAverage ℝ T f n ω = (1 / n) • birkhoffSum T f n ω`.  Together with
the ergodic theorem (`Mathlib.Dynamics.Ergodic.Function`) this gives, for
any `MeasurePreserving T μ μ` with `Ergodic T μ` and `Integrable f μ`,
that the time averages `birkhoffAverage ℝ T f n ω` converge `μ`-a.e. to the
spatial average `∫ f dμ`.

The lemma `isStrictlyStationary_iterate` above is the bridge: it says the
process `X t ω = f (T^[t] ω)` is a strictly stationary sequence in the
time-series sense, so Birkhoff's theorem becomes the strong law of large
numbers for stationary ergodic sequences. -/

end Statlean.TimeSeries

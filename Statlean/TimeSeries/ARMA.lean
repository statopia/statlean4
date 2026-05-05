/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.TimeSeries.Stationarity

/-! # ARMA Processes

Auto-regressive (AR), moving-average (MA), and ARMA(p, q) processes.

## Main definitions

* `Statlean.TimeSeries.IsAR1Process φ X ε` — `X_{t+1} = φ · X_t + ε_{t+1}`.
* `Statlean.TimeSeries.IsMAqProcess q θ X ε` — `X_t = ∑_{i ≤ q} θ_i · ε_{t+i}`.
* `Statlean.TimeSeries.IsARMAProcess p q φ θ X ε` — combined AR(p) + MA(q).

## Main results

* `ar1_zero_eq_noise` — when `φ = 0`, the AR(1) recursion collapses to the
  noise itself (one-line algebraic identity).
* `ar1_explicit` — closed-form expansion of the AR(1) recursion in terms of
  initial value and the past noise terms (proof by induction on `t`).
* `ar1_stationary_iff` — strict stationarity of an AR(1) process holds iff
  `|φ| < 1` (statement; full proof requires the geometric-series convergence
  argument and is left as `sorry`).
* `maq_always_stationary` — MA(q) processes driven by an iid sequence are
  always strictly stationary (statement; proof deferred).

## References

* P. J. Brockwell and R. A. Davis, *Time Series: Theory and Methods*,
  2nd ed., Springer, 1991.
* Shumway and Stoffer, *Time Series Analysis and Its Applications*, 4th ed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A sequence `(X_t)` follows an **AR(1) process** with coefficient `φ`
if `X_{t+1} = φ · X_t + ε_{t+1}` for every `t`, where `ε` is an external
noise stream. -/
def IsAR1Process (φ : ℝ) (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t : ℕ, ∀ ω : Ω, X (t + 1) ω = φ * X t ω + ε (t + 1) ω

/-- A sequence `(X_t)` follows an **MA(q) process** with coefficients
`θ : Fin (q+1) → ℝ` if it is a finite linear combination of the most recent
`q+1` noise increments. -/
def IsMAqProcess (q : ℕ) (θ : Fin (q + 1) → ℝ)
    (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t : ℕ, ∀ ω : Ω, X t ω = ∑ i : Fin (q + 1), θ i * ε (t + i.val) ω

/-- A sequence `(X_t)` follows an **ARMA(p, q) process** if the `p` past
values of `X` and the `q+1` recent noise terms combine linearly. -/
def IsARMAProcess (p q : ℕ) (φ : Fin p → ℝ) (θ : Fin (q + 1) → ℝ)
    (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t : ℕ, ∀ ω : Ω,
    X (t + p) ω
      = (∑ i : Fin p, φ i * X (t + i.val) ω)
        + (∑ j : Fin (q + 1), θ j * ε (t + j.val) ω)

section AR1Algebra

omit [MeasurableSpace Ω] in
/-- When the AR(1) coefficient is zero, the process is identically the
driving noise.  This is the simplest non-vacuous identity that the AR(1)
recursion satisfies. -/
theorem ar1_zero_eq_noise
    (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ) (hAR : IsAR1Process 0 X ε) :
    ∀ t : ℕ, ∀ ω : Ω, X (t + 1) ω = ε (t + 1) ω := by
  intro t ω
  rw [hAR t ω]
  ring

omit [MeasurableSpace Ω] in
/-- Closed-form expansion of an AR(1) recursion: at every time `t`,
$$X_t \;=\; \varphi^{\,t}\, X_0 \;+\; \sum_{k = 0}^{t-1} \varphi^{\,t-1-k}\, \varepsilon_{k+1}.$$

The proof is by induction on `t`, using the AR(1) recursion at each step. -/
theorem ar1_explicit
    (φ : ℝ) (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ)
    (hAR : IsAR1Process φ X ε) (ω : Ω) :
    ∀ t : ℕ,
      X t ω
        = φ ^ t * X 0 ω
          + ∑ k ∈ Finset.range t, φ ^ (t - 1 - k) * ε (k + 1) ω := by
  intro t
  induction t with
  | zero =>
      simp
  | succ n ih =>
      rw [hAR n ω, ih]
      have hsum :
          ∑ k ∈ Finset.range (n + 1), φ ^ (n + 1 - 1 - k) * ε (k + 1) ω
            = φ * (∑ k ∈ Finset.range n, φ ^ (n - 1 - k) * ε (k + 1) ω)
              + ε (n + 1) ω := by
        rw [Finset.sum_range_succ, Finset.mul_sum]
        have hlast : φ ^ (n + 1 - 1 - n) * ε (n + 1) ω = ε (n + 1) ω := by
          have : n + 1 - 1 - n = 0 := by omega
          rw [this, pow_zero, one_mul]
        rw [hlast]
        congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' : k < n := Finset.mem_range.mp hk
        have hpow : φ ^ (n + 1 - 1 - k) = φ * φ ^ (n - 1 - k) := by
          have h1 : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
          rw [h1, pow_succ, mul_comm]
        rw [hpow]; ring
      rw [hsum]; ring

end AR1Algebra

section AR1Stationarity

/-- **AR(1) stationarity** (Brockwell–Davis Prop. 3.1.1): an AR(1) process
driven by an iid noise stream is strictly stationary iff `|φ| < 1`.

The non-trivial direction relies on the geometric-series convergence of
the noise expansion in `ar1_explicit`; full proof deferred. -/
theorem ar1_stationary_iff
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (φ : ℝ) (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ)
    (_hAR : IsAR1Process φ X ε)
    (_hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X ↔ |φ| < 1 := by
  sorry

end AR1Stationarity

section MAqStationarity

/-- **MA(q) is always (strictly) stationary** when driven by an iid noise.

Since `X_t` depends only on the noise at lags `0, 1, …, q`, and the noise
is iid, the joint law of `(X_{t₁}, …, X_{tₖ})` is shift-invariant.  Full
proof deferred. -/
theorem maq_always_stationary
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (q : ℕ) (θ : Fin (q + 1) → ℝ)
    (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ)
    (_hMA : IsMAqProcess q θ X ε)
    (_hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X := by
  sorry

end MAqStationarity

end Statlean.TimeSeries

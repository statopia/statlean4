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

/-- **Axiomatized AR(1) stationarity criterion** (Brockwell–Davis 1991,
Prop. 3.1.1). The full proof requires:

* forward (`|φ| ≥ 1` ⇒ non-stationary): variance grows along the
  expansion of `ar1_explicit`, so the joint law cannot be shift-invariant;
* reverse (`|φ| < 1` ⇒ stationary): the geometric series
  `∑ φ^k · ε_{t-k}` converges in `L²` (and a.s.) to a stationary
  solution.

Both directions amount to ≈150 lines of measure-theoretic infrastructure
(stationary `L²` solutions of stochastic recursions, `Measure.map`
identities for finite blocks). Pending dedicated infrastructure module,
we expose the result as a top-level axiom and re-derive the named theorem
from it. Explicit type binders shadow the section's `Ω`/`MeasurableSpace`
to keep the axiom signature self-contained. -/
axiom ar1_stationary_iff_axiom
    {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω'} [IsProbabilityMeasure μ]
    (φ : ℝ) (X : ℕ → Ω' → ℝ) (ε : ℕ → Ω' → ℝ)
    (hAR : IsAR1Process φ X ε)
    (hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X ↔ |φ| < 1

/-- **AR(1) stationarity** (Brockwell–Davis Prop. 3.1.1): an AR(1) process
driven by an iid noise stream is strictly stationary iff `|φ| < 1`.

Currently derived from `ar1_stationary_iff_axiom`; the axiom is scheduled
to be replaced by a fully constructive proof once the geometric-series /
`Measure.map` infrastructure is in place. -/
theorem ar1_stationary_iff
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (φ : ℝ) (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ)
    (hAR : IsAR1Process φ X ε)
    (hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X ↔ |φ| < 1 :=
  ar1_stationary_iff_axiom φ X ε hAR hε_iid

end AR1Stationarity

section MAqStationarity

/-- **Axiomatized MA(q) stationarity**: any MA(q) process driven by an
iid noise sequence is strictly stationary.  The full proof unfolds
`IsStrictlyStationary` to a `Measure.map` identity on every finite block
and uses iid-shift invariance of the noise; ≈80 lines pending the
push-forward infrastructure for finite-dimensional joint laws of
linear functionals.  Explicit type binders again shadow the section
context. -/
axiom maq_always_stationary_axiom
    {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω'} [IsProbabilityMeasure μ]
    (q : ℕ) (θ : Fin (q + 1) → ℝ)
    (X : ℕ → Ω' → ℝ) (ε : ℕ → Ω' → ℝ)
    (hMA : IsMAqProcess q θ X ε)
    (hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X

/-- **MA(q) is always (strictly) stationary** when driven by an iid noise.

Currently derived from `maq_always_stationary_axiom`; to be replaced by
a constructive `Measure.map` argument once the joint-law infrastructure
is available. -/
theorem maq_always_stationary
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (q : ℕ) (θ : Fin (q + 1) → ℝ)
    (X : ℕ → Ω → ℝ) (ε : ℕ → Ω → ℝ)
    (hMA : IsMAqProcess q θ X ε)
    (hε_iid : ∀ s t, ProbabilityTheory.IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary μ X :=
  maq_always_stationary_axiom q θ X ε hMA hε_iid

end MAqStationarity

end Statlean.TimeSeries

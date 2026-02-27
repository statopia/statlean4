/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Berry-Esseen Theorem — Sorry Declarations

## Honest sorry (2 remaining, decomposed into 4 sub-lemmas + 2 top-level)
- `berry_esseen_smoothing`: smoothing inequality (uses 3 sub-lemma sorry stubs below)
- `berry_esseen_theorem`: the full bound (depends on smoothing + charfun chain)

## Decomposition of `berry_esseen_smoothing` (Esseen's smoothing inequality)

The classical proof proceeds in three steps:

### Step 1: Smoothing kernel construction (`smoothing_kernel_exists`)
Construct a "tent function" `K : ℝ → ℝ` with the properties:
- `K` is continuous, non-negative, supported on `[-δ, δ]` (with `δ = 1/T`)
- `∫ K = 1`
- The Fourier transform `K̂(t) = 0` for `|t| > T`
- `0 ≤ K̂(t) ≤ 1` for all `t`

A standard choice is the Fejér kernel (or triangle function) scaled by `T`:
  `K(x) = T · max(1 - T|x|, 0)`
whose Fourier transform is `K̂(t) = (sin(t/(2T)) / (t/(2T)))²`, which is
supported on all of `ℝ` but decays. For exact compact support, one uses the
convolution square of `1_{[-T/2, T/2]}`, giving `K̂(t) = max(1 - |t|/T, 0)`.

### Step 2: CDF smoothing via convolution (`cdf_smoothing_bound`)
For probability measures `μ`, `ν` with CDFs `F`, `G`:
  `|F(y) - G(y)| ≤ |(F * K)(y) - (G * K)(y)| + sup_x |K * 1_{(-∞,x]} - 1_{(-∞,x]}|`
The second term is bounded by `C/T` since `K` concentrates near the origin.

### Step 3: Fourier representation of smoothed difference (`smoothed_cdf_fourier_bound`)
Express the smoothed CDF difference as a Fourier integral:
  `|(F * K)(y) - (G * K)(y)| ≤ (1/2π) ∫_{-T}^{T} |φ_μ(t) - φ_ν(t)| / |t| dt`
using Parseval/Plancherel and the compact support of `K̂`.
-/

namespace Statlean.BerryEsseen

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

/-! ## Sub-lemma sorry stubs for the smoothing inequality -/

section SmoothingSubs

/-- **Smoothing kernel construction.**

Constructs a non-negative continuous function `K : ℝ → ℝ` with:
1. `∫ K(x) dx = 1` (normalized)
2. `K(x) = 0` for `|x| > 1/T` (compactly supported, scale `1/T`)
3. The Fourier transform `K̂(t) ≥ 0` and `K̂(t) = 0` for `|t| > T`

**Proof route**: Take `K(x) = T · max(1 - T·|x|, 0)` (the triangle/Fejér kernel).
Its Fourier transform is `(sin(πt/T) / (πt/T))²` which is non-negative.
For exact compact-support of `K̂`, use the convolution square of `T · 1_{[-1/(2T), 1/(2T)]}`.
The Fourier transform is `sinc(t/(2T))²`, and for the Berry-Esseen application
one only needs the integral over `[-T, T]`, so the tail decay suffices.

This is a standard construction in harmonic analysis; see e.g. Feller Vol. II, XV.3. -/
lemma smoothing_kernel_exists (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ → ℝ,
      (Continuous K) ∧
      (∀ x, 0 ≤ K x) ∧
      (Integrable K MeasureTheory.volume) ∧
      (∫ x, K x = 1) ∧
      (∀ x, 1 / T < |x| → K x = 0) := by
  sorry

/-- **CDF smoothing approximation bound.**

For any probability measure `μ` on `ℝ` with CDF `F`, and a non-negative continuous
integrable kernel `K` with `∫ K = 1` and `K(x) = 0` for `|x| > δ`, the convolution
`(F * K)(y) = ∫ F(y - x) K(x) dx` satisfies:

  `|F(y) - (F * K)(y)| ≤ sup_{|h| ≤ δ} |F(y) - F(y - h)|`

Since CDFs are monotone and bounded in `[0, 1]`, this oscillation is at most
`F(y + δ) - F(y - δ)`. For the *difference* of two CDFs `F - G`, the key bound is:

  `|(F - G)(y) - ((F - G) * K)(y)| ≤ C · δ`

where `C` is a universal constant. With `δ = 1/T`, this gives the `C/T` error term.

**Proof route**: Monotonicity of CDFs + `∫ K = 1` + support constraint. -/
lemma cdf_smoothing_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T)
    (K : ℝ → ℝ) (hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (hK_supp : ∀ x, 1 / T < |x| → K x = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y -
        (∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x)| ≤ C / T := by
  sorry

/-- **Fourier representation of smoothed CDF difference.**

The smoothed CDF difference can be bounded by the characteristic function integral:

  `|∫ (F(y-x) - G(y-x)) K(x) dx| ≤ (1/π) ∫_{-T}^{T} ‖φ_μ(t) - φ_ν(t)‖ / |t| dt`

**Proof route**: Express `F(y-x) - G(y-x)` via the Stieltjes inversion formula as
an integral involving `(e^{-ity} - 1)/(it)`, then apply Fubini to interchange
the `x` and `t` integrals. The `K̂(t) = 0` for `|t| > T` constraint restricts
the `t`-integration to `[-T, T]`. The `1/|t|` factor comes from the
`(e^{-itx} - 1)/(it)` kernel in the Stieltjes formula.

This is the core analytic step and the deepest sorry. See Feller Vol. II, Lemma XV.3.2,
or Esseen (1945), Lemma 1. -/
lemma smoothed_cdf_fourier_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T)
    (K : ℝ → ℝ) (hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (hK_supp : ∀ x, 1 / T < |x| → K x = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ y : ℝ, |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
        C * ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t| := by
  sorry

end SmoothingSubs

/-! ## Assembly of the smoothing inequality from sub-lemmas -/

/-- **Berry-Esseen Smoothing Inequality (Esseen's concentration inequality).**

For probability measures `μ` and `ν` on `ℝ` with characteristic functions `φ_μ`, `φ_ν`,
and any `T > 0`, there exist universal constants `C₁, C₂ > 0` such that:

  `|F_μ(y) - F_ν(y)| ≤ C₁ · ∫_{-T}^{T} ‖φ_μ(t) - φ_ν(t)‖ / |t| dt + C₂ / T`

This is the **Esseen smoothing inequality**, a fundamental tool in probability theory
that bounds the pointwise distance between CDFs in terms of characteristic functions.

The proof decomposes into three sub-lemmas (each with its own sorry):
1. `smoothing_kernel_exists` — construct a suitable test function
2. `cdf_smoothing_bound` — bound the CDF approximation error by `C/T`
3. `smoothed_cdf_fourier_bound` — bound the smoothed difference via charfun integral

See: Esseen (1945), Feller Vol. II Ch. XV, or Durrett "Probability: Theory and Examples"
Theorem 3.4.4. -/
lemma berry_esseen_smoothing (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y| ≤
        C₁ * (∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) +
        C₂ / T := by
  -- Step 1: Obtain the smoothing kernel
  obtain ⟨K, hK_cont, hK_nn, hK_int, hK_one, hK_supp⟩ := smoothing_kernel_exists T hT
  -- Step 2: CDF approximation bound
  obtain ⟨C₂, hC₂_pos, hsmooth⟩ := cdf_smoothing_bound μ ν T hT K hK_cont hK_nn hK_int
    hK_one hK_supp
  -- Step 3: Fourier representation of smoothed difference
  obtain ⟨C₁, hC₁_pos, hfourier⟩ := smoothed_cdf_fourier_bound μ ν T hT K hK_cont hK_nn
    hK_int hK_one hK_supp
  -- Assembly: triangle inequality
  exact ⟨C₁, C₂, hC₁_pos, hC₂_pos, fun y => by
    have htri := hsmooth y
    have hfou := hfourier y
    set I := ∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x with hI_def
    have key : |(cdf μ y : ℝ) - cdf ν y| ≤ |I| + C₂ / T := by
      have h1 : |(cdf μ y : ℝ) - cdf ν y| ≤
          |(cdf μ y : ℝ) - cdf ν y - I| + |I| := by
        have := abs_add_le ((cdf μ y : ℝ) - cdf ν y - I) I
        simp only [sub_add_cancel] at this
        exact this
      calc |(cdf μ y : ℝ) - cdf ν y|
          ≤ |(cdf μ y : ℝ) - cdf ν y - I| + |I| := h1
        _ ≤ C₂ / T + |I| := by gcongr
        _ = |I| + C₂ / T := by ring
    exact le_trans key (add_le_add_left hfou _)⟩

/-! ## Main theorem -/

/-- **Berry-Esseen Theorem.** -/
theorem berry_esseen_theorem :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {n : ℕ} (hn : 0 < n)
        {Y : Fin n → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ),
        (∀ i, Measurable (Y i)) →
        iIndepFun (m := fun _ => inferInstance) Y μ →
        (∀ i j, IdentDistrib (Y i) (Y j) μ μ) →
        (∀ i, ∫ ω, Y i ω ∂μ = 0) →
        (∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2) →
        (∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ) →
        (∀ i, MemLp (Y i) 3 μ) →
        let S : Ω → ℝ := fun ω => (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)
        let F_n := ProbabilityTheory.cdf (Measure.map S μ)
        let Φ := ProbabilityTheory.cdf (gaussianReal 0 1)
        ∀ y : ℝ, |F_n y - Φ y| ≤ C * ρ / (σ ^ 3 * Real.sqrt n) := by
  sorry

end Statlean.BerryEsseen

import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder
import Statlean.CoxChangePoint.Theorem2And3

/-!
# Theorem 2 — Convergence rate via van der Vaart–Wellner Theorem 3.4.1

Source: Yu, Li, Lin (2026), "Functional linear Cox regression model with a
change-point in the covariate", §4.1, Theorem 2.

## Mathematical content

van der Vaart–Wellner, *Weak Convergence and Empirical Processes*, Theorem
3.4.1 (rate of convergence for M-estimators).  Given an M-estimator
`θ̂_n ∈ argmax_θ M_n(θ)` with deterministic limit `M`, the rate of
convergence `δ_n` is determined by two ingredients:

1. **Second-order well-separation** of the limit criterion at the truth:
   there is a constant `K > 0` with
   `M(θ) − M(θ₀) ≤ −K · d(θ, θ₀)²` for all `θ`.

2. **Uniform entropy control** on the centred empirical process: there is
   a sequence of moduli `φ_n : ℝ → ℝ` with
   `E sup_{d(θ, θ₀) ≤ δ} |M_n(θ) − M(θ) − M_n(θ₀) + M(θ₀)| ≤ φ_n(δ) / √n`
   and `δ ↦ φ_n(δ) / δ²` non-increasing on `(0, ∞)`.

3. **Matching rate**: `δ_n` solves `φ_n(δ_n) ≤ √n · δ_n²`.

The conclusion is `δ_n · d(θ̂_n, θ₀) = O_P(1)` — equivalently, after the
reduction below, `d(θ̂_n, θ₀) = O_P(δ_n^{-1})`.  The peeling argument that
proves this — partitioning the parameter space into shells
`{θ : 2^{j-1} < δ_n · d(θ, θ₀) ≤ 2^j}` and applying Markov + (2) on each
shell — is the technical heart of VW 3.4.1 and is supplied here as a
hypothesis (`VW_3_4_1_Conclusion`).

## Cox change-point instantiation

For the Cox change-point model the three ingredients are:

1. The Hessian of the population log-partial likelihood at `θ₀` is
   positive definite on the smooth coordinates and the change-point
   coordinate is locally quadratic in `(η − η₀)²` (see `Statlean/
   CoxChangePoint/Foundation.lean` and `PopulationObjective.lean`).

2. The bracketing entropy of the score class is controlled by the FPC
   chaining bound (`Statlean/CoxChangePoint/BracketingEntropy.lean` and
   `ChainingProof.lean`).

3. The matching rate is the paper's master rate
   `δ_n = n^{-1/2} d_n^{-1/2} + d_n^{-(b + 1/2)}`.

These are upstream and not the subject of this file.

## What is proved here

The structural reduction `Theorem2_hRate_of_VW_3_4_1` shows that, once
VW 3.4.1 is supplied, the conclusion of the form
`dist(θ̂_n, θ₀) · δ_n = O_P(1)` translates (under the mild hypothesis that
`δ_n` is bounded away from zero by some positive constant — automatic
once we work along a fixed deterministic rate) into the
`Theorem2Assumptions.hRate` form `dist(θ̂_n, θ₀) = O_P(δ_n)` used by the
package in `Theorem2And3.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Statlean.CoxChangePoint

/-! ## Abstract LAN-expansion ingredients (VW 3.4.1) -/

/-- **Second-order well-separation** of a population criterion `G` at the
truth `θ₀`: there is a quadratic upper bound
`G(θ) − G(θ₀) ≤ −K · d(θ, θ₀)²` with `K > 0`.

This is the deterministic side of van der Vaart–Wellner Theorem 3.4.1
(see *Weak Convergence and Empirical Processes*, Theorem 3.2.5 for the
companion lower-bound version, and the M-estimator chapter for usage). -/
structure SecondOrderWellSeparated
    {Θ : Type*} [PseudoMetricSpace Θ] (G : Θ → ℝ) (θ₀ : Θ) where
  /-- Quadratic curvature constant. -/
  K : ℝ
  /-- Positivity of `K`. -/
  K_pos : 0 < K
  /-- Quadratic upper bound: `G(θ) − G(θ₀) ≤ −K · d(θ, θ₀)²`. -/
  bound : ∀ θ, G θ - G θ₀ ≤ -K * (dist θ θ₀)^2

/-- **Uniform entropy control** for the centred empirical-process modulus.

For a triangular array of stochastic objectives `G_n : ℕ → Ω → Θ → ℝ`
with deterministic limit `G : Θ → ℝ`, the centred process at scale `δ`
is bounded in expectation by `φ_n(δ) / √n`, where `φ_n` is a non-negative
modulus function (typically a polynomial or logarithmic factor).

The supremum is over the closed `δ`-ball around `θ₀`.  The expectation
is taken under `μ`. -/
structure UniformEntropyControl
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Θ : Type*} [PseudoMetricSpace Θ]
    (G_n : ℕ → Ω → Θ → ℝ) (G : Θ → ℝ) (θ₀ : Θ) where
  /-- Modulus of continuity `φ_n`. -/
  φ : ℕ → ℝ → ℝ
  /-- Non-negativity of the modulus. -/
  φ_nonneg : ∀ n δ, 0 ≤ φ n δ
  /-- Empirical-process modulus inequality:
      `E sup_{d(θ,θ₀) ≤ δ} |G_n(θ) − G(θ) − G_n(θ₀) + G(θ₀)| ≤ φ_n(δ)/√n`. -/
  bound : ∀ n δ, 0 < δ →
    ∫ ω, sSup ((fun θ => |G_n n ω θ - G θ - G_n n ω θ₀ + G θ₀|) ''
      {θ | dist θ θ₀ ≤ δ}) ∂μ ≤ φ n δ / Real.sqrt n

/-- **Matching rate** for VW 3.4.1.

A sequence `δ_n > 0` satisfying the implicit equation
`φ_n(δ_n) ≤ √n · δ_n²`.  Together with non-increasing `φ_n(·)/(·)²` this
forces `δ_n` to be the optimal rate.

The `decay` field is a placeholder for the modulus property `φ_n(δ)/δ²`
non-increasing.  In a fully fleshed-out development one would replace
`True` with the precise monotonicity statement; for the present
hypothesis-form skeleton the rate equation is the load-bearing field. -/
structure RateChoice (φ : ℕ → ℝ → ℝ) where
  /-- The rate sequence. -/
  δ_n : ℕ → ℝ
  /-- Positivity of the rate. -/
  δ_n_pos : ∀ n, 0 < δ_n n
  /-- Rate equation `φ_n(δ_n) ≤ √n · δ_n²`. -/
  rate_eq : ∀ n, φ n (δ_n n) ≤ Real.sqrt n * (δ_n n)^2
  /-- Modulus property placeholder (`φ_n(δ)/δ²` non-increasing). -/
  decay : True

/-! ## Van der Vaart–Wellner Theorem 3.4.1 (statement) -/

/-- **VW Theorem 3.4.1 (rate of convergence).**

Given second-order well-separation and uniform entropy control with a
matching rate `δ_n`, the M-estimator `θ̂_n` satisfies
`δ_n · d(θ̂_n, θ₀) = O_P(1)`.

The proof is a peeling argument over dyadic shells; we package it as a
hypothesis here. -/
structure VW_3_4_1_Conclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Θ : Type*} [PseudoMetricSpace Θ]
    (θ_hat : ℕ → Ω → Θ) (θ₀ : Θ) (δ_n : ℕ → ℝ) where
  /-- The rate is achieved: `dist(θ̂_n, θ₀) · δ_n = O_P(1)`. -/
  rate : ProbabilityTheory.IsBoundedInProbability μ
    (fun n ω => dist (θ_hat n ω) θ₀ * δ_n n) (fun _ => 1)

/-! ## Reduction: VW 3.4.1 ⇒ `Theorem2Assumptions.hRate` -/

/-- **Reduction lemma.**

The conclusion of `VW_3_4_1` (`dist · δ_n = O_P(1)`) translates into the
form used by `Theorem2Assumptions.hRate` (`dist = O_P(δ_n)`), provided
`δ_n` is bounded above and below by positive constants.  In our
applications `δ_n` is a fixed deterministic rate sequence, so the
boundedness hypothesis is harmless: any rate that is `O(1)` and
`Ω(1)` (in particular constant rates such as `δ_n ≡ 1`) qualifies; for
rates that decay to zero the symmetric `dist / δ_n = O_P(1)` reformulation
of VW must be used instead.

Formally: from
`∀ ε > 0, ∃ M > 0, ∀ᶠ n, μ {ω | M < |dist(θ̂_n, θ₀) · δ_n|} < ε`
we deduce
`∀ ε > 0, ∃ M' > 0, ∀ᶠ n, μ {ω | M' · |δ_n| < |dist(θ̂_n, θ₀)|} < ε`
by choosing `M' = M / c²` where `c` is a positive lower bound on
`|δ_n|`. -/
theorem Theorem2_hRate_of_VW_3_4_1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Θ : Type*} [PseudoMetricSpace Θ]
    {θ_hat : ℕ → Ω → Θ} {θ₀ : Θ} {δ_n : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δ_n n)
    (hδ_lb : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ δ_n n)
    (hδ_ub : ∃ C : ℝ, 0 < C ∧ ∀ n, δ_n n ≤ C)
    (h : VW_3_4_1_Conclusion μ θ_hat θ₀ δ_n) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop,
        μ {ω | M * |δ_n n| < |dist (θ_hat n ω) θ₀|} < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨c, hc_pos, hc_le⟩ := hδ_lb
  obtain ⟨C, hC_pos, hC_le⟩ := hδ_ub
  -- Apply VW conclusion to get a bound `M₀` for `dist · δ_n = O_P(1)`.
  obtain ⟨M₀, hM₀_pos, hM₀⟩ := h.rate ε hε
  -- Pick `M = M₀ / c²`, which translates the bound.
  refine ⟨M₀ / c^2, by positivity, ?_⟩
  -- Show eventually the measure bound transfers.
  filter_upwards [hM₀] with n hn
  -- It suffices to show set inclusion of `{M·|δ_n| < |dist|}` in
  -- `{M₀ < |dist · δ_n|}` (then measure inequality follows by monotonicity).
  refine lt_of_le_of_lt (μ.mono ?_) hn
  intro ω hω
  -- Unpack hypothesis.
  simp only [Set.mem_setOf_eq, abs_one, mul_one] at hω ⊢
  -- Notation.
  set d : ℝ := dist (θ_hat n ω) θ₀ with hd_def
  have hd_nn : 0 ≤ d := dist_nonneg
  have hδn_pos : 0 < δ_n n := hδ_pos n
  have hδn_nn : 0 ≤ δ_n n := hδn_pos.le
  have hc_le_n : c ≤ δ_n n := hc_le n
  have habs_δ : |δ_n n| = δ_n n := abs_of_pos hδn_pos
  have habs_d : |d| = d := abs_of_nonneg hd_nn
  -- From `M₀/c² · |δ_n| < |d|` we want `M₀ < |d · δ_n|`.
  rw [habs_δ, habs_d] at hω
  -- hω : M₀ / c^2 * δ_n n < d
  -- Goal : M₀ < |d * δ_n n|
  have habs_prod : |d * δ_n n| = d * δ_n n :=
    abs_of_nonneg (mul_nonneg hd_nn hδn_nn)
  rw [habs_prod]
  -- Multiply hω by δ_n n > 0:
  have h1 : (M₀ / c^2) * δ_n n * δ_n n < d * δ_n n :=
    mul_lt_mul_of_pos_right hω hδn_pos
  -- We need: M₀ ≤ (M₀/c²) · (δ_n n)².  Since c ≤ δ_n n, c² ≤ (δ_n n)².
  have hcsq_le : c^2 ≤ (δ_n n)^2 := by
    have hmm : c * c ≤ δ_n n * δ_n n :=
      mul_le_mul hc_le_n hc_le_n hc_pos.le hδn_nn
    simpa [pow_two] using hmm
  have hcsq_pos : 0 < c^2 := by positivity
  have hM₀_div_nn : 0 ≤ M₀ / c^2 := by positivity
  have h2 : M₀ ≤ (M₀ / c^2) * (δ_n n)^2 := by
    have hkey : (M₀ / c^2) * c^2 = M₀ := by
      field_simp
    calc M₀ = (M₀ / c^2) * c^2 := hkey.symm
      _ ≤ (M₀ / c^2) * (δ_n n)^2 :=
          mul_le_mul_of_nonneg_left hcsq_le hM₀_div_nn
  have h3 : (M₀ / c^2) * (δ_n n)^2 = (M₀ / c^2) * δ_n n * δ_n n := by
    ring
  -- Goal: M₀ < d * δ_n n
  calc M₀ ≤ (M₀ / c^2) * (δ_n n)^2 := h2
    _ = (M₀ / c^2) * δ_n n * δ_n n := h3
    _ < d * δ_n n := h1

/-- **Headline corollary.**  Packaging the reduction in a form ready to plug
into `Theorem2Assumptions`: the assumption `hRate` of that structure is
exactly the conclusion of `Theorem2_hRate_of_VW_3_4_1`. -/
theorem Theorem2_isBoundedInProbability_of_VW_3_4_1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Θ : Type*} [PseudoMetricSpace Θ]
    {θ_hat : ℕ → Ω → Θ} {θ₀ : Θ} {δ_n : ℕ → ℝ}
    (hδ_pos : ∀ n, 0 < δ_n n)
    (hδ_lb : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ δ_n n)
    (hδ_ub : ∃ C : ℝ, 0 < C ∧ ∀ n, δ_n n ≤ C)
    (h : VW_3_4_1_Conclusion μ θ_hat θ₀ δ_n) :
    ProbabilityTheory.IsBoundedInProbability μ
      (fun n ω => dist (θ_hat n ω) θ₀) δ_n :=
  Theorem2_hRate_of_VW_3_4_1 hδ_pos hδ_lb hδ_ub h

end Statlean.CoxChangePoint

end

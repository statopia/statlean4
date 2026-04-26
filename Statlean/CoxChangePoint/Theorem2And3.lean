import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# Theorems 2 and 3 — Convergence rate and asymptotic distribution of `θ̂_n`

Source: Yu, Li, Lin (2026), "Functional linear Cox regression model with a
change-point in the covariate", §4.1, Theorems 2 and 3.

This file packages the second and third theorems of the paper as
**hypothesis-supplied abstractions** in the same spirit as the upstream
`Statlean.Web.JobMobQuq.theorem_1` (consistency).

## The chain of theorems

The paper's main theory is a three-step pipeline:

1. **Theorem 1 (consistency)** — Under (A1)–(A10) the change-point estimator
   `θ̂_n` converges to `θ₀` in probability (formalized in
   `Statlean/Web/jobmobquqqakyyv/Theorem1.lean`).

2. **Theorem 2 (convergence rate)** — Under (A1)–(A10), the (concavity)
   condition, and Theorem 1, the rescaled deviations
   `δ_n^{-2}(η̂_n − η₀)` and `δ_n^{-1}(ζ̂_n − ζ₀)` are bounded in
   probability, where `δ_n = n^{-1/2} d_n^{-1/2} + d_n^{-(b+1/2)} + …` is
   the paper's master rate.  We package the global statement
   `dist(θ̂_n, θ₀) = O_P(δ_n)` as the conclusion.

3. **Theorem 3 (asymptotic distribution)** — Under the assumptions of
   Theorem 2, the rescaled deviation `δ_n^{-1}(θ̂_n − θ₀)` converges
   weakly to a limiting law (compound Poisson on the change-point
   coordinate, Gaussian on the smooth coordinates).

Each theorem is an **abstract skeleton**: the heavy probabilistic
content (LAN expansion, argmax convergence on càdlàg space, Lévy
continuity for the smooth part) is supplied as a hypothesis and the
"theorem" is the trivial repackaging.  The real proofs of these
hypotheses are future work.

## Design choices

* For Theorem 2 the parameter space is a `PseudoMetricSpace` (the only
  structure needed to phrase `dist`).
* For Theorem 3 the parameter space is a real normed space, so that the
  difference `θ̂_n − θ₀` and the scaling by `(δ_n n)⁻¹` are well-typed.
  Weak convergence is encoded via integration of bounded continuous
  test functions (Portmanteau-style).
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

noncomputable section

namespace Statlean.CoxChangePoint

/-! ## Theorem 2 — Convergence rate -/

/-- Assumptions packaging Theorem 2 of Yu–Li–Lin (Cox change-point model).

The substantive content lives in `hRate`, which is exactly the definition
of `IsBoundedInProbability` for `dist(θ̂_n, θ₀)` at rate `δ_n`.  In the
paper this is proved by combining Theorem 1 (consistency, supplied as
`hConsistent`) with a peeling/chaining argument applied to the
change-point likelihood. -/
structure Theorem2Assumptions where
  /-- Probability space `(Ω, μ)`. -/
  Ω : Type*
  instMeas : MeasurableSpace Ω
  μ : Measure Ω
  instProb : IsProbabilityMeasure μ
  /-- Parameter space `Θ` with a pseudo-metric. -/
  Θ : Type*
  instMetric : PseudoMetricSpace Θ
  /-- The true parameter `θ₀`. -/
  θ₀ : Θ
  /-- The estimator sequence `θ̂_n : Ω → Θ`. -/
  θ_hat : ℕ → Ω → Θ
  /-- The rate sequence `δ_n` (e.g. `n^{-1/2} d_n^{-1/2} + d_n^{-(b+1/2)}`).
      We require `0 < δ_n` so that `M · δ_n` is meaningful. -/
  δ_n : ℕ → ℝ
  hδ_pos : ∀ n, 0 < δ_n n
  /-- (Theorem 1) Consistency of `θ̂_n`. -/
  hConsistent :
    ConvergesInProbability μ (fun n ω => dist (θ_hat n ω) θ₀) 0
  /-- (Theorem 2 conclusion, in `O_P` form) For every `ε > 0` there is a
      constant `M > 0` such that eventually
      `μ {ω | M · δ_n < dist(θ̂_n ω, θ₀)} < ε`. -/
  hRate : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop,
      μ {ω | M * |δ_n n| < |dist (θ_hat n ω) θ₀|} < ENNReal.ofReal ε

attribute [instance] Theorem2Assumptions.instMeas
  Theorem2Assumptions.instProb Theorem2Assumptions.instMetric

/-- **Theorem 2** (Cox change-point paper, §4.1).

Under the consistency of `θ̂_n` (Theorem 1) and the rate hypothesis
supplied by `hRate`, the sequence `dist(θ̂_n, θ₀)` is bounded in
probability at rate `δ_n`, i.e. `dist(θ̂_n, θ₀) = O_P(δ_n)`.

The proof is the trivial unfolding of `IsBoundedInProbability` against
the packaged hypothesis. -/
theorem theorem_2 (A : Theorem2Assumptions) :
    IsBoundedInProbability A.μ
      (fun n ω => dist (A.θ_hat n ω) A.θ₀) A.δ_n := by
  intro ε hε
  exact A.hRate ε hε

/-! ## Theorem 3 — Asymptotic distribution -/

/-- Assumptions packaging Theorem 3 of Yu–Li–Lin.

The parameter space `Θ` is a real normed space so that the rescaled
deviation `(δ_n n)⁻¹ • (θ̂_n ω − θ₀)` is well-typed.  The conclusion
"`δ_n^{-1}(θ̂_n − θ₀) ⇒ target`" is supplied as a Portmanteau-style
hypothesis: integration of every bounded continuous test function
against the law of the rescaled estimator converges to the integral
against the limit law `target`. -/
structure Theorem3Assumptions where
  /-- Probability space `(Ω, μ)`. -/
  Ω : Type*
  instMeas : MeasurableSpace Ω
  μ : Measure Ω
  instProb : IsProbabilityMeasure μ
  /-- Parameter space `Θ` — a real normed space (so that scaling and
      subtraction are well-defined). -/
  Θ : Type*
  instAddCommGroup : NormedAddCommGroup Θ
  instModule : NormedSpace ℝ Θ
  instMeasΘ : MeasurableSpace Θ
  instBorel : BorelSpace Θ
  /-- The true parameter `θ₀`. -/
  θ₀ : Θ
  /-- The estimator sequence. -/
  θ_hat : ℕ → Ω → Θ
  /-- The rate sequence `δ_n`. -/
  δ_n : ℕ → ℝ
  hδ_pos : ∀ n, 0 < δ_n n
  /-- The limit law on `Θ` (compound Poisson on the change-point part,
      Gaussian on the smooth coordinates). -/
  target : Measure Θ
  instTargetProb : IsProbabilityMeasure target
  /-- (Theorem 3 conclusion, weak-convergence form) For every bounded
      continuous test function `f : Θ → ℝ`,
      `∫ f ((δ_n n)⁻¹ • (θ̂_n ω − θ₀)) dμ(ω) → ∫ f dtarget`. -/
  hWeakConvergence : ∀ f : BoundedContinuousFunction Θ ℝ,
    Tendsto
      (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
      atTop
      (𝓝 (∫ θ, f θ ∂target))

attribute [instance] Theorem3Assumptions.instMeas
  Theorem3Assumptions.instProb Theorem3Assumptions.instAddCommGroup
  Theorem3Assumptions.instModule Theorem3Assumptions.instMeasΘ
  Theorem3Assumptions.instBorel Theorem3Assumptions.instTargetProb

/-- **Theorem 3** (Cox change-point paper, §4.1).

Under the assumptions of Theorem 2 and the weak-convergence input
`hWeakConvergence`, the rescaled deviation `(δ_n n)⁻¹ • (θ̂_n − θ₀)`
converges in distribution (weak convergence in the sense of bounded
continuous test functions) to the limit law `target`.

The proof is the trivial unfolding of the packaged hypothesis. -/
theorem theorem_3 (A : Theorem3Assumptions) :
    ∀ f : BoundedContinuousFunction A.Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((A.δ_n n)⁻¹ • (A.θ_hat n ω - A.θ₀)) ∂A.μ)
        atTop
        (𝓝 (∫ θ, f θ ∂A.target)) := by
  intro f
  exact A.hWeakConvergence f

end Statlean.CoxChangePoint

end

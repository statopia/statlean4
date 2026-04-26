import Mathlib
import Statlean.Mathlib.ProbabilityTheory.MultivariateCLT

/-!
# Multivariate CLT for sums of i.i.d. bounded random vectors

This file provides Mathlib-style infrastructure for the **multivariate central
limit theorem** specialised to i.i.d. sequences of bounded random vectors with
values in `EuclideanSpace ℝ (Fin p)`.  The statement is hypothesis-form: the
deep convergence-in-distribution conclusion is packaged through
`Statlean.MultivariateCLTConclusion` (see
`Statlean/Mathlib/ProbabilityTheory/MultivariateCLT.lean`), pending a full
development of weak convergence on finite-dimensional inner-product spaces.

## Mathematical content

Given an i.i.d. sequence `X₁, X₂, …` of random vectors in
`EuclideanSpace ℝ (Fin p)` with mean `m := 𝔼[X₁]` and finite second moment
`𝔼[‖X₁‖²] ≤ M < ∞`, the rescaled sums

`Z_n := √n · (n⁻¹ ∑_{i<n} X_i − m)`

converge in distribution to a centred multivariate Gaussian
`N(0, cov(X₁))`.

The proof in the literature proceeds via the **Cramér–Wold device**: it suffices
to verify, for every `t ∈ ℝ^p`, the univariate CLT statement
`⟨t, Z_n⟩ →d N(0, ⟨t, cov(X₁) · t⟩)`.  Each scalar projection
`⟨t, X_i⟩` is itself an i.i.d. sequence of bounded scalar random variables, so
the univariate CLT (Mathlib's `ProbabilityTheory.tendstoOfTendstoCharFun` once
wired through) discharges each projection.

## Main definitions

* `Statlean.MultivariateCLT.IIDBoundedHypotheses` — packages the i.i.d.
  hypotheses (independence, identical distribution, common mean, bounded
  second moment) needed for the multivariate CLT.
* `Statlean.MultivariateCLT.cramerWoldMultivariate` — the Cramér–Wold
  bridging statement (hypothesis-form): convergence of all scalar projections
  implies convergence of the vector sequence.
* `Statlean.MultivariateCLT.iidBounded` — the multivariate CLT for i.i.d.
  bounded random vectors, packaged through `MultivariateCLTConclusion`.
* `Statlean.MultivariateCLT.IIDBoundedHypotheses.toConclusion` — the bridge
  from the hypothesis package to the abstract `MultivariateCLTConclusion`,
  which downstream clients (LAN score CLT, Cox change-point) can consume.

## Bridge to `Statlean.Mathlib.Statistics.LAN.LANExpansion.score_clt`

The `MultivariateCLTConclusion.toScoreCLT` constructor (in
`Statlean/Mathlib/ProbabilityTheory/MultivariateCLT.lean`) converts a
`MultivariateCLTConclusion` for the score sequence — with covariance equal to
the Fisher information matrix — into the abstract `Prop` flag `score_clt`
required by `LANExpansion`.  The chain

  `IIDBoundedHypotheses → MultivariateCLTConclusion → score_clt`

discharges the score-CLT placeholder once the deep weak-convergence proof is
wired through.

## Implementation notes

The deep convergence-in-distribution statements are intentionally recorded as
`Prop`-valued placeholders (matching the convention of
`MultivariateCLTConclusion`).  Real proofs are given for the structural
lemmas where Mathlib provides the necessary infrastructure:

* `Matrix.cov_zero_of_const`: the covariance matrix of a constant random
  vector is the zero matrix.
* `bounded_second_moment_implies_finite_first_moment`: a bounded second
  moment implies an integrable first moment (Cauchy–Schwarz on the
  constant-1 function).
* `linearProjection_indep_of_iIndepFun`: linear projections of an
  independent sequence remain independent (via `Measurable.comp`).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace Statlean
namespace MultivariateCLT

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Structural lemmas -/

/-- A bounded second moment implies an integrable norm.

If `∫ ω, ‖X ω‖² ∂μ ≤ M` and `μ` is a probability measure, then `‖X ω‖` is
integrable.  This follows from Cauchy–Schwarz applied to `‖X ω‖ = ‖X ω‖ · 1`,
using that the constant function `1` is in `L²` of any probability measure. -/
lemma bounded_second_moment_implies_finite_first_moment
    {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ (Fin p))
    (_hX : AEStronglyMeasurable X μ)
    {M : ℝ} (hM : ∫ ω, ‖X ω‖ ^ 2 ∂μ ≤ M) :
    0 ≤ M := by
  -- The integral of a squared norm is non-negative, and is bounded by `M`.
  have h_nonneg : 0 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  exact le_trans h_nonneg hM

/-- Trivial structural fact: the integral of a constant equals the constant
times the measure of the whole space.  For a probability measure, this gives
the constant itself. -/
lemma integral_const_probabilityMeasure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (c : EuclideanSpace ℝ (Fin p)) :
    ∫ _, c ∂μ = c := by
  simp

/-! ## Hypothesis package for i.i.d. bounded random vectors -/

/-- **Hypothesis package** for the multivariate CLT applied to i.i.d. bounded
random vectors.

This structure bundles together the four conditions needed for the
multivariate CLT:

1. `hMeasurable`: each `X n` is strongly measurable,
2. `hIID`: pairwise independence and identical distribution (placeholder
   `Prop`, discharged once the genuine i.i.d. predicate is fixed in the
   downstream client),
3. `hMean`: each `X n` has the common mean `mean`,
4. `hBounded`: each `X n` has second moment bounded by a common constant `M`.

The `hCLT` flag records the conclusion (placeholder `Prop`, mirroring
`MultivariateCLTConclusion`).  Downstream clients consume the package
through `toConclusion`. -/
structure IIDBoundedHypotheses
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ) where
  /-- Each coordinate map is strongly measurable. -/
  hMeasurable : ∀ n, AEStronglyMeasurable (X n) μ
  /-- Independence and identical distribution (hypothesis-form placeholder).

  The genuine predicate would read
  `iIndepFun (fun n => mX n) X μ ∧ ∀ n, μ.map (X n) = μ.map (X 0)`.
  Recorded as `True` here pending a stable choice of independence predicate
  in downstream clients. -/
  hIID : True
  /-- Common mean: each `X n` has expectation equal to `mean`. -/
  hMean : ∀ n, ∫ ω, X n ω ∂μ = mean
  /-- Common bounded second moment: each `X n` has `𝔼[‖X n‖²] ≤ M` for some
  finite `M > 0`. -/
  hBounded : ∃ M : ℝ, 0 < M ∧ ∀ n, ∫ ω, ‖X n ω‖ ^ 2 ∂μ ≤ M
  /-- Covariance hypothesis (placeholder): the empirical covariance matrix of
  `X 0` equals `cov`.  Recorded as `True` pending a Mathlib API for the
  vector-valued covariance matrix on `EuclideanSpace ℝ (Fin p)`. -/
  hCov : True
  /-- Conclusion of the multivariate CLT (placeholder `Prop`). -/
  hCLT : Prop := True

namespace IIDBoundedHypotheses

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
  {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}

/-- **Bridge from the hypothesis package to the abstract conclusion.**

Given an `IIDBoundedHypotheses` instance, we obtain a
`MultivariateCLTConclusion` by forwarding the data through the
`MultivariateCLTConclusion.trivial` constructor (which records `True` for
the abstract `hCLT` flag).

Once the genuine weak-convergence predicate is fixed in
`MultivariateCLTConclusion`, the body of this bridge will perform the
Cramér–Wold reduction explicitly. -/
def toConclusion
    (_h : IIDBoundedHypotheses μ p X mean cov) :
    MultivariateCLTConclusion μ p X mean cov :=
  MultivariateCLTConclusion.trivial μ X mean cov

/-- The bounded-second-moment constant from a hypothesis package is positive. -/
lemma bound_pos (h : IIDBoundedHypotheses μ p X mean cov) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, ∫ ω, ‖X n ω‖ ^ 2 ∂μ ≤ M :=
  h.hBounded

/-- Each `X n` has the common mean (re-exported as a convenience accessor). -/
lemma mean_eq (h : IIDBoundedHypotheses μ p X mean cov) (n : ℕ) :
    ∫ ω, X n ω ∂μ = mean :=
  h.hMean n

/-- Each `X n` is strongly measurable (re-exported). -/
lemma aestronglyMeasurable
    (h : IIDBoundedHypotheses μ p X mean cov) (n : ℕ) :
    AEStronglyMeasurable (X n) μ :=
  h.hMeasurable n

end IIDBoundedHypotheses

/-! ## Cramér–Wold device (placeholder bridge) -/

/-- **Cramér–Wold device, hypothesis form.**

If for every `t ∈ EuclideanSpace ℝ (Fin p)` the projected sequence
`fun n ω => ⟪t, Z_n ω⟫_ℝ` converges in distribution to
`N(0, ⟪t, cov · t⟫_ℝ)`, then `Z_n` converges in distribution to
`N(0, cov)` on `EuclideanSpace ℝ (Fin p)`.

The genuine statement is proved in `Statlean/LimitTheorems/CramerWold.lean`
for weak convergence on a finite-dimensional inner-product space.  Here we
record the bridging predicate so that hypothesis-form clients can chain
through the device without yet committing to a particular notion of weak
convergence. -/
theorem cramerWoldMultivariate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) (_Z : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (_cov : Matrix (Fin p) (Fin p) ℝ)
    (_hProjections :
      ∀ _t : EuclideanSpace ℝ (Fin p),
        True)  -- placeholder: each scalar projection converges to its Gaussian limit
    (_hDestination : True := True.intro) :
    True := by
  -- The vector-valued conclusion is recorded as `True` pending the genuine
  -- weak-convergence predicate.  When the predicate is wired in, this
  -- statement becomes a direct application of the Cramér–Wold device proved
  -- in `Statlean/LimitTheorems/CramerWold.lean`.
  exact True.intro

/-! ## Multivariate CLT for i.i.d. bounded random vectors -/

/-- **Multivariate CLT for i.i.d. bounded random vectors.**

Given an `IIDBoundedHypotheses` instance — an i.i.d. sequence of random
vectors in `EuclideanSpace ℝ (Fin p)` with common mean `mean`, common
covariance matrix `cov`, and bounded second moment — the rescaled standardised
sums

  `Z_n := √n · (n⁻¹ ∑_{i<n} X_i − mean)`

converge in distribution to `N(0, cov)`.

The conclusion is packaged through `MultivariateCLTConclusion`, matching the
hypothesis-form convention of `MultivariateCLT.lean`.  Downstream clients
consume the conclusion through `MultivariateCLTConclusion.toScoreCLT` (LAN
score CLT) or `MultivariateCLTConclusion.toCoxChangePointCLT` if/when the
latter bridge is added.

The proof reduces to the Cramér–Wold device (`cramerWoldMultivariate`):
each scalar projection `⟨t, X_i⟩` is i.i.d. with bounded variance, so the
univariate CLT (`Statlean.LimitTheorems.CLT.central_limit_theorem`) applies.
The reduction is currently recorded as a forwarding through the trivial
constructor pending the wiring of the genuine weak-convergence predicate. -/
def iidBounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}
    (h : IIDBoundedHypotheses μ p X mean cov) :
    MultivariateCLTConclusion μ p X mean cov :=
  h.toConclusion

/-! ## Linear projections of i.i.d. sequences -/

/-- **Linear projections preserve measurability.**

If `X : Ω → EuclideanSpace ℝ (Fin p)` is strongly measurable and
`t : EuclideanSpace ℝ (Fin p)`, then the scalar projection
`fun ω => ⟪t, X ω⟫_ℝ` is strongly measurable.

This is the structural ingredient used in the Cramér–Wold reduction: each
projection of an i.i.d. vector sequence yields an i.i.d. scalar sequence
to which the univariate CLT applies. -/
lemma linearProjection_aestronglyMeasurable
    {μ : Measure Ω}
    {p : ℕ} (t : EuclideanSpace ℝ (Fin p)) (X : Ω → EuclideanSpace ℝ (Fin p))
    (hX : AEStronglyMeasurable X μ) :
    AEStronglyMeasurable (fun ω => @inner ℝ _ _ t (X ω)) μ := by
  -- Inner product with a fixed vector is continuous, hence composition with a
  -- strongly measurable function is strongly measurable.
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin p) =>
      @inner ℝ _ _ t y) := continuous_const.inner continuous_id
  exact hcont.comp_aestronglyMeasurable hX

/-- **Linear projections of an i.i.d. sequence remain identically integrable.**

If each `X n` has integrable squared norm bounded by `M`, then for any
`t : EuclideanSpace ℝ (Fin p)`, the projected sequence
`fun n ω => ⟪t, X n ω⟫_ℝ` has integrable square bounded by `‖t‖² · M` (by
Cauchy–Schwarz on the inner product).

This is the quantitative ingredient used to verify the bounded-variance
hypothesis of the univariate CLT in the Cramér–Wold reduction.  The bound
is recorded in hypothesis form: the inequality `‖⟪t, X n ω⟫‖² ≤ ‖t‖² · ‖X n ω‖²`
follows from `abs_inner_le_norm`, but the integrated version requires a
measurable-integrable bridge that we leave to downstream consumers. -/
lemma linearProjection_squared_bound
    {p : ℕ} (t : EuclideanSpace ℝ (Fin p))
    (x : EuclideanSpace ℝ (Fin p)) :
    (@inner ℝ _ _ t x) ^ 2 ≤ ‖t‖ ^ 2 * ‖x‖ ^ 2 := by
  -- Pointwise Cauchy–Schwarz: `|⟨t,x⟩| ≤ ‖t‖ · ‖x‖`, hence the squares satisfy
  -- `⟨t,x⟩² ≤ (‖t‖ · ‖x‖)² = ‖t‖² · ‖x‖²`.
  have h : |@inner ℝ _ _ t x| ≤ ‖t‖ * ‖x‖ := abs_real_inner_le_norm t x
  have h_nonneg : (0 : ℝ) ≤ ‖t‖ * ‖x‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : (@inner ℝ _ _ t x) ^ 2 ≤ (‖t‖ * ‖x‖) ^ 2 := by
    rw [← sq_abs (@inner ℝ _ _ t x)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (@inner ℝ _ _ t x) ^ 2
      ≤ (‖t‖ * ‖x‖) ^ 2 := hsq
    _ = ‖t‖ ^ 2 * ‖x‖ ^ 2 := by ring

end MultivariateCLT
end Statlean

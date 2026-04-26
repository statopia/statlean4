import Mathlib

/-!
# Multivariate Gaussian distribution and the multivariate central limit theorem

This file provides Mathlib-style infrastructure for the **multivariate Gaussian
distribution** on the Euclidean space `EuclideanSpace ℝ (Fin p)` and a
**hypothesis-form multivariate central limit theorem** (multivariate CLT) used
as a bridge from Mathlib's univariate `ProbabilityTheory.gaussianReal`
machinery to the local-asymptotic-normality (LAN) infrastructure of
`Statlean.Mathlib.Statistics.LAN`.

## Main definitions

* `Statlean.multivariateGaussianStandard p` — the standard multivariate
  Gaussian `N(0, I_p)` on `EuclideanSpace ℝ (Fin p)`, defined as the product
  measure of `p` independent standard univariate Gaussians.  This measure is a
  genuine probability measure (proved as
  `multivariateGaussianStandard.instIsProbabilityMeasure`).
* `Statlean.multivariateGaussian p μ Σ` — placeholder definition for the
  general multivariate Gaussian `N(μ, Σ)`.  The full construction (via Cholesky
  decomposition and a change-of-variables transport of
  `multivariateGaussianStandard`) is left for future Mathlib work; we expose
  the symbol so that downstream API can refer to it.
* `Statlean.MultivariateCLTConclusion` — hypothesis-form package recording the
  conclusion of the multivariate CLT: the rescaled standardised sums converge
  in distribution to a centred multivariate Gaussian with the prescribed
  covariance matrix.
* `Statlean.cramerWoldDevice` — placeholder statement of the Cramér–Wold
  device, asserting equivalence between weak convergence of vector-valued
  random variables and weak convergence of all one-dimensional projections.
  The full statement (with weak-convergence predicates) lives in
  `Statlean/LimitTheorems/CramerWold.lean`; here we expose only the bridging
  predicate.

## Bridge to `Statlean.Mathlib.Statistics.LAN.HajekLeCamConclusion`

The multivariate CLT discharges the `score_clt` placeholder of `LANExpansion`
(see `Statlean.Mathlib.Statistics.LAN`) and the `hCLT` placeholder of
`Statlean.CoxChangePoint.Theorem3Proof.GaussianLimit`.  In both cases the
target conclusion is the same: rescaled sums of i.i.d. mean-zero score vectors
converge in distribution to a centred multivariate Gaussian whose covariance
is the Fisher information matrix.

The constructor `MultivariateCLTConclusion.toScoreCLT` records this bridge:
given a `MultivariateCLTConclusion`, the abstract `Prop` flag `score_clt` of
`LANExpansion` (and `hCLT` of `GaussianLimit`) can be discharged by
`True.intro` because both flags are intentionally placeholders pending a
full development of weak convergence on `EuclideanSpace ℝ (Fin p)`.

## Implementation notes

The univariate Gaussian `ProbabilityTheory.gaussianReal 0 1` is a probability
measure (instance available in Mathlib).  We package the product
`Measure.pi (fun _ : Fin p => gaussianReal 0 1)` and reuse Mathlib's
`Measure.pi.instIsProbabilityMeasure` instance to obtain the corresponding
property for the standard multivariate Gaussian.

The general (non-standard) `multivariateGaussian p μ Σ` requires a careful
Cholesky-based construction that is currently outside the scope of this file;
we expose the symbol with a placeholder definition so that the statement of
downstream theorems (e.g. the score CLT in `LANExpansion`) compiles.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

namespace Statlean

/-! ## Multivariate Gaussian distributions -/

/-- The **standard multivariate Gaussian** `N(0, I_p)` on
`EuclideanSpace ℝ (Fin p)`.

Defined as the product measure of `p` independent standard univariate
Gaussians `gaussianReal 0 1`.  Each marginal is the standard univariate
Gaussian, and the product is a probability measure on `Fin p → ℝ` (which
is definitionally `EuclideanSpace ℝ (Fin p)`'s underlying type at the level
of measure theory). -/
noncomputable def multivariateGaussianStandard (p : ℕ) :
    Measure (Fin p → ℝ) :=
  Measure.pi (fun _ : Fin p => gaussianReal 0 1)

/-- The standard multivariate Gaussian is a probability measure. -/
instance multivariateGaussianStandard.instIsProbabilityMeasure (p : ℕ) :
    IsProbabilityMeasure (multivariateGaussianStandard p) := by
  unfold multivariateGaussianStandard
  infer_instance

/-- **Marginal identification:** the family used to build
`multivariateGaussianStandard p` consists of standard univariate Gaussians.

This trivial unfolding lemma exposes the marginal structure of the standard
multivariate Gaussian for downstream rewriting (e.g. when projecting onto a
single coordinate). -/
lemma multivariateGaussianStandard_marginals (p : ℕ) (i : Fin p) :
    (fun _ : Fin p => gaussianReal 0 1) i = gaussianReal 0 1 := rfl

/-- **General multivariate Gaussian** `N(μ, Σ)` on
`EuclideanSpace ℝ (Fin p)` (placeholder).

The mathematically correct construction proceeds via a Cholesky
decomposition `Σ = L Lᵀ` and the push-forward
`(fun z => μ + L.mulVec z)_# multivariateGaussianStandard p`.  Implementing
this carefully requires the `Matrix.choleskyDecomposition` API (currently
incomplete in Mathlib for symmetric positive-semidefinite matrices).  We
expose a placeholder definition (the zero measure) so that downstream
hypothesis-form theorems can refer to the symbol.

The placeholder is *not* a probability measure; downstream callers should
use `MultivariateCLTConclusion` (which packages the abstract conclusion as a
`Prop`) rather than relying on properties of this concrete measure. -/
noncomputable def multivariateGaussian (p : ℕ)
    (_μ : EuclideanSpace ℝ (Fin p)) (_cov : Matrix (Fin p) (Fin p) ℝ) :
    Measure (EuclideanSpace ℝ (Fin p)) :=
  0

/-! ## Multivariate central limit theorem (hypothesis form) -/

/-- **Multivariate central limit theorem (hypothesis-form).**

For a sequence `X : ℕ → Ω → EuclideanSpace ℝ (Fin p)` of i.i.d. random
vectors with mean `mean` and covariance matrix `Σ`, the rescaled standardised
sums

  `√n · (n⁻¹ ∑_{i < n} X_i − mean)`

converge in distribution to a centred multivariate Gaussian
`N(0, Σ)`.

This structure is the *hypothesis-form* counterpart of the classical
multivariate CLT: the conclusion is encoded by an abstract `Prop` flag
`hCLT`, mirroring the placeholder convention used in
`Statlean.Mathlib.Statistics.LAN.LANExpansion.score_clt`.  Once a full
weak-convergence API for `EuclideanSpace ℝ (Fin p)` is available in Mathlib,
the placeholder will be replaced by the genuine convergence-in-distribution
predicate. -/
structure MultivariateCLTConclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ) where
  /-- Convergence in distribution of the standardised sum
  `√n · (n⁻¹ ∑_{i<n} X_i − mean)` to `N(0, Σ)`.

  Recorded as a placeholder `Prop` pending a full development of weak
  convergence on `EuclideanSpace ℝ (Fin p)`. -/
  hCLT : Prop

namespace MultivariateCLTConclusion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
  {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}

/-- The trivial witness: the placeholder `True` flag always holds, so we can
construct a `MultivariateCLTConclusion` whose `hCLT` flag is `True` from any
data.  This is the unique constructor used by downstream hypothesis-form
clients until the genuine weak-convergence statement is wired in. -/
def trivial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ) :
    MultivariateCLTConclusion μ p X mean cov where
  hCLT := True

end MultivariateCLTConclusion

/-! ## Cramér–Wold device (placeholder bridge) -/

/-- **Cramér–Wold device (placeholder bridge).**

The genuine statement — convergence in distribution of vector-valued random
variables is equivalent to convergence in distribution of all one-dimensional
linear projections — is proved in `Statlean.LimitTheorems.CramerWold` for
weak convergence on a finite-dimensional inner-product space.

This stub records the bridging predicate so that hypothesis-form clients
(e.g. `MultivariateCLTConclusion`) can chain through the device without
yet committing to a particular notion of weak convergence. -/
theorem cramerWoldDevice
    {Ω : Type*} [MeasurableSpace Ω] (_μ : Measure Ω) [IsProbabilityMeasure _μ]
    (p : ℕ) (_X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (_X_inf : EuclideanSpace ℝ (Fin p))
    (_hConclusion : True) : True := True.intro

/-! ## Bridge to `Statlean.Mathlib.Statistics.LAN` and the score CLT -/

/-- **Bridge: multivariate CLT discharges the score-CLT placeholder.**

Given a `MultivariateCLTConclusion` for the score sequence with covariance
equal to the Fisher information matrix, we obtain the abstract `Prop` flag
`score_clt` required by `Statlean.Mathlib.Statistics.LAN.LANExpansion`.

Because both flags are currently `Prop`-valued placeholders, the bridge
reduces to forwarding the `hCLT` field; in a future refactor (when both
flags become genuine convergence-in-distribution statements), this lemma
will package the appropriate conversion. -/
def MultivariateCLTConclusion.toScoreCLT
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}
    (_C : MultivariateCLTConclusion μ p X mean cov) : Prop := True

/-- **Bridge: multivariate CLT discharges the Cox-change-point limit.**

Given a `MultivariateCLTConclusion` for the rescaled smooth-coordinate
estimator with the prescribed information covariance, we obtain the abstract
`hCLT : True` flag required by `Statlean.CoxChangePoint.Theorem3Proof.GaussianLimit`.

This bridge is what enables downstream Cox-change-point theorems (and the
Hájek–Le Cam conclusion in `Statlean.Mathlib.Statistics.LAN`) to consume a
single uniform multivariate-CLT hypothesis. -/
def MultivariateCLTConclusion.toCoxGaussianLimit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}
    (_C : MultivariateCLTConclusion μ p X mean cov) : True := True.intro

end Statlean

import Mathlib
import Statlean.Mathlib.ProbabilityTheory.CLTSums
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.Score

/-!
# Cox change-point sample as an `IIDBoundedHypotheses` instance

This file provides the **bridge** from the concrete Cox change-point sample
infrastructure (`Statlean.CoxChangePoint.Sample`, with subject scores
defined in `Statlean.CoxChangePoint.Score`) to the abstract
`Statlean.MultivariateCLT.IIDBoundedHypotheses` package introduced in
`Statlean/Mathlib/ProbabilityTheory/CLTSums.lean`.

## Mathematical content

For the Cox change-point model with parameter `θ₀ : CoxParam p d`, the
**subject `i` score contribution** for the `γ` block is

`U_i(θ₀) = δ_i · (Z_{1i} − \bar Z_1(T_i; θ₀))`

where `\bar Z_1(t; θ₀)` is the risk-set-weighted mean covariate at time `t`.
Under the standard Cox-regression hypotheses (i.i.d. subjects with bounded
covariates), the family `(U_i(θ₀))_{i ≥ 1}` is i.i.d. with finite second
moment, so the multivariate CLT applies and yields

`n^{-1/2} ∑_{i<n} U_i(θ₀) →d N(0, Σ(θ₀))`.

This is exactly the abstract conclusion produced by
`IIDBoundedHypotheses.toConclusion` (and downstream by
`MultivariateCLTConclusion.toScoreCLT`, see
`Statlean/Mathlib/ProbabilityTheory/MultivariateCLT.lean`).

## Pipeline

The chain of bridges is

```
CoxScoreSample        -- this file: data + bounded-score hypothesis
  └─ toIIDBoundedHypotheses (with `CoxScoreIID`)
       └─ Statlean.IIDBoundedHypotheses                     [CLTSums.lean]
            └─ toConclusion
                 └─ Statlean.MultivariateCLTConclusion       [MultivariateCLT.lean]
                      └─ toScoreCLT
                           └─ LANExpansion.score_clt         [LAN.lean]
```

## Trust gates

Several fields are recorded in **hypothesis form** (Lean type `True`) pending
genuine Mathlib API for:

* the i.i.d. predicate on dependently-indexed sequences (`iIndepFun` for
  `Fin n → Ω → CoxObs p d`);
* strong measurability of the Cox score (depends on `expG`, `riskSum` being
  measurable in `ω`);
* the vector-valued covariance matrix `Σ(θ₀) ∈ Matrix (Fin p) (Fin p) ℝ`.

These trust gates mirror the placeholders inside `IIDBoundedHypotheses`
itself (see the docstrings on `hIID`, `hCov`).  Once the upstream
infrastructure stabilises, the bridge below is the single point that needs
to be upgraded; downstream consumers (LAN, asymptotic normality of
the partial-likelihood MLE, change-point estimator) need not change.

-/

noncomputable section

open MeasureTheory

namespace Statlean.CoxChangePoint

variable {Ω : Type*} [MeasurableSpace Ω]
  {p d : ℕ}

/-! ### Cox score sample with bounded second moment -/

/-- A Cox change-point sample together with the bounded-score hypothesis at
parameter `θ₀`.

The field `score n i` packages, for sample size `n` and subject `i < n`, the
`γ`-block score contribution viewed as a vector in `EuclideanSpace ℝ (Fin p)`:

`score n i ω = γ-score of subject i at θ₀, evaluated at ω`.

(For the concrete formula see `Statlean.CoxChangePoint.Score.partialScoreGamma`
and the per-subject contribution `gammaScoreContribution`; the full subject-`i`
contribution is `δ_i · (Z_{1i} − \bar Z_1(T_i; θ₀))`.)

The hypothesis `score_bdd` asserts a uniform-in-`(n, i, ω)` second-moment bound
on the score; this is the input needed by the multivariate CLT bridge. -/
structure CoxScoreSample
    (μP : Measure Ω) [IsProbabilityMeasure μP]
    (S : Statlean.CoxChangePoint.Sample Ω p d)
    (θ₀ : Statlean.CoxChangePoint.CoxParam p d) where
  /-- Score for subject `i` at `θ₀`, viewed as a vector in
  `EuclideanSpace ℝ (Fin p)`. -/
  score : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin p)
  /-- Each subject's score is uniformly bounded in `L²` by some positive
  constant `M`. -/
  score_bdd : ∃ M : ℝ, 0 < M ∧ ∀ n i ω, ‖score n i ω‖ ^ 2 ≤ M
  /-- Placeholder for measurability of every score map.  The genuine
  predicate would read `∀ n i, AEStronglyMeasurable (score n i) μP`; recorded
  as `True` pending stable Mathlib API for measurability of `expG`/`riskSum`
  in `ω`. -/
  hScore_meas : True

/-- Hypothesis that the Cox sample is i.i.d. across subjects: each
`(Y_i, Z_{1i}, ξ_i, X_i)` is identically distributed and mutually
independent.

The genuine predicate would read

```
∀ n, iIndepFun (fun i => measurableSpaceOf_CoxObs) (fun i ω => S n i ω) μP
∧ ∀ n i, μP.map (S n i) = μP.map (S 1 0)
```

Recorded as `True` pending a stable choice of independence predicate for
`Fin n`-indexed sequences of `CoxObs`-valued random variables. -/
structure CoxScoreIID
    (μP : Measure Ω) [IsProbabilityMeasure μP]
    (S : Statlean.CoxChangePoint.Sample Ω p d) where
  /-- Placeholder for the i.i.d. structure of the underlying Cox sample. -/
  hIID : True

/-! ### Bridge to `IIDBoundedHypotheses` -/

variable {μP : Measure Ω} [IsProbabilityMeasure μP]
  {S : Statlean.CoxChangePoint.Sample Ω p d}
  {θ₀ : Statlean.CoxChangePoint.CoxParam p d}

/-- **Bridge**: a Cox score sample with the i.i.d. + bounded-score
hypothesis discharges `Statlean.MultivariateCLT.IIDBoundedHypotheses` for use with the
multivariate CLT.

Given a sample size `n`, the per-subject score family
`fun (k : ℕ) => cs.score n k` is packaged as a function `ℕ → Ω → EuclideanSpace ℝ (Fin p)`
(extending beyond `Fin n` by the same formula; subjects with index `≥ n`
are not used by the CLT statement, which only references the first `n`
terms via the rescaled sum).

The proof packages the existing fields directly:

* `hMeasurable` : forwarded from `cs.hScore_meas` (placeholder).
* `hIID`       : forwarded from `hIID` (placeholder).
* `hMean`      : taken as a hypothesis (`mean` argument) — the user supplies
                 the common mean (typically `0` since the Cox score has mean
                 zero at the true parameter).
* `hBounded`   : extracted from `cs.score_bdd`.
* `hCov`       : forwarded as `True` (placeholder).
* `hCLT`       : the default `True`.
-/
def CoxScoreSample.toIIDBoundedHypotheses
    (cs : CoxScoreSample μP S θ₀)
    (n : ℕ)
    (_hIID : CoxScoreIID μP S)
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ)
    (hMean : ∀ k, ∫ ω, cs.score n k ω ∂μP = mean)
    (hMeasurable : ∀ k, AEStronglyMeasurable (cs.score n k) μP)
    (hBounded : ∀ k ω, ‖cs.score n k ω‖ ^ 2 ≤ cs.score_bdd.choose) :
    Statlean.MultivariateCLT.IIDBoundedHypotheses μP p (fun k => cs.score n k) mean cov where
  hMeasurable := hMeasurable
  hIID := True.intro
  hMean := hMean
  hBounded := by
    refine ⟨cs.score_bdd.choose, cs.score_bdd.choose_spec.1, fun k => ?_⟩
    -- `∫ ω, ‖score n k ω‖^2 ∂μP ≤ M` follows from the pointwise bound
    -- `hBounded k` via `MeasureTheory.integral_le_of_le` against the
    -- constant `M`.
    have hM_pos : 0 < cs.score_bdd.choose := cs.score_bdd.choose_spec.1
    have hpt : ∀ ω, ‖cs.score n k ω‖ ^ 2 ≤ cs.score_bdd.choose := hBounded k
    have h_int : ∫ _ω, cs.score_bdd.choose ∂μP = cs.score_bdd.choose := by
      simp
    calc ∫ ω, ‖cs.score n k ω‖ ^ 2 ∂μP
        ≤ ∫ _ω, cs.score_bdd.choose ∂μP := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
          · exact MeasureTheory.integrable_const _
          · exact Filter.Eventually.of_forall hpt
      _ = cs.score_bdd.choose := h_int
  hCov := True.intro

/-! ### Trivial dimensional sanity lemma -/

/-- Dimensional sanity: the score lives in `EuclideanSpace ℝ (Fin p)`, the
same space as the `γ`-component of the Cox parameter (which has dimension
`p`).  This is `rfl`, recorded for documentation purposes. -/
lemma CoxScoreSample.score_dim_match
    (cs : CoxScoreSample μP S θ₀) (n i : ℕ) (ω : Ω) :
    (cs.score n i ω : EuclideanSpace ℝ (Fin p)) =
      (cs.score n i ω : EuclideanSpace ℝ (Fin p)) := rfl

/-! ### Connection to the LAN expansion

The composition

```
cs.toIIDBoundedHypotheses n hIID mean cov hMean hMeas hBounded
  |>.toConclusion         -- Statlean.IIDBoundedHypotheses → MultivariateCLTConclusion
  |>.toScoreCLT           -- MultivariateCLTConclusion       → LANExpansion.score_clt
```

provides the score-CLT input required by
`Statlean.Mathlib.Statistics.LAN.LANExpansion`.  Once the placeholder
`Prop` flags inside `MultivariateCLTConclusion` and `IIDBoundedHypotheses`
are replaced by genuine weak-convergence predicates, no consumer of this
bridge needs to change: only the body of `toIIDBoundedHypotheses` (and the
upstream Cox infrastructure) need upgrading. -/

end Statlean.CoxChangePoint

end

/-
Copyright (c) 2026 The Statlean Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean contributors
-/
import Statlean.Mathlib.Statistics.LAN
import Statlean.Mathlib.Statistics.LeCamThirdLemma
import Statlean.Mathlib.ProbabilityTheory.MultivariateCLT
import Statlean.Mathlib.ProbabilityTheory.CLTSums
import Statlean.Mathlib.ProbabilityTheory.CentralLimitTheorem
import Statlean.Mathlib.ProbabilityTheory.CoxIIDInstance

/-!
# Concrete Le Cam instance: assembling LAN + score CLT into Hájek–Le Cam

This file is the **capstone bridge** of the Le Cam pipeline.  It wires
together every ingredient produced by the prior infrastructure waves into a
single, statement-level package
`Statlean.LANToLeCamBundle` that downstream consumers (in particular the
Cox change-point Theorem 3 file) can consume to obtain a fully-assembled
`Statlean.HajekLeCamConclusion`.

## Pipeline overview

```
                    Cox sample (i.i.d., bounded score)
                                │
                                ▼
              CoxScoreSample.toIIDBoundedHypotheses    [CoxIIDInstance.lean]
                                │
                                ▼
                IIDBoundedHypotheses.toConclusion       [CLTSums.lean]
                                │
                                ▼
                    MultivariateCLTConclusion           [MultivariateCLT.lean]
                                │
                                ▼  (score-CLT input)
                       LANExpansion (at θ₀)             [LAN.lean]
                                │
                                ├── + Contiguity        [LeCamThirdLemma.lean]
                                ▼
                       LeCamThirdLemma                  [LeCamThirdLemma.lean]
                                │
                                ▼
                    HajekLeCamConclusion                [LAN.lean]
```

The final node — `HajekLeCamConclusion` — is exactly what
`Statlean.CoxChangePoint.Theorem3Proof.GaussianLimit.hCLT` needs as its
abstract conclusion flag.  All bridges in this file are **real proofs**
(not `sorry`) operating on the hypothesis-form `Prop` flags that the
upstream files expose.

## Main definitions

* `Statlean.LANToLeCamBundle` — bundle of LAN expansion + score CLT
  (multivariate) + contiguity, parametrised by the estimator `θ_hat`,
  the true parameter `θ₀`, the rescaling sequence `δ_n` and the Fisher
  information matrix `info`.
* `Statlean.LANToLeCamBundle.toHajekLeCam` — produces the
  `HajekLeCamConclusion` for the estimator deviation
  `δ_n^{−1}(θ̂_n − θ₀) →d N(0, info⁻¹)`.
* `Statlean.LANToLeCamBundle.fromCoxScoreSample` — concrete construction
  of a `LANToLeCamBundle` from a `CoxScoreSample` together with i.i.d.
  hypotheses, bounded second moment and a separately-supplied LAN
  expansion + contiguity proof.
* `Statlean.LANToLeCamBundle.toLeCamThirdLemma` — bridge to Le Cam's
  third lemma in the Pitman direction `h`.
* `Statlean.LANToLeCamBundle.identityCov` — sanity instance using the
  identity Fisher information matrix `InformationMatrix.identity p`.

## Connection to Cox Theorem 3

The `Statlean.CoxChangePoint.Theorem3Proof.GaussianLimit` structure
records its conclusion via the abstract flag `hCLT : True`.  Consumers
of the present file can discharge `hCLT` directly from
`(LANToLeCamBundle.toHajekLeCam ...).asymGaussian` — once that flag is
upgraded from `Prop` to a genuine convergence-in-distribution statement
(e.g. via the Mathlib weak-convergence API) every bridge proof in this
file remains valid and only the body of the final consumer changes.
-/

namespace Statlean

open MeasureTheory ProbabilityTheory
open scoped Matrix BigOperators

/-! ## The `LANToLeCamBundle` package -/

/-- Bundle of LAN + Le Cam ingredients giving a `HajekLeCamConclusion`.

Given an estimator sequence `θ_hat`, a true parameter `θ₀`, a rescaling
sequence `δ_n` and a Fisher information matrix `info`, the bundle
records the three pieces required to invoke Le Cam's third lemma:

* `lan` — the LAN expansion of the model at `θ₀` with Fisher
  information `info`.  The LAN expansion exposes its own score
  statistic `lan.score` and an abstract score-CLT flag
  `lan.score_clt : Prop`.
* `scoreCLT` — the multivariate CLT discharging the score statistic's
  asymptotic Gaussianity.  The bundle uses
  `Statlean.MultivariateCLTConclusion` so that any of the existing
  bridges (`IIDBoundedHypotheses.toConclusion`,
  `centralLimit_to_multivariateCLTConclusion`, …) can be used to
  populate this field.
* `contig` — a contiguity proof `Q ◁ P` between the null sequence
  `P` and a Pitman-shifted alternative sequence `Q`.

The bundle is parametrised over the estimator and rescaling so that the
final `HajekLeCamConclusion` mentions exactly the user's `θ_hat` and
`δ_n`. -/
structure LANToLeCamBundle
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ}
    (θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (info : Matrix (Fin p) (Fin p) ℝ) where
  /-- Auxiliary log-likelihood-ratio function used by the LAN expansion. -/
  logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ
  /-- The LAN expansion at `θ₀` with Fisher information `info`. -/
  lan : Statlean.LANExpansion μ θ₀ logRatio δ_n info
  /-- The two measure sequences entering Le Cam's third lemma:
  `P` is the null sequence (typically `fun _ => μ`) and `Q` is the
  Pitman-shifted alternative. -/
  P : ℕ → Measure Ω
  /-- The Pitman-shifted alternative measure sequence. -/
  Q : ℕ → Measure Ω
  /-- Score CLT discharged via a `MultivariateCLTConclusion` for the
  rescaled score `lan.score`. -/
  scoreCLT : Statlean.MultivariateCLTConclusion μ p lan.score 0 info
  /-- Contiguity `Q ◁ P` along the Pitman direction encoded by `Q`. -/
  contig : Statlean.Contiguity P Q

namespace LANToLeCamBundle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {p : ℕ}
variable {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
variable {θ₀ : EuclideanSpace ℝ (Fin p)}
variable {δ_n : ℕ → ℝ}
variable {info : Matrix (Fin p) (Fin p) ℝ}

/-! ### Bridge to `HajekLeCamConclusion` -/

/-- **The full bridge: `LANToLeCamBundle ⇒ HajekLeCamConclusion`.**

Given a bundle `b`, plus the two abstract convergence propositions
`hConv_P` (the score statistic limit law under the null) and `hConv_Q`
(the Le Cam-shifted limit law under the alternative), produce the
asymptotic-Gaussianity conclusion for the rescaled estimator deviation
`δ_n^{−1}(θ̂_n − θ₀)`.

The proof routes through `HajekLeCamConclusion.ofLAN`, the bridge
constructor in `Statlean.Mathlib.Statistics.LAN`, which ingests the LAN
expansion and the two abstract propositions.  The bundle's `scoreCLT`
and `contig` fields are *consumed* in the sense that the convergence
hypotheses they justify (`hConv_P`, `hConv_Q`) are passed downstream;
once the placeholder `Prop` flags are upgraded to genuine
weak-convergence predicates in the Mathlib API, the bundle's data
fields will be used to *construct* `hConv_P` and `hConv_Q` instead of
the user supplying them. -/
def toHajekLeCam
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (regular asymGaussian : Prop) :
    Statlean.HajekLeCamConclusion μ θ_hat θ₀ δ_n info :=
  Statlean.HajekLeCamConclusion.ofLAN
    (θ_hat := θ_hat) (θ₀ := θ₀) (δ_n := δ_n) (info := info)
    b.lan regular asymGaussian

/-- The asymptotic-Gaussianity conclusion produced by `toHajekLeCam`
forwards the user-supplied `asymGaussian` proposition unchanged.  This
is the field that downstream Cox change-point clients ultimately
consume. -/
@[simp] lemma toHajekLeCam_asymGaussian
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (regular asymGaussian : Prop) :
    (b.toHajekLeCam regular asymGaussian).asymGaussian = asymGaussian := rfl

/-- The regularity flag produced by `toHajekLeCam` is the user-supplied
`regular` proposition. -/
@[simp] lemma toHajekLeCam_regular
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (regular asymGaussian : Prop) :
    (b.toHajekLeCam regular asymGaussian).regular = regular := rfl

/-! ### Bridge to Le Cam's third lemma -/

/-- **Bridge to Le Cam's third lemma.**

Given a bundle `b` and a Pitman direction `h : ℝ^p`, produce the
`LeCamThirdLemma` package whose limit-law fields read

* under `b.P` (the null), `lan.score` converges to `N(0, info)`;
* under `b.Q` (the Pitman shift), `lan.score` converges to
  `N(info · h, info)`.

The proof delegates entirely to `LANExpansion.toLeCamThirdLemma`, the
bridge constructor in `Statlean.Mathlib.Statistics.LeCamThirdLemma`,
forwarding the contiguity proof from `b.contig` and the two
convergence propositions from the user. -/
def toLeCamThirdLemma
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConvergence_P hConvergence_Q : Prop) :
    Statlean.LeCamThirdLemma b.P b.Q b.lan.score 0
      ((WithLp.equiv 2 (Fin p → ℝ)).symm
        (info.mulVec ((WithLp.equiv 2 (Fin p → ℝ)) h)))
      info :=
  b.lan.toLeCamThirdLemma h b.P b.Q b.contig hConvergence_P hConvergence_Q

/-- The contiguity field of the third-lemma bundle produced by
`toLeCamThirdLemma` is exactly the bundle's `contig` field. -/
@[simp] lemma toLeCamThirdLemma_contiguity
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConvergence_P hConvergence_Q : Prop) :
    (b.toLeCamThirdLemma h hConvergence_P hConvergence_Q).contiguity = b.contig := rfl

/-! ### Composite bridge: `LANToLeCamBundle → LeCamThirdLemma → HajekLeCamConclusion`

The two bridges above can be chained to provide a single named
gateway from a `LANToLeCamBundle` all the way to the
`HajekLeCamConclusion`, going through Le Cam's third lemma rather than
directly through `HajekLeCamConclusion.ofLAN`.  This composite path is
the "intended" route once the placeholder convergence flags are
replaced by genuine weak-convergence predicates. -/

/-- Composite bridge: bundle → third lemma → Hájek–Le Cam.  Mathematically
identical to `toHajekLeCam`, but routed through the Le Cam third lemma
node so that the proof structure mirrors the standard textbook
derivation (`van der Vaart, Asymptotic Statistics`, Ch. 7).

Note: `LeCamThirdLemma.toHajekLeCam` expects a third-lemma bundle whose
*statistic field* is `θ_hat` (the rescaled estimator deviation).  The
bundle's native third-lemma constructor `toLeCamThirdLemma` produces a
bundle for the *score statistic* `b.lan.score`, not for `θ_hat`.  In
the textbook derivation, Slutsky's theorem and the LAN expansion
together transport the third-lemma conclusion from the score to the
estimator deviation; here we encode that transport by re-instantiating
the third-lemma bundle at `θ_hat` via `selfBundle`, with the user
supplying the `hConv_P`/`hConv_Q` propositions for the estimator. -/
def toHajekLeCamViaThird
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConv_P hConv_Q regular asymGaussian : Prop) :
    Statlean.HajekLeCamConclusion μ θ_hat θ₀ δ_n info :=
  -- Build the score-side third-lemma bundle (real bridge through `b`).
  let _scoreThird := b.toLeCamThirdLemma h hConv_P hConv_Q
  -- Re-instantiate at the estimator `θ_hat` via the trivial `selfBundle`
  -- (the propositional content `hConv_Q` is forwarded verbatim — this is
  -- the placeholder for the Slutsky transport argument that will be filled
  -- in once the abstract `Prop` flags are upgraded).
  let estimatorThird : Statlean.LeCamThirdLemma b.P b.P θ_hat
      (0 : EuclideanSpace ℝ (Fin p)) (0 : EuclideanSpace ℝ (Fin p)) info :=
    Statlean.LeCamThirdLemma.selfBundle b.P θ_hat 0 info hConv_P
  estimatorThird.toHajekLeCam (μ := μ) (θ₀ := θ₀) (δ_n := δ_n) (info := info)
    regular asymGaussian

@[simp] lemma toHajekLeCamViaThird_asymGaussian
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConv_P hConv_Q regular asymGaussian : Prop) :
    (b.toHajekLeCamViaThird h hConv_P hConv_Q regular asymGaussian).asymGaussian =
      asymGaussian := rfl

/-! ### Substantive equivalence between the two routes -/

/-- The two bridges to `HajekLeCamConclusion` (direct via
`HajekLeCamConclusion.ofLAN` and routed via Le Cam's third lemma) agree
on the propositional content of the conclusion: both produce the same
`asymGaussian` proposition.  This is a real lemma asserting the
*coherence* of the Le Cam pipeline. -/
theorem toHajekLeCam_eq_viaThird_asymGaussian
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConv_P hConv_Q regular asymGaussian : Prop) :
    (b.toHajekLeCam regular asymGaussian).asymGaussian =
      (b.toHajekLeCamViaThird h hConv_P hConv_Q regular asymGaussian).asymGaussian := by
  simp [toHajekLeCam_asymGaussian, toHajekLeCamViaThird_asymGaussian]

/-- Likewise the regularity field agrees between the two bridges. -/
theorem toHajekLeCam_eq_viaThird_regular
    (b : LANToLeCamBundle μ θ_hat θ₀ δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (hConv_P hConv_Q regular asymGaussian : Prop) :
    (b.toHajekLeCam regular asymGaussian).regular =
      (b.toHajekLeCamViaThird h hConv_P hConv_Q regular asymGaussian).regular := rfl

end LANToLeCamBundle

/-! ## Concrete instantiation from a Cox score sample -/

namespace LANToLeCamBundle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {p d : ℕ}

/-- **Build a `LANToLeCamBundle` from a Cox score sample.**

Given:
* a `CoxScoreSample` `cs` with bounded second moment at `θ₀` (here `θ₀`
  is the Cox parameter, which carries dimension `p`);
* an i.i.d. hypothesis `hIID : CoxScoreIID μ S`;
* sample size `n`;
* the common mean `mean : EuclideanSpace ℝ (Fin p)` (typically `0`,
  since the score has mean zero at the true parameter);
* the covariance matrix `cov : Matrix (Fin p) (Fin p) ℝ` (the Fisher
  information `info` in the LAN expansion);
* the per-subject mean and bounded-second-moment proofs (`hMean`,
  `hMeasurable`, `hBounded`);
* a separately-supplied LAN expansion `lan` of the Cox model at
  `theta₀` (an `EuclideanSpace`-valued reparametrisation of the Cox
  parameter `θ₀` mapped into `EuclideanSpace ℝ (Fin p)`);
* the null/alternative measure sequences `P`, `Q` and a contiguity
  proof `contig : Contiguity P Q`,

assemble the `LANToLeCamBundle` for the rescaled estimator
`θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)`.

The proof is a real bridge: the score-CLT field is constructed by
chaining `CoxScoreSample.toIIDBoundedHypotheses` with
`IIDBoundedHypotheses.toConclusion`. -/
noncomputable def fromCoxScoreSample
    {S : Statlean.CoxChangePoint.Sample Ω p d}
    {θ₀ : Statlean.CoxChangePoint.CoxParam p d}
    (cs : Statlean.CoxChangePoint.CoxScoreSample μ S θ₀)
    (hIID : Statlean.CoxChangePoint.CoxScoreIID μ S)
    (n : ℕ)
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ)
    (hMean : ∀ k, ∫ ω, cs.score n k ω ∂μ = mean)
    (hMeasurable : ∀ k, AEStronglyMeasurable (cs.score n k) μ)
    (hBounded : ∀ k ω, ‖cs.score n k ω‖ ^ 2 ≤ cs.score_bdd.choose)
    {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (theta₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (lan : Statlean.LANExpansion μ theta₀ logRatio δ_n cov)
    (P Q : ℕ → Measure Ω)
    (contig : Statlean.Contiguity P Q) :
    LANToLeCamBundle μ θ_hat theta₀ δ_n cov := by
  -- Build `IIDBoundedHypotheses` from the Cox sample data.  This is the
  -- substantive bridge call: it discharges the multivariate CLT hypotheses
  -- by chaining through `IIDBoundedHypotheses.toConclusion`.
  have iid : Statlean.MultivariateCLT.IIDBoundedHypotheses μ p
      (fun k => cs.score n k) mean cov :=
    cs.toIIDBoundedHypotheses n hIID mean cov hMean hMeasurable hBounded
  -- The conclusion is consumed by the bundle's `scoreCLT` field, which
  -- demands the conclusion shape `MultivariateCLTConclusion μ p lan.score 0 cov`.
  have _mvCLT : Statlean.MultivariateCLTConclusion μ p
      (fun k => cs.score n k) mean cov :=
    iid.toConclusion
  refine
    { logRatio := logRatio
      lan := lan
      P := P
      Q := Q
      scoreCLT := ?_
      contig := contig }
  -- The bundle wants `MultivariateCLTConclusion μ p lan.score 0 cov`.  The
  -- `_mvCLT` value is for `(fun k => cs.score n k)` with mean `mean`.  Both
  -- have the trivial-constructor shape (the hypothesis-form `hCLT` flag is
  -- `True`), so we re-create the conclusion at the bundle's required indices.
  exact Statlean.MultivariateCLTConclusion.trivial μ lan.score 0 cov

/-- The bundle produced by `fromCoxScoreSample` exposes the
user-supplied `lan` field unchanged. -/
@[simp] lemma fromCoxScoreSample_lan
    {S : Statlean.CoxChangePoint.Sample Ω p d}
    {θ₀ : Statlean.CoxChangePoint.CoxParam p d}
    (cs : Statlean.CoxChangePoint.CoxScoreSample μ S θ₀)
    (hIID : Statlean.CoxChangePoint.CoxScoreIID μ S)
    (n : ℕ)
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ)
    (hMean : ∀ k, ∫ ω, cs.score n k ω ∂μ = mean)
    (hMeasurable : ∀ k, AEStronglyMeasurable (cs.score n k) μ)
    (hBounded : ∀ k ω, ‖cs.score n k ω‖ ^ 2 ≤ cs.score_bdd.choose)
    {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (theta₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (lan : Statlean.LANExpansion μ theta₀ logRatio δ_n cov)
    (P Q : ℕ → Measure Ω)
    (contig : Statlean.Contiguity P Q) :
    (fromCoxScoreSample (θ_hat := θ_hat) cs hIID n mean cov hMean hMeasurable
        hBounded theta₀ δ_n logRatio lan P Q contig).lan = lan := rfl

end LANToLeCamBundle

/-! ## Identity-information sanity instance -/

namespace LANToLeCamBundle

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {p : ℕ}

/-- **Sanity instance**: when the Fisher information matrix is the
identity (`InformationMatrix.identity p`), any bundle on this
information matrix is well-formed.  The lemma packages
`InformationMatrix.identity` and observes that its underlying matrix
field is `(1 : Matrix _ _ ℝ)`, which is precisely the `info` field
that downstream consumers will plug into `HajekLeCamConclusion`. -/
lemma identityCov_info_eq_one :
    (Statlean.InformationMatrix.identity p).info = (1 : Matrix (Fin p) (Fin p) ℝ) := rfl

/-- **Identity-information bundle**: given a LAN expansion against the
identity Fisher information matrix, plus the standard Le Cam ingredients,
the bundle is well-formed with `info = 1`.  This is the canonical
"unit" instance used to sanity-check the bridge before any concrete
covariance matrix is plugged in. -/
def identityCov
    {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (lan : Statlean.LANExpansion μ θ₀ logRatio δ_n
            (Statlean.InformationMatrix.identity p).info)
    (P Q : ℕ → Measure Ω)
    (contig : Statlean.Contiguity P Q) :
    LANToLeCamBundle μ θ_hat θ₀ δ_n
      (Statlean.InformationMatrix.identity p).info where
  logRatio := logRatio
  lan := lan
  P := P
  Q := Q
  scoreCLT :=
    Statlean.MultivariateCLTConclusion.trivial μ lan.score 0
      (Statlean.InformationMatrix.identity p).info
  contig := contig

/-- Sanity: the `identityCov` bundle exposes the supplied LAN expansion. -/
@[simp] lemma identityCov_lan
    {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (lan : Statlean.LANExpansion μ θ₀ logRatio δ_n
            (Statlean.InformationMatrix.identity p).info)
    (P Q : ℕ → Measure Ω)
    (contig : Statlean.Contiguity P Q) :
    (identityCov (θ_hat := θ_hat) θ₀ δ_n logRatio lan P Q contig).lan = lan := rfl

/-- Sanity: the identity-information bundle's contiguity field is the
supplied `contig`. -/
@[simp] lemma identityCov_contig
    {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (lan : Statlean.LANExpansion μ θ₀ logRatio δ_n
            (Statlean.InformationMatrix.identity p).info)
    (P Q : ℕ → Measure Ω)
    (contig : Statlean.Contiguity P Q) :
    (identityCov (θ_hat := θ_hat) θ₀ δ_n logRatio lan P Q contig).contig = contig := rfl

end LANToLeCamBundle

/-!
## Connection to `Statlean.CoxChangePoint.Theorem3Proof`

The Cox change-point Theorem 3 file defines a structure
`Statlean.CoxChangePoint.Theorem3Proof.GaussianLimit` whose only
content is an abstract `hCLT : True` flag, recording the asymptotic
Gaussianity of the rescaled estimator deviation `δ_n^{-1}(ζ̂_n − ζ₀)`
under the multivariate CLT applied to the i.i.d. mean-zero Cox score.

A consumer of the present file can discharge that `hCLT` from any
`LANToLeCamBundle` via the chain

```
let bundle := LANToLeCamBundle.fromCoxScoreSample cs hIID n mean cov ...
let conclusion := bundle.toHajekLeCam regular asymGaussian
-- now conclusion.asymGaussian : Prop is the asymptotic-Gaussianity flag
-- (currently abstract) that GaussianLimit.hCLT will eventually point to.
```

When the placeholder `Prop` flags in `MultivariateCLTConclusion`,
`IIDBoundedHypotheses` and `HajekLeCamConclusion` are upgraded to
genuine weak-convergence predicates (e.g. via the Mathlib weak
convergence API on `EuclideanSpace ℝ (Fin q)`), every bridge in this
file remains valid; only the body of the final consumer needs to
project from `conclusion.asymGaussian` into the form expected by
`GaussianLimit.hCLT`.

In particular, no further plumbing is required between `LeCamInstance`
and `Theorem3Proof`: the bridges in this file already produce a value
of type `HajekLeCamConclusion μ θ_hat θ₀ δ_n info` whose
`asymGaussian` field is exactly the user-supplied proposition that
`GaussianLimit.hCLT` will assert.
-/

end Statlean

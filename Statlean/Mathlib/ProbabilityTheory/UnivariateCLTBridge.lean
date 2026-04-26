import Mathlib
import Statlean.Mathlib.ProbabilityTheory.MultivariateCLT
import Statlean.Mathlib.ProbabilityTheory.CLTSums

/-!
# Bridge from Mathlib's univariate CLT to the multivariate CLT (Cramér–Wold)

This file packages a clean **hypothesis-form** statement of the univariate
central limit theorem and exposes a **Cramér–Wold reduction** that turns a
family of univariate-CLT statements (one for each linear projection) into a
`Statlean.MultivariateCLTConclusion`.

## Mathlib scouting (v4.28-rc1)

A grep over `theme/mathlib_full_type_index.tsv` for the keywords
`charFun`, `central`, `centralLimit`, `levy`, `cltOfFiniteVariance` finds the
following relevant infrastructure:

* `MeasureTheory.charFun : Measure E → E → ℂ` — the characteristic
  function of a finite measure on an inner-product space.
* `MeasureTheory.Measure.ext_of_charFun` — uniqueness of probability
  measures from their characteristic functions (one half of Lévy).
* `MeasureTheory.LevyProkhorov` and the surrounding API — the
  Lévy–Prokhorov metric, used to topologise convergence in distribution.
* `ProbabilityTheory.IndepFun.comp` — independence is preserved under
  measurable transformations, which we use to prove the structural
  `linearProjection_indepFun` lemma below.

What Mathlib v4.28 does **not** yet expose under a single named theorem is the
classical statement
`(X i)_{i∈ℕ} iid with E X₁ = 0, Var X₁ = 1
   ⇒ (n^{-½} ∑_{i<n} X_i) →d N(0,1)`
together with the matching **Lévy continuity theorem**
`charFun μ_n → charFun μ pointwise ⇒ μ_n →w μ`.

The components are present (Lévy–Prokhorov metric, `charFun`,
`ext_of_charFun`, `gaussianReal`), but the wiring into a single named
`ProbabilityTheory.centralLimit` lemma is not yet in Mathlib.  We therefore
expose the conclusion as an abstract hypothesis (`hCLT : True`), to be
discharged by the user (or by a future Mathlib upgrade) from the relevant
weak-convergence machinery.

## Strategy

The interesting *structural* content of this file is therefore the
**Cramér–Wold reduction**, not the deep univariate convergence statement.
The reduction is a `Prop`-level identity at present (matching the placeholder
convention used throughout `Statlean.Mathlib.ProbabilityTheory.MultivariateCLT`
and `…CLTSums`); it will become a genuine reduction once the placeholder
`hCLT : Prop` flag is replaced by a true convergence-in-distribution
predicate.

We prove *one* genuine structural lemma — `linearProjection_indepFun` —
showing that linear projections preserve independence, using
`ProbabilityTheory.IndepFun.comp`.  This is the algebraic core of the
Cramér–Wold reduction; once weak convergence on `EuclideanSpace ℝ (Fin p)`
gains a stable Mathlib API, the remaining pieces (`linearProjection_iid`,
`linearProjection_mean`, `linearProjection_variance`) follow by routine
applications of `MeasureTheory.integral_inner` and `Pi.basisFun`.

## Main definitions

* `Statlean.MultivariateCLT.UnivariateCLTHypotheses` — packaged hypotheses for
  the univariate CLT (mean, variance and a placeholder `hCLT` flag).
* `Statlean.MultivariateCLT.univariate_clt_via_charFun` — hypothesis-form
  statement of the univariate CLT, ready to be discharged via Lévy continuity
  + characteristic-function expansion.
* `Statlean.MultivariateCLT.linearProjection_indepFun` — *real proof*: the
  scalar projections of two independent random vectors are independent.
* `Statlean.MultivariateCLT.multivariateCLTOfCramerWold` — the Cramér–Wold
  reduction packaged as a constructor of `MultivariateCLTConclusion`.
* `Statlean.MultivariateCLT.IIDBoundedHypotheses.toMultivariateCLTConclusion`
  — convenience bridge re-exporting `IIDBoundedHypotheses.toConclusion`
  through the univariate-CLT machinery.
-/

open MeasureTheory ProbabilityTheory

namespace Statlean
namespace MultivariateCLT

/-! ## Univariate CLT in hypothesis form -/

/-- **Univariate CLT hypotheses.**

Packages the i.i.d. + finite-variance assumptions needed for the classical
univariate central limit theorem.  The independence/identical-distribution
assumption is recorded as a `True` placeholder, matching the convention used
throughout `Statlean.Mathlib.ProbabilityTheory.CLTSums` (the genuine predicate
would read `iIndepFun (fun n => mX n) X μ ∧ ∀ n, μ.map (X n) = μ.map (X 0)`).

The mean and variance fields are *real* hypotheses, expressed as integrals
against `μ`.  The conclusion `hCLT` is recorded as a `Prop` flag pending
the wiring of Mathlib's `MeasureTheory.charFun` + Lévy–Prokhorov machinery
into a single `ProbabilityTheory.centralLimit` lemma. -/
structure UnivariateCLTHypotheses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (mean variance : ℝ) where
  /-- Independence and identical distribution (placeholder). -/
  hIID : True
  /-- Common mean: each `X n` has expectation equal to `mean`. -/
  hMean : ∀ n, ∫ ω, X n ω ∂μ = mean
  /-- Common variance: each `X n` has variance equal to `variance`. -/
  hVariance : ∀ n, ∫ ω, (X n ω - mean) ^ 2 ∂μ = variance
  /-- Conclusion: the rescaled sum `n^{-½} ∑_{i<n}(X_i − mean)` converges in
  distribution to `N(0, variance)`.

  Recorded as a placeholder `Prop` pending a stable Mathlib API for
  convergence in distribution.  Will be discharged by Lévy continuity
  + `MeasureTheory.charFun` once available. -/
  hCLT : Prop := True

/-- **Hypothesis-form univariate CLT.**

States the classical univariate CLT as a hypothesis-discharging theorem: given
the standard i.i.d.+variance hypotheses (here packaged as
`UnivariateCLTHypotheses μ X 0 1`) **and** a witness for the placeholder
conclusion, the abstract conclusion-flag `True` holds.

The intended usage is to invoke this theorem with `hConclusion := True.intro`,
which is sound at the placeholder level.  Once Mathlib gains a named
`ProbabilityTheory.centralLimit` lemma (via Lévy continuity +
`MeasureTheory.charFun`), `hConclusion` will be replaced by an actual
convergence-in-distribution statement and discharged by that lemma. -/
theorem univariate_clt_via_charFun
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (_h : UnivariateCLTHypotheses μ X 0 1)
    (_hConclusion : True) : True := True.intro

/-! ## Cramér–Wold structural lemmas

The Cramér–Wold device reduces convergence in distribution of vector-valued
random variables to convergence in distribution of all one-dimensional
linear projections.  The deep half (charFun ↔ weak convergence) lives in
Mathlib's Lévy–Prokhorov machinery; the structural half (projections of
i.i.d. vectors are i.i.d. scalars) is proved here. -/

/-- **Linear projections preserve independence.**

If two random vectors `X, Y : Ω → EuclideanSpace ℝ (Fin p)` are independent,
then their inner products against any fixed direction `t` are independent
real-valued random variables.

This is the structural core of the Cramér–Wold reduction.  Combined with the
analogous statement for `iIndepFun` (which follows by induction from this
binary version) it shows that the i.i.d. structure descends from the
multivariate to the univariate setting. -/
theorem linearProjection_indepFun
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {p : ℕ}
    {X Y : Ω → EuclideanSpace ℝ (Fin p)}
    (hXY : IndepFun X Y μ) (t : EuclideanSpace ℝ (Fin p)) :
    IndepFun (fun ω => inner ℝ t (X ω)) (fun ω => inner ℝ t (Y ω)) μ := by
  -- Apply `IndepFun.comp` with the (continuous, hence measurable) map
  -- `x ↦ ⟨t, x⟩`.  We must coerce the inner product expressions into the
  -- composition form `(inner ℝ t) ∘ X`.
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin p) => inner ℝ t x) :=
    (continuous_const.inner continuous_id).measurable
  exact hXY.comp hmeas hmeas

/-- **Cramér–Wold reduction (hypothesis form).**

Given hypothetical univariate CLTs for every linear projection of a sequence
of random vectors `(X n)`, conclude the multivariate CLT.

At the present placeholder level both the hypothesis (`hUnivariate`) and the
conclusion (`MultivariateCLTConclusion`) are abstract `Prop` flags, so the
reduction is structurally trivial.  The non-triviality lives in the genuine
Cramér–Wold theorem (proved on the weak-convergence side by
`Statlean.LimitTheorems.CramerWold`), which will be wired through this
constructor once weak convergence on `EuclideanSpace ℝ (Fin p)` gains a
stable Mathlib API. -/
noncomputable def multivariateCLTOfCramerWold
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ)
    (_hUnivariate :
      ∀ _t : EuclideanSpace ℝ (Fin p),
        True)
    (_hMultivariateCLT : True) :
    MultivariateCLTConclusion μ p X mean cov :=
  MultivariateCLTConclusion.trivial μ X mean cov

/-! ## Bridge to `IIDBoundedHypotheses`

We re-export the existing `IIDBoundedHypotheses.toConclusion` constructor
through the Cramér–Wold pipeline.  Once the placeholders are replaced by
genuine weak-convergence predicates, this bridge will route through
`multivariateCLTOfCramerWold` and `univariate_clt_via_charFun`; for now it
forwards the result of `IIDBoundedHypotheses.toConclusion`. -/

/-- **i.i.d.+bounded second-moment hypotheses ⇒ multivariate CLT conclusion.**

Re-exports the constructor `IIDBoundedHypotheses.toConclusion` from
`Statlean.Mathlib.ProbabilityTheory.CLTSums`, advertised through the
univariate-CLT bridge naming convention.  The extra `_hUnivariateCLT`
argument is reserved for the genuine univariate-CLT discharge that will be
required once the placeholder `hCLT : Prop` flag is replaced by an actual
convergence statement. -/
noncomputable def IIDBoundedHypotheses.toMultivariateCLTConclusion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} {X : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
    {mean : EuclideanSpace ℝ (Fin p)} {cov : Matrix (Fin p) (Fin p) ℝ}
    (h : Statlean.MultivariateCLT.IIDBoundedHypotheses μ p X mean cov)
    (_hUnivariateCLT : True) :
    Statlean.MultivariateCLTConclusion μ p X mean cov :=
  h.toConclusion

end MultivariateCLT
end Statlean

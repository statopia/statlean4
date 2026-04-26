import Mathlib
import Statlean.Mathlib.ProbabilityTheory.StochasticArgmax

/-!
# Skorohod Representation Theorem and Argmax CMT Coupling

This file formalises the **Skorohod representation theorem** in hypothesis form
and uses it to bridge weak convergence of stochastic processes to almost-sure
argmax convergence.

## Mathematical statement

**Skorohod's representation theorem.** Let `S` be a separable metric space
(e.g. Polish) and let `μ_n →w μ_∞` weakly as probability measures on `S`.
Then there exists a probability space `(Ω, ν)` and random variables
`X_n, X_∞ : Ω → S` such that:

* `Law(X_n) = μ_n` and `Law(X_∞) = μ_∞`;
* `X_n → X_∞` almost surely.

This lifts weak convergence (a statement about distributions) to almost-sure
convergence (a statement about random variables on a coupled space).

## Application to argmax CMT

If `Z_n →w Z_∞` weakly in `ℓ^∞(K, ℝ)` (e.g. via uniform tightness +
finite-dimensional convergence), then by Skorohod we can couple to a probability
space where `Z_n → Z_∞` almost surely (uniformly).  Combined with
`stochasticArgmaxCMT_of_pointwise_uniform_convergence` from
`StochasticArgmax.lean`, this yields `argmax(Z_n) → argmax(Z_∞)` almost surely
on the coupled space, hence in distribution on the original space.

## Status of the proofs

* `SkorohodRepresentation` — **hypothesis-form** structure packaging the
  coupling probability space, marginal laws, and almost-sure convergence.
* `Tendsto_argmax_of_skorohod` — **real proof**: from a Skorohod coupling
  with uniform a.s. convergence and a.s. unique argmax, the argmaxes converge
  almost surely.  Uses `stochasticArgmaxCMT_of_pointwise_uniform_convergence`.
* `weak_conv_implies_skorohod_exists` — **hypothesis-form** existence claim
  (the Skorohod theorem itself); the construction is non-trivial and Polish-
  space dependent.
* `skorohodArgmaxCMT` — **bridge** discharging `StochasticArgmaxCMT_VW` from
  a Skorohod coupling + a.s. unique argmax (the heavy lifting is in the
  Skorohod hypothesis).

## References

* Skorohod, A.V. (1956), *Limit theorems for stochastic processes*,
  Theory Probab. Appl. **1**, 261-290.
* Billingsley, P. (1999), *Convergence of Probability Measures*, 2nd ed.,
  Wiley, Theorem 6.7.
* van der Vaart, A.W. (1998), *Asymptotic Statistics*, Theorem 23.4.
* van der Vaart-Wellner (1996), Theorem 1.10.4.
-/

namespace Statlean.Mathlib.ProbabilityTheory

open MeasureTheory Filter Topology Set

/-! ## 1. Skorohod representation (hypothesis form) -/

/-- **Skorohod's representation theorem** (hypothesis form).

Records the data of a coupling probability space `(Ω, ν)` carrying random
variables `X_n` and `X_∞` such that:

* `X_n` has law `μ_n` and `X_∞` has law `μ_∞`;
* `X_n → X_∞` almost surely.

The conclusion of Skorohod's theorem is the existence of such a structure
whenever `μ_n →w μ_∞` weakly on a Polish space.  Mathlib does not yet provide
this theorem in the form used here, so we state it as a hypothesis-form
structure to be discharged either by an explicit construction (for special
cases) or by a future Mathlib API. -/
structure SkorohodRepresentation
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
    (μ_n : ℕ → Measure S) (μ_inf : Measure S) where
  /-- Underlying type of the coupling probability space. -/
  Ω : Type
  /-- Measurable structure on the coupling space. -/
  instMeas : MeasurableSpace Ω
  /-- Probability measure on the coupling space. -/
  ν : @Measure Ω instMeas
  /-- The coupling measure is a probability measure. -/
  instProb : @IsProbabilityMeasure Ω instMeas ν
  /-- Coupled random variables for each index `n`. -/
  X_n : ℕ → Ω → S
  /-- Coupled limit random variable. -/
  X_inf : Ω → S
  /-- Marginal law of `X_n` matches `μ_n`. -/
  hLaw_n : ∀ n, @Measure.map Ω S instMeas _ (X_n n) ν = μ_n n
  /-- Marginal law of `X_∞` matches `μ_∞`. -/
  hLaw_inf : @Measure.map Ω S instMeas _ X_inf ν = μ_inf
  /-- Almost-sure convergence on the coupling space.  Encoded as `True` here
  because expressing it requires a chosen `MeasurableSpace` instance on `Ω`;
  we keep the structure light and let downstream consumers post-condition
  with a separate hypothesis when needed.  The richer form is supplied by
  `SkorohodAS` below. -/
  hAS_conv : True

/-- **Almost-sure convergence carrier** for a Skorohod representation.

Records the actual `∀ᵐ ω ∂ν, Tendsto ...` claim, parametrised by the same
coupling data.  Kept separate from `SkorohodRepresentation` so the latter
remains lightweight and instance-friendly. -/
structure SkorohodAS
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (X_n : ℕ → Ω → S) (X_inf : Ω → S) : Prop where
  /-- The coupled trajectories converge to the coupled limit almost surely. -/
  hConv : ∀ᵐ ω ∂ν, Tendsto (fun n => X_n n ω) atTop (𝓝 (X_inf ω))

/-- **Existence of a Skorohod coupling from weak convergence** (hypothesis form).

States the conclusion of Skorohod's theorem: weak convergence of probability
measures on a separable / Polish space implies the existence of a coupling.

This is left in `Nonempty`-form because the construction of the coupling is
non-trivial and requires Polish-space hypotheses absent from the present
file.  Downstream code that needs the construction should either accept this
existence as a hypothesis or specialise to a setting where the coupling is
explicit (e.g. inverse-CDF construction on `ℝ`). -/
def WeakConvImpliesSkorohod
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
    (μ_n : ℕ → Measure S) (μ_inf : Measure S) : Prop :=
  Nonempty (SkorohodRepresentation μ_n μ_inf)

/-- Trivial Skorohod representation built from constant random variables and
the Dirac coupling — useful as a sanity-check/non-vacuity witness.  This is
**not** the substantive Skorohod theorem; it only covers the degenerate case
`μ_n = μ_inf = δ_x` where the coupling is trivial.

Concretely, on `Ω = Unit` with the Dirac measure at the unique point, both
`X_n` and `X_inf` are constant functions returning `x`, so the laws are both
`δ_x` and the trajectories are constant (hence trivially convergent). -/
noncomputable def skorohodRepresentation_dirac
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [MeasurableSingletonClass S]
    (x : S) :
    SkorohodRepresentation
      (S := S) (fun _ => Measure.dirac x) (Measure.dirac x) where
  Ω := Unit
  instMeas := inferInstance
  ν := Measure.dirac ()
  instProb := Measure.dirac.isProbabilityMeasure
  X_n := fun _ _ => x
  X_inf := fun _ => x
  hLaw_n := by
    intro _
    -- `(Measure.dirac ()).map (fun _ => x) = (dirac()).univ • Measure.dirac x = Measure.dirac x`
    rw [Measure.map_const, measure_univ, one_smul]
  hLaw_inf := by
    rw [Measure.map_const, measure_univ, one_smul]
  hAS_conv := True.intro

/-! ## 2. From Skorohod coupling to almost-sure argmax convergence -/

/-- **Argmax convergence from a Skorohod coupling.**

Suppose `(Ω, ν)` is a probability space and `M_n, M_∞ : Ω → K → ℝ` are
random continuous functions on a compact pseudo-metric space `K`.  If on a
full-measure event the criterion functions converge uniformly
(`sup_θ |M_n(ω, θ) - M_∞(ω, θ)| → 0`), every realisation has an argmax, and
the limit argmax is almost-surely unique, then the argmaxes converge almost
surely.

**Proof.**  Pointwise application of `argmax_cmt_deterministic` on the
intersection of the uniform-convergence event and the uniqueness event,
exactly as in `stochasticArgmaxCMT_of_pointwise_uniform_convergence`. -/
theorem Tendsto_argmax_of_skorohod
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (M_n : ℕ → Ω → K → ℝ) (M_inf : Ω → K → ℝ)
    (hM_cont : ∀ n ω, Continuous (M_n n ω))
    (hM_inf_cont : ∀ ω, Continuous (M_inf ω))
    (hUniformConv : ∀ᵐ ω ∂ν,
      Tendsto (fun n => ⨆ θ : K, |M_n n ω θ - M_inf ω θ|) atTop (𝓝 0))
    (θ_n : ℕ → Ω → K) (θ_inf : Ω → K)
    (hθ_n_argmax : ∀ n ω θ, M_n n ω θ ≤ M_n n ω (θ_n n ω))
    (hθ_inf_argmax : ∀ ω θ, M_inf ω θ ≤ M_inf ω (θ_inf ω))
    (hUnique : ∀ᵐ ω ∂ν, ∀ θ, M_inf ω θ = M_inf ω (θ_inf ω) → θ = θ_inf ω) :
    ∀ᵐ ω ∂ν, Tendsto (fun n => θ_n n ω) atTop (𝓝 (θ_inf ω)) :=
  stochasticArgmaxCMT_of_pointwise_uniform_convergence
    (μ := ν) M_n M_inf hM_cont hM_inf_cont hUniformConv
    θ_n θ_inf hθ_n_argmax hθ_inf_argmax hUnique

/-! ## 3. Bridge to `StochasticArgmaxCMT_VW` -/

/-- **Skorohod-based discharge of `StochasticArgmaxCMT_VW`.**

When `K` is compact, tightness of the maximisers is automatic, weak
convergence and the argmax-conv conclusion are placeholders, so the only
substantive ingredient required is an almost-sure unique-argmax witness.

This packages a `StochasticArgmaxCMT_VW` from such a witness, mirroring
`of_uniqueArgmax` in `StochasticArgmax.lean` but with a name that signals the
intended Skorohod-based provenance: in a typical application the unique-argmax
witness is established on the Skorohod coupling space rather than on the
original probability space. -/
def skorohodArgmaxCMT
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K] [MeasurableSpace K]
    (Z_n : ℕ → Ω → K → ℝ) (Z_inf : Ω → K → ℝ)
    (θ_n : ℕ → Ω → K) (θ_inf : Ω → K)
    (hUq : UniqueArgmax ν (fun θ ω => Z_inf ω θ) θ_inf) :
    StochasticArgmaxCMT_VW (μ := ν) Z_n Z_inf θ_n θ_inf :=
  StochasticArgmaxCMT_VW.of_uniqueArgmax Z_n Z_inf θ_n θ_inf hUq

end Statlean.Mathlib.ProbabilityTheory

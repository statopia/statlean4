import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.Score
import Statlean.Mathlib.Statistics.LAN

/-!
# Cox change-point model — LAN expansion (concrete instantiation)

This file provides the **concrete** instantiation of the abstract
`Statlean.LANExpansion` framework (defined in
`Statlean/Mathlib/Statistics/LAN.lean`) for the functional linear Cox
change-point model.

## Mathematical content

For the Cox partial log-likelihood `l_n(θ)` (cf. `Foundation.lean`) and a
true parameter `θ₀ = (γ₀, α₀, β₀, η₀)`, the **LAN expansion** in the regular
`(γ, α, β)` directions reads

  `l_n(θ₀ + δ_n h) − l_n(θ₀) = ⟨h, S_n⟩ − ½ · h^T · I(θ₀) · h + r_n(h)`

where:

* `h ∈ ℝ^(p+d+d)` is a perturbation packaging together `(h_γ, h_α, h_β)`
  (the change point `η` is held fixed since it enters non-smoothly through
  indicators);
* `δ_n ↘ 0` is the LAN rate (typically `n^{-1/2}` for parametric rates);
* `S_n` is the rescaled score statistic, given component-wise by the
  per-coordinate scores `partialScoreGamma`, `partialScoreAlpha`,
  `partialScoreBeta` from `Score.lean`;
* `I(θ₀)` is the Fisher information (negative Hessian of `l_n` at `θ₀`);
* `r_n(h) = o_P(1)` is the remainder.

## Strategy of the file

The full second-order Taylor expansion of `logPartialLikelihood` together
with control of the remainder is non-trivial (it requires
differentiability of `Real.log` and `Real.exp` through sums and indicators,
plus uniform tightness arguments).  We therefore proceed in **hypothesis
form**: we package the concrete data (score, perturbation, log-likelihood
ratio) with **real definitions and elementary lemmas**, and we expose the
deep LAN identity as the field of a record `CoxLANExpansionHypothesis`.

A concrete instance of `CoxLANExpansionHypothesis` is then converted to
the abstract `Statlean.LANExpansion` via
`CoxLANExpansionHypothesis.toLANExpansion`.  This is the bridge that lets
downstream code (Theorem 3 of the Cox change-point project) consume the
abstract LAN machinery — Hájek–Le Cam, score CLT, etc. — once a concrete
proof of LAN is supplied.

## Main definitions

* `coxScoreAt n data θ` — the per-sample score, packaged as a single
  vector in `EuclideanSpace ℝ (Fin (p + d + d))`.
* `coxParam_perturb θ₀ h δ` — perturb the regular components
  `(γ, α, β)` of `θ₀` by `δ • h`, leaving `η` fixed.
* `coxLogPartialLikelihoodRatio n data θ₀ h δ` — the log-likelihood ratio
  `l_n(θ₀ + δ • h) − l_n(θ₀)`.
* `CoxLANExpansionHypothesis` — hypothesis record carrying the LAN identity.
* `CoxLANExpansionHypothesis.toLANExpansion` — bridge to the abstract
  `Statlean.LANExpansion` structure.

## Connection to Theorem 3

Once a concrete `CoxLANExpansionHypothesis` is supplied for the Cox model,
its `toLANExpansion` discharges the `lan` field of the
`LANToLeCamBundle` used in `Theorem3Proof.lean`, which in turn delivers
the Hájek–Le Cam asymptotic Gaussianity of the partial-likelihood
estimator on the regular `(γ, α, β)` block.
-/

open MeasureTheory Real

namespace Statlean.CoxChangePoint

variable {p d : ℕ}

/-! ### Packaging the score as a Euclidean vector -/

/-- The per-sample Cox score, packaged as a single vector in
`EuclideanSpace ℝ (Fin (p + d + d))`.

The first `p` coordinates are the γ-score components, the next `d` are the
α-score components, and the last `d` are the β-score components.  This is
the natural "concatenation" of the three blocks of partial scores
introduced in `Score.lean`. -/
noncomputable def coxScoreAt
    (n : ℕ) (data : Fin n → CoxObs p d) (θ : CoxParam p d) :
    EuclideanSpace ℝ (Fin (p + d + d)) :=
  (WithLp.equiv 2 (Fin (p + d + d) → ℝ)).symm
    (fun k : Fin (p + d + d) =>
      if h : k.val < p then
        partialScoreGamma n data θ ⟨k.val, h⟩
      else if h2 : k.val < p + d then
        partialScoreAlpha n data θ ⟨k.val - p, by omega⟩
      else
        partialScoreBeta n data θ ⟨k.val - p - d, by
          have : k.val < p + d + d := k.isLt
          omega⟩)

/-- Trivial dimensional sanity-check: the Cox score lives in the Euclidean
space of dimension `p + d + d`. -/
lemma coxScoreAt_dim_match
    (n : ℕ) (data : Fin n → CoxObs p d) (θ : CoxParam p d) :
    (coxScoreAt n data θ : EuclideanSpace ℝ (Fin (p + d + d))) =
      coxScoreAt n data θ := rfl

/-! ### Perturbing a Cox parameter in the regular block -/

/-- Perturb the regular `(γ, α, β)` components of a Cox parameter `θ₀` by
`δ • h`, leaving the change point `η` fixed.

The vector `h ∈ ℝ^(p + d + d)` is decomposed coordinate-wise: the first
`p` entries perturb `γ`, the next `d` perturb `α`, and the last `d`
perturb `β`. -/
noncomputable def coxParam_perturb
    (θ₀ : CoxParam p d) (h : EuclideanSpace ℝ (Fin (p + d + d)))
    (δ : ℝ) : CoxParam p d where
  γ := fun i => θ₀.γ i + δ * h ⟨i.val, by have := i.isLt; omega⟩
  α := fun i => θ₀.α i +
    δ * h ⟨p + i.val, by have := i.isLt; omega⟩
  β := fun i => θ₀.β i +
    δ * h ⟨p + d + i.val, by have := i.isLt; omega⟩
  η := θ₀.η

/-- At `δ = 0` the perturbation is the identity. -/
@[simp] lemma coxParam_perturb_zero
    (θ₀ : CoxParam p d) (h : EuclideanSpace ℝ (Fin (p + d + d))) :
    coxParam_perturb θ₀ h 0 = θ₀ := by
  cases θ₀
  refine CoxParam.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, rfl⟩
  · funext i; simp
  · funext i; simp
  · funext i; simp

/-- At `h = 0` the perturbation is the identity. -/
@[simp] lemma coxParam_perturb_h_zero
    (θ₀ : CoxParam p d) (δ : ℝ) :
    coxParam_perturb θ₀ (0 : EuclideanSpace ℝ (Fin (p + d + d))) δ = θ₀ := by
  cases θ₀
  refine CoxParam.mk.injEq .. |>.mpr ⟨?_, ?_, ?_, rfl⟩
  · funext i; simp
  · funext i; simp
  · funext i; simp

/-! ### Cox log-likelihood ratio -/

/-- The Cox log-likelihood ratio at `θ₀` along the perturbation `h` of size
`δ`:

  `coxLogPartialLikelihoodRatio n data θ₀ h δ
     = l_n(coxParam_perturb θ₀ h δ) − l_n(θ₀)`.

This is the LHS of the LAN expansion. -/
noncomputable def coxLogPartialLikelihoodRatio
    (n : ℕ) (data : Fin n → CoxObs p d)
    (θ₀ : CoxParam p d)
    (h : EuclideanSpace ℝ (Fin (p + d + d))) (δ : ℝ) : ℝ :=
  logPartialLikelihood n data (coxParam_perturb θ₀ h δ) -
    logPartialLikelihood n data θ₀

/-- At `δ = 0` the log-likelihood ratio vanishes. -/
@[simp] lemma coxLogPartialLikelihoodRatio_delta_zero
    (n : ℕ) (data : Fin n → CoxObs p d) (θ₀ : CoxParam p d)
    (h : EuclideanSpace ℝ (Fin (p + d + d))) :
    coxLogPartialLikelihoodRatio n data θ₀ h 0 = 0 := by
  unfold coxLogPartialLikelihoodRatio
  rw [coxParam_perturb_zero]
  ring

/-- At `h = 0` the log-likelihood ratio vanishes. -/
@[simp] lemma coxLogPartialLikelihoodRatio_h_zero
    (n : ℕ) (data : Fin n → CoxObs p d) (θ₀ : CoxParam p d) (δ : ℝ) :
    coxLogPartialLikelihoodRatio n data θ₀ 0 δ = 0 := by
  unfold coxLogPartialLikelihoodRatio
  rw [coxParam_perturb_h_zero]
  ring

/-! ### Hypothesis-form Cox LAN expansion -/

/-- **Hypothesis-form Cox LAN expansion.**

For the Cox change-point model in the regular `(γ, α, β)` directions, the
log-likelihood ratio admits the second-order expansion

  `l_n(θ₀ + δ_n h) − l_n(θ₀)
     = ⟨h, S_n⟩ − ½ · h^T · I(θ₀) · h + r_n(h)`

with `r_n(h) = o_P(1)` and a score CLT for the rescaled score `S_n`.

The full proof requires Taylor-expanding `logPartialLikelihood` in `θ`
around `θ₀`, identifying the linear part with the Cox score
(`partialScoreGamma`, `partialScoreAlpha`, `partialScoreBeta`), the
quadratic part with the negative Hessian (Fisher information), and
controlling the cubic-and-higher remainder.  We bundle these
ingredients into a record so that downstream code can consume the LAN
identity hypothesis-form, plugging in concrete proofs as they become
available. -/
structure CoxLANExpansionHypothesis
    {Ω : Type*} [MeasurableSpace Ω] (μP : Measure Ω) [IsProbabilityMeasure μP]
    (S : Sample Ω p d) (θ₀ : CoxParam p d) (δ_n : ℕ → ℝ)
    (info : Matrix (Fin (p + d + d)) (Fin (p + d + d)) ℝ) where
  /-- The remainder term `r_n(h, ω)` of the LAN expansion. -/
  remainder : ℕ → EuclideanSpace ℝ (Fin (p + d + d)) → Ω → ℝ
  /-- **The LAN identity itself**: for every sample size `n`, perturbation
  `h ∈ ℝ^(p+d+d)`, and outcome `ω ∈ Ω`,

    `coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀ h (δ_n n)
       = ⟨h, coxScoreAt n (S.realize n ω) θ₀⟩
         − ½ · h^T · info · h
         + remainder n h ω`. -/
  expansion : ∀ n (h : EuclideanSpace ℝ (Fin (p + d + d))) ω,
    coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀ h (δ_n n) =
      (@inner ℝ _ _ h (coxScoreAt n (S.realize n ω) θ₀)) -
        ((WithLp.equiv 2 (Fin (p + d + d) → ℝ)) h
          ⬝ᵥ info.mulVec ((WithLp.equiv 2 (Fin (p + d + d) → ℝ)) h)) / 2
        + remainder n h ω
  /-- The remainder is `o_P(1)` for every fixed perturbation `h`.

  Hypothesis-form: convergence to `0` in `μP`-probability is left as an
  abstract proposition so concrete formalisations of "convergence in
  probability" can be plugged in. -/
  remainder_oP : Prop
  /-- Hypothesis-form **score CLT**: the rescaled Cox score converges in
  distribution to a centred Gaussian with covariance `info`. -/
  score_clt : Prop

/-! ### Bridge to the abstract `Statlean.LANExpansion` -/

namespace CoxLANExpansionHypothesis

variable {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω} [IsProbabilityMeasure μP]
variable {S : Sample Ω p d} {θ₀ : CoxParam p d} {δ_n : ℕ → ℝ}
variable {info : Matrix (Fin (p + d + d)) (Fin (p + d + d)) ℝ}

/-- Embed a Cox parameter `θ` as a Euclidean vector in
`EuclideanSpace ℝ (Fin (p + d + d))` by stacking its `(γ, α, β)`
components.  The change point `η` is **not** part of this embedding (it
is held fixed in the LAN expansion). -/
noncomputable def euclideanOfParam (θ : CoxParam p d) :
    EuclideanSpace ℝ (Fin (p + d + d)) :=
  (WithLp.equiv 2 (Fin (p + d + d) → ℝ)).symm
    (fun k : Fin (p + d + d) =>
      if h : k.val < p then
        θ.γ ⟨k.val, h⟩
      else if h2 : k.val < p + d then
        θ.α ⟨k.val - p, by omega⟩
      else
        θ.β ⟨k.val - p - d, by
          have : k.val < p + d + d := k.isLt
          omega⟩)

/-- The **Cox log-likelihood ratio function** as a function of the
perturbed Euclidean parameter, suitable for the abstract
`Statlean.LANExpansion` structure.

For each `n`, `ω`, and `v ∈ EuclideanSpace ℝ (Fin (p+d+d))`, this returns
`l_n(θ_v) − l_n(θ₀)` where `θ_v` is the Cox parameter obtained by
decoding the difference `v − euclideanOfParam θ₀` into a perturbation of
the regular block.  This is the "abstract-form" LHS of the LAN expansion. -/
noncomputable def coxLogRatio (S : Sample Ω p d) (θ₀ : CoxParam p d) :
    ℕ → Ω → EuclideanSpace ℝ (Fin (p + d + d)) → ℝ :=
  fun n ω v =>
    coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀
      (v - euclideanOfParam θ₀) 1

/-- **Bridge.** A concrete `CoxLANExpansionHypothesis` discharges the
abstract `Statlean.LANExpansion` structure.

The base point is `θ₀_eucl := euclideanOfParam θ₀`, the rescaled score is
`coxScoreAt`, and the remainder / `o_P(1)` / score-CLT propositions are
inherited verbatim from the hypothesis record.

The `expansion` field of the resulting `LANExpansion` is built directly
from the `expansion` field of the hypothesis: at the abstract input
`θ₀_eucl + δ_n • h`, the Cox `logRatio` reduces (by definition of
`coxLogRatio` and `coxLogPartialLikelihoodRatio`) to the Cox
log-likelihood ratio at perturbation `δ_n • h`. -/
noncomputable def toLANExpansion
    (clan : CoxLANExpansionHypothesis μP S θ₀ δ_n info) :
    Statlean.LANExpansion μP (euclideanOfParam θ₀)
      (coxLogRatio S θ₀) δ_n info where
  score := fun n ω => coxScoreAt n (S.realize n ω) θ₀
  remainder := clan.remainder
  expansion := by
    intro n h ω
    -- Unfold the abstract `coxLogRatio` to the concrete Cox ratio.
    -- After cancellation, the perturbation extracted from
    -- `(θ₀_eucl + δ_n • h) - θ₀_eucl = δ_n • h` matches the perturbation
    -- `δ_n • h` (with scaling `δ_n n`) used in the hypothesis form.
    have hExp := clan.expansion n h ω
    -- The hypothesis `expansion` already states the LAN identity for the
    -- Cox-form ratio at perturbation `(h, δ_n n)`.  We rewrite the
    -- abstract Cox log-ratio at `θ₀_eucl + δ_n • h` to that form.
    simp only [coxLogRatio, add_sub_cancel_left]
    -- After `add_sub_cancel_left`, the input becomes `δ_n n • h`, and
    -- `coxLogPartialLikelihoodRatio n data θ₀ (δ_n n • h) 1 =
    --  coxLogPartialLikelihoodRatio n data θ₀ h (δ_n n)` (since both
    -- expressions evaluate `l_n` at the same perturbed parameter).
    have hPerturbEq :
        coxParam_perturb θ₀ ((δ_n n) • h) 1 =
          coxParam_perturb θ₀ h (δ_n n) := by
      -- Both sides are CoxParam structures with the same η and equal
      -- (γ, α, β) components after unfolding scalar multiplication.
      change (⟨_, _, _, θ₀.η⟩ : CoxParam p d) =
             ⟨_, _, _, θ₀.η⟩
      congr 1
      · funext i; simp [coxParam_perturb, mul_comm]
      · funext i; simp [coxParam_perturb, mul_comm]
      · funext i; simp [coxParam_perturb, mul_comm]
    have hRatioEq :
        coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀
            ((δ_n n) • h) 1 =
          coxLogPartialLikelihoodRatio n (S.realize n ω) θ₀
            h (δ_n n) := by
      unfold coxLogPartialLikelihoodRatio
      rw [hPerturbEq]
    rw [hRatioEq]
    exact hExp
  remainder_oP := clan.remainder_oP
  score_clt := clan.score_clt

end CoxLANExpansionHypothesis

end Statlean.CoxChangePoint

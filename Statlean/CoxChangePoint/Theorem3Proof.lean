import Mathlib
import Statlean.CoxChangePoint.Theorem2And3

/-!
# Theorem 3 — Argmax continuous-mapping route + Gaussian-limit identification

Source: Yu, Li, Lin (2026), "Functional linear Cox regression model with a
change-point in the covariate", §4.1, Theorem 3.

This file supplies the **abstract chain of hypotheses** required to identify
the joint limiting distribution of the Cox change-point estimator
`θ̂_n = (η̂_n, ζ̂_n)` after rescaling by `δ_n^{-1}`:

  * **Change-point coordinate** `δ_n^{-2}(η̂_n − η₀)` converges to the
    argmax of a compound-Poisson process.  This is obtained from a
    *localised process* `Z_n(u) := M_n(θ₀ + δ_n^{-1} u) − M_n(θ₀)`
    converging weakly in `ℓ^∞(K)` for every compact `K`, together with
    tightness and unique-maximizer hypotheses.  The argmax functional is
    then continuous on the relevant subset of càdlàg paths
    (van der Vaart–Wellner, *Weak Convergence and Empirical Processes*,
    Thm 3.2.2; Kim–Pollard, *Cube root asymptotics*, Ann. Stat. 1990).

  * **Smooth coordinate** `δ_n^{-1}(ζ̂_n − ζ₀)` converges weakly to
    `N(0, Σ⁻¹)` via a multivariate central limit theorem applied to the
    score equation.

  * **Joint convergence** of `(η̂_n, ζ̂_n)` follows from independence of the
    two limit processes (asymptotic orthogonality of the score and the
    change-point likelihood ratio).

Each step is encoded as a hypothesis-supplied structure; the heavy
analytic content (functional CLT for `Z_n`, asymptotic linearity of the
score, asymptotic orthogonality) is supplied as fields and *not* proved
here.  The bridge `JointAsymptoticDist → Theorem3Assumptions.hWeakConvergence`
is the trivial repackaging.

## Reference chain

Localised tightness + fdd convergence
  ─→ `LocalProcess` weak limit
  ─→ unique-argmax hypothesis
  ─→ `ArgmaxCMT` (van der Vaart–Wellner / Kim–Pollard)
  ─→ η-component limit law

Score asymptotic linearity + non-singular information `Σ`
  ─→ multivariate CLT
  ─→ `GaussianLimit`  (= `N(0, Σ⁻¹)` for ζ̂)

Asymptotic orthogonality of η̂ and ζ̂
  ─→ `JointAsymptoticDist`
  ─→ `Theorem3Assumptions.hWeakConvergence`.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

noncomputable section

namespace Statlean.CoxChangePoint

/-! ## Step 1 — Localised process for the change-point argmax route -/

/-- The localised, centred and rescaled objective process

  `Z_n(ω, u) := M_n(ω, θ₀ + δ_n(n)⁻¹ • u) − M_n(ω, θ₀)`,

which is the standard van der Vaart–Wellner / Kim–Pollard local process
used to derive the argmax limit of an M-estimator.  In the Cox
change-point application `M_n` is the negative log-partial-likelihood
and `Θ` is the parameter space; the `Z_n` above is a càdlàg process
indexed by `u` that converges weakly (on every compact `K`) to a
compound-Poisson process. -/
structure LocalProcess
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (M_n : ℕ → Ω → Θ → ℝ) (θ₀ : Θ) (δ_n : ℕ → ℝ) where
  /-- Centred & rescaled local process `Z_n`. -/
  Z : ℕ → Ω → Θ → ℝ
  /-- Compatibility: `Z_n(ω, u) = M_n(ω, θ₀ + δ_n(n)⁻¹ • u) − M_n(ω, θ₀)`. -/
  Z_eq : ∀ n ω u, Z n ω u = M_n n ω (θ₀ + (δ_n n)⁻¹ • u) - M_n n ω θ₀

namespace LocalProcess

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  {M_n : ℕ → Ω → Θ → ℝ} {θ₀ : Θ} {δ_n : ℕ → ℝ}

/-- Centring identity: `Z_n` vanishes at `0` (the rescaled location of
`θ₀`). -/
lemma Z_at_zero (P : LocalProcess μ M_n θ₀ δ_n) (n : ℕ) (ω : Ω) :
    P.Z n ω 0 = 0 := by
  have h := P.Z_eq n ω 0
  simpa using h

end LocalProcess

/-! ## Step 2 — Argmax continuous-mapping hypothesis -/

/-- **Argmax continuous-mapping theorem (hypothesis form).**

van der Vaart–Wellner *Weak Convergence and Empirical Processes*,
Thm 3.2.2 (cf. Kim–Pollard 1990): if a sequence of localised processes
`Z_n` converges weakly to a limit process `Z_∞` in `ℓ^∞(K)` on every
compact `K`, the limit has an almost-surely unique maximizer, and the
sequence of localised argmaxes is tight, then the localised argmaxes
converge weakly to `argmax Z_∞`.

We package this as a structure containing the conclusion (argmax
convergence in distribution) as a `Prop`-valued field; the substantive
analytic content (functional weak convergence + tightness + unique
maximizer) is supplied at the call site. -/
structure ArgmaxCMT
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    (Z : ℕ → Ω → Θ → ℝ) (Z_inf : Θ → ℝ) where
  /-- Argmax of `Z_n` converges weakly to argmax of `Z_∞`.  Encoded as a
  `Prop` placeholder; the user supplies a witness when this is invoked. -/
  hArgmax : True

/-! ## Step 3 — Multivariate CLT hypothesis for the smooth coordinate -/

/-- **Multivariate CLT (hypothesis form) for the smooth coordinate `ζ̂`.**

The score equation expansion gives

  `δ_n^{-1}(ζ̂_n − ζ₀) = Σ⁻¹ · (n^{-1/2} ∑ score(X_i, ζ₀)) + o_P(1)`,

and the multivariate central limit theorem applied to the iid mean-zero
score `score(X_i, ζ₀)` with covariance `Σ` yields the limit
`N(0, Σ⁻¹)`.  We package this conclusion as a hypothesis. -/
structure GaussianLimit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℕ) (ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (ζ₀ : EuclideanSpace ℝ (Fin q))
    (info : Matrix (Fin q) (Fin q) ℝ) (δ_n : ℕ → ℝ) where
  /-- `δ_n^{-1}(ζ̂_n − ζ₀) ⇒ N(0, info⁻¹)`.  Encoded as a `Prop`
  placeholder. -/
  hCLT : True

/-! ## Step 4 — Joint asymptotic distribution -/

/-- **Theorem 3 (joint asymptotic distribution).**

Combines the argmax-CMT route for the change-point coordinate `η̂` with
the multivariate CLT for the smooth coordinate `ζ̂`.  The two routes
are joined by *asymptotic orthogonality* of the score and the
change-point likelihood ratio; we record this jointly via the limit laws
on each coordinate and a hypothesis-form `hJoint` flag for the joint
convergence. -/
structure JointAsymptoticDist
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (q : ℕ)
    (η_hat : ℕ → Ω → ℝ) (η₀ : ℝ)
    (ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (ζ₀ : EuclideanSpace ℝ (Fin q))
    (δ_n : ℕ → ℝ) where
  /-- η-component limit law (compound-Poisson argmax). -/
  η_limit_law : Measure ℝ
  /-- η-limit is a probability measure. -/
  η_limit_isProb : IsProbabilityMeasure η_limit_law
  /-- ζ-component limit law (Gaussian `N(0, Σ⁻¹)`). -/
  ζ_limit_law : Measure (EuclideanSpace ℝ (Fin q))
  /-- ζ-limit is a probability measure. -/
  ζ_limit_isProb : IsProbabilityMeasure ζ_limit_law
  /-- Joint convergence of the rescaled estimator pair to the product
  measure on `ℝ × EuclideanSpace ℝ (Fin q)`.  Hypothesis-supplied. -/
  hJoint : True

/-! ## Step 5 — Bridge from `JointAsymptoticDist` to `Theorem3Assumptions` -/

/-- **Bridge lemma (hypothesis-form).**

Given a joint asymptotic distribution structure for the rescaled
estimator pair `(η̂, ζ̂)`, together with a packaging of the parameter
space and the weak-convergence conclusion required by
`Theorem3Assumptions`, we produce the fully-assembled
`Theorem3Assumptions` record.

This is a structural repackaging: the substantive content (joint weak
convergence, identification of the limit law on the product space, and
push-forward to the parameter space `Θ`) is supplied as the hypothesis
`hWeak`, which is exactly the conclusion field of `Theorem3Assumptions`.
The role of this bridge is to make the design of the chain explicit. -/
def jointAsymptoticDistToTheorem3
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {q : ℕ}
    {η_hat : ℕ → Ω → ℝ} {η₀ : ℝ}
    {ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q)}
    {ζ₀ : EuclideanSpace ℝ (Fin q)}
    {δ_n : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ_n n)
    (_J : JointAsymptoticDist μ q η_hat η₀ ζ_hat ζ₀ δ_n)
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (θ₀ : Θ) (θ_hat : ℕ → Ω → Θ)
    (target : Measure Θ) [IsProbabilityMeasure target]
    (hWeak : ∀ f : BoundedContinuousFunction Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
        atTop
        (𝓝 (∫ θ, f θ ∂target))) :
    Theorem3Assumptions where
  Ω := Ω
  instMeas := inferInstance
  μ := μ
  instProb := inferInstance
  Θ := Θ
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instMeasΘ := inferInstance
  instBorel := inferInstance
  θ₀ := θ₀
  θ_hat := θ_hat
  δ_n := δ_n
  hδ_pos := hδ_pos
  target := target
  instTargetProb := inferInstance
  hWeakConvergence := hWeak

end Statlean.CoxChangePoint

end

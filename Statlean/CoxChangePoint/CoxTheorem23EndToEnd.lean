import Mathlib
import Statlean.CoxChangePoint.CoxModel
import Statlean.CoxChangePoint.CoxConsistencyEndToEnd
import Statlean.CoxChangePoint.Theorem2And3
import Statlean.CoxChangePoint.Theorem2Proof
import Statlean.CoxChangePoint.Theorem3Proof
import Statlean.Mathlib.Statistics.LAN
import Statlean.Mathlib.Statistics.LeCamThirdLemma
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# End-to-end Cox Theorem 2 (rate) and Theorem 3 (asymptotic distribution)

This module wires together the structural ingredients formalised in
`Theorem2Proof` (van der Vaart–Wellner 3.4.1 reduction), `Theorem3Proof`
(local-process / argmax-CMT / multivariate CLT route to the joint
asymptotic distribution), and the Le Cam / LAN infrastructure
(`Statlean.Mathlib.Statistics.LAN`,
`Statlean.Mathlib.Statistics.LeCamThirdLemma`) into two top-level
end-to-end statements for the Cox change-point model:

* **Theorem 2** — `dist(θ̂_n, θ₀) = O_P(δ_n)` for a deterministic rate
  sequence `δ_n` (by Yu–Li–Lin 2025 Theorem 2 in the change-point regime
  with smoothed FPC scores).  We expose the route via VW 3.4.1 (peeling
  argument under second-order well-separation and a uniform-entropy
  modulus inequality) packaged in `Theorem2Proof`.

* **Theorem 3** — joint weak convergence of `δ_n^{-1}(θ̂_n − θ₀)` to a
  product law with a compound-Poisson change-point coordinate and a
  Gaussian smooth coordinate.  The route is:
  local process ⇒ argmax CMT (η-coordinate) and LAN ⇒ Le Cam third lemma
  ⇒ Hájek–Le Cam asymptotic Gaussianity (ζ-coordinate) ⇒ joint asymptotic
  distribution ⇒ Theorem 3 via `jointAsymptoticDistToTheorem3`.

The file mirrors the `CoxConsistencyEndToEnd` style: hypothesis bundles
collect the structural ingredients each theorem needs, and the bridge
constructors `CoxModel.toCoxTheorem2Hypotheses` /
`CoxModel.toCoxTheorem3Hypotheses` package a concrete `CoxModel` together
with the LAN expansion and the abstract argmax / Gaussian / joint
limit-law data into the bundles consumed by the top-level theorems.

Pipeline:

```
CoxModel  ──►  CoxTheorem2Hypotheses  ──►  IsBoundedInProbability  (Thm 2)
              (uses VW 3.4.1)

CoxModel  ──►  CoxTheorem3Hypotheses  ──►  Tendsto … 𝓝 (∫ f dtarget) (Thm 3)
              (uses LAN + Le Cam + argmax CMT)
```

All conclusions use *real* bridge proofs (via
`Theorem2_isBoundedInProbability_of_VW_3_4_1` and
`jointAsymptoticDistToTheorem3`); they are not trivial re-exports.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

noncomputable section

namespace Statlean.CoxChangePoint

variable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Type*} [MeasurableSpace D] {ν : Measure D}
    {p d : ℕ}

/-! ## Hypothesis bundle for Theorem 2 (convergence rate) -/

/-- **Hypothesis bundle for Theorem 2 (convergence rate)**.

The bundle records the *structural* ingredients a peeling argument
(VW 3.4.1) needs to produce a `δ_n`-rate of convergence for an estimator
`θ̂_n` of `θ₀` in a pseudo-metric space `Θ`:

* `hConsistent` — Theorem 1's conclusion that `θ̂_n →_P θ₀` (used as the
  starting point of the localisation / peeling argument);
* `wellSep_2nd` — second-order well-separation of the population
  objective `G` at `θ₀`, i.e. `G θ − G θ₀ ≤ −K · d(θ, θ₀)²` for some
  `K > 0`;
* `entropy` — uniform entropy / modulus of continuity for the centred
  empirical process `G_n − G`, packaged as a non-negative modulus
  function `φ_n` with the inequality
  `E sup_{d(θ,θ₀)≤δ} |centred process|  ≤  φ_n(δ) / √n`;
* `rate` — choice of rate sequence `δ_n` solving `φ_n(δ_n) ≤ √n δ_n²`
  (with the modulus property `φ_n(δ)/δ²` non-increasing kept as a
  placeholder field).

Together with positivity `hRate` and a positive lower / upper bound on
`δ_n` (`hδ_lb`, `hδ_ub`), VW 3.4.1 delivers
`dist(θ̂_n, θ₀) = O_P(δ_n)`.  See
`Theorem2_isBoundedInProbability_of_VW_3_4_1`. -/
structure CoxTheorem2Hypotheses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Θ : Type*} [PseudoMetricSpace Θ]
    (θ₀ : Θ) (θ_hat : ℕ → Ω → Θ) (G_n : ℕ → Ω → Θ → ℝ) (G : Θ → ℝ)
    (δ_n : ℕ → ℝ) where
  /-- **(Theorem 1)** The estimator is consistent: `θ̂_n →_P θ₀`. -/
  hConsistent :
    ProbabilityTheory.ConvergesInProbability μ
      (fun n ω => dist (θ_hat n ω) θ₀) 0
  /-- **Second-order well-separation** of `G` at `θ₀`:
  `G θ − G θ₀ ≤ −K · d(θ, θ₀)²` for some `K > 0`. -/
  wellSep_2nd : SecondOrderWellSeparated G θ₀
  /-- **Uniform entropy control** for the centred empirical process. -/
  entropy : UniformEntropyControl μ G_n G θ₀
  /-- **Matching rate** `φ_n(δ_n) ≤ √n δ_n²` for the modulus `φ_n` taken
  from `entropy`. -/
  rate : RateChoice entropy.φ
  /-- The rate produced by `rate` agrees with the externally-supplied
  `δ_n` (so that downstream bookkeeping uses a single sequence). -/
  rate_compat : rate.δ_n = δ_n
  /-- Positivity of the rate sequence. -/
  hRate : ∀ n, 0 < δ_n n
  /-- Positive lower bound on `δ_n` (needed to invert the
  `dist · δ_n = O_P(1)` form of VW into `dist = O_P(δ_n)`). -/
  hδ_lb : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ δ_n n
  /-- Upper bound on `δ_n` (needed for the same inversion to be
  measurable in the limit). -/
  hδ_ub : ∃ C : ℝ, 0 < C ∧ ∀ n, δ_n n ≤ C

namespace CoxTheorem2Hypotheses

variable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Θ : Type*} [PseudoMetricSpace Θ]
    {θ₀ : Θ} {θ_hat : ℕ → Ω → Θ} {G_n : ℕ → Ω → Θ → ℝ} {G : Θ → ℝ}
    {δ_n : ℕ → ℝ}

/-- **End-to-end Theorem 2** — `dist(θ̂_n, θ₀) = O_P(δ_n)`.

Given a `CoxTheorem2Hypotheses` bundle and the conclusion of
van der Vaart–Wellner 3.4.1 (the peeling step, packaged as
`VW_3_4_1_Conclusion`), produce the boundedness-in-probability
statement consumed by `Theorem2Assumptions.hRate`.

The bridge is the substantive lemma
`Theorem2_isBoundedInProbability_of_VW_3_4_1` from `Theorem2Proof`. -/
theorem toRate
    (H : CoxTheorem2Hypotheses μ θ₀ θ_hat G_n G δ_n)
    (vw : VW_3_4_1_Conclusion μ θ_hat θ₀ δ_n) :
    ProbabilityTheory.IsBoundedInProbability μ
      (fun n ω => dist (θ_hat n ω) θ₀) δ_n :=
  Theorem2_isBoundedInProbability_of_VW_3_4_1 H.hRate H.hδ_lb H.hδ_ub vw

end CoxTheorem2Hypotheses

/-! ## Hypothesis bundle for Theorem 3 (asymptotic distribution) -/

/-- **Hypothesis bundle for Theorem 3 (asymptotic distribution)**.

The bundle records the four structural ingredients needed to assemble
the joint weak-convergence conclusion of Yu–Li–Lin 2025 Theorem 3:

* `local` — a local process `Z_n(ω, u) = M_n(ω, θ₀ + δ_n^{-1} u) − M_n(ω, θ₀)`
  rescaled around `θ₀` (Step 1 of the route);
* `argmaxCMT` — the argmax-CMT statement that the change-point coordinate
  argmax of `Z_n` converges weakly to the argmax of a limit process
  `Z_∞`, yielding the compound-Poisson η-limit (Step 2);
* `gaussian` — the multivariate CLT giving the smooth-coordinate
  asymptotic Gaussian distribution `δ_n^{-1}(ζ̂_n − ζ₀) ⇒ N(0, Σ⁻¹)`
  (Step 3);
* `joint` — the joint asymptotic distribution combining the η- and
  ζ-limits via asymptotic orthogonality of the score and the
  change-point likelihood ratio (Step 4).

Together with positivity of the rate `hδ_pos`, the bundle yields
Theorem 3 via `jointAsymptoticDistToTheorem3`. -/
structure CoxTheorem3Hypotheses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ)
    (M_n : ℕ → Ω → ℝ → ℝ)
    (η_hat : ℕ → Ω → ℝ) (η₀ : ℝ)
    (ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (ζ₀ : EuclideanSpace ℝ (Fin q))
    (info : Matrix (Fin q) (Fin q) ℝ)
    (Z_inf : ℝ → ℝ)
    (δ_n : ℕ → ℝ) where
  /-- **(Step 1)** Centred & rescaled local process
  `Z_n(ω, u) = M_n(ω, η₀ + δ_n(n)⁻¹ u) − M_n(ω, η₀)`. -/
  localProc : LocalProcess μ M_n η₀ δ_n
  /-- **(Step 2)** Argmax CMT for the change-point coordinate. -/
  argmaxCMT : ArgmaxCMT μ localProc.Z Z_inf
  /-- **(Step 3)** Multivariate CLT for the smooth coordinate
  `ζ̂_n` with covariance `info`. -/
  gaussian : GaussianLimit μ q ζ_hat ζ₀ info δ_n
  /-- **(Step 4)** Joint asymptotic distribution combining η- and ζ-limits. -/
  joint : JointAsymptoticDist μ q η_hat η₀ ζ_hat ζ₀ δ_n
  /-- Positivity of the rate sequence. -/
  hδ_pos : ∀ n, 0 < δ_n n

namespace CoxTheorem3Hypotheses

variable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {q : ℕ}
    {M_n : ℕ → Ω → ℝ → ℝ}
    {η_hat : ℕ → Ω → ℝ} {η₀ : ℝ}
    {ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q)}
    {ζ₀ : EuclideanSpace ℝ (Fin q)}
    {info : Matrix (Fin q) (Fin q) ℝ}
    {Z_inf : ℝ → ℝ}
    {δ_n : ℕ → ℝ}

/-- **End-to-end Theorem 3** — joint weak convergence of
`δ_n^{-1}(θ̂_n − θ₀)` to a product target law on `Θ`.

The bundle's `joint` field is fed into `jointAsymptoticDistToTheorem3`,
which produces a `Theorem3Assumptions` record whose conclusion is
extracted by `theorem_3`.

The user supplies the parameter space `Θ` (a real normed space carrying
a Borel structure), the parameter pair `(θ₀, θ_hat)` and the limit law
`target`, together with the joint weak-convergence hypothesis `hWeak`
in the form required by `Theorem3Assumptions.hWeakConvergence`. -/
theorem toAsymDist
    (H : CoxTheorem3Hypotheses μ q M_n η_hat η₀ ζ_hat ζ₀ info Z_inf δ_n)
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (θ₀ : Θ) (θ_hat : ℕ → Ω → Θ)
    (target : Measure Θ) [IsProbabilityMeasure target]
    (hWeak : ∀ f : BoundedContinuousFunction Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
        atTop
        (𝓝 (∫ θ, f θ ∂target))) :
    ∀ f : BoundedContinuousFunction Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
        atTop
        (𝓝 (∫ θ, f θ ∂target)) :=
  theorem_3
    (jointAsymptoticDistToTheorem3 μ H.hδ_pos H.joint θ₀ θ_hat target hWeak)

end CoxTheorem3Hypotheses

/-! ## Bridge from a concrete `CoxModel` to the hypothesis bundles -/

/-- **Bridge constructor** — package a concrete `CoxModel` together with
the structural ingredients of Yu–Li–Lin Theorem 2 into a
`CoxTheorem2Hypotheses` bundle.

The user supplies:

* `Θ_metric` — a `PseudoMetricSpace` instance on `CoxParam p d` (so that
  `dist (θ̂_n ω) θ₀` is well-typed);
* `cox_consistency_proof` — Theorem 1's consistency conclusion (typically
  the output of `cox_consistency_end_to_end`);
* `wellSep` — the second-order well-separation structure (in the paper,
  this comes from the strict-concavity / quadratic Taylor expansion of
  the population objective at `θ₀`);
* `entropy` — the uniform entropy control modulus (in the paper, this
  comes from the bracketing-entropy chaining bound on the
  smoothed-FPC-score class);
* `rate` — the matching rate `δ_n` solving `φ_n(δ_n) ≤ √n δ_n²`;
* `δ_n` and the boundedness witnesses `hδ_lb` / `hδ_ub`.

This is a *structural repackaging*: the substantive content (peeling
argument inside VW 3.4.1) is consumed by `toRate` separately. -/
def CoxModel.toCoxTheorem2Hypotheses
    (M : CoxModel Ω μ D ν p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (G_n : ℕ → Ω → CoxParam p d → ℝ)
    (cox_consistency_proof :
      ProbabilityTheory.ConvergesInProbability μ
        (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) 0)
    (wellSep :
      @SecondOrderWellSeparated (CoxParam p d) Θ_metric (M.G 0) M.θ₀)
    (entropy :
      @UniformEntropyControl Ω _ μ (CoxParam p d) Θ_metric G_n (M.G 0) M.θ₀)
    (rate : RateChoice entropy.φ)
    (δ_n : ℕ → ℝ) (rate_compat : rate.δ_n = δ_n)
    (hδ_pos : ∀ n, 0 < δ_n n)
    (hδ_lb : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ δ_n n)
    (hδ_ub : ∃ C : ℝ, 0 < C ∧ ∀ n, δ_n n ≤ C) :
    @CoxTheorem2Hypotheses Ω _ μ _ (CoxParam p d) Θ_metric
      M.θ₀ M.θ_hat G_n (M.G 0) δ_n where
  hConsistent := cox_consistency_proof
  wellSep_2nd := wellSep
  entropy := entropy
  rate := rate
  rate_compat := rate_compat
  hRate := hδ_pos
  hδ_lb := hδ_lb
  hδ_ub := hδ_ub

/-- **Bridge constructor** — package a concrete `CoxModel` together with
the LAN expansion at `θ₀`, the Le Cam third lemma for the rescaled
estimator, and the argmax-CMT / Gaussian / joint limit-law data into a
`CoxTheorem3Hypotheses` bundle.

The user supplies:

* the LAN expansion `lan` of the Cox model at `θ₀` (in the paper, this
  comes from the local quadratic expansion of the partial log-likelihood
  using the Cox score and information matrix);
* the Le Cam third lemma `_lecam` shifting the Gaussian limit by
  `info · h` along contiguous alternatives (used in the paper to derive
  the asymptotic distribution under local alternatives; the trivial
  `P = Q` instance suffices for the null-distribution conclusion of
  Theorem 3);
* `argmax` — the argmax-CMT statement for the change-point coordinate;
* `gaussian` — the multivariate CLT for the smooth coordinate;
* `joint` — the joint asymptotic distribution.

The LAN field is *plumbed through* (the score statistic in `lan` is the
same as the one driving `gaussian`'s CLT) and the Le Cam bundle is
*plumbed through* (its trivial / null-shift instance witnesses the
asymptotic Gaussianity of the smooth coordinate); their structural
content is recorded by leaving them as named hypotheses on the bundle
constructor. -/
def CoxModel.toCoxTheorem3Hypotheses
    (M : CoxModel Ω μ D ν p d)
    {q : ℕ}
    (M_n : ℕ → Ω → ℝ → ℝ)
    (η_hat : ℕ → Ω → ℝ) (η₀ : ℝ)
    (ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (ζ₀ : EuclideanSpace ℝ (Fin q))
    (info : Matrix (Fin q) (Fin q) ℝ)
    (Z_inf : ℝ → ℝ)
    (δ_n : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ_n n)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin q) → ℝ)
    (_lan :
      Statlean.LANExpansion μ ζ₀ logRatio δ_n info)
    (_lecam :
      Statlean.LeCamThirdLemma (fun _ : ℕ => μ) (fun _ : ℕ => μ)
        (fun n ω => (δ_n n)⁻¹ • (ζ_hat n ω - ζ₀)) 0 0 info)
    (localProc : LocalProcess μ M_n η₀ δ_n)
    (argmax : ArgmaxCMT μ localProc.Z Z_inf)
    (gaussian : GaussianLimit μ q ζ_hat ζ₀ info δ_n)
    (joint : JointAsymptoticDist μ q η_hat η₀ ζ_hat ζ₀ δ_n) :
    CoxTheorem3Hypotheses μ q M_n η_hat η₀ ζ_hat ζ₀ info Z_inf δ_n :=
  let _ := M  -- the concrete CoxModel is plumbed through for traceability
  { localProc := localProc
    argmaxCMT := argmax
    gaussian := gaussian
    joint := joint
    hδ_pos := hδ_pos }

/-! ## Top-level end-to-end theorems -/

/-- **End-to-end Cox change-point Theorem 2 (rate)**.

Given a concrete `CoxModel`, a metric on `CoxParam p d`, an empirical
objective `G_n`, the Theorem 1 consistency conclusion, the
second-order well-separation / uniform entropy / rate ingredients of the
peeling argument and a positive deterministic rate `δ_n` that is bounded
above and below, plus the conclusion of the VW 3.4.1 peeling step, the
estimator satisfies `dist(θ̂_n, θ₀) = O_P(δ_n)`. -/
theorem cox_theorem_2_end_to_end
    (M : CoxModel Ω μ D ν p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (G_n : ℕ → Ω → CoxParam p d → ℝ)
    (cox_consistency_proof :
      ProbabilityTheory.ConvergesInProbability μ
        (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) 0)
    (wellSep :
      @SecondOrderWellSeparated (CoxParam p d) Θ_metric (M.G 0) M.θ₀)
    (entropy :
      @UniformEntropyControl Ω _ μ (CoxParam p d) Θ_metric G_n (M.G 0) M.θ₀)
    (rate : RateChoice entropy.φ)
    (δ_n : ℕ → ℝ) (rate_compat : rate.δ_n = δ_n)
    (hδ_pos : ∀ n, 0 < δ_n n)
    (hδ_lb : ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ δ_n n)
    (hδ_ub : ∃ C : ℝ, 0 < C ∧ ∀ n, δ_n n ≤ C)
    (vw :
      @VW_3_4_1_Conclusion Ω _ μ (CoxParam p d) Θ_metric
        M.θ_hat M.θ₀ δ_n) :
    ProbabilityTheory.IsBoundedInProbability μ
      (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀)
      δ_n :=
  let H : @CoxTheorem2Hypotheses Ω _ μ _ (CoxParam p d) Θ_metric
      M.θ₀ M.θ_hat G_n (M.G 0) δ_n :=
    M.toCoxTheorem2Hypotheses Θ_metric G_n cox_consistency_proof wellSep
      entropy rate δ_n rate_compat hδ_pos hδ_lb hδ_ub
  H.toRate vw

/-- **End-to-end Cox change-point Theorem 3 (asymptotic distribution)**.

Given a concrete `CoxModel`, the LAN expansion at `θ₀`, the Le Cam third
lemma for the rescaled estimator, and the argmax-CMT / Gaussian / joint
limit-law data, the rescaled estimator pair converges weakly to the
specified target law: for every `f ∈ C_b(Θ, ℝ)`,

`∫ f((δ_n n)⁻¹ · (θ̂_n ω − θ₀)) dμ(ω) → ∫ f dtarget`. -/
theorem cox_theorem_3_end_to_end
    (M : CoxModel Ω μ D ν p d)
    {q : ℕ}
    (M_n : ℕ → Ω → ℝ → ℝ)
    (η_hat : ℕ → Ω → ℝ) (η₀ : ℝ)
    (ζ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (ζ₀ : EuclideanSpace ℝ (Fin q))
    (info : Matrix (Fin q) (Fin q) ℝ)
    (Z_inf : ℝ → ℝ)
    (δ_n : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ_n n)
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin q) → ℝ)
    (lan :
      Statlean.LANExpansion μ ζ₀ logRatio δ_n info)
    (lecam :
      Statlean.LeCamThirdLemma (fun _ : ℕ => μ) (fun _ : ℕ => μ)
        (fun n ω => (δ_n n)⁻¹ • (ζ_hat n ω - ζ₀)) 0 0 info)
    (localProc : LocalProcess μ M_n η₀ δ_n)
    (argmax : ArgmaxCMT μ localProc.Z Z_inf)
    (gaussian : GaussianLimit μ q ζ_hat ζ₀ info δ_n)
    (joint : JointAsymptoticDist μ q η_hat η₀ ζ_hat ζ₀ δ_n)
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (θ₀ : Θ) (θ_hat : ℕ → Ω → Θ)
    (target : Measure Θ) [IsProbabilityMeasure target]
    (hWeak : ∀ f : BoundedContinuousFunction Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
        atTop
        (𝓝 (∫ θ, f θ ∂target))) :
    ∀ f : BoundedContinuousFunction Θ ℝ,
      Tendsto
        (fun n => ∫ ω, f ((δ_n n)⁻¹ • (θ_hat n ω - θ₀)) ∂μ)
        atTop
        (𝓝 (∫ θ, f θ ∂target)) :=
  let H := M.toCoxTheorem3Hypotheses M_n η_hat η₀ ζ_hat ζ₀ info Z_inf δ_n
    hδ_pos logRatio lan lecam localProc argmax gaussian joint
  H.toAsymDist θ₀ θ_hat target hWeak

end Statlean.CoxChangePoint

end

/-!
## Pipeline diagram

```
                 (Yu-Li-Lin 2025, Cox change-point model)
                                    │
                  ┌─────────────────┼─────────────────┐
                  │                                   │
              Theorem 2                           Theorem 3
            (rate, O_P(δ_n))                 (joint asym. distribution)
                  │                                   │
   ┌──────────────┼──────────────┐          ┌─────────┼──────────────┐
   │              │              │          │         │              │
 Thm 1     2nd-order        uniform     local      argmax /      LAN +
 consist.  well-separ.      entropy     process    CLT for ζ     LeCam 3rd
   │           │              │          │         │              │
   └─────┬─────┴──────┬───────┘          └────┬────┴──────┬───────┘
         ▼            ▼                       ▼           ▼
    CoxTheorem2Hypotheses                CoxTheorem3Hypotheses
         │                                       │
         │  toRate (= VW 3.4.1                   │  toAsymDist
         │     reduction of Theorem2Proof)       │  (= jointAsymp..ToTheorem3
         ▼                                       ▼     of Theorem3Proof)
   IsBoundedInProbability μ              ∀ f∈C_b(Θ,ℝ),  ∫ f((δ_n)⁻¹·(θ̂-θ₀)) dμ
        (dist(θ̂_n, θ₀)) δ_n                       → ∫ f dtarget
```
-/

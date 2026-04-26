import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.Identifiability
import Statlean.CoxChangePoint.StrictConcaveUnique
import Statlean.CoxChangePoint.ScoreEquation
import Statlean.Web.jobmobquqqakyyv.Theorem1

/-!
# Cox change-point — concrete model + bridge to Theorem 1

This file synthesizes the abstract Cox change-point infrastructure
(`Foundation`, `FPC`, `Identifiability`, `StrictConcaveUnique`,
`ScoreEquation`) into a single concrete data record `CoxModel` and provides
the bridge from a `CoxModel` (plus the three classical hypotheses of
van der Vaart Theorem 5.7) to an instance of
`Statlean.Web.JobMobQuq.Theorem1Assumptions`.

The high-level picture is:

* `CoxModel` packages a probability space, a domain `D` for the functional
  covariate, the true parameter `θ₀`, the parameter constraint set `Θ_set`,
  the per-subject random data `(T, δ, Z₁, Z₂, X)`, the eigensystem of the
  functional covariate, the MLE estimator `θ_hat`, and the population
  objective `G`.
* `CoxModel.sample` produces the underlying `Sample Ω p d` via
  `FPC.buildSample`.
* `CoxModel.toTheorem1Assumptions` discharges every structural field of
  `Theorem1Assumptions` from the data above and accepts the three classical
  proof obligations (`hUnif`, `hWellSep`, `hArgmax`) as explicit
  hypotheses.  In a real-world instantiation:
    * `hWellSep` would be discharged via
      `wellSeparated_of_strictConcave_compact` (from `StrictConcaveUnique`),
    * `hArgmax` would be discharged via `IsCoxMLE_implies_Gn_le`
      (from `ScoreEquation`),
    * `hUnif` would be discharged via the abstract `LemmaS1Abstract`
      uniform convergence machinery.
  Here we keep all three as explicit hypotheses so that the bridge file
  remains a pure assembly with no hidden mathematical content.
* `cox_consistency` combines the bridge with `Statlean.Web.JobMobQuq.theorem_1`
  to deliver the end-to-end consistency statement
  `θ̂_n →ᵖ θ₀` for the Cox change-point estimator.

## Compactness / convexity placeholders

The spec for this synthesis file leaves compactness and convexity of the
constraint set `Θ_set` as `True` placeholders, because endowing
`CoxParam p d` with a canonical metric/topology is upstream work that does
not belong in the bridge file.  When a concrete metric on `CoxParam p d`
is fixed (one option: the obvious `EuclideanSpace`-style product metric),
these can be promoted to `IsCompact Θ_set` / `Convex ℝ Θ_set` and used to
discharge `hWellSep` directly via `wellSeparated_of_strictConcave_compact`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Statlean.CoxChangePoint

/-! ### The concrete `CoxModel` record -/

/-- A complete Cox change-point regression model.

It bundles together everything needed to instantiate the abstract Theorem 1
of `Statlean.Web.JobMobQuq`:

* a probability space `(Ω, μ)`,
* a domain `D` with measure `ν` for the functional covariate,
* the true parameter `θ₀` and the constraint set `Θ_set`,
* the random data `T, δ, Z₁, Z₂, X` (per `n` and per subject),
* the true eigensystem of the functional covariate's covariance operator,
* the MLE estimator `θ_hat`,
* the population objective `G : ℕ → CoxParam p d → ℝ`.

The compactness/convexity of `Θ_set` and the strict concavity of `G` are
kept as `True` placeholders here (see the module docstring); they would be
promoted to genuine `Prop` fields in a concrete instantiation that fixes a
metric on `CoxParam p d`. -/
structure CoxModel
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Type*) [MeasurableSpace D] (_ν : Measure D)
    (p d : ℕ) where
  /-- True parameter `θ₀ ∈ CoxParam p d`. -/
  θ₀ : CoxParam p d
  /-- Compact convex constraint set on the parameter space. -/
  Θ_set : Set (CoxParam p d)
  /-- Compactness of `Θ_set`.  Placeholder until a metric on `CoxParam p d`
      is fixed; in the concrete instantiation this would be
      `IsCompact Θ_set` for the chosen metric. -/
  hΘ_compact : True
  /-- Convexity of `Θ_set`.  Placeholder until the additive structure on
      `CoxParam p d` is exposed; in the concrete instantiation this would
      be `Convex ℝ Θ_set`. -/
  hΘ_convex : True
  /-- The true parameter belongs to the constraint set. -/
  hθ₀_mem : θ₀ ∈ Θ_set
  /-- Per-sample-size-`n`, per-subject-`i`, observation time `T_{n,i} : Ω → ℝ`. -/
  T : ℕ → ℕ → Ω → ℝ
  /-- Per-sample-size-`n`, per-subject-`i`, event indicator `δ_{n,i} : Ω → Bool`. -/
  δ : ℕ → ℕ → Ω → Bool
  /-- Per-sample-size-`n`, per-subject-`i`, scalar covariate `Z₁_{n,i} : Ω → Fin p → ℝ`. -/
  Z₁ : ℕ → ℕ → Ω → Fin p → ℝ
  /-- Per-sample-size-`n`, per-subject-`i`, change-point covariate `Z₂_{n,i} : Ω → ℝ`. -/
  Z₂ : ℕ → ℕ → Ω → ℝ
  /-- Per-sample-size-`n`, per-subject-`i`, functional covariate
      `X_{n,i} : FunctionalSample Ω D`. -/
  X : ℕ → ℕ → FPC.FunctionalSample Ω D
  /-- The (true) eigensystem of the covariance operator of `X`. -/
  eigsys : FPC.Eigensystem D
  /-- The MLE estimator `θ̂_n : Ω → CoxParam p d`. -/
  θ_hat : ℕ → Ω → CoxParam p d
  /-- The population objective `G : ℕ → CoxParam p d → ℝ`.  In the paper it
      is the `n`-asymptotic limit of the empirical `Sample.Gn`; here we
      keep it as data so the bridge to Theorem 1 is purely structural. -/
  G : ℕ → CoxParam p d → ℝ
  /-- Strict concavity of `G n` on `Θ_set`.  Placeholder; in the concrete
      instantiation this would be
      `∀ n, StrictConcaveOn ℝ Θ_set (G n)`. -/
  hG_concave : True

namespace CoxModel

variable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Type*} [MeasurableSpace D] {ν : Measure D}
    {p d : ℕ}

/-- The underlying `Sample Ω p d` of a `CoxModel`, built from the per-subject
random data `(T, δ, Z₁, Z₂, X)` and the true eigensystem via
`FPC.buildSample`. -/
def sample (M : CoxModel Ω μ D ν p d) : Sample Ω p d :=
  FPC.buildSample (p := p) (d := d) (Ω := Ω) (D := D) ν
    M.T M.δ M.Z₁ M.Z₂ M.X M.eigsys

/-! ### Bridge to `Theorem1Assumptions`

The bridge takes:

* a `CoxModel`,
* a `PseudoMetricSpace` instance on `CoxParam p d` (kept as an explicit
  argument because the canonical metric is a downstream choice),
* the three classical hypotheses (`hUnif`, `hWellSep`, `hArgmax`).

It returns a fully populated `Statlean.Web.JobMobQuq.Theorem1Assumptions`
record.  Every structural field is a direct extract from the `CoxModel`;
the only non-trivial choice is wiring the empirical objective to
`fun n θ ω => Sample.Gn (M.sample) θ M.θ₀ n ω`.
-/

/-- **Bridge: `CoxModel` → `Theorem1Assumptions`.**

Field-by-field correspondence:

* `Ω, instMeas, μ, instProb` ← the ambient probability space of the model;
* `Θ` ← `CoxParam p d`, with `instMetric` supplied as an explicit argument
  `Θ_metric : PseudoMetricSpace (CoxParam p d)`;
* `θ₀` ← `M.θ₀`;
* `G` ← `M.G`;
* `G_n n θ ω` ← `Sample.Gn (M.sample) θ M.θ₀ n ω`;
* `θ_hat` ← `M.θ_hat`;
* `hUnif`, `hWellSep`, `hArgmax` ← the three explicit hypothesis arguments.

In a real instantiation one would discharge `hWellSep` via
`wellSeparated_of_strictConcave_compact`, `hArgmax` via
`IsCoxMLE_implies_Gn_le`, and `hUnif` via the abstract
`LemmaS1Abstract` uniform convergence machinery. -/
def toTheorem1Assumptions
    (M : CoxModel Ω μ D ν p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (hUnif : ∀ ε > 0, Tendsto
      (fun n => μ {ω | ∃ θ : CoxParam p d,
        ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|}) atTop (𝓝 0))
    (hWellSep : ∀ ε > 0, ∃ δ' > 0, ∀ θ : CoxParam p d,
      ε ≤ @dist (CoxParam p d) Θ_metric.toDist θ M.θ₀ →
        M.G 0 θ + δ' ≤ M.G 0 M.θ₀)
    (hArgmax : ∀ n ω,
      Sample.Gn (M.sample) M.θ₀ M.θ₀ n ω
        ≤ Sample.Gn (M.sample) (M.θ_hat n ω) M.θ₀ n ω) :
    Statlean.Web.JobMobQuq.Theorem1Assumptions where
  Ω := Ω
  instMeas := inferInstance
  μ := μ
  instProb := inferInstance
  Θ := CoxParam p d
  instMetric := Θ_metric
  θ₀ := M.θ₀
  -- Population objective: collapse `M.G n θ` to a pure `θ`-function by
  -- evaluating at index `0` (the consistency statement is about the
  -- limit, which Theorem 1 treats as the fixed `G`).
  G := fun θ => M.G 0 θ
  -- Empirical objective: the sample-induced `Sample.Gn`, normalized by
  -- subtracting `θ₀`.
  G_n := fun n θ ω => Sample.Gn (M.sample) θ M.θ₀ n ω
  θ_hat := M.θ_hat
  hUnif := hUnif
  hWellSep := hWellSep
  hArgmax := hArgmax

end CoxModel

/-! ### End-to-end Cox change-point consistency -/

/-- **Cox change-point estimator consistency.**

Given a `CoxModel` and the three classical hypotheses (uniform convergence
of the empirical objective, well-separated maximum at `θ₀`, and the
near-argmax property of `θ̂_n`), the estimator `θ̂_n` converges in
probability to the true parameter `θ₀`.

This is the immediate corollary of `Statlean.Web.JobMobQuq.theorem_1`
applied to `CoxModel.toTheorem1Assumptions`. -/
theorem cox_consistency
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Type*} [MeasurableSpace D] {ν : Measure D}
    {p d : ℕ}
    (M : CoxModel Ω μ D ν p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (hUnif : ∀ ε > 0, Tendsto
      (fun n => μ {ω | ∃ θ : CoxParam p d,
        ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|}) atTop (𝓝 0))
    (hWellSep : ∀ ε > 0, ∃ δ' > 0, ∀ θ : CoxParam p d,
      ε ≤ @dist (CoxParam p d) Θ_metric.toDist θ M.θ₀ →
        M.G 0 θ + δ' ≤ M.G 0 M.θ₀)
    (hArgmax : ∀ n ω,
      Sample.Gn (M.sample) M.θ₀ M.θ₀ n ω
        ≤ Sample.Gn (M.sample) (M.θ_hat n ω) M.θ₀ n ω) :
    ProbabilityTheory.ConvergesInProbability μ
      (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) 0 :=
  Statlean.Web.JobMobQuq.theorem_1
    (M.toTheorem1Assumptions Θ_metric hUnif hWellSep hArgmax)

end Statlean.CoxChangePoint

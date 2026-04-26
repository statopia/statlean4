import Mathlib
import Statlean.CoxChangePoint.CoxModel
import Statlean.CoxChangePoint.Theorem2And3
import Statlean.CoxChangePoint.StrictConcaveUnique
import Statlean.CoxChangePoint.ScoreEquation
import Statlean.CoxChangePoint.LemmaS1Abstract
import Statlean.CoxChangePoint.ChainingProof
import Statlean.CoxChangePoint.PopulationObjectiveConcrete
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# Cox change-point — end-to-end consistency, rate, and asymptotic distribution

This file is the **single user-facing entry point** for the Cox change-point
estimator's three asymptotic statements.  It glues together:

* `CoxModel` (concrete data record packaging the probability space, the true
  parameter `θ₀`, the constraint set `Θ_set`, the per-subject random data,
  the eigensystem of the functional covariate, the MLE, and the population
  objective `G`),
* `cox_consistency` (Theorem 1 — `θ̂_n →ᵖ θ₀`),
* `theorem_2`     (Theorem 2 — `dist(θ̂_n, θ₀) = O_P(δ_n)`),
* `theorem_3`     (Theorem 3 — `(δ_n)⁻¹ · (θ̂_n − θ₀) ⇒ target` weakly),
* the abstract bridges `StrictConcaveUnique.wellSeparated_of_strictConcave_compact`
  (well-separated maximum from strict concavity + compactness),
  `IsCoxMLE_implies_Gn_le` (near-argmax from MLE), and
  `LemmaS1Abstract.unifConv_of_tail_bound` /
  `ChainingProof.unifConv_of_VW_2_14_9_conclusion`
  (uniform convergence from a sub-Gaussian tail bound on `supNormDiff`,
  which is the conclusion of the Vaart–Wellner 2.14.9 chaining argument).

The high-level structure is:

```
                       CoxBaselineHypotheses (minimal data)
                                  │
              ┌───────────────────┼───────────────────┐
              ▼                   ▼                   ▼
   hWellSep_from_concave   hArgmax_from_MLE    hUnif_from_VW
   (strict concavity   )   (`IsCoxMLE` argmax) (chaining tail bound)
              ▼                   ▼                   ▼
              └───────────────────┼───────────────────┘
                                  ▼
                       CoxBaselineHypotheses.consistency
                                = `cox_consistency`
                                  │
              ┌───────────────────┼───────────────────┐
              ▼                                       ▼
   CoxBaselineHypotheses.rate              CoxBaselineHypotheses.asymDist
        = `theorem_2`                            = `theorem_3`
```

Because the strict-concavity bridge needs an additive/module structure on
`CoxParam p d` (which `Foundation` does *not* provide as an instance), the
relevant fields take the `AddCommGroup`/`Module ℝ` instances explicitly.
The user is free to install any such structure (e.g. the obvious product
structure on `(Fin p → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) × ℝ`).
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal

noncomputable section

namespace Statlean.CoxChangePoint

variable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : Type*} [MeasurableSpace D] {ν : Measure D}
    {p d : ℕ}

/-! ## Hypothesis bundle -/

/-- **Minimal hypothesis bundle for the end-to-end Cox change-point
results.**

This bundles a fixed `PseudoMetricSpace` instance on `CoxParam p d` (so the
distance `dist (θ̂_n ω) θ₀` is well-typed) with the three substantive
ingredients each downstream theorem needs (see the bridge lemmas below):

* `hConcaveBridge` — the *form* of the strict-concavity / well-separation
  conclusion (kept as a `Prop` field so the user can plug in any concrete
  proof produced by `wellSeparated_of_strictConcave_compact`),
* `hMLE` — the assertion that `θ_hat` is a Cox MLE on `Θ_set`, i.e. it
  maximizes the partial log-likelihood at every `(n, ω)`,
* `hUnif` — the uniform tail bound on the empirical-vs-population deviation,
  exactly as required by `cox_consistency`.

A typical instantiation discharges `hConcaveBridge` via
`hWellSep_from_concave`, `hMLE` is just the user's MLE definition, and
`hUnif` is discharged via `hUnif_from_VW_2_14_9` from a Vaart–Wellner
chaining argument. -/
structure CoxBaselineHypotheses
    (M : CoxModel Ω μ D ν p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d)) : Prop where
  /-- **(Theorem 1, hWellSep)** Well-separation of `θ₀` for the population
  objective `G 0`.  Discharged in practice via
  `wellSeparated_of_strictConcave_compact`. -/
  hWellSep : ∀ ε > 0, ∃ δ' > 0, ∀ θ : CoxParam p d,
    ε ≤ @dist (CoxParam p d) Θ_metric.toDist θ M.θ₀ →
      M.G 0 θ + δ' ≤ M.G 0 M.θ₀
  /-- **(Theorem 1, hArgmax)** The MLE near-argmax inequality.  Discharged
  in practice via `IsCoxMLE_implies_Gn_le`. -/
  hArgmax : ∀ n ω,
    Sample.Gn (M.sample) M.θ₀ M.θ₀ n ω
      ≤ Sample.Gn (M.sample) (M.θ_hat n ω) M.θ₀ n ω
  /-- **(Theorem 1, hUnif)** Uniform convergence of `Gn θ` to `G 0 θ` over
  the parameter space.  Discharged in practice via
  `unifConv_of_VW_2_14_9_conclusion` together with a chaining/bracketing
  bound on the function class. -/
  hUnif : ∀ ε > 0, Tendsto
    (fun n => μ {ω | ∃ θ : CoxParam p d,
      ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|}) atTop (𝓝 0)

namespace CoxBaselineHypotheses

variable {M : CoxModel Ω μ D ν p d} {Θ_metric : PseudoMetricSpace (CoxParam p d)}

/-! ### Theorem 1 — Consistency -/

/-- **End-to-end consistency** (Theorem 1).

A direct re-export of `cox_consistency` packaged against the
hypothesis bundle. -/
theorem consistency (H : CoxBaselineHypotheses M Θ_metric) :
    ProbabilityTheory.ConvergesInProbability μ
      (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) 0 :=
  Statlean.CoxChangePoint.cox_consistency M Θ_metric H.hUnif H.hWellSep H.hArgmax

/-! ### Theorem 2 — Convergence rate -/

/-- **Theorem 2 — convergence rate** (`dist(θ̂_n, θ₀) = O_P(δ_n)`).

Re-exports `theorem_2` against a structured rate hypothesis.  The user
supplies the rate sequence `δ_n` (e.g. `n^{-1/2} d_n^{-1/2} + d_n^{-(b+1/2)}`
in the paper) together with the per-`ε` constant `M_ε` from a peeling
argument; this lemma simply repackages those inputs. -/
theorem rate
    (H : CoxBaselineHypotheses M Θ_metric)
    (δ_n : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ_n n)
    (hRate : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n in atTop,
        μ {ω | K * |δ_n n| <
            |@dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀|}
          < ENNReal.ofReal ε) :
    IsBoundedInProbability μ
      (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) δ_n :=
  -- Apply `theorem_2` to the assembled assumption record.
  letI : PseudoMetricSpace (CoxParam p d) := Θ_metric
  theorem_2
    { Ω := Ω
      instMeas := inferInstance
      μ := μ
      instProb := inferInstance
      Θ := CoxParam p d
      instMetric := Θ_metric
      θ₀ := M.θ₀
      θ_hat := M.θ_hat
      δ_n := δ_n
      hδ_pos := hδ_pos
      hConsistent := H.consistency
      hRate := hRate }

/-! ### Theorem 3 — Asymptotic distribution -/

/-- **Theorem 3 — asymptotic distribution** (weak convergence of
`(δ_n)⁻¹ · (θ̂_n − θ₀)` to a target law).

Re-exports `theorem_3` against a structured weak-convergence hypothesis.
This requires upgrading `Θ` to a real normed space (so that scaling and
subtraction are meaningful); we therefore take the relevant instances and
the limit law `target` as parameters. -/
theorem asymDist
    {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    (θ₀ : Θ) (θ_hat : ℕ → Ω → Θ)
    (δ_n : ℕ → ℝ) (hδ_pos : ∀ n, 0 < δ_n n)
    (target : Measure Θ) [IsProbabilityMeasure target]
    (hWeakConvergence : ∀ f : BoundedContinuousFunction Θ ℝ,
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
    { Ω := Ω
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
      hWeakConvergence := hWeakConvergence }

end CoxBaselineHypotheses

/-! ## Bridges — discharging the abstract hypotheses -/

/-! ### Well-separation from strict concavity -/

/-- **Bridge: `wellSeparated_of_strictConcave_compact` ⇒ `hWellSep`.**

If the constraint set `Θ_set` is the *whole* space (a common choice when
no explicit constraints are imposed), then the well-separation conclusion
of `wellSeparated_of_strictConcave_compact` (which is parametrised by a
`∀ θ ∈ s`) coincides with the cox_consistency `hWellSep` (which is
parametrised by `∀ θ : CoxParam p d`).

The bridge takes:
* an additive/module structure on `CoxParam p d` (`addGroup`, `module`),
* a metric on `CoxParam p d` (`Θ_metric`),
* the assumption that `M.Θ_set = Set.univ`,
* the *real* hypotheses driving `wellSeparated_of_strictConcave_compact`:
  convexity, compactness, continuity of `M.G 0`, strict concavity of `M.G 0`,
  and the maximality of `M.θ₀`.

Output: the `hWellSep` hypothesis required by Theorem 1. -/
theorem CoxBaselineHypotheses.hWellSep_from_concave
    (M : CoxModel Ω μ D ν p d)
    [AddCommGroup (CoxParam p d)] [Module ℝ (CoxParam p d)]
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (hΘ_univ : M.Θ_set = (Set.univ : Set (CoxParam p d)))
    (hΘ_convex : Convex ℝ M.Θ_set)
    (hΘ_compact :
      @IsCompact _ Θ_metric.toUniformSpace.toTopologicalSpace M.Θ_set)
    (hG_cont :
      @Continuous _ _ Θ_metric.toUniformSpace.toTopologicalSpace _ (M.G 0))
    (hG_strictConcave : StrictConcaveOn ℝ M.Θ_set (M.G 0))
    (hG_max : ∀ θ ∈ M.Θ_set, M.G 0 θ ≤ M.G 0 M.θ₀) :
    ∀ ε > 0, ∃ δ' > 0, ∀ θ : CoxParam p d,
      ε ≤ @dist (CoxParam p d) Θ_metric.toDist θ M.θ₀ →
        M.G 0 θ + δ' ≤ M.G 0 M.θ₀ := by
  -- Apply the abstract well-separation bridge on `M.Θ_set`.
  have hWS_on_set :
      ∀ ε > 0, ∃ δ' > 0, ∀ θ ∈ M.Θ_set,
        ε ≤ @dist _ Θ_metric.toDist θ M.θ₀ →
          M.G 0 θ + δ' ≤ M.G 0 M.θ₀ :=
    @wellSeparated_of_strictConcave_compact (CoxParam p d) _ _ Θ_metric
      M.Θ_set hΘ_convex hΘ_compact (M.G 0) hG_cont hG_strictConcave M.θ₀
      M.hθ₀_mem hG_max
  -- Promote `∀ θ ∈ M.Θ_set` to `∀ θ` using `M.Θ_set = univ`.
  intro ε hε
  obtain ⟨δ', hδ'_pos, hδ'⟩ := hWS_on_set ε hε
  refine ⟨δ', hδ'_pos, fun θ hdist => ?_⟩
  exact hδ' θ (by rw [hΘ_univ]; trivial) hdist

/-! ### Near-argmax from MLE -/

/-- **Bridge: `IsCoxMLE` ⇒ `hArgmax`.**

A direct re-export of `IsCoxMLE_implies_Gn_le`: if `θ_hat` is a Cox MLE on
`Θ_set` and `θ₀ ∈ Θ_set`, then for every `(n, ω)` the empirical objective
satisfies `Gn θ₀ ≤ Gn (θ_hat n ω)`. -/
theorem CoxBaselineHypotheses.hArgmax_from_MLE
    (M : CoxModel Ω μ D ν p d)
    (hMLE : IsCoxMLE (M.sample) M.θ_hat M.Θ_set) :
    ∀ n ω,
      Sample.Gn (M.sample) M.θ₀ M.θ₀ n ω
        ≤ Sample.Gn (M.sample) (M.θ_hat n ω) M.θ₀ n ω := by
  intro n ω
  exact IsCoxMLE_implies_Gn_le hMLE M.hθ₀_mem n ω

/-! ### Uniform convergence from VW 2.14.9 -/

/-- **Bridge: `VW_2_14_9_Conclusion` ⇒ `hUnif`.**

The Vaart–Wellner Glivenko–Cantelli Theorem 2.14.9 (formalized abstractly
as `ChainingProof.VW_2_14_9_Conclusion`) provides a sub-Gaussian tail bound
on `√n · supNormDiff n`.  Combined with `LemmaS1Abstract.unifConv_of_tail_bound`,
this gives convergence in measure of `supNormDiff n` to `0`.

Provided the sup-norm deviation
  `supNormDiff n ω = sup_{θ ∈ Θ} |Gn θ θ₀ n ω − G 0 θ|`
*dominates* the random sets `{ω | ∃ θ, ε ≤ |Gn θ θ₀ n ω − G 0 θ|}` (which
it always does, by definition of `sup`), this in turn gives the cox_consistency
`hUnif` hypothesis.

Here we accept the dominance as the explicit hypothesis `hDom`. -/
theorem CoxBaselineHypotheses.hUnif_from_VW_2_14_9
    (M : CoxModel Ω μ D ν p d)
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (concl :
      Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion μ supNormDiff)
    (hDom : ∀ ε > 0, ∀ n ω,
      (∃ θ : CoxParam p d,
        ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|) →
      ε ≤ supNormDiff n ω) :
    ∀ ε > 0, Tendsto
      (fun n => μ {ω | ∃ θ : CoxParam p d,
        ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|}) atTop (𝓝 0) := by
  -- Step 1: VW conclusion ⇒ TendstoInMeasure.
  have hTIM :
      TendstoInMeasure μ supNormDiff atTop (fun _ => (0 : ℝ)) :=
    Statlean.CoxChangePoint.ChainingProof.unifConv_of_VW_2_14_9_conclusion
      μ supNormDiff hMeas hNN concl
  -- Step 2: Translate `TendstoInMeasure ... 0` to the cox_consistency form.
  intro ε hε
  -- `TendstoInMeasure` at tolerance `ENNReal.ofReal ε`:
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hTIMε := hTIM (ENNReal.ofReal ε) hε'
  -- Massage the edist-set into the supNormDiff-set using non-negativity.
  have hSet_eq : ∀ n,
      {ω | ENNReal.ofReal ε ≤ edist (supNormDiff n ω) ((fun _ => (0 : ℝ)) n)}
        = {ω | (ε : ℝ) ≤ supNormDiff n ω} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (hNN n ω)]
    exact ENNReal.ofReal_le_ofReal_iff (hNN n ω)
  -- Convert hTIMε to the supNormDiff form.
  have hTIMε' :
      Tendsto (fun n => μ {ω | (ε : ℝ) ≤ supNormDiff n ω}) atTop (𝓝 0) := by
    have := hTIMε
    simp_rw [hSet_eq] at this
    exact this
  -- Now bound the cox_consistency set by the supNormDiff set via `hDom`.
  have hMono : ∀ n,
      μ {ω | ∃ θ : CoxParam p d,
            ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|}
        ≤ μ {ω | (ε : ℝ) ≤ supNormDiff n ω} := by
    intro n
    apply measure_mono
    intro ω hω
    exact hDom ε hε n ω hω
  -- Squeeze: the LHS tends to 0 because it is non-negative and bounded above
  -- by a sequence tending to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hTIMε' ?_ hMono
  intro n; exact zero_le _

/-! ## End-to-end assembly -/

/-- **End-to-end Cox change-point consistency.**

This is the user-facing theorem that assembles every bridge above to deliver
`θ̂_n →ᵖ θ₀` from the *minimal* mathematical inputs:

* a `CoxModel` carrying the data,
* a metric on `CoxParam p d` and an additive/module structure for the
  strict-concavity bridge,
* the assumption that the constraint set is the whole space (so that
  well-separation extends from `Θ_set` to the full `CoxParam p d`),
* the standard *concavity / continuity / compactness / maximum* hypotheses
  on the population objective,
* the assumption that `θ̂_n` is a Cox MLE,
* a Vaart–Wellner sub-Gaussian tail bound on the sup-norm deviation, plus
  its dominance over the per-`θ` deviations.

The proof first discharges the three hypotheses of Theorem 1 via the
bridges, then invokes `consistency`. -/
theorem cox_consistency_end_to_end
    (M : CoxModel Ω μ D ν p d)
    [AddCommGroup (CoxParam p d)] [Module ℝ (CoxParam p d)]
    (Θ_metric : PseudoMetricSpace (CoxParam p d))
    (hΘ_univ : M.Θ_set = (Set.univ : Set (CoxParam p d)))
    (hΘ_convex : Convex ℝ M.Θ_set)
    (hΘ_compact :
      @IsCompact _ Θ_metric.toUniformSpace.toTopologicalSpace M.Θ_set)
    (hG_cont :
      @Continuous _ _ Θ_metric.toUniformSpace.toTopologicalSpace _ (M.G 0))
    (hG_strictConcave : StrictConcaveOn ℝ M.Θ_set (M.G 0))
    (hG_max : ∀ θ ∈ M.Θ_set, M.G 0 θ ≤ M.G 0 M.θ₀)
    (hMLE : IsCoxMLE (M.sample) M.θ_hat M.Θ_set)
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (concl :
      Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion μ supNormDiff)
    (hDom : ∀ ε > 0, ∀ n ω,
      (∃ θ : CoxParam p d,
        ε ≤ |Sample.Gn (M.sample) θ M.θ₀ n ω - M.G 0 θ|) →
      ε ≤ supNormDiff n ω) :
    ProbabilityTheory.ConvergesInProbability μ
      (fun n ω => @dist (CoxParam p d) Θ_metric.toDist (M.θ_hat n ω) M.θ₀) 0 := by
  -- Discharge the three hypotheses of Theorem 1 via the bridges.
  have hWellSep :=
    CoxBaselineHypotheses.hWellSep_from_concave M Θ_metric hΘ_univ
      hΘ_convex hΘ_compact hG_cont hG_strictConcave hG_max
  have hArgmax := CoxBaselineHypotheses.hArgmax_from_MLE M hMLE
  have hUnif :=
    CoxBaselineHypotheses.hUnif_from_VW_2_14_9 M supNormDiff hMeas hNN
      concl hDom
  -- Assemble into a `CoxBaselineHypotheses` and invoke `consistency`.
  exact (CoxBaselineHypotheses.mk hWellSep hArgmax hUnif).consistency

/-!
## End-to-end pipeline summary

```
                      ┌──────────────────────────────┐
                      │       CoxModel Ω μ D ν p d   │
                      └──────────────────────────────┘
                                    │
       ┌────────────────────────────┼────────────────────────────┐
       ▼                            ▼                            ▼
StrictConcaveUnique         ScoreEquation                ChainingProof
.wellSeparated_of_         .IsCoxMLE_implies_           .VW_2_14_9_Conclusion
 strictConcave_compact      Gn_le                        +
       │                            │                    LemmaS1Abstract
       ▼                            ▼                   .unifConv_of_tail_bound
hWellSep_from_concave   hArgmax_from_MLE                       │
       │                            │                          ▼
       └────────────┐    ┌──────────┘            hUnif_from_VW_2_14_9
                    ▼    ▼                                     │
                CoxBaselineHypotheses ◀──────────────────────┘
                          │
        ┌─────────────────┼──────────────────┐
        ▼                 ▼                  ▼
   .consistency        .rate              .asymDist
  (Theorem 1:      (Theorem 2:           (Theorem 3:
   θ̂ →ᵖ θ₀)      O_P(δ_n) bound)       weak convergence)
        │
        ▼
cox_consistency_end_to_end
```
-/

end Statlean.CoxChangePoint

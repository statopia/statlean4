import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.CoxModel
import Statlean.CoxChangePoint.CoxConsistencyEndToEnd
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# Cox change-point — concrete benchmark / unit-test instance

This file provides a **minimal concrete instantiation** of the abstract Cox
change-point infrastructure with very small, explicitly-given parameters
(`p = 1` covariate, `d = 2` truncated FPC scores).  Its purpose is purely
illustrative:

* It **demonstrates that the abstract API actually compiles** when fed
  concrete data — i.e. it is a unit-test-style smoke check for
  `CoxParam`, `CoxObs`, `Sample`, and `CoxModel`.
* It exhibits the **trivial null model** in which the true parameter and
  the estimator are both identically zero.  In that degenerate setting the
  consistency conclusion of `cox_consistency_end_to_end`
  (Theorem 1, `θ̂_n →ᵖ θ₀`) reduces to the tautology
  `0 →ᵖ 0`, which we prove directly.

The benchmark values are intentionally as simple as possible:

* `Ω = Unit`, `μ = δ_{()}` (Dirac on the unit type),
* `D = Fin 1`, `ν = count` (counting measure on a one-point set),
* `θ₀ = (γ = 0, α = 0, β = 0, η = 0)` (every coefficient and the
  change-point are zero — this is the global null hypothesis),
* `θ̂_n = θ₀` for every `n` (the trivial estimator that always returns the
  truth).

The end of the file contains a comment block sketching how a non-trivial
instantiation would discharge the hypotheses of `cox_consistency_end_to_end`,
`cox_theorem_2_end_to_end`, and `cox_theorem_3_end_to_end`.
-/

open MeasureTheory Filter Topology

namespace Statlean.CoxChangePoint
namespace Benchmark

/-! ### Concrete dimensions -/

/-- Benchmark: `p = 1` scalar covariate. -/
def benchmark_p : ℕ := 1

/-- Benchmark: `d = 2` truncated FPC scores. -/
def benchmark_d : ℕ := 2

/-! ### Trivial probability space -/

/-- Benchmark probability space: the one-point space `Unit`. -/
def benchmark_Ω : Type := Unit

instance : MeasurableSpace benchmark_Ω := ⊤

/-- Benchmark measure: the Dirac mass at the unique element `()`. -/
noncomputable def benchmark_μ : MeasureTheory.Measure benchmark_Ω :=
  MeasureTheory.Measure.dirac ()

instance : IsProbabilityMeasure benchmark_μ := by
  unfold benchmark_μ
  infer_instance

/-! ### Trivial functional covariate domain -/

/-- Benchmark functional covariate domain: the one-point set `Fin 1`. -/
def benchmark_D : Type := Fin 1

instance : MeasurableSpace benchmark_D := ⊤

/-- Benchmark base measure on `D`: the counting measure. -/
noncomputable def benchmark_ν : MeasureTheory.Measure benchmark_D :=
  MeasureTheory.Measure.count

/-! ### Concrete Cox parameter -/

/-- Benchmark true parameter: `γ = α = β = 0` and `η = 0`.
    This is the global null model: every coefficient and the change-point are
    zero. -/
def benchmark_θ₀ : Statlean.CoxChangePoint.CoxParam benchmark_p benchmark_d :=
  { γ := fun _ => 0
    α := fun _ => 0
    β := fun _ => 0
    η := 0 }

/-! ### Concrete observation -/

/-- Benchmark single observation: `T = 1`, event observed (`δ = true`),
    `Z₁ = 0`, `Z₂ = 0`, `ξ = 0`. -/
def benchmark_obs : Statlean.CoxChangePoint.CoxObs benchmark_p benchmark_d :=
  { T := 1
    δ := true
    Z₁ := fun _ => 0
    Z₂ := 0
    ξ := fun _ => 0 }

/-! ### Concrete sample -/

/-- Benchmark sample: every subject (at every sample size, every `ω`)
    receives the same `benchmark_obs`. -/
def benchmark_sample :
    Statlean.CoxChangePoint.Sample benchmark_Ω benchmark_p benchmark_d :=
  fun _ _ _ => benchmark_obs

/-! ### Concrete eigensystem -/

/-- Benchmark eigensystem: every eigenvalue is `0` and every eigenfunction is
    the constant `0`.  Trivially measurable since `benchmark_D` carries the
    discrete σ-algebra. -/
noncomputable def benchmark_eigsys :
    Statlean.CoxChangePoint.FPC.Eigensystem benchmark_D :=
  { lam := fun _ => 0
    phi := fun _ _ => 0
    lam_nonneg := fun _ => le_refl 0
    phi_meas := fun _ => measurable_const }

/-! ### Concrete CoxModel -/

/-- The benchmark `CoxModel`.  Every per-subject random datum is constant
    (`T = 1`, `δ = true`, `Z₁ = 0`, `Z₂ = 0`, `X = 0`), the eigensystem is
    zero, the estimator coincides with the truth, and `G ≡ 0`. -/
noncomputable def benchmark_model :
    Statlean.CoxChangePoint.CoxModel
      benchmark_Ω benchmark_μ benchmark_D benchmark_ν
      benchmark_p benchmark_d :=
  { θ₀ := benchmark_θ₀
    Θ_set := Set.univ
    hΘ_compact := trivial
    hΘ_convex := trivial
    hθ₀_mem := Set.mem_univ _
    T := fun _ _ _ => 1
    δ := fun _ _ _ => true
    Z₁ := fun _ _ _ _ => 0
    Z₂ := fun _ _ _ => 0
    X := fun _ _ _ _ => 0
    eigsys := benchmark_eigsys
    θ_hat := fun _ _ => benchmark_θ₀
    G := fun _ _ => 0
    hG_concave := trivial }

/-! ### Smoke-test theorems

The two theorems below show that the benchmark instantiation type-checks and
that the consistency statement collapses to a trivial tautology in the null
model. -/

/-- The benchmark estimator is identically the true parameter. -/
theorem benchmark_θ_hat_eq_θ₀ (n : ℕ) (ω : benchmark_Ω) :
    benchmark_model.θ_hat n ω = benchmark_θ₀ := rfl

/-- **Trivial consistency.**

For *any* `PseudoMetricSpace` instance on `CoxParam benchmark_p benchmark_d`,
the benchmark estimator converges in probability to `θ₀`, because
`dist (θ̂_n ω) θ₀ ≡ 0`.

This is a direct unit-test demonstration that the *form* of the consistency
conclusion delivered by `cox_consistency_end_to_end` is sensible: in the
trivial null model where the estimator equals the truth, the conclusion
becomes `0 →ᵖ 0`. -/
theorem benchmark_consistency_trivially_true
    (Θ_metric : PseudoMetricSpace
      (Statlean.CoxChangePoint.CoxParam benchmark_p benchmark_d)) :
    ∀ ε > 0, Filter.Tendsto
      (fun n => benchmark_μ {ω | ε < @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀})
      Filter.atTop (nhds 0) := by
  intro ε hε
  -- The estimator equals the truth, so the inner distance is 0.
  have h_zero : ∀ (n : ℕ) (ω : benchmark_Ω),
      @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀ = 0 := by
    intro n ω
    -- `θ_hat n ω = θ₀ = benchmark_θ₀`, and `benchmark_model.θ₀ = benchmark_θ₀`.
    rw [benchmark_θ_hat_eq_θ₀]
    -- Both sides are now `benchmark_θ₀`.
    exact dist_self _
  -- The set `{ω | ε < 0}` is empty.
  have h_set : ∀ n,
      {ω : benchmark_Ω | ε < @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀} = ∅ := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt,
      h_zero n ω]
    exact hε.le
  -- Hence the measure is constantly 0, which trivially tends to 0.
  simp only [h_set, measure_empty]
  exact tendsto_const_nhds

/-- **Even more directly:** the benchmark estimator converges in probability to
`θ₀` in the sense of `ProbabilityTheory.ConvergesInProbability`, when the
distance is read as a real number on either side via any chosen
`PseudoMetricSpace` on `CoxParam`. -/
theorem benchmark_convergesInProbability
    (Θ_metric : PseudoMetricSpace
      (Statlean.CoxChangePoint.CoxParam benchmark_p benchmark_d)) :
    ProbabilityTheory.ConvergesInProbability benchmark_μ
      (fun n ω => @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀) 0 := by
  intro ε hε
  -- The inner real value is 0, so `|0 - 0| = 0 < ε` is false.
  have h_zero : ∀ (n : ℕ) (ω : benchmark_Ω),
      @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀ = 0 := by
    intro n ω
    rw [benchmark_θ_hat_eq_θ₀]
    exact dist_self _
  have h_set : ∀ n,
      {ω : benchmark_Ω | ε < |(fun n ω => @dist _ Θ_metric.toDist
        (benchmark_model.θ_hat n ω) benchmark_model.θ₀) n ω - 0|} = ∅ := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt,
      h_zero n ω, sub_zero, abs_zero]
    exact hε.le
  simp only [h_set, measure_empty]
  exact tendsto_const_nhds

/-! ## Hooking up to the end-to-end theorems

The three end-to-end results live in `CoxConsistencyEndToEnd.lean`:

* `cox_consistency_end_to_end` (Theorem 1 — `θ̂_n →ᵖ θ₀`),
* `CoxBaselineHypotheses.rate` / `cox_theorem_2_end_to_end`
  (Theorem 2 — `dist(θ̂_n, θ₀) = O_P(δ_n)`),
* `CoxBaselineHypotheses.asymDist` / `cox_theorem_3_end_to_end`
  (Theorem 3 — `(δ_n)⁻¹ · (θ̂_n − θ₀) ⇒ target` weakly).

In a *non-trivial* instantiation one would have to:

1. **Endow** `CoxParam p d` with a normed-space / pseudo-metric structure
   (e.g. the obvious product Euclidean metric on
   `(Fin p → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) × ℝ`).
2. **Discharge** `hΘ_compact`, `hΘ_convex`, `hG_cont`,
   `hG_strictConcave`, `hG_max` for the chosen population objective.
3. **Discharge** `hMLE`, i.e. provide an actual maximum-likelihood
   estimator and prove it satisfies `IsCoxMLE`.
4. **Discharge** the chaining hypothesis (`VW_2_14_9_Conclusion` together
   with `hDom`) on the sub-Gaussian sup-norm deviation `supNormDiff`.

For the present *benchmark* (trivial null model) all of these are
vacuously satisfied — but the benchmark is not intended as a substantive
application of the end-to-end theorems; it is a smoke-test that the data
record `CoxModel` accepts concrete inputs and that the consistency
conclusion makes sense in the simplest possible case. -/

end Benchmark
end Statlean.CoxChangePoint

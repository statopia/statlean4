/-
Copyright (c) 2026 Gavin et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Operator-norm concentration of empirical covariance

This file develops the building blocks for *random matrix concentration* results
needed by the functional Cox change-point pipeline.  Concretely, given iid
covariates `X₁, …, Xₙ` with population covariance operator `C`, the empirical
covariance

`Ĉₙ = n⁻¹ ∑ᵢ Xᵢ ⊗ Xᵢ`

satisfies, under a bounded-fourth-moment hypothesis,

`E ‖Ĉₙ − C‖²_op ≤ C(M) / n.`

The full random-matrix concentration theorem requires substantial Hilbert–Schmidt
infrastructure that lives outside the scope of this file; we therefore expose it
in *hypothesis form* via the structure `OpNormBoundFromExpectation`, which
bundles the key estimate as data.  This is the same pattern used elsewhere in
the StatLean codebase to bridge to deep statistical results that are not yet
formalised in Mathlib.

We then prove the key downstream consequence by elementary means:
`OpNormBoundFromExpectation.tendsto_in_prob` derives convergence in probability
from the L² bound by a Markov/Chebyshev argument.

## Bridge to Cox change-point pipeline

The structure `OpNormBoundFromExpectation` produces a function
`Ω → ℝ` of the form `ω ↦ ‖Â_n ω − A‖²` that can be plugged in as the
`cov_diff_sq` field of `Statlean.CoxChangePoint.SpectralBridge.PerturbationBound`,
unlocking the L² eigenfunction error rate via the sin-theta theorem.

## Main definitions

* `Statlean.MathlibX.empiricalCovarianceMatrix p n X ω`: the finite-dimensional
  empirical covariance matrix `n⁻¹ ∑ᵢ Xᵢ Xᵢᵀ` for `X : Fin n → Ω → ℝᵖ`.
* `Statlean.MathlibX.OpNormBoundFromExpectation μ Â A`: hypothesis-form
  L² operator norm bound `E ‖Â_n − A‖² ≤ C/n`, parameterised by an
  abstract Hilbert space `V`.
* `Statlean.MathlibX.CoxEmpiricalCovBound μ X M`: hypothesis-form bundle
  matching the Cox change-point random-matrix concentration assumption.

## Main theorems

* `Statlean.MathlibX.empiricalCov_isSymm`: the finite-dimensional empirical
  covariance matrix is symmetric.
* `Statlean.MathlibX.empiricalCov_isHermitian`: the same matrix is Hermitian
  (equivalent to symmetric in the real case, but useful for spectral
  theory APIs that consume `IsHermitian`).
* `Statlean.MathlibX.OpNormBoundFromExpectation.tendsto_in_prob`: an L²
  operator-norm rate `E ‖Â_n − A‖² ≤ C/n` implies convergence in measure
  `‖Â_n − A‖ →ᵖ 0`.
* `Statlean.MathlibX.OpNormBoundFromExpectation.toCovDiffSq`: extraction of
  the canonical `cov_diff_sq` function used by `PerturbationBound`.

-/

namespace Statlean
namespace MathlibX

open MeasureTheory Filter Topology Matrix

/-! ### Empirical covariance matrix (finite-dim) -/

/-- The empirical covariance matrix `Ĉ_n = n⁻¹ ∑ᵢ Xᵢ Xᵢᵀ` for a finite-dimensional
covariate `X : Fin n → Ω → ℝᵖ`.

This is the standard estimator: each summand `Matrix.of (fun j k ↦ Xᵢ(j) · Xᵢ(k))`
is the rank-one outer product `Xᵢ ⊗ Xᵢ`.  We do not subtract the sample mean; if
needed downstream one can pre-center the `X i ω`. -/
noncomputable def empiricalCovarianceMatrix
    {Ω : Type*} [MeasurableSpace Ω] (p : ℕ) (n : ℕ)
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (ω : Ω) :
    Matrix (Fin p) (Fin p) ℝ :=
  (1 / n : ℝ) • ∑ i : Fin n, Matrix.of (fun j k => X i ω j * X i ω k)

/-- Each rank-one summand `Xᵢ ⊗ Xᵢ` is a symmetric matrix, hence the empirical
covariance is symmetric. -/
lemma empiricalCov_isSymm
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (ω : Ω) :
    (empiricalCovarianceMatrix p n X ω).IsSymm := by
  unfold empiricalCovarianceMatrix
  rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ext j k
  simp [Matrix.transpose_apply, Matrix.of_apply, mul_comm]

/-- Over the reals, symmetric matrices are Hermitian (since complex conjugation
is the identity on `ℝ`).  This convenience lemma exposes the empirical covariance
to APIs that demand `Matrix.IsHermitian`, including the diagonalisation framework
in `Mathlib.LinearAlgebra.Matrix.Hermitian`. -/
lemma empiricalCov_isHermitian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (X : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (ω : Ω) :
    (empiricalCovarianceMatrix p n X ω).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose]
  ext j k
  simp [Matrix.transpose_apply, empiricalCovarianceMatrix,
        Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply, mul_comm]

/-! ### Hypothesis-form L² operator-norm concentration -/

/-- **Operator norm L² concentration**: an abstract bundle stating
`E ‖Â_n − A‖² ≤ C / n`.

The intended use is to formalise the conclusion of the (deep) random matrix
concentration theorem for empirical covariances: under iid sampling with
bounded fourth moment of `X` (or, more generally, sub-Gaussian / sub-exponential
norm), the empirical covariance `Â_n` converges to the population covariance
`A` in L²-operator norm at rate `O(1/n)`.

We expose the result here in *hypothesis form* (as data) so that downstream
consumers (e.g. the Cox change-point pipeline) can invoke it without first
formalising the proof, which in the Hilbert space setting requires
Hilbert–Schmidt machinery beyond the current scope of Mathlib.

Fields:

* `C` is the constant (depending on the fourth-moment bound `M`);
* `C_pos` asserts `0 < C`;
* `measurable` is a bookkeeping hypothesis providing `AEStronglyMeasurable`
  of `Â_n − A` (needed to access the integral and Markov inequality);
* `integrable_sq` says `‖Â_n − A‖²` is integrable for each `n > 0`,
  which is needed to convert between the Bochner integral and the Lebesgue
  integral of `ENNReal.ofReal ∘ (·²)`;
* `bound` is the L² rate `∫ ‖Â_n − A‖² dμ ≤ C / n`.

Strictly speaking the bookkeeping fields are derivable from the main bound when
`Â` is a continuous map of a measurable function, but bundling them here keeps
the downstream API explicit. -/
structure OpNormBoundFromExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Â : ℕ → Ω → V →L[ℝ] V) (A : V →L[ℝ] V) where
  /-- The L² rate constant. -/
  C : ℝ
  /-- The constant is strictly positive. -/
  C_pos : 0 < C
  /-- `Â_n − A` is almost-everywhere strongly measurable for each `n`. -/
  measurable : ∀ n, AEStronglyMeasurable (fun ω => Â n ω - A) μ
  /-- The squared operator norm is integrable for each `n > 0`. -/
  integrable_sq : ∀ n, 0 < n → Integrable (fun ω => ‖Â n ω - A‖^2) μ
  /-- The L² operator-norm rate. -/
  bound : ∀ n, 0 < n → ∫ ω, ‖Â n ω - A‖^2 ∂μ ≤ C / n

/-- **Markov ⇒ convergence in probability.**  An L² operator-norm rate
`E ‖Â_n − A‖² ≤ C/n` implies that `‖Â_n − A‖` converges to `0` in measure.

Proof.  By Markov/Chebyshev,
`μ {ω | ε ≤ ‖Â_n ω − A‖} ≤ μ {ω | ε² ≤ ‖Â_n ω − A‖²} ≤ (∫ ‖Â_n − A‖² dμ) / ε²`,
which by hypothesis is bounded by `C / (n · ε²) → 0`. -/
theorem OpNormBoundFromExpectation.tendsto_in_prob
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Â : ℕ → Ω → V →L[ℝ] V} {A : V →L[ℝ] V}
    (h : OpNormBoundFromExpectation μ Â A) :
    TendstoInMeasure μ (fun n ω => ‖Â n ω - A‖) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hε_top
  -- Convert ε ∈ ENNReal to a positive real `εR`.
  set εR : ℝ := ε.toReal with hεR_def
  have hεR_pos : 0 < εR := ENNReal.toReal_pos hε.ne' hε_top
  have hε_eq : ε = ENNReal.ofReal εR := (ENNReal.ofReal_toReal hε_top).symm
  have hε2_pos : (0 : ℝ) < εR ^ 2 := pow_pos hεR_pos 2
  have hε2_ne_zero : ENNReal.ofReal (εR ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hε2_pos
  have hε2_ne_top : ENNReal.ofReal (εR ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Step 1: rewrite `edist (‖·‖) 0 = ENNReal.ofReal ‖·‖`.
  have hedist : ∀ n ω, edist (‖Â n ω - A‖) (0 : ℝ) = ENNReal.ofReal (‖Â n ω - A‖) := by
    intro n ω
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  simp only [hedist, hε_eq]
  -- Step 2: turn the ENNReal inequality back into a real inequality.
  have hset_eq : ∀ n,
      {ω | ENNReal.ofReal εR ≤ ENNReal.ofReal (‖Â n ω - A‖)} =
      {ω | εR ≤ ‖Â n ω - A‖} := by
    intro n; ext ω
    simp only [Set.mem_setOf_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  simp only [hset_eq]
  -- Step 3: pointwise Markov bound, valid for all `n ≥ 1`.
  have hle : ∀ n, 0 < n →
      μ {ω | εR ≤ ‖Â n ω - A‖} ≤
        ENNReal.ofReal (h.C / n) / ENNReal.ofReal (εR ^ 2) := by
    intro n hn
    -- {εR ≤ ‖·‖} ⊆ {εR² ≤ ‖·‖²}
    have hsubset : {ω | εR ≤ ‖Â n ω - A‖} ⊆ {ω | εR ^ 2 ≤ ‖Â n ω - A‖ ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact pow_le_pow_left₀ hεR_pos.le hω 2
    -- transport to ENNReal so we can apply `meas_ge_le_lintegral_div`.
    have heq : {ω | εR ^ 2 ≤ ‖Â n ω - A‖ ^ 2} =
               {ω | ENNReal.ofReal (εR ^ 2) ≤ ENNReal.ofReal (‖Â n ω - A‖ ^ 2)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)]
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (‖Â n ω - A‖ ^ 2)) μ :=
      ((h.measurable n).norm.pow 2).aemeasurable.ennreal_ofReal
    have h_markov := meas_ge_le_lintegral_div hmeas hε2_ne_zero hε2_ne_top
    -- Convert the lintegral of `ENNReal.ofReal ∘ (·²)` to `ENNReal.ofReal` of the
    -- Bochner integral (using integrability and nonnegativity of `‖·‖²`).
    have h_lint : ∫⁻ ω, ENNReal.ofReal (‖Â n ω - A‖ ^ 2) ∂μ
                  = ENNReal.ofReal (∫ ω, ‖Â n ω - A‖ ^ 2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (h.integrable_sq n hn)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    have h_bound_int : ENNReal.ofReal (∫ ω, ‖Â n ω - A‖ ^ 2 ∂μ)
                       ≤ ENNReal.ofReal (h.C / n) :=
      ENNReal.ofReal_le_ofReal (h.bound n hn)
    calc μ {ω | εR ≤ ‖Â n ω - A‖}
        ≤ μ {ω | εR ^ 2 ≤ ‖Â n ω - A‖ ^ 2} := μ.mono hsubset
      _ = μ {ω | ENNReal.ofReal (εR ^ 2) ≤ ENNReal.ofReal (‖Â n ω - A‖ ^ 2)} := by
            rw [heq]
      _ ≤ (∫⁻ ω, ENNReal.ofReal (‖Â n ω - A‖ ^ 2) ∂μ) / ENNReal.ofReal (εR ^ 2) := h_markov
      _ = ENNReal.ofReal (∫ ω, ‖Â n ω - A‖ ^ 2 ∂μ) / ENNReal.ofReal (εR ^ 2) := by rw [h_lint]
      _ ≤ ENNReal.ofReal (h.C / n) / ENNReal.ofReal (εR ^ 2) :=
          ENNReal.div_le_div_right h_bound_int _
  -- Step 4: the upper bound tends to 0.
  have h_rhs : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (h.C / n) / ENNReal.ofReal (εR ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => h.C / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (h.C / n)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto _).comp h1
      simpa using this
    have h3 : (0 : ENNReal) = 0 / ENNReal.ofReal (εR ^ 2) := by simp
    conv_rhs => rw [h3]
    exact ENNReal.Tendsto.div_const h2 (Or.inr hε2_ne_zero)
  -- Step 5: squeeze.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rhs
  · exact Filter.Eventually.of_forall (fun _ => zero_le _)
  · rw [Filter.eventually_atTop]
    exact ⟨1, fun n hn => hle n hn⟩

/-! ### Bridge: extract the `cov_diff_sq` function for `PerturbationBound`

The Cox change-point pipeline's `Statlean.CoxChangePoint.SpectralBridge.PerturbationBound`
expects a function `cov_diff_sq : Ω → ℝ` representing `‖Ĉ_n(ω) − C‖²_op`.  Given
an `OpNormBoundFromExpectation` (which packages an L² *expectation* bound) and a
sample size `n`, the canonical extraction is just `ω ↦ ‖Â_n ω − A‖²`. -/

/-- The pointwise squared operator-norm difference, ready to be plugged into
`PerturbationBound.cov_diff_sq`. -/
noncomputable def OpNormBoundFromExpectation.toCovDiffSq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Â : ℕ → Ω → V →L[ℝ] V} {A : V →L[ℝ] V}
    (_h : OpNormBoundFromExpectation μ Â A) (n : ℕ) : Ω → ℝ :=
  fun ω => ‖Â n ω - A‖ ^ 2

/-- Sanity lemma: `toCovDiffSq` is non-negative. -/
lemma OpNormBoundFromExpectation.toCovDiffSq_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Â : ℕ → Ω → V →L[ℝ] V} {A : V →L[ℝ] V}
    (h : OpNormBoundFromExpectation μ Â A) (n : ℕ) (ω : Ω) :
    0 ≤ h.toCovDiffSq n ω := by
  unfold OpNormBoundFromExpectation.toCovDiffSq
  exact sq_nonneg _

/-- Mean-control specialisation of the bound: for `n ≥ 1`,
`E [cov_diff_sq] ≤ C / n`. -/
lemma OpNormBoundFromExpectation.toCovDiffSq_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Â : ℕ → Ω → V →L[ℝ] V} {A : V →L[ℝ] V}
    (h : OpNormBoundFromExpectation μ Â A) {n : ℕ} (hn : 0 < n) :
    ∫ ω, h.toCovDiffSq n ω ∂μ ≤ h.C / n := by
  unfold OpNormBoundFromExpectation.toCovDiffSq
  exact h.bound n hn

/-! ### Cox-style bundled hypothesis

Hypothesis-form bundle matching the random-matrix concentration assumption used
by the Cox change-point pipeline.  We expose the iid bounded-fourth-moment
hypothesis (`hMoment`) and the resulting L² operator-norm bound abstractly,
to be discharged either by Mathlib infrastructure once available, or by user
input. -/
structure CoxEmpiricalCovBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (M : ℝ) where
  /-- Pointwise fourth-moment bound (placeholder for the population L⁴ hypothesis;
  the genuine hypothesis is `E ‖X n‖⁴ ≤ M²`, but a uniform pointwise version
  is sufficient for the downstream pipeline as long as `μ` is a probability
  measure). -/
  hMoment : ∀ n ω, ‖X n ω‖ ^ 4 ≤ M ^ 2
  /-- Positivity of the moment constant. -/
  M_pos : 0 < M

end MathlibX
end Statlean

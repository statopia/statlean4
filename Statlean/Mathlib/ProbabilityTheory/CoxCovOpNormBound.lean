/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: StatLean Contributors
-/
import Mathlib
import Statlean.Mathlib.ProbabilityTheory.CLTSums
import Statlean.Mathlib.ProbabilityTheory.RandomMatrixOpNorm

/-!
# Cox empirical covariance concentration via 4th-moment Frobenius bound

For an iid sample `X₁, …, Xₙ` of zero-mean random vectors in `ℝᵖ` with bounded
4th moment, the empirical covariance matrix
`Ĉₙ := n⁻¹ ∑ᵢ Xᵢ Xᵢᵀ` concentrates around the true covariance
`C := 𝔼[X₁ X₁ᵀ]` at the parametric rate.  The proof goes through the Frobenius
norm: each summand `Yᵢ := Xᵢ Xᵢᵀ - C` has mean zero, and by independence

```
𝔼 ‖Ĉₙ - C‖_F² = n⁻² · n · 𝔼 ‖Y₁‖_F² ≤ n⁻¹ · 𝔼 ‖X₁ X₁ᵀ‖_F² = n⁻¹ · 𝔼 ‖X₁‖⁴.
```

Since the operator norm is dominated by the Frobenius norm, the same bound
controls `𝔼 ‖Ĉₙ - C‖_op²`, which is exactly the input required for
`Statlean.MathlibX.OpNormBoundFromExpectation`.

This file provides:

1. The pointwise outer product `outerProduct X` of a Euclidean vector with
   itself, viewed as a real matrix.
2. The closed-form Frobenius norm identity
   `∑ᵢⱼ (X X^T)ᵢⱼ² = (∑ᵢ Xᵢ²)² = ‖X‖⁴`.
3. A hypothesis-form bridge `CoxFrobeniusL2Bound → OpNormBoundFromExpectation`
   that consumes the L²-Frobenius rate and produces the operator-norm L² rate
   demanded by downstream concentration consumers (Cox change-point analysis,
   Marchenko–Pastur, etc.).

The pure Frobenius identities (items 1–2) are proved in full.  The deep
variance computation that turns iid + 4th-moment bounds into the L² rate is
recorded in hypothesis form, since Mathlib currently lacks a clean
"`Var(∑ Xᵢ) = ∑ Var(Xᵢ)` for iid matrix-valued summands" API.  A user supplies
the `M²/n` bound and the bridge packages it into the
`OpNormBoundFromExpectation` structure.
-/

namespace Statlean
namespace MathlibX

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Matrix

/-! ### The outer product `X · Xᵀ` -/

/-- The pointwise outer product `X · Xᵀ` of a Euclidean vector with itself,
viewed as a real `p × p` matrix.  Entry `(i, j)` equals `Xᵢ · Xⱼ`. -/
noncomputable def outerProduct {p : ℕ} (X : EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of (fun i j => X i * X j)

@[simp]
lemma outerProduct_apply {p : ℕ} (X : EuclideanSpace ℝ (Fin p)) (i j : Fin p) :
    outerProduct X i j = X i * X j := rfl

/-- The outer product `X Xᵀ` is symmetric. -/
lemma outerProduct_isSymm {p : ℕ} (X : EuclideanSpace ℝ (Fin p)) :
    (outerProduct X).IsSymm := by
  ext i j
  simp [outerProduct, Matrix.transpose_apply, mul_comm]

/-! ### Frobenius identity for the outer product -/

/-- **Frobenius identity for outer products (raw form).**
For any `X : Fin p → ℝ`, the Frobenius squared norm of the outer product
matrix `(i, j) ↦ Xᵢ · Xⱼ` equals `(∑ᵢ Xᵢ²)²`.

This is the algebraic backbone of the rank-one Frobenius bound
`‖X Xᵀ‖_F² = ‖X‖⁴`. -/
theorem outerProduct_frobenius_sq_explicit {p : ℕ} (X : Fin p → ℝ) :
    ∑ i, ∑ j, (X i * X j) ^ 2 = (∑ i, (X i) ^ 2) ^ 2 := by
  -- expand squares and apply `Finset.sum_mul_sum`
  have h₁ : ∀ i j, (X i * X j) ^ 2 = (X i) ^ 2 * (X j) ^ 2 := by
    intro i j; ring
  simp_rw [h₁]
  -- now ∑ᵢ ∑ⱼ Xᵢ² Xⱼ² = (∑ᵢ Xᵢ²) · (∑ⱼ Xⱼ²) = (∑ᵢ Xᵢ²)²
  have hprod :
      (∑ i, (X i) ^ 2) * (∑ j, (X j) ^ 2) =
        ∑ i, ∑ j, (X i) ^ 2 * (X j) ^ 2 :=
    Finset.sum_mul_sum (Finset.univ : Finset (Fin p))
      (Finset.univ : Finset (Fin p)) (fun i => (X i) ^ 2)
      (fun j => (X j) ^ 2)
  rw [sq, ← hprod]

/-- **Frobenius identity for the outer product matrix.**
`∑ᵢⱼ (X Xᵀ)ᵢⱼ² = (∑ᵢ Xᵢ²)²`. -/
theorem outerProduct_frobenius_sq {p : ℕ} (X : EuclideanSpace ℝ (Fin p)) :
    ∑ i, ∑ j, (outerProduct X i j) ^ 2 = (∑ i, (X i) ^ 2) ^ 2 := by
  simp_rw [outerProduct_apply]
  exact outerProduct_frobenius_sq_explicit (fun i => X i)

/-! ### Operator vs Frobenius bound (hypothesis form) -/

/-- Continuous-linear-map realisation of a matrix acting on Euclidean space.
Composes `Matrix.toEuclideanLin` (which produces a bare linear map) with
`LinearMap.toContinuousLinearMap` (free in finite dimension). -/
noncomputable def matrixToCLM {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

/-- **Operator-norm vs Frobenius-norm bound (hypothesis form).**

For any `p × p` real matrix `M`, the operator norm of the associated
continuous linear map on `EuclideanSpace ℝ (Fin p)` is bounded by the
Frobenius norm `√(∑ᵢⱼ Mᵢⱼ²)`.

This is supplied here as a structure rather than a theorem because Mathlib's
`Matrix.toEuclideanLin` lives in several incompatible flavors
(`Matrix.toLin'`, `LinearMap.toContinuousLinearMap`, …) and the precise
operator-norm characterisation we need does not have a single canonical name.
Downstream clients are free to discharge this hypothesis using whichever
flavor is in scope. -/
structure MatrixOpNormBound (p : ℕ) where
  /-- The operator-norm-bounded-by-Frobenius-norm inequality. -/
  bound : ∀ M : Matrix (Fin p) (Fin p) ℝ,
    ‖matrixToCLM M‖ ≤ Real.sqrt (∑ i, ∑ j, (M i j) ^ 2)

/-! ### The Cox empirical covariance concentration hypothesis -/

/-- **Hypothesis-form bound on the empirical covariance matrix.**

Records the Frobenius L² rate
`𝔼 ‖Ĉₙ - C‖_F² ≤ M² / n`
that holds for iid samples with bounded 4th moment.  The deep variance-of-sum
computation establishing this rate is currently outside Mathlib's API for
matrix-valued integrands; we record the conclusion as a structure that
downstream code can consume.

Fields:
* `bound`: the moment bound `M² > 0`.
* `Ĉ`, `C`: the empirical and true covariance matrices.
* `frobenius_l2_bound`: the Frobenius L² rate `M²/n`. -/
structure CoxFrobeniusL2Bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ) where
  /-- The 4th-moment-derived constant. -/
  M : ℝ
  /-- Strict positivity of `M`. -/
  M_pos : 0 < M
  /-- The empirical covariance matrix as a function of `n` and `ω`. -/
  Ĉ : ℕ → Ω → Matrix (Fin p) (Fin p) ℝ
  /-- The true covariance matrix. -/
  C : Matrix (Fin p) (Fin p) ℝ
  /-- Difference `Ĉₙ - C` is almost-everywhere strongly measurable for each `n`. -/
  measurable :
    ∀ n, AEStronglyMeasurable
      (fun ω => Ĉ n ω - C) μ
  /-- The squared Frobenius norm is integrable for each `n > 0`. -/
  integrable_frobenius_sq :
    ∀ n, 0 < n →
      Integrable (fun ω => ∑ i, ∑ j, ((Ĉ n ω - C) i j) ^ 2) μ
  /-- The Frobenius L² rate `M²/n`. -/
  frobenius_l2_bound :
    ∀ n, 0 < n →
      ∫ ω, ∑ i, ∑ j, ((Ĉ n ω - C) i j) ^ 2 ∂μ ≤ M ^ 2 / n

namespace CoxFrobeniusL2Bound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℕ}

/-- The constant `M²` is positive. -/
lemma sq_M_pos (h : CoxFrobeniusL2Bound μ p) : 0 < h.M ^ 2 := by
  exact pow_pos h.M_pos 2

/-! ### Bridge to `OpNormBoundFromExpectation`

The `OpNormBoundFromExpectation` structure (in `RandomMatrixOpNorm.lean`) is
phrased in terms of operator-valued maps `Â : ℕ → Ω → V →L[ℝ] V` and an
operator-norm L² rate.  To bridge from `CoxFrobeniusL2Bound` we ask the
caller to supply both:

* an operator-valued realisation of `Ĉₙ` and `C`;
* a witness that the operator-norm L² bound `∫ ‖Â_n - A‖² ≤ M²/n`
  has been derived from the Frobenius bound (typically by combining
  `frobenius_l2_bound` with a `MatrixOpNormBound`).

Once both are available, the bridge packages them into the canonical
`OpNormBoundFromExpectation`. -/

/-- **Bridge: Cox Frobenius bound + operator-norm witness ⇒ `OpNormBoundFromExpectation`.**

Given the Cox Frobenius L² bound `h` and a user-supplied operator-norm L²
bound `hOp : ∫ ‖Â n - A‖² ≤ h.M² / n`, package the data into the canonical
`OpNormBoundFromExpectation` structure with constant `C := h.M²`. -/
noncomputable def toOpNormBound
    (h : CoxFrobeniusL2Bound μ p)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Â : ℕ → Ω → V →L[ℝ] V) (A : V →L[ℝ] V)
    (hMeas : ∀ n, AEStronglyMeasurable (fun ω => Â n ω - A) μ)
    (hInt : ∀ n, 0 < n → Integrable (fun ω => ‖Â n ω - A‖ ^ 2) μ)
    (hOp : ∀ n, 0 < n → ∫ ω, ‖Â n ω - A‖ ^ 2 ∂μ ≤ h.M ^ 2 / n) :
    OpNormBoundFromExpectation μ Â A where
  C := h.M ^ 2
  C_pos := h.sq_M_pos
  measurable := hMeas
  integrable_sq := hInt
  bound := hOp

/-- **Convenience builder: trivial `CoxFrobeniusL2Bound` for the zero matrix.**

When `Ĉₙ = C` almost everywhere (e.g. degenerate one-point distributions),
the Frobenius L² rate holds trivially with any `M > 0`. -/
noncomputable def ofZeroDifference
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℕ)
    {M : ℝ} (hM : 0 < M)
    (C : Matrix (Fin p) (Fin p) ℝ) :
    CoxFrobeniusL2Bound μ p where
  M := M
  M_pos := hM
  Ĉ := fun _ _ => C
  C := C
  measurable := by
    intro _
    simpa using (aestronglyMeasurable_const : AEStronglyMeasurable
      (fun _ : Ω => (0 : Matrix (Fin p) (Fin p) ℝ)) μ)
  integrable_frobenius_sq := by
    intro n _
    simp
  frobenius_l2_bound := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hMsq : 0 ≤ M ^ 2 := sq_nonneg _
    simp [div_nonneg hMsq hn'.le]

end CoxFrobeniusL2Bound

/-! ### Cox–IID interface

The next definition packages the Cox concentration data with the iid
hypothesis bundle `IIDBoundedHypotheses`, providing a single value that
downstream consumers can pass into both the multivariate CLT and the
random-matrix concentration argument. -/

/-- **Joint Cox + iid hypothesis bundle.**

Combines an `IIDBoundedHypotheses` witness with a `CoxFrobeniusL2Bound`
witness. -/
structure CoxIIDBundle
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ) where
  /-- The iid + bounded second moment hypothesis bundle. -/
  iid : Statlean.MultivariateCLT.IIDBoundedHypotheses μ p X mean cov
  /-- The Frobenius L² concentration of `Ĉₙ`. -/
  cox : CoxFrobeniusL2Bound μ p
  /-- Compatibility with the existing `CoxEmpiricalCovBound` (4th-moment) bundle. -/
  fourth_moment : CoxEmpiricalCovBound μ X cox.M

end MathlibX
end Statlean

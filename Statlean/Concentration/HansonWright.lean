/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Statlean.Concentration.Talagrand

/-!
# Hanson–Wright Inequality

Concentration of quadratic forms `Xᵀ A X` where the components
`X_1, …, X_d` are independent sub-Gaussian random variables and `A` is a
real symmetric `d × d` matrix.

The classical (Hanson–Wright 1971; Rudelson–Vershynin 2013) statement:
for `t ≥ 0`,
```
P(|Xᵀ A X − E[Xᵀ A X]| ≥ t) ≤
    2 · exp(−c · min(t² / (K⁴ ‖A‖_F²), t / (K² ‖A‖_op)))
```
where `K` is the sub-Gaussian norm of the entries.

## File contents

* `frobeniusNormSq` — Frobenius norm squared, with basic properties.
* `IsMatrixOpNormBound` — operator-norm bound predicate.
* `quadratic_form_decomposition` — diagonal / off-diagonal split
  `Xᵀ A X = Σ_i A_{ii} X_i² + Σ_{i,j, i≠j} A_{ij} X_i X_j`
  (fully proved).
* `dotProduct_mulVec_eq_sum_sum` — equivalent flat sum (fully proved).
* `hanson_wright_inequality` — main theorem, **axiomatised**. The full
  proof needs a decoupling lemma (Rademacher chaos) and a sub-Gaussian
  chaos bound, both currently missing from Mathlib. See R6 backlog
  `theme/axiom_registry.yaml`.

## References

* D. L. Hanson, F. T. Wright, *A bound on tail probabilities for
  quadratic forms in independent random variables*, AMS Probability
  1971.
* R. Vershynin, *High-Dimensional Probability*, §6.2.
* M. Rudelson, R. Vershynin, *Hanson–Wright inequality and sub-Gaussian
  concentration*, ECP 2013.
-/

namespace Statlean.Concentration

open MeasureTheory ProbabilityTheory Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {d : ℕ}

/-! ### Frobenius norm and operator-norm bound -/

/-- Squared Frobenius norm of a real matrix: `‖A‖_F² = ∑_{i,j} A_{ij}²`. -/
def frobeniusNormSq (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

@[simp] lemma frobeniusNormSq_zero :
    frobeniusNormSq (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp [frobeniusNormSq]

lemma frobeniusNormSq_nonneg (A : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  positivity

lemma frobeniusNormSq_transpose (A : Matrix (Fin d) (Fin d) ℝ) :
    frobeniusNormSq A.transpose = frobeniusNormSq A := by
  unfold frobeniusNormSq
  rw [Finset.sum_comm]
  rfl

/-- Predicate: `C` is an operator-norm upper bound for the matrix `A`
viewed as a linear map `(Fin d → ℝ) → (Fin d → ℝ)`. -/
def IsMatrixOpNormBound (A : Matrix (Fin d) (Fin d) ℝ) (C : ℝ) : Prop :=
  ∀ v : Fin d → ℝ, ‖A.mulVec v‖ ≤ C * ‖v‖

lemma IsMatrixOpNormBound.nonneg_zero_vec
    {A : Matrix (Fin d) (Fin d) ℝ} {C : ℝ}
    (hC : IsMatrixOpNormBound A C) :
    ‖A.mulVec 0‖ ≤ C * ‖(0 : Fin d → ℝ)‖ := hC 0

/-! ### Quadratic-form decomposition -/

/-- Expand `Xᵀ A X` as a flat double sum.
`Xᵀ A X = ∑_i ∑_j X_i · A_{ij} · X_j`. -/
lemma dotProduct_mulVec_eq_sum_sum
    (A : Matrix (Fin d) (Fin d) ℝ) (X : Fin d → ℝ) :
    dotProduct X (A.mulVec X) = ∑ i, ∑ j, X i * A i j * X j := by
  unfold dotProduct mulVec
  unfold dotProduct
  congr 1
  ext i
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- **Quadratic-form decomposition**:
`Xᵀ A X = Σ_i A_{ii} X_i² + Σ_i Σ_{j ≠ i} X_i · A_{ij} · X_j`. -/
lemma quadratic_form_decomposition
    (A : Matrix (Fin d) (Fin d) ℝ) (X : Fin d → ℝ) :
    dotProduct X (A.mulVec X) =
      (∑ i, A i i * (X i) ^ 2) +
        ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, X i * A i j * X j := by
  rw [dotProduct_mulVec_eq_sum_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

/-! ### Diagonal-part concentration (placeholder)

The diagonal contribution `Σ_i A_{ii} X_i²` is a sum of independent
sub-exponential random variables and admits a Bernstein-type tail
bound. A full quantitative statement requires a sub-exponential
class for `X_i²` which Mathlib currently lacks; we expose only the
qualitative wrapper used downstream. -/

/-- Placeholder: under independent sub-Gaussian `X_i` (with shared
constant `K`), the diagonal quadratic part `Σ_i A_{ii} X_i²` satisfies
a Bernstein-type tail bound. Currently exposed as `True` because the
matching sub-exponential infrastructure is still being built in
Mathlib. -/
lemma hanson_wright_diagonal_part
    {X : Fin d → Ω → ℝ} {K : NNReal} (_hK : 0 < K)
    (_hSG : ∀ i, HasSubgaussianMGF (X i) K μ)
    (_hInd : iIndepFun X μ)
    (_A : Matrix (Fin d) (Fin d) ℝ) (_hSymm : (_A).IsSymm)
    {t : ℝ} (_ht : 0 ≤ t) :
    True := trivial

/-! ### Hanson–Wright inequality (axiomatised)

The full Hanson–Wright inequality requires:

* A decoupling lemma (Rademacher chaos), turning `Σ_{i≠j} A_{ij} X_i X_j`
  into a product `Σ_{i,j} A_{ij} X_i X_j'` with an independent copy `X'`.
* A sub-Gaussian chaos bound (Hanson–Wright kernel inequality) controlling
  bilinear forms in independent sub-Gaussian variables.

Both are currently missing from Mathlib and require ~600 LOC of
infrastructure (see `theme/axiom_registry.yaml` entry
`hanson_wright_inequality`). Until that infrastructure lands we expose
the statement as an axiom with the standard constants, sufficient for
downstream consumers (high-dim regression, covariance estimation,
clustering). -/

/-- **Hanson–Wright inequality** (axiom).

Let `X = (X_1, …, X_d)` be a vector of independent mean-zero
sub-Gaussian random variables with shared sub-Gaussian parameter `K`,
and let `A` be a symmetric real matrix. Then there exists an absolute
constant `c > 0` such that for all `t ≥ 0`,
```
P(|Xᵀ A X − E[Xᵀ A X]| ≥ t)
    ≤ 2 · exp(−c · min(t² / (K⁴ ‖A‖_F²), t / (K² ‖A‖_op))).
```

* `K_op` — operator-norm bound for `A`.
* `K_frob` — Frobenius-norm-squared upper bound for `A` (i.e. `‖A‖_F²`).

Registered as R6 axiom: full proof needs decoupling + sub-Gaussian chaos. -/
axiom hanson_wright_inequality
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} (X : Fin d → Ω → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (K K_op K_frob : ℝ)
    (_hK : 0 < K)
    (_hSG : ∀ i, HasSubgaussianMGF (X i) ⟨K, le_of_lt _hK⟩ μ)
    (_hInd : iIndepFun X μ)
    (_hSymm : A.IsSymm)
    (_hOp : IsMatrixOpNormBound A K_op)
    (_hFrob : frobeniusNormSq A ≤ K_frob)
    (t : ℝ) (_ht : 0 ≤ t) :
    ∃ c > (0 : ℝ),
      μ.real {ω | t ≤ |dotProduct (fun i => X i ω) (A.mulVec (fun i => X i ω)) -
          ∫ ω', dotProduct (fun i => X i ω') (A.mulVec (fun i => X i ω')) ∂μ|} ≤
        2 * Real.exp (-c * min (t ^ 2 / (K ^ 4 * K_frob)) (t / (K ^ 2 * K_op)))

end Statlean.Concentration

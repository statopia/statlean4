import Statlean.Regression.Lasso

/-!
# Multi-Task Lasso (Obozinski–Wainwright–Jordan 2011)

In multi-task linear regression we estimate `T` related response vectors
jointly:
```
  Y = X · B + Ξ,   X ∈ ℝ^{n×p}, Y ∈ ℝ^{n×T}, B ∈ ℝ^{p×T}.
```
The **Multi-task Lasso** imposes shared sparsity across tasks by
penalising the `ℓ_{2,1}` mixed norm of the row vectors of `B`:
```
  min_B  (1/(2n))‖Y - XB‖_F² + λ · ∑_j ‖B_j·‖₂.
```
Each row corresponds to a feature; the penalty drives entire rows
(i.e., feature columns of `B`) to zero simultaneously across tasks.

## Main definitions

* `rowL2Norm B j` — `√(∑_t B_{jt}²)`.
* `rowL21Norm B` — `∑_j ‖B_j·‖₂`.
* `multiTaskLassoLoss X Y lam B`.
* `IsMultiTaskLassoEstimator X Y lam B̂`.

## Main results

* `rowL2Norm_nonneg`, `rowL2Norm_zero_row`.
* `rowL21Norm_nonneg`, `rowL21Norm_zero`.
* `multiTaskLassoLoss_nonneg`.

## References

* G. Obozinski, M. J. Wainwright, M. I. Jordan, *Support union recovery
  in high-dimensional multivariate regression*, Ann. Statist. 39 (2011).
* A. Argyriou, T. Evgeniou, M. Pontil, *Convex multi-task feature
  learning*, Mach. Learn. 73 (2008).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p T : ℕ}

/-- The **row ℓ² norm**: `‖B_j·‖₂ := √(∑_t B_{jt}²)`. -/
noncomputable def rowL2Norm (B : Fin p → Fin T → ℝ) (j : Fin p) : ℝ :=
  Real.sqrt (∑ t, (B j t)^2)

lemma rowL2Norm_nonneg (B : Fin p → Fin T → ℝ) (j : Fin p) :
    0 ≤ rowL2Norm B j := Real.sqrt_nonneg _

@[simp] lemma rowL2Norm_zero_row (j : Fin p) :
    rowL2Norm (fun (_ : Fin p) (_ : Fin T) => (0 : ℝ)) j = 0 := by
  unfold rowL2Norm
  simp

/-- The **mixed `ℓ_{2,1}` row norm**: `∑_j ‖B_j·‖₂`. -/
noncomputable def rowL21Norm (B : Fin p → Fin T → ℝ) : ℝ :=
  ∑ j, rowL2Norm B j

lemma rowL21Norm_nonneg (B : Fin p → Fin T → ℝ) :
    0 ≤ rowL21Norm B := by
  unfold rowL21Norm
  exact Finset.sum_nonneg (fun j _ => rowL2Norm_nonneg B j)

@[simp] lemma rowL21Norm_zero :
    rowL21Norm (fun (_ : Fin p) (_ : Fin T) => (0 : ℝ)) = 0 := by
  unfold rowL21Norm
  simp

/-- The **multi-task Lasso objective**:
`(1/(2n))‖Y - XB‖_F² + λ · ∑_j ‖B_j·‖₂`. -/
noncomputable def multiTaskLassoLoss
    (X : Fin n → Fin p → ℝ) (Y : Fin n → Fin T → ℝ) (lam : ℝ)
    (B : Fin p → Fin T → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) *
    ∑ i, ∑ t, (Y i t - ∑ j, X i j * B j t)^2
    + lam * rowL21Norm B

/-- A matrix `Bh` is a **multi-task Lasso estimator** if it minimises
the multi-task objective. -/
def IsMultiTaskLassoEstimator
    (X : Fin n → Fin p → ℝ) (Y : Fin n → Fin T → ℝ) (lam : ℝ)
    (Bh : Fin p → Fin T → ℝ) : Prop :=
  ∀ B : Fin p → Fin T → ℝ,
    multiTaskLassoLoss X Y lam Bh ≤ multiTaskLassoLoss X Y lam B

/-- Multi-task Lasso loss is non-negative for `λ ≥ 0` and positive sample
size `n`. -/
lemma multiTaskLassoLoss_nonneg
    (X : Fin n → Fin p → ℝ) (Y : Fin n → Fin T → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (B : Fin p → Fin T → ℝ) (hn : 0 < (n : ℝ)) :
    0 ≤ multiTaskLassoLoss X Y lam B := by
  unfold multiTaskLassoLoss
  have h1 : 0 ≤ (1 / (2 * (n : ℝ))) *
              ∑ i, ∑ t, (Y i t - ∑ j, X i j * B j t)^2 := by
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro t _
      exact sq_nonneg _
  have h2 : 0 ≤ lam * rowL21Norm B := mul_nonneg hlam (rowL21Norm_nonneg _)
  linarith

end Statlean.Regression

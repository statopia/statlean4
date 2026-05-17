import Statlean.Regression.Lasso

/-!
# Fused Lasso (Tibshirani–Saunders–Rosset–Zhu–Knight 2005)

The Fused Lasso augments the standard Lasso with a **total-variation**
term to encourage both coordinate sparsity AND smoothness across
consecutive coordinates:
```
  min_β  (1/(2n)) ‖y - X β‖² + λ₁ ‖β‖₁ + λ₂ · TV(β),
  TV(β)  := ∑_{i = 0}^{p-2} |β_{i+1} - β_i|.
```
The fused penalty is useful whenever the coordinates of `β` represent
positions along an ordered axis (genomic loci, time-series knots,
image rows).  When `λ₂ = 0` the objective reduces to the ordinary
Lasso; when `λ₁ = 0` it becomes a one-dimensional total-variation
denoising problem.

## Main definitions

* `totalVariation β`            — the TV penalty on `Fin p → ℝ`.
* `fusedLassoLoss X y λ₁ λ₂ β`  — the fused-Lasso objective.
* `IsFusedLassoEstimator`       — the minimisation predicate.

## Main results

* `totalVariation_nonneg`                 — TV ≥ 0.
* `totalVariation_const`                  — TV vanishes on constant vectors.
* `totalVariation_smul`                   — `TV(c·β) = |c|·TV(β)`.
* `fusedLassoLoss_nonneg`                 — objective is non-negative.
* `fusedLassoLoss_eq_lasso_of_lam2_zero`  — degenerates to Lasso.

## References

* R. Tibshirani, M. Saunders, S. Rosset, J. Zhu, K. Knight,
  *Sparsity and smoothness via the fused Lasso*,
  JRSS B **67** (2005), 91–108.
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-! ### Total variation pseudonorm -/

/-- **Total variation** of a vector along `Fin p`: the sum of
consecutive absolute differences.  When `p ≤ 1` the index type
`Fin (p - 1)` is empty (`Nat` truncated subtraction), so the sum is
`0`. -/
def totalVariation {p : ℕ} (β : Fin p → ℝ) : ℝ :=
  ∑ i : Fin (p - 1),
    |β ⟨i.val + 1, by have := i.isLt; omega⟩ -
     β ⟨i.val,     by have := i.isLt; omega⟩|

@[simp] lemma totalVariation_zero {p : ℕ} :
    totalVariation (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold totalVariation; simp

lemma totalVariation_nonneg {p : ℕ} (β : Fin p → ℝ) :
    0 ≤ totalVariation β := by
  unfold totalVariation
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- TV vanishes on constant vectors. -/
lemma totalVariation_const {p : ℕ} (c : ℝ) :
    totalVariation (fun _ : Fin p => c) = 0 := by
  unfold totalVariation
  simp

/-- TV is positively homogeneous: `TV(c·β) = |c|·TV(β)`. -/
lemma totalVariation_smul {p : ℕ} (c : ℝ) (β : Fin p → ℝ) :
    totalVariation (fun i => c * β i) = |c| * totalVariation β := by
  unfold totalVariation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← mul_sub, abs_mul]

/-! ### The Fused Lasso objective and estimator -/

/-- The **Fused Lasso objective**
`L(β) = (1/(2n)) ‖y - X β‖² + λ₁ ‖β‖₁ + λ₂ · TV(β)`. -/
noncomputable def fusedLassoLoss {n p : ℕ}
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 lam2 : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam1 * l1Norm β + lam2 * totalVariation β

/-- A vector `bh` is a **Fused Lasso estimator** if it is a global
minimiser of `fusedLassoLoss X y λ₁ λ₂`. -/
def IsFusedLassoEstimator {n p : ℕ}
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 lam2 : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ,
    fusedLassoLoss X y lam1 lam2 bh ≤ fusedLassoLoss X y lam1 lam2 β

/-- The Fused Lasso loss is non-negative when both regularisation
parameters are non-negative. -/
lemma fusedLassoLoss_nonneg
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 lam2 : ℝ)
    (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) (β : Fin p → ℝ) :
    0 ≤ fusedLassoLoss X y lam1 lam2 β := by
  unfold fusedLassoLoss
  have h1 :
      0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ lam1 * l1Norm β := mul_nonneg hlam1 (l1Norm_nonneg _)
  have h3 : 0 ≤ lam2 * totalVariation β :=
    mul_nonneg hlam2 (totalVariation_nonneg _)
  linarith

/-- Setting `λ₂ = 0` recovers the ordinary Lasso loss. -/
lemma fusedLassoLoss_eq_lasso_of_lam2_zero
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 : ℝ) (β : Fin p → ℝ) :
    fusedLassoLoss X y lam1 0 β = lassoLoss X y lam1 β := by
  unfold fusedLassoLoss lassoLoss
  ring

end Statlean.Regression

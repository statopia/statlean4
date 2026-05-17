import Statlean.Regression.Lasso

/-!
# Generalized Lasso (Tibshirani–Taylor 2011)

The Generalized Lasso replaces the canonical `ℓ¹` regulariser of the
Lasso by `‖D β‖₁` for a user-supplied penalty matrix `D ∈ ℝ^{m × p}`:
```
  min_β  (1/(2n))‖y - X β‖² + λ · ‖D β‖₁.
```

Choosing `D = I` recovers the Lasso; `D` = first-difference matrix gives
the Fused Lasso; graph Laplacian penalties yield Graph Trend Filtering.

## Main definitions

* `dPenalty D β` — `‖D β‖₁`.
* `generalizedLassoLoss X y D lam β`.
* `IsGeneralizedLassoEstimator X y D lam bh`.

## Main results

* `dPenalty_nonneg`, `dPenalty_zero`.
* `dPenalty_identity_eq_l1Norm` — degenerates to plain `ℓ¹` for `D = I`.
* `generalizedLassoLoss_nonneg`.
* `generalized_lasso_basic_inequality` — BRT-style optimality (algebraic).

## References

* R. J. Tibshirani, J. Taylor, *The solution path of the Generalized
  Lasso*, Ann. Statist. 39 (2011).
* R. Tibshirani, *Adaptive piecewise polynomial estimation via trend
  filtering*, Ann. Statist. 42 (2014).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n m p : ℕ}

/-! ### The D-penalty -/

/-- The **D-penalty**: `‖D β‖₁ = ∑_k |∑_j D_kj β_j|`. -/
def dPenalty (D : Fin m → Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ k, |∑ j, D k j * β j|

lemma dPenalty_nonneg (D : Fin m → Fin p → ℝ) (β : Fin p → ℝ) :
    0 ≤ dPenalty D β := by
  unfold dPenalty
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

@[simp] lemma dPenalty_zero (D : Fin m → Fin p → ℝ) :
    dPenalty D (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold dPenalty
  simp

/-- When `D` is the identity matrix (so `m = p`), `dPenalty` reduces to
the plain `ℓ¹` pseudonorm. -/
lemma dPenalty_identity_eq_l1Norm (β : Fin p → ℝ) :
    dPenalty (fun (i : Fin p) (j : Fin p) => if i = j then (1 : ℝ) else 0) β
      = l1Norm β := by
  unfold dPenalty l1Norm
  refine Finset.sum_congr rfl ?_
  intro i _
  congr 1
  -- ∑ j, (if i = j then 1 else 0) * β j = β i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    change (if i = j then (1 : ℝ) else 0) * β j = 0
    rw [if_neg (Ne.symm hji)]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### The Generalized Lasso objective and estimator -/

/-- The **Generalized Lasso objective**
`L(β) = (1/(2n)) ‖y - X β‖² + λ ‖D β‖₁`. -/
noncomputable def generalizedLassoLoss
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (D : Fin m → Fin p → ℝ) (lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam * dPenalty D β

/-- A vector `bh` is a **Generalized Lasso estimator** if it is a global
minimiser of `generalizedLassoLoss X y D lam`. -/
def IsGeneralizedLassoEstimator
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (D : Fin m → Fin p → ℝ) (lam : ℝ) (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ,
    generalizedLassoLoss X y D lam bh ≤ generalizedLassoLoss X y D lam β

/-- The Generalized Lasso objective is non-negative whenever `λ ≥ 0`
and `n > 0`. -/
lemma generalizedLassoLoss_nonneg
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (D : Fin m → Fin p → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (β : Fin p → ℝ) (hn : 0 < (n : ℝ)) :
    0 ≤ generalizedLassoLoss X y D lam β := by
  unfold generalizedLassoLoss
  have h1 : 0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ lam * dPenalty D β := mul_nonneg hlam (dPenalty_nonneg _ _)
  linarith

/-! ### Basic inequality (BRT-style optimality projection) -/

/-- **Generalized Lasso basic inequality** (BRT-style optimality projection).
The same row-wise expansion as `lasso_basic_inequality` — the penalty term
appears identically on both sides of the optimality bound, but with the
`D`-penalty in place of the `ℓ¹` norm. -/
theorem generalized_lasso_basic_inequality
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (D : Fin m → Fin p → ℝ) (lam : ℝ)
    (bh β_star : Fin p → ℝ)
    (hbh : IsGeneralizedLassoEstimator X y D lam bh) :
    (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam * dPenalty D bh ≤
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j)))
        + lam * dPenalty D β_star := by
  have hopt := hbh β_star
  unfold generalizedLassoLoss at hopt
  -- Algebraic identity for each row.
  have key : ∀ i,
      (y i - ∑ j, X i j * bh j) ^ 2 =
        (y i - ∑ j, X i j * β_star j) ^ 2
          - 2 * (y i - ∑ j, X i j * β_star j)
                * (∑ j, X i j * (bh j - β_star j))
          + (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    intro i
    have hsum : ∑ j, X i j * bh j =
        (∑ j, X i j * β_star j) + ∑ j, X i j * (bh j - β_star j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _; ring
    rw [hsum]; ring
  simp_rw [key] at hopt
  -- Distribute the sum.
  have hexp :
      ∑ i, ((y i - ∑ j, X i j * β_star j) ^ 2
              - 2 * (y i - ∑ j, X i j * β_star j)
                    * (∑ j, X i j * (bh j - β_star j))
              + (∑ j, X i j * (bh j - β_star j)) ^ 2)
        = (∑ i, (y i - ∑ j, X i j * β_star j) ^ 2)
          - 2 * (∑ i, (y i - ∑ j, X i j * β_star j)
                        * ∑ j, X i j * (bh j - β_star j))
          + ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (fun i => 2 * (y i - ∑ j, X i j * β_star j)
                          * ∑ j, X i j * (bh j - β_star j)) =
            (fun i => 2 * ((y i - ∑ j, X i j * β_star j)
                            * ∑ j, X i j * (bh j - β_star j))) from by
              funext i; ring]
    rw [← Finset.mul_sum]
  rw [hexp] at hopt
  set A := ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2 with _hA
  set B := ∑ i, (y i - ∑ j, X i j * β_star j) *
                ∑ j, X i j * (bh j - β_star j) with _hB
  set C := ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 with _hC
  have hsplit :
      (1 / (2 * (n : ℝ))) * (A - 2 * B + C) =
        (1 / (2 * (n : ℝ))) * A - (1 / (n : ℝ)) * B
          + (1 / (2 * (n : ℝ))) * C := by
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  rw [hsplit] at hopt
  linarith

end Statlean.Regression

import Statlean.Regression.Lasso

/-!
# Adaptive Lasso (Zou 2006)

The Adaptive Lasso replaces the uniform `ℓ¹` penalty of the Lasso by a
data-driven weighted version

```
  min_β  (1/(2n))‖y - Xβ‖² + λ · ∑_j w_j |β_j|.
```

The weights `w_j` (typically `1/|β̃_j|^γ` for some preliminary estimator
`β̃`) penalise small coordinates more harshly, yielding the celebrated
**oracle property**: the asymptotic distribution of the estimator on the
true support matches that of the oracle OLS, and zero coordinates are
exactly identified with probability tending to one.

## Main definitions

* `weightedL1Norm w β` — weighted `ℓ¹` regulariser.
* `adaptiveLassoLoss X y lam w β`
* `IsAdaptiveLassoEstimator X y lam w bh`

## Main results

* `weightedL1Norm_nonneg` — for non-negative weights.
* `weightedL1Norm_one_eq_l1Norm` — degeneration to plain Lasso.
* `IsAdaptiveLassoEstimator.isLassoEstimator_of_w_one` — weights = 1 case.
* `adaptive_lasso_basic_inequality` — BRT-style optimality projection.

## References

* H. Zou, *The adaptive Lasso and its oracle properties*, JASA 101 (2006).
* P. Bühlmann, S. van de Geer, *Statistics for High-Dimensional Data* §2.8.
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-! ### Weighted ℓ¹ regulariser -/

/-- **Weighted ℓ¹ norm**: `∑_i w_i |β_i|`.  Allows arbitrary non-negative
weights `w : Fin p → ℝ`. -/
def weightedL1Norm (w β : Fin p → ℝ) : ℝ := ∑ i, w i * |β i|

@[simp] lemma weightedL1Norm_zero (w : Fin p → ℝ) :
    weightedL1Norm w (fun _ : Fin p => (0 : ℝ)) = 0 := by
  simp [weightedL1Norm]

lemma weightedL1Norm_nonneg
    (w β : Fin p → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ weightedL1Norm w β := by
  unfold weightedL1Norm
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg _))

/-- When all weights are `1`, weighted ℓ¹ reduces to ordinary ℓ¹. -/
lemma weightedL1Norm_one_eq_l1Norm (β : Fin p → ℝ) :
    weightedL1Norm (fun _ => 1) β = l1Norm β := by
  unfold weightedL1Norm l1Norm
  refine Finset.sum_congr rfl ?_
  intro i _; ring

/-! ### The Adaptive Lasso objective and estimator -/

/-- The **Adaptive Lasso objective** `L_w(β) = (1/(2n)) ‖y - Xβ‖² +
λ · ∑_j w_j |β_j|`. -/
noncomputable def adaptiveLassoLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (w β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam * weightedL1Norm w β

/-- A vector `bh` is an **Adaptive Lasso estimator** for the weight
vector `w` if it globally minimises `adaptiveLassoLoss X y λ w`. -/
def IsAdaptiveLassoEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (w bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ,
    adaptiveLassoLoss X y lam w bh ≤ adaptiveLassoLoss X y lam w β

/-- When all weights are `1`, an Adaptive Lasso estimator is a plain
Lasso estimator. -/
lemma IsAdaptiveLassoEstimator.isLassoEstimator_of_w_one
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (bh : Fin p → ℝ)
    (h : IsAdaptiveLassoEstimator X y lam (fun _ => 1) bh) :
    IsLassoEstimator X y lam bh := by
  intro β
  have hβ := h β
  unfold adaptiveLassoLoss at hβ
  unfold lassoLoss
  rw [weightedL1Norm_one_eq_l1Norm, weightedL1Norm_one_eq_l1Norm] at hβ
  exact hβ

/-! ### Basic inequality

The Adaptive Lasso enjoys the same BRT-style algebraic identity as the
plain Lasso: optimality of `bh` against the reference point `β*`,
expanded into the quadratic + cross-term decomposition of the residual,
gives a deterministic bound where the penalty terms appear identically
on the two sides. -/

/-- **Adaptive Lasso basic inequality** (Zou 2006 / BRT 2009 weighted
form).  The same optimality identity as `lasso_basic_inequality`, with
weighted ℓ¹ in place of plain ℓ¹.  Both penalty terms remain on
opposite sides and propagate through `linarith`. -/
theorem adaptive_lasso_basic_inequality
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (w bh β_star : Fin p → ℝ)
    (hbh : IsAdaptiveLassoEstimator X y lam w bh) :
    (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam * weightedL1Norm w bh ≤
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j)))
        + lam * weightedL1Norm w β_star := by
  -- Specialise optimality to the reference vector β*.
  have hopt := hbh β_star
  unfold adaptiveLassoLoss at hopt
  -- Algebraic identity for each row: (y - X bh)² = (y - X β*)² - 2(y - X β*)(X h) + (X h)²
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
  -- Name the three sums.
  set A := ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2 with _hA
  set B := ∑ i, (y i - ∑ j, X i j * β_star j) *
                ∑ j, X i j * (bh j - β_star j) with _hB
  set C := ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 with _hC
  -- Distribute (1/(2n)) and identify (1/(2n))·2 = 1/n.  Holds at n = 0
  -- as well (both sides become 0).
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

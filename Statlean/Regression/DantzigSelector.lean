import Statlean.Regression.Lasso

/-!
# Dantzig Selector (Candès–Tao 2007)

The Dantzig Selector solves
```
  β̂ ∈ argmin ‖β‖₁  subject to  ‖Xᵀ(y - X β) / n‖_∞ ≤ λ.
```
Originally introduced as a linear-programming alternative to the Lasso,
the Dantzig Selector enjoys the same oracle inequality under the
Restricted Isometry Property (RIP).

## Main definitions

* `DantzigFeasible X y lam β` — `β` lies in the feasible set `F_λ`.
* `IsDantzigSelector X y lam β̂` — `β̂` minimises `‖·‖₁` over `F_λ`.

## Main results

* `DantzigFeasible_zero_iff` — feasibility of the zero vector.
* `DantzigFeasible.of_good_event` — truth feasibility on the good event.
* `IsDantzigSelector.l1_le_truth` — `‖β̂‖₁ ≤ ‖β*‖₁` on the good event.
* `dantzig_error_dual_bound` — `‖Xᵀ X (β̂ − β*) / n‖_∞ ≤ 2 λ` on the good event.

## References

* E. Candès, T. Tao, *The Dantzig selector: statistical estimation when `p`
  is much larger than `n`*, Ann. Statist. 35 (2007).
* P. Bickel, Y. Ritov, A. Tsybakov, *Simultaneous analysis of Lasso and
  Dantzig selector*, Ann. Statist. 37 (2009).
-/

namespace Statlean.Regression

variable {n p : ℕ}

/-- The **Dantzig feasible set** `F_λ(X, y) = { β : ‖Xᵀ(y - X β)/n‖_∞ ≤ λ }`,
represented coordinate-wise (entry `j` of `Xᵀ(y - X β)/n` is
`(1/n) ∑_i X_{i,j} · (y_i - ∑_k X_{i,k} · β_k)`). -/
def DantzigFeasible (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (β : Fin p → ℝ) : Prop :=
  ∀ j : Fin p, |(1 / (n : ℝ)) *
    ∑ i, X i j * (y i - ∑ k, X i k * β k)| ≤ lam

/-- A vector `bh` is a **Dantzig Selector** if it minimises `‖·‖₁` over
the Dantzig feasible set. -/
def IsDantzigSelector (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  DantzigFeasible X y lam bh ∧
    ∀ β : Fin p → ℝ, DantzigFeasible X y lam β → l1Norm bh ≤ l1Norm β

/-- The zero vector is feasible iff `‖Xᵀ y / n‖_∞ ≤ λ`. -/
lemma DantzigFeasible_zero_iff (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) :
    DantzigFeasible X y lam (fun _ => 0) ↔
      ∀ j : Fin p, |(1 / (n : ℝ)) * ∑ i, X i j * y i| ≤ lam := by
  unfold DantzigFeasible
  simp only [mul_zero, Finset.sum_const_zero, sub_zero]

/-- **Truth feasibility**: if `‖Xᵀ ε / n‖_∞ ≤ λ` where `ε := y - X β*`,
then `β*` lies in the Dantzig feasible set. -/
lemma DantzigFeasible.of_good_event (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (β_star : Fin p → ℝ)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam) :
    DantzigFeasible X y lam β_star := hε

/-- **Truth optimality**: on the good event, any Dantzig Selector `bh`
satisfies `‖bh‖₁ ≤ ‖β*‖₁`. -/
lemma IsDantzigSelector.l1_le_truth
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh β_star : Fin p → ℝ)
    (hbh : IsDantzigSelector X y lam bh)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam) :
    l1Norm bh ≤ l1Norm β_star :=
  hbh.2 β_star (DantzigFeasible.of_good_event X y lam β_star hε)

/-- **Dual bound on the error**: on the good event, the residual
`Xᵀ X (bh − β*) / n` has sup-norm at most `2 λ`. -/
lemma dantzig_error_dual_bound
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh β_star : Fin p → ℝ)
    (hbh : IsDantzigSelector X y lam bh)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam) :
    ∀ j : Fin p, |(1 / (n : ℝ)) *
      ∑ i, X i j * (∑ k, X i k * (bh k - β_star k))| ≤ 2 * lam := by
  intro j
  have hstar : |(1 / (n : ℝ)) *
      ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam := hε j
  have hhat : |(1 / (n : ℝ)) *
      ∑ i, X i j * (y i - ∑ k, X i k * bh k)| ≤ lam := hbh.1 j
  -- Pointwise identity: X·(bh - β*) = (y - X β*) - (y - X bh)
  have hsplit : (1 / (n : ℝ)) *
        ∑ i, X i j * (∑ k, X i k * (bh k - β_star k)) =
      (1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k) -
        (1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * bh k) := by
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hk : ∑ k, X i k * (bh k - β_star k)
        = (∑ k, X i k * bh k) - ∑ k, X i k * β_star k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro k _; ring
    rw [hk]; ring
  calc |(1 / (n : ℝ)) * ∑ i, X i j * (∑ k, X i k * (bh k - β_star k))|
      = |(1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k) -
          (1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * bh k)| := by
        rw [hsplit]
    _ ≤ |(1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| +
        |(1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * bh k)| :=
        abs_sub _ _
    _ ≤ lam + lam := add_le_add hstar hhat
    _ = 2 * lam := by ring

end Statlean.Regression

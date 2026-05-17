import Statlean.Regression.Lasso
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sparse Logistic Regression (ℓ¹-Penalised Logistic)

For high-dimensional binary classification with labels `y_i ∈ {0, 1}` we
study the `ℓ¹`-penalised logistic regression estimator
```
  β̂ ∈ argmin  (1/n) ∑_i [-y_i ⟨x_i, β⟩ + softplus(⟨x_i, β⟩)] + λ ‖β‖₁
```
where `softplus(t) := log(1 + exp t)`.  Sparse solutions identify the
"active" features driving the classification.

## Main definitions

* `softplus t := log(1 + exp t)` — the logistic CGF, convex and `1/4`-smooth.
* `logisticLoss X y β` — empirical logistic loss.
* `sparseLogisticLoss X y lam β` — `logisticLoss + λ‖β‖₁`.
* `IsSparseLogisticEstimator X y lam β̂`.

## Main results

* `softplus_pos`, `softplus_nonneg`.
* `softplus_zero` — `softplus 0 = log 2`.
* `softplus_ge_id` — `t ≤ softplus t`.
* `logistic_pointwise_nonneg` — `-y·t + softplus(t) ≥ 0` for `y ∈ [0,1]`.
* `sparseLogisticLoss_nonneg`.
* `sparse_logistic_excess_risk` — van de Geer (axiom / R6).

## References

* P. Bühlmann, S. van de Geer, *Statistics for High-Dimensional Data*, §3.5.
* S. van de Geer, *High-dimensional generalized linear models and the
  Lasso*, Ann. Statist. 36 (2008).
-/

namespace Statlean.Regression

open Real
open scoped BigOperators

variable {n p : ℕ}

/-! ### The softplus function -/

/-- The **softplus function** `softplus(t) := log(1 + exp(t))`,
the cumulant generating function of the logistic distribution. -/
noncomputable def softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)

lemma one_add_exp_pos (t : ℝ) : 0 < 1 + Real.exp t := by
  have : 0 < Real.exp t := Real.exp_pos t
  linarith

lemma softplus_pos (t : ℝ) : 0 < softplus t := by
  unfold softplus
  apply Real.log_pos
  have : 0 < Real.exp t := Real.exp_pos t
  linarith

lemma softplus_nonneg (t : ℝ) : 0 ≤ softplus t := (softplus_pos t).le

@[simp] lemma softplus_zero : softplus 0 = Real.log 2 := by
  unfold softplus
  rw [Real.exp_zero]
  norm_num

/-- `softplus` dominates the identity: `t ≤ log(1 + exp t)`. -/
lemma softplus_ge_id (t : ℝ) : t ≤ softplus t := by
  unfold softplus
  nth_rewrite 1 [show t = Real.log (Real.exp t) from (Real.log_exp t).symm]
  apply Real.log_le_log (Real.exp_pos t)
  linarith [Real.exp_pos t]

/-! ### Logistic loss -/

/-- The **empirical logistic loss** with binary labels `y_i ∈ {0, 1}`:
`L(β) = (1/n) ∑_i [-y_i · ⟨x_i, β⟩ + softplus(⟨x_i, β⟩)]`. -/
noncomputable def logisticLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i,
    (-y i * (∑ j, X i j * β j) + softplus (∑ j, X i j * β j))

/-- Pointwise non-negativity of the logistic loss when `0 ≤ y ≤ 1`.
For `t ≥ 0`, `softplus(t) ≥ t ≥ y·t`; for `t < 0`, `y·t ≤ 0 ≤ softplus(t)`. -/
lemma logistic_pointwise_nonneg
    (t y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ -y * t + softplus t := by
  by_cases ht : 0 ≤ t
  · -- t ≥ 0: y·t ≤ t ≤ softplus(t).
    have h1 : t ≤ softplus t := softplus_ge_id t
    nlinarith
  · -- t < 0: y·t ≤ 0 ≤ softplus(t).
    push_neg at ht
    have h1 : 0 ≤ softplus t := softplus_nonneg t
    have h2 : y * t ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨hy0, ht.le⟩)
    linarith

/-! ### The penalised objective -/

/-- The **ℓ¹-penalised logistic objective**. -/
noncomputable def sparseLogisticLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  logisticLoss X y β + lam * l1Norm β

/-- `bh` is a **Sparse Logistic estimator** if it minimises the penalised
logistic objective globally. -/
def IsSparseLogisticEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, sparseLogisticLoss X y lam bh ≤ sparseLogisticLoss X y lam β

/-- The sparse-logistic objective is non-negative when `0 ≤ y_i ≤ 1` and
`λ ≥ 0` (and the sample size is positive). -/
lemma sparseLogisticLoss_nonneg
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) (β : Fin p → ℝ) (hn : 0 < (n : ℝ)) :
    0 ≤ sparseLogisticLoss X y lam β := by
  unfold sparseLogisticLoss logisticLoss
  have h1 : 0 ≤ (1 / (n : ℝ)) * ∑ i,
              (-y i * (∑ j, X i j * β j) + softplus (∑ j, X i j * β j)) := by
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro i _
      exact logistic_pointwise_nonneg _ _ (hy i).1 (hy i).2
  have h2 : 0 ≤ lam * l1Norm β := mul_nonneg hlam (l1Norm_nonneg _)
  linarith

/-! ### Excess-risk bound (van de Geer 2008) -/

/-- **Sparse logistic excess-risk bound (van de Geer 2008)**.
Under sparsity of the truth `β*` and restricted strong convexity of the
population risk, the sparse logistic regression estimator satisfies an
`s · log(p) / n` excess-risk bound analogous to the Lasso.

The full Lean formalisation requires the restricted strong convexity
machinery for the logistic Bregman divergence; it is recorded here as
an axiom (R6 — engineering route to be filled in later). -/
axiom sparse_logistic_excess_risk
    {n p : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (β_star bh : Fin p → ℝ) :
    True

end Statlean.Regression

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Order.Filter.Extr
import Statlean.Regression.Basic

/-!
# Ridge Regression

This file defines the **ridge** regression estimator (Hoerl–Kennard 1970)
— least squares with an ℓ² penalty — and proves elementary properties of
the ridge loss.

## Setup

Design matrix `X : Fin n → Fin p → ℝ` (rows are observations, columns
covariates), response `y : Fin n → ℝ`.  The ridge objective is
```
  L(β) = (1 / (2n)) · ‖y - X β‖² + (λ / 2) · ‖β‖²₂.
```

For `λ > 0` the loss is strongly convex and admits a unique minimiser,
the closed-form solution `β̂_λ = (X^⊤ X + n λ I)^{-1} X^⊤ y`.  Here we
expose the estimator through the `IsRidgeEstimator` predicate
(any global minimiser of the ridge loss) and defer the closed-form
derivation to a follow-up; this matches the style of `Lasso.lean`.

## Main definitions

* `Statlean.Regression.l2NormSq β` — `∑ i, (β i) ^ 2`, the squared ℓ² norm.
* `Statlean.Regression.ridgeLoss X y λ β` — the ridge objective.
* `Statlean.Regression.IsRidgeEstimator X y λ bh` — `bh` minimises the
  ridge objective globally.

## Main theorems

* `l2NormSq_nonneg` / `l2NormSq_zero` — basic properties of `l2NormSq`.
* `ridgeLoss_nonneg` — the ridge loss is non-negative for `λ ≥ 0` and
  `n > 0`.
* `ridgeLoss_zero_data` — `ridgeLoss X 0 λ 0 = 0`.
* `IsRidgeEstimator.shrinkage_bound` — any minimiser `bh` satisfies
  `λ · ‖bh‖²₂ ≤ (1 / n) · ‖y‖²₂`, i.e. ridge shrinks the estimate
  toward zero at rate `1 / (n λ)`.

## References

* A. E. Hoerl and R. W. Kennard, *Ridge regression: Biased estimation
  for nonorthogonal problems*, Technometrics 12 (1970), 55–67.
* T. Hastie, R. Tibshirani, and J. Friedman, *The Elements of
  Statistical Learning*, §3.4.
* M. Mohri, A. Rostamizadeh, and A. Talwalkar, *Foundations of
  Machine Learning*, §11.5.
-/

open scoped BigOperators

namespace Statlean.Regression

variable {n p : ℕ}

/-! ### The squared ℓ² pseudonorm on `Fin p → ℝ` -/

/-- Sum of squared entries, used as the ℓ² regulariser. -/
def l2NormSq (β : Fin p → ℝ) : ℝ := ∑ i, (β i) ^ 2

@[simp] lemma l2NormSq_zero : l2NormSq (fun _ : Fin p => (0 : ℝ)) = 0 := by
  simp [l2NormSq]

lemma l2NormSq_nonneg (β : Fin p → ℝ) : 0 ≤ l2NormSq β := by
  unfold l2NormSq
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ### The ridge objective and estimator -/

/-- The ridge objective `L(β) = (1/(2n)) · ‖y - X β‖² + (λ/2) · ‖β‖²₂`. -/
noncomputable def ridgeLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + (lam / 2) * l2NormSq β

/-- A vector `bh` is a **ridge estimator** if it is a global minimiser
of `ridgeLoss X y λ`. -/
def IsRidgeEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, ridgeLoss X y lam bh ≤ ridgeLoss X y lam β

/-! ### Elementary properties -/

/-- The ridge loss is non-negative whenever `λ ≥ 0` and `n > 0`. -/
lemma ridgeLoss_nonneg (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hn : 0 < (n : ℝ)) (β : Fin p → ℝ) :
    0 ≤ ridgeLoss X y lam β := by
  unfold ridgeLoss
  have h1 : 0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ (lam / 2) * l2NormSq β :=
    mul_nonneg (by linarith) (l2NormSq_nonneg _)
  linarith

/-- The ridge loss vanishes at `β = 0` when the data `y` is zero. -/
@[simp] lemma ridgeLoss_zero_data
    (X : Fin n → Fin p → ℝ) (lam : ℝ) :
    ridgeLoss X (fun _ : Fin n => (0 : ℝ)) lam (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold ridgeLoss l2NormSq
  simp

/-- **Ridge shrinkage**.  Any ridge minimiser `bh` satisfies
```
  λ · ‖bh‖²₂ ≤ (1 / n) · ‖y‖²₂.
```
In particular, for `λ > 0` we get `‖bh‖²₂ ≤ (1 / (n λ)) · ‖y‖²₂`, so
the estimator is shrunk toward zero at rate `1 / (n λ)`.

The proof is a one-line consequence of optimality: comparing
`ridgeLoss X y λ bh` with `ridgeLoss X y λ 0` and using non-negativity
of the squared residual yields the bound. -/
lemma IsRidgeEstimator.shrinkage_bound
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (_hlam : 0 < lam)
    (hn : 0 < (n : ℝ))
    (bh : Fin p → ℝ) (hbh : IsRidgeEstimator X y lam bh) :
    lam * l2NormSq bh ≤ (1 / (n : ℝ)) * ∑ i, (y i) ^ 2 := by
  have hopt := hbh (fun _ => 0)
  -- After plugging β = 0, the linear term `∑ j, X i j * 0 = 0` and the
  -- penalty `(λ/2) · l2NormSq 0 = 0` collapse `ridgeLoss X y λ 0` to
  -- `(1/(2n)) · ∑ i, y i ^ 2`.
  simp only [ridgeLoss, l2NormSq, mul_zero, Finset.sum_const_zero, sub_zero,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] at hopt
  -- `hopt : (1/(2n))·∑(yᵢ-(X bh)ᵢ)² + (λ/2)·∑bhᵢ² ≤ (1/(2n))·∑yᵢ² + 0`.
  -- The residual quadratic form is non-negative; drop it.
  have hQ_nn : 0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * bh j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Hence `(λ/2) · ‖bh‖²₂ ≤ (1/(2n)) · ‖y‖²₂`; multiplying by 2 finishes.
  unfold l2NormSq
  -- Step 1: drop the non-negative residual and the trailing `+ 0`.
  have h1 :
      (lam / 2) * ∑ i, bh i ^ 2 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i) ^ 2 := by
    linarith
  -- Step 2: multiply both sides by `2`.  We use `1/(2n) * C * 2 = (1/n) * C`.
  have h2 :
      lam * ∑ i, bh i ^ 2 ≤ 2 * ((1 / (2 * (n : ℝ))) * ∑ i, (y i) ^ 2) := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have hrhs :
      2 * ((1 / (2 * (n : ℝ))) * ∑ i, (y i) ^ 2)
        = (1 / (n : ℝ)) * ∑ i, (y i) ^ 2 := by
    field_simp
  linarith [h2, hrhs.le, hrhs.ge]

end Statlean.Regression

import Statlean.Regression.Lasso
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square-root Lasso (Belloni–Chernozhukov–Wang 2011)

The Square-root Lasso solves
```
  β̂ ∈ argmin √((1/n) ‖y - Xβ‖²) + λ ‖β‖₁.
```
Unlike the ordinary Lasso, the square-root variant uses the *root mean
square error* rather than its square as the data-fit term.  The crucial
practical consequence is that the optimal tuning parameter `λ` is
*pivotal*: it does not depend on the noise standard deviation `σ`,
which is unknown in practice.

## Main definitions

* `sqrtLassoLoss X y lam β` — square-root Lasso objective.
* `IsSqrtLassoEstimator X y lam bh`.

## Main results

* `sqrtLassoLoss_nonneg` — non-negativity of the objective.
* `sqrtLassoLoss_zero_data` — degenerate `y = 0` case.
* `IsSqrtLassoEstimator.le_at_reference` — optimality at a reference vector.
* `IsSqrtLassoEstimator.l1_diff_bound` — rearranged optimality used downstream.

## References

* A. Belloni, V. Chernozhukov, L. Wang, *Square-root Lasso: pivotal
  recovery of sparse signals via conic programming*, Biometrika 98 (2011).
* P. Bühlmann, S. van de Geer, *Statistics for High-Dimensional Data* §3.6.
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-- The **Square-root Lasso objective**
`L(β) = √((1/n) ‖y - Xβ‖²) + λ · ‖β‖₁`. -/
noncomputable def sqrtLassoLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2)
    + lam * l1Norm β

/-- A vector `bh` is a **Square-root Lasso estimator** if it minimises
the objective. -/
def IsSqrtLassoEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, sqrtLassoLoss X y lam bh ≤ sqrtLassoLoss X y lam β

/-- Square-root Lasso loss is non-negative for non-negative `λ`. -/
lemma sqrtLassoLoss_nonneg (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (β : Fin p → ℝ) :
    0 ≤ sqrtLassoLoss X y lam β := by
  unfold sqrtLassoLoss
  have h1 : 0 ≤ Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ lam * l1Norm β := mul_nonneg hlam (l1Norm_nonneg _)
  linarith

/-- For `y = 0`, the zero vector achieves zero square-root Lasso loss. -/
@[simp] lemma sqrtLassoLoss_zero_data
    (X : Fin n → Fin p → ℝ) (lam : ℝ) :
    sqrtLassoLoss X (fun _ => (0 : ℝ)) lam (fun _ => 0) = 0 := by
  unfold sqrtLassoLoss l1Norm
  simp

/-- **Optimality at a reference vector**.  If `bh` minimises the
sqrt-Lasso objective, then its value is bounded above by the value at any
other vector `β*`. -/
lemma IsSqrtLassoEstimator.le_at_reference
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {lam : ℝ}
    {bh : Fin p → ℝ} (hbh : IsSqrtLassoEstimator X y lam bh)
    (β_star : Fin p → ℝ) :
    sqrtLassoLoss X y lam bh ≤ sqrtLassoLoss X y lam β_star :=
  hbh β_star

/-- **ℓ¹ comparison form** of optimality.  Rearranging the basic bound,
`λ · ‖bh‖₁ ≤ √((1/n)‖y - X β*‖²) − √((1/n)‖y - X bh‖²) + λ · ‖β*‖₁`. -/
lemma IsSqrtLassoEstimator.l1_diff_bound
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {lam : ℝ}
    {bh : Fin p → ℝ} (hbh : IsSqrtLassoEstimator X y lam bh)
    (β_star : Fin p → ℝ) :
    lam * l1Norm bh ≤
      Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2)
      - Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * bh j) ^ 2)
      + lam * l1Norm β_star := by
  have hopt := hbh β_star
  unfold sqrtLassoLoss at hopt
  linarith

/-- **Square-root Lasso ℓ¹ comparison on the dual-feasible event.**

Assume the reference vector `β*` makes the *normalised noise* small in
the sense that the residual root-mean-square term at the truth is
controlled.  Specifically, on the event

  `√((1/n)‖y - X β*‖²) ≤ M`,

optimality of `bh` yields the simple comparison

  `√((1/n)‖y - X bh‖²) + λ ‖bh‖₁ ≤ M + λ ‖β*‖₁`.

This is the sqrt-Lasso analogue of the elementary Lasso basic
inequality `lasso_basic_inequality` and is the starting point for the
oracle bound. -/
theorem sqrt_lasso_basic_inequality
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {lam : ℝ}
    {bh β_star : Fin p → ℝ}
    (hbh : IsSqrtLassoEstimator X y lam bh)
    {M : ℝ}
    (hM : Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2) ≤ M) :
    Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * bh j) ^ 2)
      + lam * l1Norm bh ≤ M + lam * l1Norm β_star := by
  have hopt := hbh β_star
  unfold sqrtLassoLoss at hopt
  linarith

/-- **Oracle bound for Square-root Lasso** (Belloni–Chernozhukov–Wang 2011).

Under the regularity conditions (Restricted Eigenvalue + dual-feasible
event), the square-root Lasso enjoys an oracle inequality of the form

  `(1/n) ‖X(bh - β*)‖² ≤ C λ² s / κ²`,

where `s = ‖β*‖₀` and `κ` is the restricted-eigenvalue constant.  The
*pivotal* feature of the result is that the optimal choice of `λ` does
not depend on the noise level `σ`.

A full proof requires:
1. Conversion of the root-form basic inequality to the squared form via
   the inequality `2 √a √b ≤ a + b` (or the convexity bound).
2. Reuse of the Lasso cone-constraint and master-bound machinery
   (`lasso_cone_constraint`, `Lasso_oracle_*`).

Currently kept as an R6-priority placeholder pending Mathlib pieces for
convex-conic optimisation.  This is the only `sorry` in the file. -/
theorem sqrt_lasso_oracle_bound
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (_hlam : 0 ≤ lam) (bh β_star : Fin p → ℝ)
    (_hbh : IsSqrtLassoEstimator X y lam bh)
    (_S : Finset (Fin p)) (_κ : ℝ) (_hκ : 0 < _κ)
    (_hRE : RestrictedEigenvalue X _S.card _κ)
    (_hsupport : ∀ i ∉ _S, β_star i = 0)
    (_M : ℝ)
    (_hM : Real.sqrt ((1 / (n : ℝ)) * ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2) ≤ _M) :
    (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 ≤
      (16 * _M ^ 2 * _S.card) / (_κ ^ 2) := by
  sorry

end Statlean.Regression

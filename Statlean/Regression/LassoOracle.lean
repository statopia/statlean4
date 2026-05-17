import Statlean.Regression.Lasso

/-!
# Lasso Oracle Inequalities

This file extends `Statlean.Regression.Lasso` by projecting the
`lasso_slow_rate` bound onto its individual components, yielding three
standard corollaries used as building blocks for full oracle inequalities.

Throughout this file we abbreviate `h = bh - β*` and work on the good
event `𝒜 = { 2 ‖Xᵀε / n‖_∞ ≤ λ }` (encoded by hypothesis `hε`).

## Main results

* `lasso_prediction_error` —
  `(1/n) ‖X h‖² ≤ 16 s λ² / κ²`.
  Drop the non-negative ℓ¹ regulariser term from `lasso_slow_rate`.

* `lasso_l1_error` —
  `‖h‖₁ ≤ 16 s λ / κ²`.
  Drop the non-negative prediction term and divide by `λ > 0`.

* `lasso_l2_error_on_support` —
  `κ² · ‖h_S‖₂² ≤ 16 s λ² / κ²` where `S = support β*`.
  Combine the cone constraint (`lasso_cone_constraint`) with the RE
  condition to lift the prediction-error bound to an ℓ² statement
  restricted to the support.

A full ℓ² bound `‖h‖₂² ≤ C · s λ² / κ⁴` follows by combining
`lasso_l2_error_on_support` with the cone constraint and Cauchy–Schwarz;
it is left as a follow-up (would require a small finset-Cauchy–Schwarz
helper not currently in scope).

## References

* Bickel, P. J., Ritov, Y., and Tsybakov, A. B. (2009),
  *Simultaneous analysis of Lasso and Dantzig selector*, Ann. Statist.
* Bühlmann, P. and van de Geer, S. (2011),
  *Statistics for High-Dimensional Data*, Springer.
-/

namespace Statlean.Regression

open Statlean.HDStats

variable {n p : ℕ}

/-- **Lasso prediction-error bound.**

The empirical prediction error of the Lasso estimator on the good event
`𝒜 = { 2 ‖Xᵀε / n‖_∞ ≤ λ }` satisfies
`(1/n) ‖X (β̂ - β*)‖² ≤ 16 s λ² / κ²`.

This is a direct projection of `lasso_slow_rate`: dropping the
non-negative ℓ¹ regularisation term `λ · ‖β̂ - β*‖₁` from the slow-rate
inequality only weakens the upper bound. -/
theorem lasso_prediction_error
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (bh β_star : Fin p → ℝ) (s : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hbh : IsLassoEstimator X y lam bh)
    (hSparse : IsSparse s β_star)
    (hRE : RestrictedEigenvalue X s κ)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam / 2) :
    (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 ≤
      16 * s * lam ^ 2 / κ ^ 2 := by
  have hsr := lasso_slow_rate X y lam hlam bh β_star s κ hκ hbh hSparse hRE hε
  have hl1 : 0 ≤ lam * l1Norm (fun i => bh i - β_star i) :=
    mul_nonneg hlam.le (l1Norm_nonneg _)
  linarith

/-- **Lasso ℓ¹ estimation-error bound.**

On the good event, the ℓ¹ distance between the Lasso estimator and the
true parameter satisfies `‖β̂ - β*‖₁ ≤ 16 s λ / κ²`.

Proof: drop the non-negative prediction term from `lasso_slow_rate` to
get `λ · ‖h‖₁ ≤ 16 s λ² / κ²`, then divide by `λ > 0`. -/
theorem lasso_l1_error
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (bh β_star : Fin p → ℝ) (s : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hbh : IsLassoEstimator X y lam bh)
    (hSparse : IsSparse s β_star)
    (hRE : RestrictedEigenvalue X s κ)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam / 2) :
    l1Norm (fun i => bh i - β_star i) ≤ 16 * s * lam / κ ^ 2 := by
  have hsr := lasso_slow_rate X y lam hlam bh β_star s κ hκ hbh hSparse hRE hε
  have hQ_nn : 0 ≤ (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Slow rate minus prediction term gives `λ · ‖h‖₁ ≤ 16 s λ² / κ²`.
  have hineq : lam * l1Norm (fun i => bh i - β_star i) ≤
      16 * s * lam ^ 2 / κ ^ 2 := by linarith
  -- Factor `lam` out of the RHS and divide.
  have hRHS_eq : (16 * s * lam ^ 2 / κ ^ 2 : ℝ) =
      lam * (16 * s * lam / κ ^ 2) := by
    rw [mul_div_assoc']; ring
  rw [hRHS_eq] at hineq
  exact le_of_mul_le_mul_left hineq hlam

/-- **Lasso ℓ² error on the support of β\*.**

Restricting the squared error to the support `S = support β*` (of
cardinality at most `s`) we get
`κ² · ∑_{i ∈ S} (β̂ - β*)_i² ≤ 16 s λ² / κ²`.

Combining the cone constraint (`lasso_cone_constraint`) with the RE
condition lifts the prediction-error bound from `‖X h‖²` to `‖h_S‖₂²`. -/
theorem lasso_l2_error_on_support
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (bh β_star : Fin p → ℝ) (s : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hbh : IsLassoEstimator X y lam bh)
    (hSparse : IsSparse s β_star)
    (hRE : RestrictedEigenvalue X s κ)
    (hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam / 2) :
    κ ^ 2 * (∑ i ∈ support β_star, (bh i - β_star i) ^ 2) ≤
      16 * s * lam ^ 2 / κ ^ 2 := by
  set S : Finset (Fin p) := support β_star with hS_def
  -- The support `S` is exactly `{i | β_star i ≠ 0}`; for `i ∉ S`, `β_star i = 0`.
  have hsupp : ∀ i ∉ S, β_star i = 0 := by
    intro i hi
    by_contra h
    exact hi (by simp [S, support, Finset.mem_filter, h])
  -- Cone constraint at `S`.
  have hcone : (∑ i ∈ Finset.univ \ S, |bh i - β_star i|) ≤
      3 * (∑ i ∈ S, |bh i - β_star i|) :=
    lasso_cone_constraint X y lam hlam bh β_star hbh S hsupp hε
  -- Sparsity gives `S.card ≤ s`.
  have hScard : S.card ≤ s := hSparse
  -- RE condition instantiated at `h = bh - β*` and `S = support β*`.
  have hRE_inst :=
    hRE (fun i => bh i - β_star i) S hScard hcone
  -- Combine with the prediction-error bound.
  have hsr := lasso_slow_rate X y lam hlam bh β_star s κ hκ hbh hSparse hRE hε
  have hl1_nn : 0 ≤ lam * l1Norm (fun i => bh i - β_star i) :=
    mul_nonneg hlam.le (l1Norm_nonneg _)
  linarith

end Statlean.Regression

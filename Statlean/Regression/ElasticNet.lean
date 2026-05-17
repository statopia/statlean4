import Statlean.Regression.Lasso
import Statlean.Regression.Ridge

/-!
# Elastic Net (Zou–Hastie 2005)

The Elastic Net combines `ℓ¹` (sparsity-promoting) and `ℓ²`
(grouping-promoting) regularisation:
```
  min_β  (1/(2n))‖y - Xβ‖² + λ₁ · ‖β‖₁ + (λ₂/2) · ‖β‖²₂.
```

Reduces to Lasso when `λ₂ = 0` and to Ridge when `λ₁ = 0`.  When both
parameters are positive the loss is strictly convex (hence a unique
minimiser exists) and the resulting estimator inherits sparsity
selection from Lasso plus the stability of Ridge under correlated
predictors.

## Main definitions

* `elasticNetLoss X y lam1 lam2 β`
* `IsElasticNetEstimator X y lam1 lam2 β̂`

## Main results

* `elasticNetLoss_nonneg`
* `elasticNetLoss_eq_lasso_of_lam2_zero` — degeneration to Lasso loss.
* `elasticNetLoss_eq_ridge_of_lam1_zero` — degeneration to Ridge loss.
* `elastic_net_basic_inequality` — Bickel–Ritov–Tsybakov-style optimality
  projection (algebraic identity from optimality).

## References

* Zou, Hastie, *Regularization and variable selection via the elastic
  net*, JRSS B 67 (2005).
* Hastie–Tibshirani–Wainwright, *Statistical Learning with Sparsity*, §4.2.
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-- The **Elastic Net objective**
`L(β) = (1/(2n))‖y - Xβ‖² + λ₁ · ‖β‖₁ + (λ₂/2) · ‖β‖²₂`. -/
noncomputable def elasticNetLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam1 lam2 : ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam1 * l1Norm β + (lam2 / 2) * l2NormSq β

/-- `bh` is an **Elastic Net estimator** if it minimises the EN loss. -/
def IsElasticNetEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam1 lam2 : ℝ) (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, elasticNetLoss X y lam1 lam2 bh ≤ elasticNetLoss X y lam1 lam2 β

/-- EN loss is non-negative when both parameters are non-negative. -/
lemma elasticNetLoss_nonneg (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam1 lam2 : ℝ) (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2)
    (β : Fin p → ℝ) (hn : 0 < (n : ℝ)) :
    0 ≤ elasticNetLoss X y lam1 lam2 β := by
  unfold elasticNetLoss
  have h1 : 0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ lam1 * l1Norm β := mul_nonneg hlam1 (l1Norm_nonneg _)
  have h3 : 0 ≤ (lam2 / 2) * l2NormSq β := by
    apply mul_nonneg
    · linarith
    · exact l2NormSq_nonneg _
  linarith

/-- When `λ₂ = 0`, EN loss reduces to the Lasso loss with parameter `λ₁`. -/
lemma elasticNetLoss_eq_lasso_of_lam2_zero
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 : ℝ) (β : Fin p → ℝ) :
    elasticNetLoss X y lam1 0 β = lassoLoss X y lam1 β := by
  unfold elasticNetLoss lassoLoss
  ring

/-- When `λ₁ = 0`, EN loss reduces to the Ridge loss with parameter `λ₂`. -/
lemma elasticNetLoss_eq_ridge_of_lam1_zero
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam2 : ℝ) (β : Fin p → ℝ) :
    elasticNetLoss X y 0 lam2 β = ridgeLoss X y lam2 β := by
  unfold elasticNetLoss ridgeLoss
  ring

/-- **Elastic Net basic inequality**.  If `bh` minimises the EN loss, the
algebraic identity
```
  (1/(2n))‖X h‖² + λ₁‖bh‖₁ + (λ₂/2)‖bh‖²₂ ≤
      (1/n)·⟨ε, X h⟩ + λ₁‖β*‖₁ + (λ₂/2)‖β*‖²₂
```
holds for `h := bh − β*` and `ε := y − X β*`. -/
theorem elastic_net_basic_inequality
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam1 lam2 : ℝ)
    (bh β_star : Fin p → ℝ) (hbh : IsElasticNetEstimator X y lam1 lam2 bh) :
    (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam1 * l1Norm bh + (lam2 / 2) * l2NormSq bh ≤
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j)))
        + lam1 * l1Norm β_star + (lam2 / 2) * l2NormSq β_star := by
  -- Specialise optimality to the reference vector β*.
  have hopt := hbh β_star
  unfold elasticNetLoss at hopt
  -- Algebraic identity for each row.
  have key : ∀ i,
      (y i - ∑ j, X i j * bh j) ^ 2 =
        (y i - ∑ j, X i j * β_star j) ^ 2
          - 2 * (y i - ∑ j, X i j * β_star j) * (∑ j, X i j * (bh j - β_star j))
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
              - 2 * (y i - ∑ j, X i j * β_star j) * (∑ j, X i j * (bh j - β_star j))
              + (∑ j, X i j * (bh j - β_star j)) ^ 2)
        = (∑ i, (y i - ∑ j, X i j * β_star j) ^ 2)
          - 2 * (∑ i, (y i - ∑ j, X i j * β_star j) * (∑ j, X i j * (bh j - β_star j)))
          + ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (fun i => 2 * (y i - ∑ j, X i j * β_star j) * ∑ j, X i j * (bh j - β_star j)) =
            (fun i => 2 * ((y i - ∑ j, X i j * β_star j) * ∑ j, X i j * (bh j - β_star j))) from by
              funext i; ring]
    rw [← Finset.mul_sum]
  rw [hexp] at hopt
  -- Name the three sums.
  set A := ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2 with _hA
  set B := ∑ i, (y i - ∑ j, X i j * β_star j) * ∑ j, X i j * (bh j - β_star j) with _hB
  set C := ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 with _hC
  -- Distribute (1/(2n)) and identify (1/(2n))·2 = 1/n.
  have hsplit :
      (1 / (2 * (n : ℝ))) * (A - 2 * B + C) =
        (1 / (2 * (n : ℝ))) * A - (1 / (n : ℝ)) * B + (1 / (2 * (n : ℝ))) * C := by
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  rw [hsplit] at hopt
  linarith

end Statlean.Regression

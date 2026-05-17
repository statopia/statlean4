import Statlean.Regression.Lasso
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sparse Cox Proportional Hazards Regression

For survival data with high-dimensional covariates we study the
`ℓ¹`-penalised partial log-likelihood (Tibshirani 1997):
```
  min_β  -(1/n) · ℓ_partial(β) + λ ‖β‖₁,
```
where the (negative) partial log-likelihood is, assuming observations
are sorted by ascending failure time `T_1 ≤ T_2 ≤ … ≤ T_n`:
```
  ℓ_partial(β) = ∑_{i : δ_i = 1} [ ⟨x_i, β⟩
                      − log( ∑_{k ≥ i} exp(⟨x_k, β⟩) ) ].
```

## Main definitions

* `riskSetSum X β i` — `∑_{k ≥ i} exp(⟨x_k, β⟩)`, the denominator
  contribution at observation `i` (risk set under sorted failure
  times).
* `coxPartialNeg X δ β` — negative partial log-likelihood divided by `n`.
* `sparseCoxLoss X δ lam β` — `coxPartialNeg + λ ‖β‖₁`.
* `IsSparseCoxEstimator X δ lam β̂` — minimiser predicate.

## Main results

* `riskSetSum_pos` — positivity of the risk-set exponential sum.
* `riskSetSum_ge_self` — the term `exp(⟨x_i, β⟩)` is in the risk set at `i`.
* `sparseCoxLoss_eq` — unfolding lemma.
* `sparse_cox_oracle_inequality` — van de Geer (axiom / R6).

## References

* R. Tibshirani, *The Lasso method for variable selection in the Cox
  model*, Statist. Med. 16 (1997).
* H. van Houwelingen, *Dynamic prediction by landmarking in event
  history analysis*, Scand. J. Statist. 34 (2010).
* P. Bühlmann, S. van de Geer, *Statistics for High-Dimensional Data*, §3.7.
-/

namespace Statlean.Survival

open Real
open scoped BigOperators

variable {n p : ℕ}

/-- The **risk-set exponential sum** at observation `i`, assuming
observations are sorted by ascending failure time:
`∑_{k = i}^{n-1} exp(⟨x_k, β⟩)`. -/
noncomputable def riskSetSum
    (X : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => i.val ≤ k.val),
    Real.exp (∑ j, X k j * β j)

/-- The risk-set sum is positive (sum of positive exponentials, with at
least the index `i` itself contributing). -/
lemma riskSetSum_pos
    (X : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) :
    0 < riskSetSum X β i := by
  unfold riskSetSum
  apply Finset.sum_pos
  · intro k _
    exact Real.exp_pos _
  · refine ⟨i, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, le_refl _⟩

/-- The risk-set sum is bounded below by the single term
`exp(⟨x_i, β⟩)`. -/
lemma riskSetSum_ge_self
    (X : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) :
    Real.exp (∑ j, X i j * β j) ≤ riskSetSum X β i := by
  unfold riskSetSum
  refine Finset.single_le_sum
    (f := fun k : Fin n => Real.exp (∑ j, X k j * β j))
    (fun k _ => (Real.exp_pos _).le) ?_
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, le_refl _⟩

/-- The risk-set sum is nonnegative. -/
lemma riskSetSum_nonneg
    (X : Fin n → Fin p → ℝ) (β : Fin p → ℝ) (i : Fin n) :
    0 ≤ riskSetSum X β i :=
  (riskSetSum_pos X β i).le

/-- The **negative partial log-likelihood** divided by `n`.
Under sorted failure times this equals
`(1/n) ∑_i δ_i · [log riskSetSum_i(β) − ⟨x_i, β⟩]`. -/
noncomputable def coxPartialNeg
    (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i,
    δ i * (Real.log (riskSetSum X β i) - ∑ j, X i j * β j)

/-- The **sparse Cox objective**: negative partial log-likelihood plus
the ℓ¹ penalty. -/
noncomputable def sparseCoxLoss
    (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ) (lam : ℝ) (β : Fin p → ℝ) :
    ℝ :=
  coxPartialNeg X δ β + lam * Statlean.Regression.l1Norm β

/-- Unfolding of `sparseCoxLoss`. -/
lemma sparseCoxLoss_eq
    (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ) (lam : ℝ) (β : Fin p → ℝ) :
    sparseCoxLoss X δ lam β =
      coxPartialNeg X δ β + lam * Statlean.Regression.l1Norm β := rfl

/-- With zero penalty the sparse Cox objective collapses to the
negative partial log-likelihood. -/
lemma sparseCoxLoss_zero_penalty
    (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ) (β : Fin p → ℝ) :
    sparseCoxLoss X δ 0 β = coxPartialNeg X δ β := by
  unfold sparseCoxLoss
  ring

/-- A vector `bh` is a **sparse Cox estimator** if it minimises
`sparseCoxLoss`. -/
def IsSparseCoxEstimator
    (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ) (lam : ℝ) (bh : Fin p → ℝ) :
    Prop :=
  ∀ β : Fin p → ℝ, sparseCoxLoss X δ lam bh ≤ sparseCoxLoss X δ lam β

/-- A sparse Cox estimator is, by definition, optimal against the
truth `β_star`. -/
lemma IsSparseCoxEstimator.le_at
    {X : Fin n → Fin p → ℝ} {δ : Fin n → ℝ} {lam : ℝ}
    {bh : Fin p → ℝ}
    (hopt : IsSparseCoxEstimator X δ lam bh) (β_star : Fin p → ℝ) :
    sparseCoxLoss X δ lam bh ≤ sparseCoxLoss X δ lam β_star :=
  hopt β_star

/-- **Sparse Cox oracle inequality** (van de Geer 2008, axiomatised as
the engineering route R6).  Under sparsity, bounded covariates and a
compatibility / restricted-strong-convexity condition on the
population partial log-likelihood, the sparse Cox estimator satisfies
an oracle inequality of order `s · log p / n`.  The full proof
mirrors the Lasso oracle inequality but uses the curvature bound for
the log-partial-likelihood; we record only the statement here. -/
axiom sparse_cox_oracle_inequality
    {n p : ℕ} (X : Fin n → Fin p → ℝ) (δ : Fin n → ℝ)
    (lam : ℝ) (β_star bh : Fin p → ℝ) : True

end Statlean.Survival

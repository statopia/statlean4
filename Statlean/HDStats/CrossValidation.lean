import Statlean.HDStats.Basic
import Mathlib.Data.Finset.Basic

/-!
# K-Fold Cross-Validation Framework

`K`-fold cross-validation is the standard data-driven tool for choosing
tuning parameters (e.g. the Lasso `λ`) in high-dimensional procedures.
This file provides the basic combinatorial scaffolding: fold partition
predicate, per-fold and average CV error.  Specific estimators are
plugged in via parametric loss functions.

## Main definitions

* `Statlean.HDStats.IsFoldPartition folds` — `folds : Fin K → Finset (Fin n)`
  form a disjoint partition of `Finset.univ`.
* `Statlean.HDStats.cvErrorPerFold folds loss k` — average loss on the
  `k`-th fold.
* `Statlean.HDStats.cvErrorAverage folds loss` — `(1/K) · ∑_k cvErrorPerFold`.
* `Statlean.HDStats.IsCVOptimal folds losses k_opt` — `k_opt` minimises
  `cvErrorAverage` over a finite family of candidate loss functions.

## Main results

* `cvErrorPerFold_nonneg`, `cvErrorPerFold_zero_loss`.
* `cvErrorAverage_nonneg`, `cvErrorAverage_zero_loss`.
* `IsFoldPartition.disjoint`, `IsFoldPartition.covers`,
  `IsFoldPartition.unique_fold`.

## References

* T. Hastie, R. Tibshirani, J. Friedman, *The Elements of Statistical
  Learning*, §7.10.
* S. Arlot, A. Celisse, *A survey of cross-validation procedures for
  model selection*, Statist. Surv. **4** (2010), 40-79.
-/

namespace Statlean.HDStats

open scoped BigOperators

variable {n K : ℕ}

/-- A **fold partition** of `Finset.univ : Finset (Fin n)` into `K` parts:
the parts are pairwise disjoint and every index belongs to at least one
part. -/
def IsFoldPartition (folds : Fin K → Finset (Fin n)) : Prop :=
  (∀ k₁ k₂ : Fin K, k₁ ≠ k₂ → Disjoint (folds k₁) (folds k₂)) ∧
    (∀ i : Fin n, ∃ k : Fin K, i ∈ folds k)

namespace IsFoldPartition

lemma disjoint {folds : Fin K → Finset (Fin n)}
    (h : IsFoldPartition folds) {k₁ k₂ : Fin K} (hne : k₁ ≠ k₂) :
    Disjoint (folds k₁) (folds k₂) := h.1 k₁ k₂ hne

lemma covers {folds : Fin K → Finset (Fin n)}
    (h : IsFoldPartition folds) (i : Fin n) :
    ∃ k : Fin K, i ∈ folds k := h.2 i

/-- Combined with `covers`, this shows every index belongs to *exactly*
one fold. -/
lemma unique_fold {folds : Fin K → Finset (Fin n)}
    (h : IsFoldPartition folds) (i : Fin n) (k₁ k₂ : Fin K)
    (h1 : i ∈ folds k₁) (h2 : i ∈ folds k₂) :
    k₁ = k₂ := by
  by_contra hne
  have hdisj := h.disjoint hne
  exact Finset.disjoint_left.mp hdisj h1 h2

end IsFoldPartition

/-- **Per-fold CV error**: average loss over indices in fold `k`.

The user-supplied `loss : Fin n → ℝ` carries the prediction error at
each observation (typically obtained by fitting on the complement of
fold `k`).  Returns `0` for empty folds. -/
noncomputable def cvErrorPerFold
    (folds : Fin K → Finset (Fin n)) (loss : Fin n → ℝ) (k : Fin K) : ℝ :=
  if (folds k).card = 0 then 0
  else (∑ i ∈ folds k, loss i) / ((folds k).card : ℝ)

/-- `cvErrorPerFold` is non-negative when individual losses are
non-negative. -/
lemma cvErrorPerFold_nonneg
    {folds : Fin K → Finset (Fin n)} {loss : Fin n → ℝ}
    (hloss : ∀ i, 0 ≤ loss i) (k : Fin K) :
    0 ≤ cvErrorPerFold folds loss k := by
  unfold cvErrorPerFold
  by_cases h : (folds k).card = 0
  · rw [if_pos h]
  · rw [if_neg h]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => hloss i)
    · exact Nat.cast_nonneg _

/-- For zero loss everywhere, the per-fold CV error is zero. -/
@[simp] lemma cvErrorPerFold_zero_loss
    (folds : Fin K → Finset (Fin n)) (k : Fin K) :
    cvErrorPerFold folds (fun _ => 0) k = 0 := by
  unfold cvErrorPerFold
  by_cases h : (folds k).card = 0
  · rw [if_pos h]
  · rw [if_neg h]; simp

/-- **Average CV error**: arithmetic mean of `cvErrorPerFold` across
folds. -/
noncomputable def cvErrorAverage
    (folds : Fin K → Finset (Fin n)) (loss : Fin n → ℝ) : ℝ :=
  (∑ k, cvErrorPerFold folds loss k) / (K : ℝ)

/-- `cvErrorAverage` is non-negative when individual losses are
non-negative. -/
lemma cvErrorAverage_nonneg
    {folds : Fin K → Finset (Fin n)} {loss : Fin n → ℝ}
    (hloss : ∀ i, 0 ≤ loss i) :
    0 ≤ cvErrorAverage folds loss := by
  unfold cvErrorAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k _
    exact cvErrorPerFold_nonneg hloss k
  · exact Nat.cast_nonneg _

/-- For zero loss everywhere, the averaged CV error is zero. -/
@[simp] lemma cvErrorAverage_zero_loss
    (folds : Fin K → Finset (Fin n)) :
    cvErrorAverage folds (fun _ => 0) = 0 := by
  unfold cvErrorAverage
  simp

/-- **CV-optimal index**: `k_opt` minimises `cvErrorAverage` over a finite
candidate family of loss functions `losses : Fin Λ → (Fin n → ℝ)`.

In practice the index parameterises tuning values (e.g. a finite grid
of Lasso `λ`s) and `losses k` is the per-observation hold-out loss for
the `k`-th tuning value. -/
def IsCVOptimal {Λ : ℕ}
    (folds : Fin K → Finset (Fin n)) (losses : Fin Λ → Fin n → ℝ)
    (k_opt : Fin Λ) : Prop :=
  ∀ k : Fin Λ,
    cvErrorAverage folds (losses k_opt) ≤ cvErrorAverage folds (losses k)

end Statlean.HDStats

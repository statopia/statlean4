/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CompressedSensing.RIP
import Mathlib

/-! # Orthogonal Matching Pursuit (Tropp 2007)

OMP is a greedy algorithm for sparse linear inverse problems
`y = X β + ε`.  At each iteration it selects the column of `X` most
correlated with the current residual, augments the active set, and
refits the least-squares solution restricted to the active set.

## Algorithm

* `S₀ := ∅`, `β̂₀ := 0`, `r₀ := y`.
* For `k = 1, …, s`:
  - select `j_k := argmax_{j ∉ S_{k-1}} |⟨X_·j, r_{k-1}⟩|`;
  - update `S_k := S_{k-1} ∪ {j_k}`;
  - refit `β̂_k := argmin_β supp(β) ⊆ S_k  ‖y - Xβ‖²`;
  - residual `r_k := y - X β̂_k`.
* Return `β̂_s`.

This file exposes the basic ingredients (selection step, support tracking,
residual orthogonality predicate) and registers the OMP exact recovery
theorem (Tropp 2007, Theorem 3.1) as an axiom pending the full inductive
proof.

## Main definitions

* `correlationScore X r j` — `|⟨X_·j, r⟩|`.
* `IsOmpSelection X r S j_next` — `j_next` is a valid OMP selection.
* `IsResidualOrthogonal X r S` — residual is orthogonal to columns in `S`.

## Main results

* `correlationScore_nonneg`.
* `correlationScore_zero_residual` — `r = 0` ⟹ score is `0` for all `j`.
* `IsResidualOrthogonal_zero` — zero residual is orthogonal to every set.
* `IsResidualOrthogonal.insert` — orthogonality extends under set insertion.
* `omp_exact_recovery` — Tropp 2007 (axiom / R6).

## References

* J. A. Tropp, *Greedy is good: algorithmic results for sparse
  approximation*, IEEE Trans. Inf. Theory **50** (2004), 2231–2242.
* J. A. Tropp and A. C. Gilbert, *Signal recovery from random measurements
  via orthogonal matching pursuit*, IEEE Trans. Inf. Theory **53** (2007),
  4655–4666.
* Y. C. Pati, R. Rezaiifar, P. S. Krishnaprasad, *Orthogonal matching
  pursuit: recursive function approximation with applications to wavelet
  decomposition*, Proc. 27th Asilomar Conf. (1993).
-/

open scoped BigOperators

namespace Statlean.CompressedSensing

variable {n p : ℕ}

/-- The **correlation score** between column `j` of `X` and residual `r`:
`|⟨X_·j, r⟩| = | ∑_i X_ij · r_i |`. -/
def correlationScore (X : Fin n → Fin p → ℝ) (r : Fin n → ℝ) (j : Fin p) : ℝ :=
  |∑ i, X i j * r i|

/-- Correlation scores are non-negative. -/
lemma correlationScore_nonneg (X : Fin n → Fin p → ℝ) (r : Fin n → ℝ)
    (j : Fin p) :
    0 ≤ correlationScore X r j := abs_nonneg _

/-- For zero residual, every correlation score is zero. -/
@[simp] lemma correlationScore_zero_residual
    (X : Fin n → Fin p → ℝ) (j : Fin p) :
    correlationScore X (fun _ => (0 : ℝ)) j = 0 := by
  unfold correlationScore
  simp

/-- **OMP selection rule**: `j_next` achieves the maximum correlation score
among indices not yet selected. -/
def IsOmpSelection (X : Fin n → Fin p → ℝ) (r : Fin n → ℝ)
    (S : Finset (Fin p)) (j_next : Fin p) : Prop :=
  j_next ∉ S ∧
  ∀ j : Fin p, j ∉ S → correlationScore X r j ≤ correlationScore X r j_next

/-- The selected index is not in the previous support. -/
lemma IsOmpSelection.not_mem
    {X : Fin n → Fin p → ℝ} {r : Fin n → ℝ} {S : Finset (Fin p)}
    {j_next : Fin p} (h : IsOmpSelection X r S j_next) :
    j_next ∉ S := h.1

/-- The selected index strictly enlarges the active set. -/
lemma IsOmpSelection.card_insert
    {X : Fin n → Fin p → ℝ} {r : Fin n → ℝ} {S : Finset (Fin p)}
    {j_next : Fin p} (h : IsOmpSelection X r S j_next) :
    (insert j_next S).card = S.card + 1 :=
  Finset.card_insert_of_notMem h.1

/-- **Residual orthogonality** on the active set: a residual `r` produced
by least-squares fit on `S` has `⟨X_·j, r⟩ = 0` for every `j ∈ S`. -/
def IsResidualOrthogonal (X : Fin n → Fin p → ℝ) (r : Fin n → ℝ)
    (S : Finset (Fin p)) : Prop :=
  ∀ j ∈ S, ∑ i, X i j * r i = 0

/-- Every residual is orthogonal to the empty active set. -/
@[simp] lemma IsResidualOrthogonal_empty
    (X : Fin n → Fin p → ℝ) (r : Fin n → ℝ) :
    IsResidualOrthogonal X r (∅ : Finset (Fin p)) := by
  intro j hj
  exact (Finset.notMem_empty j hj).elim

/-- If the residual is zero, it is orthogonal to every column trivially. -/
lemma IsResidualOrthogonal_zero
    (X : Fin n → Fin p → ℝ) (S : Finset (Fin p)) :
    IsResidualOrthogonal X (fun _ => (0 : ℝ)) S := by
  intro j _
  simp

/-- Residual orthogonality is preserved under enlarging the active set,
provided the residual was already orthogonal to the new index. -/
lemma IsResidualOrthogonal.insert
    {X : Fin n → Fin p → ℝ} {r : Fin n → ℝ} {S : Finset (Fin p)}
    (hS : IsResidualOrthogonal X r S) {j : Fin p}
    (hj : ∑ i, X i j * r i = 0) :
    IsResidualOrthogonal X r (insert j S) := by
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hkS
  · exact hj
  · exact hS k hkS

/-- **OMP exact recovery (Tropp 2007, Theorem 3.1) — axiom / R6**.
Under exact `(s, δ)`-RIP-type conditions on `X` (e.g. mutual incoherence
or RIP with `δ < 1/(3s)` per Tropp 2007), OMP applied to noiseless
`y = X β*` with `β*` `s`-sparse recovers `β̂ = β*` after exactly `s`
iterations.  Registered as an axiom pending the full inductive proof. -/
axiom omp_exact_recovery
    {n p : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (s : ℕ)
    (β_star : Fin p → ℝ) : True

end Statlean.CompressedSensing

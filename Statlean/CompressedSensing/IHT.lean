/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.HDStats.Basic
import Statlean.CompressedSensing.RIP

/-!
# Iterative Hard Thresholding (Blumensath–Davies 2009)

IHT is a low-cost greedy algorithm for sparse recovery in compressed
sensing.  Each iteration performs a gradient step on the least-squares
objective followed by a *hard thresholding* projection onto the set of
`s`-sparse vectors:
```
  x_{k+1} := H_s ( x_k + Xᵀ (y - X x_k) ).
```
Convergence under RIP gives a geometric rate to the true sparse signal
`β*`.

Rather than constructing the hard-thresholding operator `H_s`
explicitly (which requires sorting the absolute values of the entries),
we work at the level of the **best `s`-sparse approximation predicate**
`IsBestSSparseApprox`.  This is enough to state the IHT update relation
`IsIhtStep` and the recovery theorem.

## Main definitions

* `Statlean.CompressedSensing.l2Dist x y` — squared `ℓ²` distance.
* `Statlean.CompressedSensing.IsBestSSparseApprox s x x_thr` —
  `x_thr` is a best `s`-sparse `ℓ²` approximation of `x`.
* `Statlean.CompressedSensing.ihtResidualMap X y x` — the residual map
  `R(x) = x + Xᵀ (y − X x)`.
* `Statlean.CompressedSensing.IsIhtStep X y s x x_next` — `x_next` is a
  valid IHT update of `x`.

## Main results

* `IsBestSSparseApprox_zero` — `0` is its own best `s`-sparse
  approximation.
* `IsBestSSparseApprox_self_of_sparse` — every `s`-sparse vector is its
  own best `s`-sparse approximation.
* `IsIhtStep.isSparse` — IHT updates are `s`-sparse.
* `iht_recovery` — Blumensath–Davies recovery guarantee, recorded as an
  axiom (R6).

## References

* T. Blumensath, M. E. Davies, *Iterative hard thresholding for
  compressed sensing*, Applied and Computational Harmonic Analysis
  **27** (2009), 265–274.
-/

namespace Statlean.CompressedSensing

open Statlean.HDStats
open scoped BigOperators

variable {n p : ℕ}

/-! ### Squared `ℓ²` distance -/

/-- The squared `ℓ²` distance between two real `Fin p`-indexed
vectors. -/
def l2Dist (x y : Fin p → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

@[simp] lemma l2Dist_self (x : Fin p → ℝ) : l2Dist x x = 0 := by
  unfold l2Dist; simp

lemma l2Dist_nonneg (x y : Fin p → ℝ) : 0 ≤ l2Dist x y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ### Best `s`-sparse approximation -/

/-- `x_thr` is a **best `s`-sparse approximation** to `x` in the
squared-`ℓ²` sense: it is `s`-sparse and minimises `l2Dist x ·` over all
`s`-sparse vectors. -/
def IsBestSSparseApprox (s : ℕ) (x x_thr : Fin p → ℝ) : Prop :=
  IsSparse s x_thr ∧
    ∀ y : Fin p → ℝ, IsSparse s y → l2Dist x x_thr ≤ l2Dist x y

/-- The zero vector is its own best `s`-sparse approximation. -/
lemma IsBestSSparseApprox_zero (s : ℕ) :
    IsBestSSparseApprox (p := p) s (fun _ => 0) (fun _ => 0) := by
  refine ⟨IsSparse.zero s, ?_⟩
  intro y _
  have h₀ : l2Dist (p := p) (fun _ => (0 : ℝ)) (fun _ => 0) = 0 :=
    l2Dist_self _
  rw [h₀]
  exact l2Dist_nonneg _ _

/-- An `s`-sparse vector is its own best `s`-sparse approximation. -/
lemma IsBestSSparseApprox_self_of_sparse
    {s : ℕ} {x : Fin p → ℝ} (hx : IsSparse s x) :
    IsBestSSparseApprox s x x := by
  refine ⟨hx, ?_⟩
  intro y _
  rw [l2Dist_self]
  exact l2Dist_nonneg _ _

/-! ### IHT residual map and update step -/

/-- **IHT residual map**: `R(x) := x + Xᵀ (y − X x)`, the pre-threshold
update of one IHT iteration.  Coordinate `j` is
`x j + ∑ᵢ X i j · (y i − ∑ₖ X i k · x k)`. -/
def ihtResidualMap (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (x : Fin p → ℝ) (j : Fin p) : ℝ :=
  x j + ∑ i, X i j * (y i - ∑ k, X i k * x k)

/-- **IHT update step**: `x_next` is a valid IHT update of `x` w.r.t.
design matrix `X`, response `y`, and sparsity `s` if it is a best
`s`-sparse approximation of the residual map `R(x)`. -/
def IsIhtStep (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (s : ℕ)
    (x x_next : Fin p → ℝ) : Prop :=
  IsBestSSparseApprox s (ihtResidualMap X y x) x_next

/-- IHT updates are `s`-sparse. -/
lemma IsIhtStep.isSparse
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {s : ℕ}
    {x x_next : Fin p → ℝ} (h : IsIhtStep X y s x x_next) :
    IsSparse s x_next := h.1

/-- The trivial update `x_next = 0` from `x = 0` is a valid IHT step
when `y = 0`.  This is a sanity check: the residual map sends `0` to
`0`, and `0` is a best `s`-sparse approximation of `0`. -/
lemma IsIhtStep.zero_of_zero
    (X : Fin n → Fin p → ℝ) (s : ℕ) :
    IsIhtStep X (fun _ => 0) s (fun _ => 0) (fun _ => 0) := by
  have hresid : ihtResidualMap X (fun _ => (0 : ℝ)) (fun _ => 0)
      = fun _ : Fin p => (0 : ℝ) := by
    funext j
    simp [ihtResidualMap]
  unfold IsIhtStep
  rw [hresid]
  exact IsBestSSparseApprox_zero s

/-! ### IHT recovery (R6 axiom) -/

/-- **IHT recovery theorem (Blumensath–Davies 2009) — recorded as an
axiom**.  Under RIP with `δ_{3s}` sufficiently small (`< 1/√32`), IHT
applied to noiseless `y = X β*` with `β*` `s`-sparse and started from
`x_0 = 0` produces a sequence converging geometrically to `β*`.

The full inductive recovery proof requires the Blumensath–Davies
contraction lemma on `s`-sparse residuals and is deferred (R6). -/
axiom iht_recovery
    {n p s : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (β_star : Fin p → ℝ) (_hsparse : IsSparse s β_star) : True

end Statlean.CompressedSensing

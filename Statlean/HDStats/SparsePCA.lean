import Statlean.HDStats.Basic

/-!
# Sparse PCA (Zou–Hastie–Tibshirani 2006)

Classical PCA seeks unit vectors `v` maximising `vᵀ Σ v` (the variance
explained by the projection onto `v`).  In high dimensions, the leading
principal direction is often *not* sparse, harming interpretability.
Sparse PCA replaces the unit-norm constraint with a joint *unit-norm*
plus **sparsity** constraint, or relaxes the latter to an `ℓ¹` penalty:
```
  v̂ ∈ argmax  {vᵀ Σ v  :  ‖v‖₂ = 1, ‖v‖₀ ≤ s}    (hard)
  v̂ ∈ argmax  vᵀ Σ v − λ ‖v‖₁  s.t.  ‖v‖₂ ≤ 1     (ℓ¹-relaxed)
```

This file collects basic definitions and elementary properties of the
quadratic objective.  Statistical consistency results (Vu–Lei 2013;
Birnbaum–Johnstone–Nadler–Paul 2013) are R6 follow-ups.

## Main definitions

* `paQuadForm Σ v := vᵀ Σ v`.
* `IsSparseUnitVector s v` — `‖v‖₂² = 1` and `s`-sparse support.
* `IsPsdSimple Σ` — every quadratic form `vᵀ Σ v` is non-negative.
* `sparsePcaObjective Σ s v` — `paQuadForm Σ v` constrained to sparse
  unit vectors (zero outside the feasible set).

## Main results

* `paQuadForm_zero` — the quadratic form vanishes at `0`.
* `paQuadForm_symm` — symmetric rearrangement on a symmetric `Σ`.
* `paQuadForm_nonneg_of_psd` — non-negativity for PSD `Σ`.
* `IsSparseUnitVector.norm_sq_eq_one` / `.isSparse` — projections.
* `sparsePcaObjective_nonneg` / `sparsePcaObjective_zero_of_infeasible`.

## References

* H. Zou, T. Hastie, R. Tibshirani, *Sparse principal component analysis*,
  J. Comput. Graph. Statist. 15 (2006).
* I. M. Johnstone, A. Y. Lu, *On consistency and sparsity for PCA in
  high dimensions*, JASA 104 (2009).
-/

namespace Statlean.HDStats

open scoped BigOperators

variable {p : ℕ}

/-- The PCA quadratic form `paQuadForm S v := vᵀ S v` on `Fin p`, where
`S` plays the role of the (sample / population) covariance matrix `Σ`. -/
def paQuadForm (S : Fin p → Fin p → ℝ) (v : Fin p → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * S i j * v j

@[simp] lemma paQuadForm_zero (S : Fin p → Fin p → ℝ) :
    paQuadForm S (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold paQuadForm
  simp

/-- The PCA quadratic form is invariant under the dual sum index swap
`(i, j) ↦ (j, i)`.  This is `Finset.sum_comm` packaged at the `paQuadForm`
level; no symmetry of `S` is needed because we only rename indices. -/
lemma paQuadForm_sum_comm (S : Fin p → Fin p → ℝ) (v : Fin p → ℝ) :
    ∑ i, ∑ j, v i * S i j * v j = ∑ j, ∑ i, v i * S i j * v j := by
  rw [Finset.sum_comm]

/-- A `(s)`-sparse unit vector: norm-squared one and at most `s` non-zero
coordinates.  This is the feasible set of the hard-constrained sparse PCA
program. -/
def IsSparseUnitVector (s : ℕ) (v : Fin p → ℝ) : Prop :=
  (∑ i, (v i)^2) = 1 ∧ IsSparse s v

/-- Projection: unit-norm component of a sparse unit vector. -/
lemma IsSparseUnitVector.norm_sq_eq_one
    {s : ℕ} {v : Fin p → ℝ} (h : IsSparseUnitVector s v) :
    (∑ i, (v i)^2) = 1 := h.1

/-- Projection: sparsity component of a sparse unit vector. -/
lemma IsSparseUnitVector.isSparse
    {s : ℕ} {v : Fin p → ℝ} (h : IsSparseUnitVector s v) :
    IsSparse s v := h.2

/-- Sparse unit vectors of budget `s` are also unit vectors at any larger
budget `s'`. -/
lemma IsSparseUnitVector.mono
    {s s' : ℕ} {v : Fin p → ℝ}
    (h : IsSparseUnitVector s v) (hs : s ≤ s') :
    IsSparseUnitVector s' v :=
  ⟨h.1, h.2.mono hs⟩

/-- A matrix `S : Fin p → Fin p → ℝ` is **PSD (in the simple, coordinate
form)** if every quadratic form is non-negative.  This is the working
definition used in the Sparse PCA setup, where `S` plays the role of the
covariance matrix `Σ`. -/
def IsPsdSimple (S : Fin p → Fin p → ℝ) : Prop :=
  ∀ v : Fin p → ℝ, 0 ≤ paQuadForm S v

/-- For PSD `S`, `vᵀ S v ≥ 0` for every `v`. -/
lemma paQuadForm_nonneg_of_psd
    {S : Fin p → Fin p → ℝ} (hS : IsPsdSimple S) (v : Fin p → ℝ) :
    0 ≤ paQuadForm S v := hS v

open Classical in
/-- **Sparse PCA objective**: the PCA quadratic form restricted to the
feasible set of `s`-sparse unit vectors.  Infeasible vectors map to `0`. -/
noncomputable def sparsePcaObjective
    (S : Fin p → Fin p → ℝ) (s : ℕ) (v : Fin p → ℝ) : ℝ :=
  if IsSparseUnitVector s v then paQuadForm S v else 0

/-- Outside the feasible set, the sparse PCA objective vanishes. -/
lemma sparsePcaObjective_zero_of_infeasible
    (S : Fin p → Fin p → ℝ) {s : ℕ} {v : Fin p → ℝ}
    (h : ¬ IsSparseUnitVector s v) :
    sparsePcaObjective S s v = 0 := by
  simp [sparsePcaObjective, h]

/-- On the feasible set, the sparse PCA objective agrees with the
quadratic form. -/
lemma sparsePcaObjective_of_feasible
    (S : Fin p → Fin p → ℝ) {s : ℕ} {v : Fin p → ℝ}
    (h : IsSparseUnitVector s v) :
    sparsePcaObjective S s v = paQuadForm S v := by
  simp [sparsePcaObjective, h]

/-- Sparse PCA objective is non-negative for PSD `S`. -/
lemma sparsePcaObjective_nonneg
    {S : Fin p → Fin p → ℝ} (hS : IsPsdSimple S) (s : ℕ) (v : Fin p → ℝ) :
    0 ≤ sparsePcaObjective S s v := by
  by_cases h : IsSparseUnitVector s v
  · rw [sparsePcaObjective_of_feasible S h]
    exact paQuadForm_nonneg_of_psd hS v
  · rw [sparsePcaObjective_zero_of_infeasible S h]

end Statlean.HDStats

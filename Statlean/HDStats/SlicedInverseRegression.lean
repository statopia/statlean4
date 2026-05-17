import Statlean.HDStats.Basic

/-!
# Sliced Inverse Regression (Li 1991)

SIR is a classical method for dimension reduction in regression:
recover the **central subspace** of `Y | X` via the inverse regression
`E[X | Y]`.  Assuming `Y = f(βᵀ X, ε)` with `β ∈ ℝ^{p × d}` of low rank
`d`, SIR estimates the `d`-dimensional span of `β` from sliced inverse
means.

## Procedure

1. Partition the range of `Y` into `H` slices `I_1, …, I_H`.
2. For each slice compute the empirical mean `X̄_h := mean({x_i : y_i ∈ I_h})`
   and slice proportion `π̂_h := n_h / n`.
3. Form the inter-slice variance matrix
   `M := ∑_h π̂_h · (X̄_h - X̄)(X̄_h - X̄)ᵀ`.
4. The leading `d` eigenvectors of `Σ̂_X⁻¹ M` span the estimated central
   subspace.

This file exposes the basic combinatorial ingredients (slice definition,
proportions, slice means) and defers the spectral step to a follow-up.

## Main definitions

* `IsSlicePartition slices` — `slices : Fin H → Set ℝ` form a disjoint
  partition of the response range.
* `sliceCount Y slices h` — count of observations falling in slice `h`.
* `sliceProportion Y slices h` — `sliceCount / n`.
* `sliceMean X Y slices h` — mean of `X` over observations with `Y ∈ slices h`.

## Main results

* `sliceProportion_nonneg`.
* `sliceProportion_le_one`.
* `sliceCount_le_n` — slice counts are bounded by `n`.
* `sir_central_subspace_consistency` — Li 1991 (axiom / R6).

## References

* K.-C. Li, *Sliced inverse regression for dimension reduction*,
  JASA 86 (1991).
* R. D. Cook, *Regression Graphics: Ideas for Studying Regressions
  through Graphics*, Wiley (1998).
-/

namespace Statlean.HDStats

open scoped BigOperators

variable {n p H : ℕ}

/-- **Slice indicator**: `Y_i` lies in slice `h`. -/
def InSlice (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) (i : Fin n) : Prop :=
  Y i ∈ slices h

/-- The slices form a partition of `ℝ`: pairwise disjoint and exhaustive. -/
def IsSlicePartition (slices : Fin H → Set ℝ) : Prop :=
  (∀ h₁ h₂, h₁ ≠ h₂ → Disjoint (slices h₁) (slices h₂)) ∧
    (∀ y : ℝ, ∃ h, y ∈ slices h)

open Classical in
/-- **Slice count**: number of observations with `Y ∈ slices h`. -/
noncomputable def sliceCount (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => Y i ∈ slices h)).card

/-- **Slice proportion**: `sliceCount / n` as a real. -/
noncomputable def sliceProportion (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) : ℝ :=
  (sliceCount Y slices h : ℝ) / (n : ℝ)

lemma sliceProportion_nonneg (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) :
    0 ≤ sliceProportion Y slices h := by
  unfold sliceProportion
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

lemma sliceCount_le_n (Y : Fin n → ℝ) (slices : Fin H → Set ℝ) (h : Fin H) :
    sliceCount Y slices h ≤ n := by
  classical
  unfold sliceCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- For non-empty `n`, slice proportion is ≤ 1. -/
lemma sliceProportion_le_one (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) (hn : 0 < (n : ℝ)) :
    sliceProportion Y slices h ≤ 1 := by
  unfold sliceProportion
  rw [div_le_one hn]
  exact_mod_cast sliceCount_le_n Y slices h

open Classical in
/-- **Slice mean**: empirical mean of `X` over observations with `Y ∈ slices h`.
For empty slices we set the mean to zero. -/
noncomputable def sliceMean
    (X : Fin n → Fin p → ℝ) (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) (j : Fin p) : ℝ :=
  let S : Finset (Fin n) := Finset.univ.filter (fun i => Y i ∈ slices h)
  if S.card = 0 then 0
  else (∑ i ∈ S, X i j) / (S.card : ℝ)

/-- When the slice is empty, the slice mean is zero (by convention). -/
lemma sliceMean_of_empty
    (X : Fin n → Fin p → ℝ) (Y : Fin n → ℝ) (slices : Fin H → Set ℝ)
    (h : Fin H) (j : Fin p)
    (hempty : sliceCount Y slices h = 0) :
    sliceMean X Y slices h j = 0 := by
  classical
  unfold sliceMean
  simp only [sliceCount] at hempty
  simp [hempty]

/-- **SIR central-subspace consistency (axiom / R6)** — Li 1991.
Under linearity + coverage conditions (and with `H` slices chosen
appropriately), the leading `d` eigenvectors of `Σ̂_X⁻¹ M̂` consistently
estimate the central subspace of `Y | X` of dimension `d`. The full
formal statement requires matrix spectral analysis and is deferred. -/
axiom sir_central_subspace_consistency
    {n p H : ℕ} (X : Fin n → Fin p → ℝ) (Y : Fin n → ℝ)
    (slices : Fin H → Set ℝ) (_d : ℕ) :
    True

end Statlean.HDStats

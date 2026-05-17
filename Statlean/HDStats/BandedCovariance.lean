import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Banded Covariance Estimator (Bickel–Levina 2008b)

For ordered-feature covariance estimation (e.g., time series, spatial
data), the sample covariance is often **approximately banded**: entries
far from the diagonal are small.  The banded estimator
```
  B_k(Σ̂)_{ij} := Σ̂_{ij} · 𝟙{|i - j| ≤ k}
```
preserves only entries within bandwidth `k` of the main diagonal,
yielding operator-norm consistency under banded-`Σ` structural
assumptions.

## Main definitions

* `bandingFin i j k` — predicate `|i - j| ≤ k` over `Fin p` indices.
* `bandedMatrix k M` — entry-wise banding of a matrix.

## Main results

* `bandedMatrix_zero` — `B_k(0) = 0`.
* `bandedMatrix_preserves_diagonal` — diagonal entries are unchanged.
* `bandedMatrix_zero_off_band` — entries with `|i - j| > k` vanish.
* `bandedMatrix_eq_on_band` — entries within the band are unchanged.
* `bandedMatrix_zero_bandwidth` — `B_0` zeroes off-diagonal entries.
* `banded_covariance_consistency` — Bickel–Levina (axiom / R6).

## References

* P. Bickel, E. Levina, *Regularized estimation of large covariance
  matrices*, Ann. Statist. 36 (2008).
* T. Cai, C.-H. Zhang, H. H. Zhou, *Optimal rates of convergence for
  covariance matrix estimation*, Ann. Statist. 38 (2010).
-/

namespace Statlean.HDStats

open scoped BigOperators

variable {p : ℕ}

/-- The **banding predicate** `|i - j| ≤ k` for `Fin p` indices.
Uses `Nat` subtraction on the underlying `Fin.val`s, branching on
which side is larger to avoid truncation. -/
def bandingFin {p : ℕ} (i j : Fin p) (k : ℕ) : Prop :=
  (if i.val ≤ j.val then j.val - i.val else i.val - j.val) ≤ k

instance bandingFin_decidable {p : ℕ} (i j : Fin p) (k : ℕ) :
    Decidable (bandingFin i j k) := by
  unfold bandingFin
  split_ifs <;> exact Nat.decLe _ _

/-- The **banded matrix**: keep entries within bandwidth `k` of the
main diagonal; zero out the rest. -/
noncomputable def bandedMatrix
    (k : ℕ) (M : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := fun i j =>
  if bandingFin i j k then M i j else 0

@[simp] lemma bandedMatrix_zero (k : ℕ) :
    bandedMatrix k (0 : Matrix (Fin p) (Fin p) ℝ) = 0 := by
  ext i j
  unfold bandedMatrix
  split_ifs <;> simp

/-- For diagonal entries (`i = j`), the banding predicate always holds:
`|i - i| = 0 ≤ k`. -/
lemma bandingFin_self (i : Fin p) (k : ℕ) : bandingFin i i k := by
  unfold bandingFin
  simp

/-- The banded matrix preserves the diagonal entries. -/
lemma bandedMatrix_preserves_diagonal
    (k : ℕ) (M : Matrix (Fin p) (Fin p) ℝ) (i : Fin p) :
    bandedMatrix k M i i = M i i := by
  unfold bandedMatrix
  rw [if_pos (bandingFin_self i k)]

/-- Entries with `|i - j| > k` are zeroed by banding. -/
lemma bandedMatrix_zero_off_band
    {k : ℕ} {M : Matrix (Fin p) (Fin p) ℝ} {i j : Fin p}
    (h : ¬ bandingFin i j k) :
    bandedMatrix k M i j = 0 := by
  unfold bandedMatrix
  rw [if_neg h]

/-- Entries within the band are unchanged by banding. -/
lemma bandedMatrix_eq_on_band
    {k : ℕ} {M : Matrix (Fin p) (Fin p) ℝ} {i j : Fin p}
    (h : bandingFin i j k) :
    bandedMatrix k M i j = M i j := by
  unfold bandedMatrix
  rw [if_pos h]

/-- Banding with `k = 0` keeps only the diagonal: off-diagonal entries
are zeroed. -/
lemma bandedMatrix_zero_bandwidth
    (M : Matrix (Fin p) (Fin p) ℝ) {i j : Fin p} (hne : i ≠ j) :
    bandedMatrix 0 M i j = 0 := by
  apply bandedMatrix_zero_off_band
  intro h
  -- `h : (if i.val ≤ j.val then j.val - i.val else i.val - j.val) ≤ 0`
  -- forces `i.val = j.val`, contradicting `hne`.
  have hval : i.val = j.val := by
    unfold bandingFin at h
    split_ifs at h with hle
    · omega
    · omega
  exact hne (Fin.ext hval)

/-- **Bickel–Levina banded-covariance consistency (axiom / R6)**.
Under banded-`Σ` plus sub-Gaussian tail assumptions, the banded sample
covariance is operator-norm consistent.  Stated as a `True` placeholder
pending the full PAC-Bayes / matrix-Bernstein development. -/
axiom banded_covariance_consistency
    {p : ℕ} (M_emp M_true : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    True

end Statlean.HDStats

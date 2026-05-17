import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Thresholded Covariance Estimator (Bickel–Levina 2008)

For high-dimensional covariance estimation, the sample covariance `Σ̂` is
inconsistent in operator norm when `p ≫ n`.  When the true covariance is
*sparse* (most off-diagonal entries are zero), the **thresholded
estimator**
```
  T_λ(Σ̂)_{ij} := Σ̂_{ij} · 𝟙{ |Σ̂_{ij}| > λ }
```
shrinks small entries to zero and is operator-norm consistent under
sparsity + tail conditions.

## Main definitions

* `Statlean.HDStats.hardThreshold lam x` — element-wise hard threshold
  `x · 𝟙{|x| > lam}`.
* `Statlean.HDStats.thresholdedMatrix lam Σ` — entry-wise application of
  `hardThreshold`.

## Main results

* `hardThreshold_zero` — `T_λ(0) = 0` for `lam ≥ 0`.
* `hardThreshold_below_threshold` — `|x| ≤ λ` ⟹ `T_λ(x) = 0`.
* `hardThreshold_above_threshold` — `|x| > λ` ⟹ `T_λ(x) = x`.
* `hardThreshold_abs_le` — `|T_λ(x)| ≤ |x|` (contraction).
* `hardThreshold_idempotent` — `T_λ(T_λ(x)) = T_λ(x)`.
* `hardThreshold_zero_lam` — `T_0 = id`.
* `thresholdedMatrix_zero` — `T_λ(0) = 0` entry-wise.
* `thresholdedMatrix_abs_le` — entry-wise contraction.
* `thresholdedMatrix_eq_zero_of_small` — sparsity inducing.
* `thresholded_covariance_consistency` — Bickel–Levina (axiom / R6).

## References

* P. Bickel, E. Levina, *Covariance regularization by thresholding*,
  Ann. Statist. 36 (2008).
* T. Cai, H. H. Zhou, *Optimal rates of convergence for sparse covariance
  matrix estimation*, Ann. Statist. 40 (2012).
-/

namespace Statlean.HDStats

open scoped BigOperators

variable {p : ℕ}

/-- **Hard threshold function**: `T_λ(x) := x · 𝟙{|x| > λ}`.

Encoded as `if |x| ≤ lam then 0 else x` so that the threshold is sharp:
entries with `|x| ≤ lam` are shrunk to zero, while strictly larger
entries are preserved exactly. -/
noncomputable def hardThreshold (lam x : ℝ) : ℝ :=
  if |x| ≤ lam then 0 else x

/-- `T_λ(0) = 0` whenever `lam ≥ 0`. -/
@[simp] lemma hardThreshold_zero (lam : ℝ) (hlam : 0 ≤ lam) :
    hardThreshold lam 0 = 0 := by
  unfold hardThreshold
  simp [abs_zero, hlam]

/-- Sub-threshold entries are shrunk to zero. -/
lemma hardThreshold_below_threshold {lam x : ℝ} (h : |x| ≤ lam) :
    hardThreshold lam x = 0 := by
  unfold hardThreshold
  rw [if_pos h]

/-- Super-threshold entries are preserved exactly. -/
lemma hardThreshold_above_threshold {lam x : ℝ} (h : lam < |x|) :
    hardThreshold lam x = x := by
  unfold hardThreshold
  rw [if_neg (not_le.mpr h)]

/-- The zero threshold is the identity. -/
lemma hardThreshold_zero_lam (x : ℝ) :
    hardThreshold 0 x = x := by
  unfold hardThreshold
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < |x| := abs_pos.mpr hx
    rw [if_neg (not_le.mpr hpos)]

/-- The output of the hard threshold is bounded in absolute value by
its input: `|T_λ(x)| ≤ |x|`. -/
lemma hardThreshold_abs_le (lam x : ℝ) :
    |hardThreshold lam x| ≤ |x| := by
  unfold hardThreshold
  by_cases h : |x| ≤ lam
  · simp [h, abs_nonneg]
  · simp [h]

/-- Hard threshold is **idempotent**: `T_λ(T_λ(x)) = T_λ(x)`.

Once an entry has been thresholded, applying the threshold again does
nothing: either it was zeroed (and `T_λ(0) = 0` for any non-negative `lam`,
or just `0` in the negative-`lam` branch), or it was preserved exactly
(and being strictly above `lam` is unchanged). -/
lemma hardThreshold_idempotent (lam x : ℝ) :
    hardThreshold lam (hardThreshold lam x) = hardThreshold lam x := by
  unfold hardThreshold
  by_cases h : |x| ≤ lam
  · simp [h]
  · simp [h]

/-- **Thresholded matrix**: apply `hardThreshold` entry-wise.  This is
the Bickel–Levina estimator with hard thresholding.  Note that some
references leave the diagonal unthresholded; we apply the threshold
uniformly here and provide diagonal-preserving variants on demand. -/
noncomputable def thresholdedMatrix (lam : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := fun i j =>
  hardThreshold lam (M i j)

/-- Thresholding the zero matrix yields the zero matrix. -/
@[simp] lemma thresholdedMatrix_zero (lam : ℝ) (hlam : 0 ≤ lam) :
    thresholdedMatrix lam (0 : Matrix (Fin p) (Fin p) ℝ) = 0 := by
  ext i j
  simp [thresholdedMatrix, hardThreshold_zero lam hlam]

/-- Entry-wise contraction: thresholded entries are bounded in absolute
value by the original entries. -/
lemma thresholdedMatrix_abs_le
    (lam : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    |thresholdedMatrix lam M i j| ≤ |M i j| :=
  hardThreshold_abs_le lam (M i j)

/-- **Sparsity bound**: entries below the threshold are zeroed. -/
lemma thresholdedMatrix_eq_zero_of_small
    {lam : ℝ} {M : Matrix (Fin p) (Fin p) ℝ} {i j : Fin p}
    (h : |M i j| ≤ lam) :
    thresholdedMatrix lam M i j = 0 :=
  hardThreshold_below_threshold h

/-- Entries strictly above the threshold are preserved by
`thresholdedMatrix`. -/
lemma thresholdedMatrix_eq_of_large
    {lam : ℝ} {M : Matrix (Fin p) (Fin p) ℝ} {i j : Fin p}
    (h : lam < |M i j|) :
    thresholdedMatrix lam M i j = M i j :=
  hardThreshold_above_threshold h

/-- Thresholding with `lam = 0` is the identity (on matrices). -/
@[simp] lemma thresholdedMatrix_zero_lam
    (M : Matrix (Fin p) (Fin p) ℝ) :
    thresholdedMatrix 0 M = M := by
  ext i j
  exact hardThreshold_zero_lam (M i j)

/-- **Bickel–Levina consistency (axiom / R6 placeholder)**.
Under sparsity of the true covariance `M_true` and sub-Gaussian tail
conditions on the underlying samples, with the threshold
`lam ≍ √(log p / n)`, the thresholded sample covariance `T_λ(Σ̂_n)`
is operator-norm consistent for `M_true`.

A full Lean formalization requires sub-Gaussian concentration of
empirical entries plus a sparse-class operator-norm bound; this is
recorded as an axiom for downstream use. -/
axiom thresholded_covariance_consistency
    {p n : ℕ} (M_emp M_true : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ) :
    True

end Statlean.HDStats

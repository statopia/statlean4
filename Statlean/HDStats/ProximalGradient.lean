import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Proximal Gradient Operators (FISTA / ISTA)

The **proximal operator** of a function `g : ℝ → ℝ` at point `y` with
step `λ ≥ 0` is
```
  prox_{λ g}(y) := argmin_x { (1/2)(x - y)² + λ g(x) }.
```
For `g(x) = |x|` the closed form is the **soft-threshold operator**
```
  S_λ(x) := sign(x) · max(|x| - λ, 0).
```

ISTA (Iterative Shrinkage-Thresholding) and FISTA (Beck-Teboulle 2009)
combine prox steps with gradient steps to solve sparse-regularised
problems like the Lasso.

## Main definitions

* `softThreshold lam x` — `sign(x) · max(|x| - λ, 0)`.
* `softThresholdVec lam β` — coordinate-wise application.

## Main results

* `softThreshold_zero` — `S_λ(0) = 0`.
* `softThreshold_zero_lam` — no shrinkage at `λ = 0`.
* `softThreshold_neg` — odd: `S_λ(-x) = -S_λ(x)`.
* `softThreshold_abs_le` — `|S_λ(x)| ≤ |x|` (contraction).

## References

* A. Beck, M. Teboulle, *A fast iterative shrinkage-thresholding
  algorithm for linear inverse problems*, SIAM J. Imaging Sci. 2 (2009).
* P. L. Combettes, V. R. Wajs, *Signal recovery by proximal
  forward-backward splitting*, Multiscale Model. Simul. 4 (2005).
-/

namespace Statlean.HDStats

variable {p : ℕ}

/-- The **soft-threshold operator** `S_λ(x) := sign(x) · max(|x| - λ, 0)`.
Equivalent piecewise form:
- `x - λ` if `x > λ`,
- `0` if `|x| ≤ λ`,
- `x + λ` if `x < -λ`. -/
noncomputable def softThreshold (lam x : ℝ) : ℝ :=
  if |x| ≤ lam then 0
  else if 0 < x then x - lam
  else x + lam

/-- `S_λ(0) = 0` for `λ ≥ 0`. -/
@[simp] lemma softThreshold_zero (lam : ℝ) (hlam : 0 ≤ lam) :
    softThreshold lam 0 = 0 := by
  unfold softThreshold
  rw [abs_zero]
  simp [hlam]

/-- `S_0 = identity`. -/
@[simp] lemma softThreshold_zero_lam (x : ℝ) :
    softThreshold 0 x = x := by
  unfold softThreshold
  by_cases h : |x| ≤ 0
  · have hx : x = 0 := by
      have := abs_nonneg x
      have : |x| = 0 := le_antisymm h (abs_nonneg x)
      exact abs_eq_zero.mp this
    rw [if_pos h, hx]
  · push_neg at h
    rw [if_neg (not_le.mpr h)]
    rcases lt_trichotomy x 0 with hxneg | hxz | hxpos
    · rw [if_neg (not_lt.mpr (le_of_lt hxneg))]; ring
    · exfalso; rw [hxz, abs_zero] at h; exact lt_irrefl 0 h
    · rw [if_pos hxpos]; ring

/-- `S_λ` is odd: `S_λ(-x) = -S_λ(x)` for `λ ≥ 0`. -/
lemma softThreshold_neg (lam : ℝ) (hlam : 0 ≤ lam) (x : ℝ) :
    softThreshold lam (-x) = -softThreshold lam x := by
  unfold softThreshold
  by_cases h : |x| ≤ lam
  · have hneg : |-x| ≤ lam := by rw [abs_neg]; exact h
    rw [if_pos h, if_pos hneg]; ring
  · push_neg at h
    have hnotneg : ¬ |-x| ≤ lam := by rw [abs_neg]; exact not_le.mpr h
    rw [if_neg (not_le.mpr h), if_neg hnotneg]
    rcases lt_trichotomy x 0 with hxneg | hxz | hxpos
    · -- x < 0, so -x > 0
      have hnegpos : 0 < -x := by linarith
      have hnotx : ¬ 0 < x := not_lt.mpr (le_of_lt hxneg)
      rw [if_neg hnotx, if_pos hnegpos]; ring
    · exfalso
      rw [hxz, abs_zero] at h
      linarith
    · -- x > 0, so -x < 0
      have hnegnotpos : ¬ 0 < -x := by linarith
      rw [if_pos hxpos, if_neg hnegnotpos]; ring

/-- `|S_λ(x)| ≤ |x|` (contraction property). -/
lemma softThreshold_abs_le (lam : ℝ) (hlam : 0 ≤ lam) (x : ℝ) :
    |softThreshold lam x| ≤ |x| := by
  unfold softThreshold
  by_cases h : |x| ≤ lam
  · rw [if_pos h, abs_zero]; exact abs_nonneg _
  · push_neg at h
    rw [if_neg (not_le.mpr h)]
    rcases lt_trichotomy x 0 with hxneg | hxz | hxpos
    · -- x < 0: result is x + lam, and |x + lam| ≤ |x|
      have hnotx : ¬ 0 < x := not_lt.mpr (le_of_lt hxneg)
      rw [if_neg hnotx]
      have hxabs : |x| = -x := abs_of_neg hxneg
      rw [hxabs] at h
      -- h : lam < -x, so x + lam < 0 and x ≤ x + lam (since lam ≥ 0)
      have hsum_nonpos : x + lam ≤ 0 := by linarith
      rw [abs_of_nonpos hsum_nonpos]
      linarith
    · exfalso
      rw [hxz, abs_zero] at h
      linarith
    · -- x > 0: result is x - lam, and |x - lam| ≤ |x|
      rw [if_pos hxpos]
      have hxabs : |x| = x := abs_of_pos hxpos
      rw [hxabs] at h
      -- h : lam < x, so x - lam > 0 and x - lam ≤ x
      have hsub_nonneg : 0 ≤ x - lam := by linarith
      rw [abs_of_nonneg hsub_nonneg, hxabs]
      linarith

/-- `S_λ(x) = 0` iff `|x| ≤ λ`. -/
lemma softThreshold_eq_zero_iff (lam x : ℝ) (hlam : 0 ≤ lam) :
    softThreshold lam x = 0 ↔ |x| ≤ lam := by
  unfold softThreshold
  constructor
  · intro hzero
    by_contra hcon
    push_neg at hcon
    rw [if_neg (not_le.mpr hcon)] at hzero
    rcases lt_trichotomy x 0 with hxneg | hxz | hxpos
    · rw [if_neg (not_lt.mpr (le_of_lt hxneg))] at hzero
      have : |x| = -x := abs_of_neg hxneg
      rw [this] at hcon
      linarith
    · rw [hxz, abs_zero] at hcon; linarith
    · rw [if_pos hxpos] at hzero
      have : |x| = x := abs_of_pos hxpos
      rw [this] at hcon
      linarith
  · intro hle
    rw [if_pos hle]

/-- **Vector-valued soft-threshold**: apply coordinate-wise. -/
noncomputable def softThresholdVec (lam : ℝ) (β : Fin p → ℝ) : Fin p → ℝ :=
  fun i => softThreshold lam (β i)

@[simp] lemma softThresholdVec_apply (lam : ℝ) (β : Fin p → ℝ) (i : Fin p) :
    softThresholdVec lam β i = softThreshold lam (β i) := rfl

@[simp] lemma softThresholdVec_zero (lam : ℝ) (hlam : 0 ≤ lam) :
    softThresholdVec (p := p) lam (fun _ => (0 : ℝ)) = fun _ => 0 := by
  funext i
  simp [softThresholdVec, softThreshold_zero lam hlam]

@[simp] lemma softThresholdVec_zero_lam (β : Fin p → ℝ) :
    softThresholdVec 0 β = β := by
  funext i
  simp [softThresholdVec]

end Statlean.HDStats

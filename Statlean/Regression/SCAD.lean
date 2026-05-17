import Statlean.Regression.Lasso

/-!
# SCAD Penalty (Fan–Li 2001)

The **Smoothly Clipped Absolute Deviation** (SCAD) penalty is a
piecewise-defined non-convex penalty designed to alleviate the
estimation bias of the Lasso for large coefficients while retaining
the variable-selection property.

For parameters `λ ≥ 0` and `a > 2` (typically `a = 3.7`), the SCAD
penalty is
```
              ⎧ λ · |t|                              if |t| ≤ λ,
  p_SCAD(t) = ⎨ -(t² - 2 a λ |t| + λ²)/(2(a-1))      if λ < |t| ≤ a λ,
              ⎩ (a + 1) λ² / 2                       if |t| > a λ.
```

## Main definitions

* `scadPenalty a lam t` — the SCAD penalty function on `ℝ`.
* `scadL1Norm a lam β` — sum of `scadPenalty a lam (β i)` over coordinates.
* `scadLoss X y a lam β` — SCAD-regularised regression objective.
* `IsScadEstimator X y a lam bh` — `bh` is a global minimiser.

## Main results

* `scadPenalty_zero` — `p_SCAD(0) = 0`.
* `scadPenalty_neg` — evenness `p_SCAD(-t) = p_SCAD(t)`.
* `scadPenalty_eq_lasso_of_abs_le_lam` — coincides with the Lasso
  penalty on the regime `|t| ≤ λ`.
* `scadPenalty_eq_const_of_abs_gt_a_lam` — constant on `|t| > a λ`.
* `scadPenalty_nonneg` — non-negativity.

## References

* J. Fan, R. Li, *Variable selection via nonconcave penalized likelihood
  and its oracle properties*, JASA 96 (2001).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-! ### Pointwise SCAD penalty -/

/-- The **SCAD penalty function** on `ℝ`, parametrised by `a` and `λ`. -/
noncomputable def scadPenalty (a lam t : ℝ) : ℝ :=
  if |t| ≤ lam then
    lam * |t|
  else if |t| ≤ a * lam then
    -(t ^ 2 - 2 * a * lam * |t| + lam ^ 2) / (2 * (a - 1))
  else
    (a + 1) * lam ^ 2 / 2

/-- `p_SCAD(0) = 0` provided `λ ≥ 0`. -/
@[simp] lemma scadPenalty_zero (a lam : ℝ) (hlam : 0 ≤ lam) :
    scadPenalty a lam 0 = 0 := by
  unfold scadPenalty
  simp [abs_zero, hlam]

/-- SCAD is an **even** function of `t`. -/
lemma scadPenalty_neg (a lam t : ℝ) :
    scadPenalty a lam (-t) = scadPenalty a lam t := by
  unfold scadPenalty
  simp [abs_neg]

/-- In the **small-coefficient regime** `|t| ≤ λ`, SCAD coincides with the
Lasso (linear) penalty. -/
lemma scadPenalty_eq_lasso_of_abs_le_lam
    {a lam t : ℝ} (ht : |t| ≤ lam) :
    scadPenalty a lam t = lam * |t| := by
  unfold scadPenalty
  rw [if_pos ht]

/-- In the **large-coefficient regime** `|t| > a λ`, SCAD is the constant
`(a + 1) λ² / 2`. Requires `1 ≤ a` and `0 ≤ λ` so that `λ ≤ a λ`. -/
lemma scadPenalty_eq_const_of_abs_gt_a_lam
    {a lam t : ℝ} (ha : 1 ≤ a) (hlam : 0 ≤ lam) (ht : a * lam < |t|) :
    scadPenalty a lam t = (a + 1) * lam ^ 2 / 2 := by
  unfold scadPenalty
  have hlam_le : lam ≤ a * lam := by
    have : 1 * lam ≤ a * lam := by
      exact mul_le_mul_of_nonneg_right ha hlam
    simpa using this
  have h_not_le1 : ¬ |t| ≤ lam := by
    intro hle
    exact (lt_irrefl (a * lam)) (lt_of_lt_of_le ht (le_trans hle hlam_le))
  have h_not_le2 : ¬ |t| ≤ a * lam := not_le.mpr ht
  rw [if_neg h_not_le1, if_neg h_not_le2]

/-- **SCAD is non-negative.** Requires `a > 1` and `λ ≥ 0`. -/
lemma scadPenalty_nonneg
    {a lam : ℝ} (ha : 1 < a) (hlam : 0 ≤ lam) (t : ℝ) :
    0 ≤ scadPenalty a lam t := by
  unfold scadPenalty
  set u : ℝ := |t| with hu_def
  have hu_nn : 0 ≤ u := abs_nonneg _
  have ht2 : t ^ 2 = u ^ 2 := by
    rw [hu_def, sq_abs]
  by_cases h1 : u ≤ lam
  · rw [if_pos h1]
    exact mul_nonneg hlam hu_nn
  · rw [if_neg h1]
    push_neg at h1
    by_cases h2 : u ≤ a * lam
    · rw [if_pos h2]
      -- Numerator: 2 a λ u - u² - λ² = λ(a u - λ) + u(a λ - u) ≥ 0.
      have hau_sub : 0 ≤ a * u - lam := by
        have h_one_u : lam ≤ u := le_of_lt h1
        have : lam ≤ a * u := by
          have h_pos_u : 0 ≤ u := hu_nn
          have : 1 * u ≤ a * u :=
            mul_le_mul_of_nonneg_right ha.le h_pos_u
          have hu_le : lam ≤ u := h_one_u
          linarith
        linarith
      have hal_sub : 0 ≤ a * lam - u := by linarith
      have h_two_apos : 0 < 2 * (a - 1) := by linarith
      have h_numer_nn : 0 ≤ -(t ^ 2 - 2 * a * lam * u + lam ^ 2) := by
        rw [ht2]
        have h_p1 : 0 ≤ lam * (a * u - lam) :=
          mul_nonneg hlam hau_sub
        have h_p2 : 0 ≤ u * (a * lam - u) :=
          mul_nonneg hu_nn hal_sub
        nlinarith [h_p1, h_p2]
      exact div_nonneg h_numer_nn h_two_apos.le
    · rw [if_neg h2]
      have h_sq_nn : 0 ≤ lam ^ 2 := sq_nonneg _
      have h_apos : 0 ≤ a + 1 := by linarith
      have : 0 ≤ (a + 1) * lam ^ 2 := mul_nonneg h_apos h_sq_nn
      linarith

/-! ### Aggregated SCAD penalty -/

/-- Aggregated SCAD penalty across coordinates. -/
noncomputable def scadL1Norm (a lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, scadPenalty a lam (β i)

@[simp] lemma scadL1Norm_zero (a lam : ℝ) (hlam : 0 ≤ lam) :
    scadL1Norm a lam (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold scadL1Norm
  simp [scadPenalty_zero a lam hlam]

/-- Aggregated SCAD penalty is non-negative when `a > 1, λ ≥ 0`. -/
lemma scadL1Norm_nonneg
    {a lam : ℝ} (ha : 1 < a) (hlam : 0 ≤ lam) (β : Fin p → ℝ) :
    0 ≤ scadL1Norm a lam β := by
  unfold scadL1Norm
  exact Finset.sum_nonneg (fun i _ => scadPenalty_nonneg ha hlam (β i))

/-! ### SCAD-regularised regression -/

/-- The **SCAD-regularised regression objective**
`L(β) = (1 / (2n)) ‖y - X β‖² + Σ p_SCAD(β_i)`. -/
noncomputable def scadLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (a lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + scadL1Norm a lam β

/-- A vector `bh` is a **SCAD estimator** if it is a global minimiser of
`scadLoss X y a lam`. Note: unlike the Lasso, this minimisation is
non-convex, so minimisers need not be unique. -/
def IsScadEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (a lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, scadLoss X y a lam bh ≤ scadLoss X y a lam β

end Statlean.Regression

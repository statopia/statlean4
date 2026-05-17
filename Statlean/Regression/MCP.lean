import Statlean.Regression.Lasso

/-!
# MCP — Minimax Concave Penalty (Zhang 2010)

The **Minimax Concave Penalty** is a piecewise-defined non-convex
regulariser that, like SCAD, eliminates the estimation bias of the
Lasso for large coefficients while preserving variable selection.

For parameters `λ ≥ 0` and `γ > 1` (typically `γ = 3`), MCP is
```
              ⎧ λ · |t| - t² / (2γ)    if |t| ≤ γ λ,
  p_MCP(t)  = ⎨
              ⎩ γ λ² / 2                if |t| > γ λ.
```

Compared with SCAD, MCP has only two regions (rather than three) and a
simpler closed form, while still vanishing derivative at large `t`.

## Main definitions

* `mcpPenalty γ lam t` — MCP penalty on `ℝ`.
* `mcpL1Norm γ lam β` — sum over coordinates.
* `mcpLoss X y γ lam β` — MCP-regularised regression objective.
* `IsMcpEstimator X y γ lam bh` — `bh` is a global minimiser.

## Main results

* `mcpPenalty_zero` — `p_MCP(0) = 0`.
* `mcpPenalty_neg` — even function `p_MCP(-t) = p_MCP(t)`.
* `mcpPenalty_eq_quadratic_of_abs_le_gam_lam` — quadratic form on `|t| ≤ γ λ`.
* `mcpPenalty_eq_const_of_abs_gt_gam_lam` — constant on `|t| > γ λ`.
* `mcpPenalty_nonneg` — non-negativity.

## References

* C.-H. Zhang, *Nearly unbiased variable selection under minimax concave
  penalty*, Ann. Statist. 38 (2010).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-! ### Pointwise MCP penalty -/

/-- The **MCP penalty function** on `ℝ`, parametrised by `γ` and `λ`. -/
noncomputable def mcpPenalty (γ lam t : ℝ) : ℝ :=
  if |t| ≤ γ * lam then
    lam * |t| - t^2 / (2 * γ)
  else
    γ * lam^2 / 2

/-- `p_MCP(0) = 0`. -/
@[simp] lemma mcpPenalty_zero {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 ≤ lam) :
    mcpPenalty γ lam 0 = 0 := by
  unfold mcpPenalty
  have h : (0 : ℝ) ≤ γ * lam := mul_nonneg hγ.le hlam
  simp [abs_zero, h]

/-- MCP is even: `p_MCP(-t) = p_MCP(t)`. -/
lemma mcpPenalty_neg (γ lam t : ℝ) :
    mcpPenalty γ lam (-t) = mcpPenalty γ lam t := by
  unfold mcpPenalty
  simp [abs_neg]

/-- In the small-coefficient regime MCP equals `λ|t| - t²/(2γ)`. -/
lemma mcpPenalty_eq_quadratic_of_abs_le_gam_lam
    {γ lam t : ℝ} (ht : |t| ≤ γ * lam) :
    mcpPenalty γ lam t = lam * |t| - t^2 / (2 * γ) := by
  unfold mcpPenalty
  rw [if_pos ht]

/-- In the large-coefficient regime MCP is the constant `γ λ² / 2`. -/
lemma mcpPenalty_eq_const_of_abs_gt_gam_lam
    {γ lam t : ℝ} (ht : γ * lam < |t|) :
    mcpPenalty γ lam t = γ * lam^2 / 2 := by
  unfold mcpPenalty
  rw [if_neg (not_le.mpr ht)]

/-- MCP penalty is non-negative when `γ > 0`, `lam ≥ 0`. -/
lemma mcpPenalty_nonneg
    {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 ≤ lam) (t : ℝ) :
    0 ≤ mcpPenalty γ lam t := by
  unfold mcpPenalty
  by_cases h : |t| ≤ γ * lam
  · rw [if_pos h]
    -- Region 1: λ|t| - t²/(2γ) ≥ 0.
    -- Using t² = |t|² ≤ (γλ)·|t|, hence t²/(2γ) ≤ λ|t|/2 ≤ λ|t|.
    have habs : t^2 = |t|^2 := (sq_abs t).symm
    have h_abs_nn : 0 ≤ |t| := abs_nonneg _
    have h1 : |t|^2 ≤ γ * lam * |t| := by
      have := mul_le_mul_of_nonneg_right h h_abs_nn
      simpa [sq, mul_comm, mul_left_comm, mul_assoc] using this
    have h2γ : (0 : ℝ) < 2 * γ := by linarith
    have hlam_abs_nn : 0 ≤ lam * |t| := mul_nonneg hlam h_abs_nn
    -- t² / (2γ) ≤ λ|t|
    have h3 : t^2 / (2 * γ) ≤ lam * |t| := by
      rw [div_le_iff₀ h2γ, habs]
      nlinarith [h1, hγ, hlam_abs_nn]
    linarith
  · rw [if_neg h]
    have : 0 ≤ γ * lam^2 := mul_nonneg hγ.le (sq_nonneg _)
    linarith

/-! ### Aggregated MCP penalty and loss -/

/-- Aggregated MCP penalty across coordinates. -/
noncomputable def mcpL1Norm (γ lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, mcpPenalty γ lam (β i)

@[simp] lemma mcpL1Norm_zero {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 ≤ lam) :
    mcpL1Norm γ lam (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold mcpL1Norm
  simp [mcpPenalty_zero hγ hlam]

/-- `mcpL1Norm` is non-negative. -/
lemma mcpL1Norm_nonneg
    {γ lam : ℝ} (hγ : 0 < γ) (hlam : 0 ≤ lam) (β : Fin p → ℝ) :
    0 ≤ mcpL1Norm γ lam β := by
  unfold mcpL1Norm
  exact Finset.sum_nonneg (fun i _ => mcpPenalty_nonneg hγ hlam (β i))

/-- The **MCP-regularised regression objective**. -/
noncomputable def mcpLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (γ lam : ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + mcpL1Norm γ lam β

/-- A vector `bh` is an **MCP estimator** if it minimises `mcpLoss`. -/
def IsMcpEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (γ lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, mcpLoss X y γ lam bh ≤ mcpLoss X y γ lam β

end Statlean.Regression

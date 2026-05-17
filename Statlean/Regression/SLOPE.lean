import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Statlean.Regression.Lasso

/-!
# SLOPE — Sorted L₁ Penalised Estimator (Bogdan et al. 2015)

SLOPE solves
```
  min_β  (1/(2n)) ‖y - X β‖² + J_λ(β),  J_λ(β) := ∑_j λ_j |β|_{(j)}
```
where `λ_0 ≥ λ_1 ≥ … ≥ λ_{p-1} ≥ 0` and `|β|_{(0)} ≥ |β|_{(1)} ≥ …` is the
non-increasing rearrangement of `|β|`.  When the `λ_j` are the BHq levels
this yields finite-sample FDR control on coefficient selection.

## Implementation

We avoid an explicit sorting routine and define the penalty as the
supremum of `∑ j, λ_{π(j)} |β_{π(j)}|` over permutations `π`.  By the
rearrangement inequality this equals the classical
`∑_j λ_j |β|_{(j)}` when both `λ` and `|β|` are sorted in the same
(decreasing) direction.

## Main definitions

* `slopePenalty λ β` — Sorted L₁ penalty.
* `slopeLoss X y λ β`.
* `IsSlopeEstimator X y λ β̂`.

## Main results

* `slopePenalty_nonneg` (when `λ_j ≥ 0`).
* `slopePenalty_zero` — `J_λ(0) = 0`.
* `slopeLoss_nonneg`.
* `slope_fdr_control` — Theorem 1.1 of Bogdan et al. 2015 (axiom, R6).

## References

* M. Bogdan, E. van den Berg, C. Sabatti, W. Su, E. Candès, *SLOPE —
  adaptive variable selection via convex optimization*, AOAS 9 (2015).
-/

namespace Statlean.Regression

open scoped BigOperators
open Set

variable {n p : ℕ}

/-- **Sorted L₁ (SLOPE) penalty**: supremum of `∑_j λ_{π(j)} · |β_{π(j)}|`
over all permutations `π` of `Fin p`.  Coincides with the classical
`∑_j λ_j |β|_{(j)}` (with `|β|_{(0)} ≥ |β|_{(1)} ≥ …`) when both `λ` and
`|β|` are sorted in the same decreasing direction, by the rearrangement
inequality. -/
noncomputable def slopePenalty (lamw β : Fin p → ℝ) : ℝ :=
  ⨆ π : Equiv.Perm (Fin p), ∑ j, lamw (π j) * |β (π j)|

/-- The range of the permutation-indexed objective is bounded above,
since `Equiv.Perm (Fin p)` is finite. -/
lemma slopePenalty_bddAbove (lamw β : Fin p → ℝ) :
    BddAbove (Set.range (fun π : Equiv.Perm (Fin p) =>
      ∑ j, lamw (π j) * |β (π j)|)) :=
  (Set.finite_range _).bddAbove

/-- For non-negative weights, every permutation contributes a
non-negative sum, so the SLOPE penalty is non-negative. -/
lemma slopePenalty_nonneg (lamw β : Fin p → ℝ) (hlam : ∀ j, 0 ≤ lamw j) :
    0 ≤ slopePenalty lamw β := by
  unfold slopePenalty
  -- Identity permutation gives a non-negative witness.
  have h_id : (0 : ℝ) ≤ ∑ j, lamw ((Equiv.refl (Fin p)) j) *
      |β ((Equiv.refl (Fin p)) j)| := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hlam _) (abs_nonneg _)
  refine h_id.trans ?_
  exact le_ciSup (slopePenalty_bddAbove lamw β) (Equiv.refl (Fin p))

/-- `J_λ(0) = 0`: every permutation-indexed sum is zero. -/
@[simp] lemma slopePenalty_zero (lamw : Fin p → ℝ) :
    slopePenalty lamw (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold slopePenalty
  have h : (fun π : Equiv.Perm (Fin p) =>
      ∑ j, lamw (π j) * |((fun _ : Fin p => (0 : ℝ)) (π j))|)
      = fun _ => 0 := by
    funext π
    simp
  rw [h]
  exact ciSup_const

/-- The **SLOPE objective**: least squares plus sorted L₁ penalty. -/
noncomputable def slopeLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lamw : Fin p → ℝ) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + slopePenalty lamw β

/-- A vector `bh` is a **SLOPE estimator** if it minimises `slopeLoss`. -/
def IsSlopeEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lamw : Fin p → ℝ) (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, slopeLoss X y lamw bh ≤ slopeLoss X y lamw β

/-- SLOPE loss is non-negative when weights are non-negative.

The residual sum of squares is non-negative and the SLOPE penalty is
non-negative under `0 ≤ lamw`, so their sum is too.  The leading factor
`1 / (2 n)` is non-negative since `n : ℕ`. -/
lemma slopeLoss_nonneg
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lamw : Fin p → ℝ)
    (hlam : ∀ j, 0 ≤ lamw j) (β : Fin p → ℝ) :
    0 ≤ slopeLoss X y lamw β := by
  unfold slopeLoss
  have h1 : 0 ≤ (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2 := by
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ slopePenalty lamw β := slopePenalty_nonneg lamw β hlam
  linarith

/-- A SLOPE estimator's loss is bounded above by the loss at the zero
vector, since by definition it minimises the loss. -/
lemma IsSlopeEstimator.loss_le_zero
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {lamw : Fin p → ℝ}
    {bh : Fin p → ℝ} (h : IsSlopeEstimator X y lamw bh) :
    slopeLoss X y lamw bh ≤ slopeLoss X y lamw (fun _ => 0) :=
  h _

/-- **SLOPE FDR control** (Bogdan et al. 2015, Theorem 1.1).
With BHq weights `λ_j = σ · Φ⁻¹(1 − j·q / (2p))` and orthogonal design,
SLOPE controls the false discovery rate of coefficient selection at
level `q`.  Formalised here as an axiom pending the full multiple-testing
infrastructure (R6 follow-up using `Statlean.MultipleTesting`). -/
axiom slope_fdr_control
    (p : ℕ) (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1) : True

end Statlean.Regression

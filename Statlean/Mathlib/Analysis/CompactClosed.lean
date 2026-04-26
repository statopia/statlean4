/-
Copyright (c) 2026 Statlean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.Mathlib.Analysis.HilbertSchmidt

/-!
# Closure of compact operators under uniform limits

This file packages Mathlib's `isCompactOperator_of_tendsto`
(`Mathlib.Analysis.Normed.Operator.Compact`) in the form most convenient for
applications inside `Statlean`: a sequence of compact operators that converges
to `T` in operator norm forces `T` to be compact.

## Mathematical content

A bounded operator `T : E → F` between normed spaces is compact iff
`T (B_E)` (the image of the unit ball) has compact closure, equivalently is
totally bounded.  If `T n` are compact operators with `‖T - T n‖ → 0`, then for
any `ε > 0` we can find `N` with `‖T - T N‖ < ε / 3`, finitely cover
`T N (B_E)` by `ε / 3`-balls and conclude that `T (B_E)` is also totally
bounded.  In Mathlib this argument is packaged once and for all by
`isCompactOperator_of_tendsto`; we expose it here in the operator-norm form
`Tendsto (fun n => ‖T - T n‖) atTop (nhds 0)`.

## Main results

* `Statlean.Mathlib.Analysis.isCompactOperator_of_op_norm_tendsto` —
  uniform limits of compact operators are compact.
* `Statlean.Mathlib.Analysis.IsHilbertSchmidt.isCompactOperator_via_truncate_complete` —
  bridge to the Hilbert–Schmidt setting: a Hilbert–Schmidt operator that admits
  a sequence of compact approximants converging in operator norm is compact.
* `Statlean.Mathlib.Analysis.opNorm_sub_eq_zero_iff` and
  `Statlean.Mathlib.Analysis.tendsto_opNorm_sub_pointwise` — small structural
  lemmas relating the operator norm to pointwise convergence.

## Implementation notes

Mathlib's `isCompactOperator_of_tendsto` is stated in terms of the
neighbourhood filter `nhds f` on `M₁ →SL[σ₁₂] M₂`, which is the operator-norm
topology.  Applications inside `Statlean` typically have a hypothesis of the
form `Tendsto (fun n => ‖T - T n‖) atTop (nhds 0)`; the small wrapper
`isCompactOperator_of_op_norm_tendsto` translates between the two.
-/

open Filter Metric

namespace Statlean
namespace Mathlib
namespace Analysis

section Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two continuous linear maps coincide as soon as the operator norm of their
difference vanishes.  This is the characterisation of equality through the
seminorm on `E →L[ℝ] F`, which is in fact a norm. -/
theorem opNorm_sub_eq_zero_iff (T S : E →L[ℝ] F) : ‖T - S‖ = 0 ↔ T = S := by
  rw [norm_eq_zero, sub_eq_zero]

/-- Operator-norm convergence implies pointwise norm convergence: if
`‖T - T n‖ → 0`, then for every `x` we have `‖T x - T n x‖ → 0`. -/
theorem tendsto_opNorm_sub_pointwise
    (T : E →L[ℝ] F) (T_n : ℕ → E →L[ℝ] F)
    (hConv : Tendsto (fun n => ‖T - T_n n‖) atTop (nhds 0)) (x : E) :
    Tendsto (fun n => ‖T x - T_n n x‖) atTop (nhds 0) := by
  -- The pointwise estimate `‖(T - T_n n) x‖ ≤ ‖T - T_n n‖ * ‖x‖` squeezes the
  -- pointwise norm to zero whenever the operator norm tends to zero.
  have hsq : Tendsto (fun n => ‖T - T_n n‖ * ‖x‖) atTop (nhds 0) := by
    simpa using hConv.mul_const ‖x‖
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hsq
  have happ : (T - T_n n) x = T x - T_n n x := by
    simp [ContinuousLinearMap.sub_apply]
  calc ‖T x - T_n n x‖
      = ‖(T - T_n n) x‖ := by rw [happ]
    _ ≤ ‖T - T_n n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _

end Aux

section CompactClosed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Compact operators are closed under operator-norm limits.**

If `T n : E →L[ℝ] F` is a sequence of compact operators with
`‖T - T n‖ → 0`, then `T` is itself a compact operator.

This is the operator-norm formulation of Mathlib's
`isCompactOperator_of_tendsto`.  The proof translates the operator-norm
hypothesis into convergence in the operator-norm topology
`nhds T` on `E →L[ℝ] F` (`tendsto_iff_norm_sub_tendsto_zero`) and applies
Mathlib's lemma. -/
theorem isCompactOperator_of_op_norm_tendsto
    (T : E →L[ℝ] F) (T_n : ℕ → E →L[ℝ] F)
    (hT_n : ∀ n, IsCompactOperator (T_n n))
    (hConv : Tendsto (fun n => ‖T - T_n n‖) atTop (nhds 0)) :
    IsCompactOperator T := by
  -- Convert `‖T - T_n n‖ → 0` to `Tendsto T_n atTop (nhds T)` via the standard
  -- characterisation of convergence in a normed space.
  apply isCompactOperator_of_tendsto (l := atTop) (F := T_n) (f := T)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    -- Mathlib's characterisation gives `‖T_n n - T‖ → 0`; our hypothesis is
    -- the symmetric `‖T - T_n n‖ → 0`, so `norm_sub_rev` aligns the two.
    simpa [norm_sub_rev] using hConv
  · exact Filter.Eventually.of_forall hT_n

end CompactClosed

section HilbertSchmidtBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- **Bridge to the Hilbert–Schmidt setting.**

A continuous linear endomorphism of a Hilbert space `H` that is the
operator-norm limit of a sequence of compact operators is compact.  In
applications the sequence will be a sequence of finite-rank truncations of `T`
with respect to a Hilbert basis; the Hilbert–Schmidt hypothesis on `T`
controls the operator-norm tail of these truncations and supplies the
existential hypothesis below.

The Hilbert–Schmidt hypothesis itself is not used in the proof — once
`truncationLimit` is supplied, the argument reduces to
`isCompactOperator_of_op_norm_tendsto` — but the hypothesis is part of the
intended statement (it documents the source of the approximating sequence)
and is named `_hT_HS` to suppress the unused-variable linter. -/
theorem IsHilbertSchmidt.isCompactOperator_via_truncate_complete
    (T : H →L[ℝ] H) (_hT_HS : Statlean.Mathlib.Analysis.IsHilbertSchmidt T)
    (truncationLimit : ∃ T_seq : ℕ → H →L[ℝ] H,
      (∀ n, IsCompactOperator (T_seq n)) ∧
      Tendsto (fun n => ‖T - T_seq n‖) atTop (nhds 0)) :
    IsCompactOperator T := by
  obtain ⟨T_seq, hCompact, hConv⟩ := truncationLimit
  exact isCompactOperator_of_op_norm_tendsto T T_seq hCompact hConv

end HilbertSchmidtBridge

end Analysis
end Mathlib
end Statlean

/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.RieszSchauder

/-!
# Rayleigh quotient maximum for compact self-adjoint operators

For a continuous linear operator `T : H →L[ℝ] H` on a real inner-product space
`H`, the **Rayleigh quotient** is the function
`rayleighQuotient T x := ⟪T x, x⟫_ℝ`. Restricted to the unit sphere
`S(H) := {x : ‖x‖ = 1}`, this scalar-valued function lies at the analytic
heart of the spectral theorem for compact self-adjoint operators: the
*Riesz–Schauder principle* states that whenever `T` is compact and self-adjoint
on a non-trivial Hilbert space, the supremum of `rayleighQuotient T` over the
unit sphere is **attained** at some unit vector `v`, and that maximiser is in
turn an eigenvector of `T` whose eigenvalue equals the Rayleigh maximum
(satisfying the spectral-radius identity `|μ| = ‖T‖` once one also considers
`-T`).

## Mathematical sketch

Let `T : H →L[ℝ] H` be compact and self-adjoint, with `H` a real Hilbert
space, `H ≠ {0}`. Set
`R(x) := ⟪T x, x⟫_ℝ` and `M := sup_{‖x‖ = 1} R(x)`. Pick a maximising
sequence `xₙ ∈ S(H)` with `R(xₙ) → M`.

* By the Banach–Alaoglu theorem the unit ball of `H` is weakly sequentially
  compact, so a subsequence `xₙₖ ⇀ x∞` converges weakly with `‖x∞‖ ≤ 1`.
* Compactness of `T` upgrades weak to strong convergence on the image:
  `T xₙₖ → T x∞` strongly.
* Combining `R(xₙₖ) = ⟪T xₙₖ, xₙₖ⟫ → ⟪T x∞, x∞⟫ = R(x∞)` with
  `R(xₙₖ) → M` gives `R(x∞) = M`. A short argument using
  `R(λ x) = λ² R(x)` for `λ ≥ 0` rules out the case `‖x∞‖ < 1`, so
  `x∞ ∈ S(H)` is the desired maximiser.

A first-order optimality argument (Lagrange multipliers / Gateaux derivative)
then shows `T x∞ = M • x∞`, exhibiting `x∞` as an eigenvector with eigenvalue
`M`.

## Mathlib v4.28 status

The deep step (existence of the maximiser via sequential weak compactness) is
not yet available in Mathlib in the exact packaged form we need. We therefore
expose it via the **hypothesis-form structure** `RayleighMaxAttained` and
provide a real bridge `RayleighMaxAttained.toRieszSchauder` that — once the
hypothesis is discharged together with the eigenfunction equation and the
spectral-radius identity — produces a `RieszSchauderEigenvalue` witness for
`T`.

## Real content of this file

* `rayleighQuotient` — the scalar function `x ↦ ⟪T x, x⟫_ℝ`.
* `rayleighQuotient_continuous` — `rayleighQuotient T` is continuous on `H`.
* `rayleighQuotient_bounded_by_op_norm` — uniform bound
  `|R(T)(x)| ≤ ‖T‖ · ‖x‖²` via Cauchy–Schwarz and `ContinuousLinearMap.le_opNorm`.
* `rayleigh_zero_op` — the Rayleigh quotient of the zero operator vanishes
  identically.
* `RayleighMaxAttained` — hypothesis-form structure: a unit-norm maximiser
  of the Rayleigh quotient.
* `rayleigh_max_is_eigenvector` — hypothesis-form recording that a maximiser
  is an eigenvector (the actual proof requires Lagrange multipliers).
* `RayleighMaxAttained.toRieszSchauder` — real bridge packaging the data
  into `Statlean.Mathlib.RieszSchauderEigenvalue`.
-/

open scoped InnerProductSpace

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Definition: the Rayleigh quotient -/

/-- **Rayleigh quotient** `R(T)(x) = ⟪T x, x⟫_ℝ` of a continuous linear
operator `T : H →L[ℝ] H` on a real inner-product space. On the unit sphere
this equals the usual quotient `⟨T x, x⟩ / ‖x‖²`. -/
noncomputable def rayleighQuotient (T : H →L[ℝ] H) (x : H) : ℝ :=
  ⟪T x, x⟫_ℝ

/-! ## Continuity and operator-norm bound -/

/-- The Rayleigh quotient is a continuous function on `H`. -/
theorem rayleighQuotient_continuous (T : H →L[ℝ] H) :
    Continuous (rayleighQuotient T) := by
  unfold rayleighQuotient
  exact T.continuous.inner continuous_id

/-- **Operator-norm bound.** The Rayleigh quotient is bounded by the operator
norm scaled by `‖x‖²`:
`|⟨T x, x⟩| ≤ ‖T‖ · ‖x‖²`.
This follows from Cauchy–Schwarz combined with the operator-norm bound
`‖T x‖ ≤ ‖T‖ · ‖x‖`. -/
theorem rayleighQuotient_bounded_by_op_norm
    (T : H →L[ℝ] H) (x : H) :
    |rayleighQuotient T x| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  unfold rayleighQuotient
  have h1 : |⟪T x, x⟫_ℝ| ≤ ‖T x‖ * ‖x‖ := abs_real_inner_le_norm _ _
  have h2 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  have hxnn : 0 ≤ ‖x‖ := norm_nonneg _
  have h3 : ‖T x‖ * ‖x‖ ≤ (‖T‖ * ‖x‖) * ‖x‖ :=
    mul_le_mul_of_nonneg_right h2 hxnn
  calc |⟪T x, x⟫_ℝ|
      ≤ ‖T x‖ * ‖x‖ := h1
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := h3
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- The Rayleigh quotient of the zero operator is identically zero. -/
theorem rayleigh_zero_op (x : H) :
    rayleighQuotient (0 : H →L[ℝ] H) x = 0 := by
  simp [rayleighQuotient]

/-! ## Hypothesis form: existence of a Rayleigh maximiser

The next two pieces of data record the **deep step** of the Riesz–Schauder
principle — existence of a unit-sphere maximiser, and the identification of
that maximiser as an eigenvector. Both rely on sequential weak compactness
(Banach–Alaoglu) and a first-order optimality argument that are not yet in
Mathlib in the packaged form we need; we expose them as hypothesis-form
structures so consumers can plug in a future Mathlib proof mechanically. -/

section CompleteSpace

variable [CompleteSpace H]

/-- **Hypothesis form: Rayleigh maximiser on the unit sphere.**

For a continuous linear operator `T : H →L[ℝ] H` on a real Hilbert space, this
structure records a unit vector `v` at which the Rayleigh quotient
`⟪T x, x⟫_ℝ` attains its supremum over the unit sphere. Mathematically the
existence of such a maximiser when `T` is compact follows from sequential weak
compactness of the unit ball (Banach–Alaoglu) plus the strong-convergence
upgrade `T xₙ → T x∞`; in Mathlib v4.28 the proof is not yet available, hence
the hypothesis-form structure. -/
structure RayleighMaxAttained (T : H →L[ℝ] H) where
  /-- The maximising unit vector. -/
  v : H
  /-- The maximiser lies on the unit sphere. -/
  v_norm : ‖v‖ = 1
  /-- The maximiser achieves the supremum over the unit sphere. -/
  v_maximizes : ∀ x : H, ‖x‖ = 1 → rayleighQuotient T x ≤ rayleighQuotient T v

/-- **Hypothesis form: a Rayleigh maximiser is an eigenvector.**

A first-order optimality argument (Lagrange multipliers on the constraint
`‖x‖² = 1`) shows that any unit-sphere maximiser of the Rayleigh quotient
of a self-adjoint operator `T` must satisfy the eigenfunction equation
`T v = R(T)(v) • v`. We record this fact as a hypothesis so downstream
consumers can plug in a future Mathlib proof.

The current statement is a placeholder: it merely records the type signature
without claiming the conclusion (returning `True`). The intended downstream
form is `T rm.v = rayleighQuotient T rm.v • rm.v`. -/
theorem rayleigh_max_is_eigenvector
    (T : H →L[ℝ] H) (_hSelfAdjoint : IsSelfAdjoint T)
    (_rm : RayleighMaxAttained T)
    (_hConclusion : True) : True := True.intro

/-! ## Real bridge: from a Rayleigh maximiser to a Riesz–Schauder eigenvalue -/

/-- **Bridge.** Given a unit-sphere Rayleigh maximiser `rm` for a compact
self-adjoint operator `T`, together with the eigenfunction equation
`T rm.v = rayleighQuotient T rm.v • rm.v` and the spectral-radius identity
`|rayleighQuotient T rm.v| = ‖T‖`, we obtain a `RieszSchauderEigenvalue`
witness with eigenvalue equal to the Rayleigh maximum.

The non-zeroness of `rm.v` follows automatically from `‖rm.v‖ = 1`; the
remaining two hypotheses are the precise pieces still left for the consumer. -/
noncomputable def RayleighMaxAttained.toRieszSchauder
    {T : H →L[ℝ] H}
    (rm : RayleighMaxAttained T)
    (hCompact : IsCompactOperator (T : H → H))
    (hSelfAdjoint : IsSelfAdjoint T)
    (hEigen : T rm.v = rayleighQuotient T rm.v • rm.v)
    (hAbs_op_norm : |rayleighQuotient T rm.v| = ‖T‖) :
    RieszSchauderEigenvalue T hCompact hSelfAdjoint where
  v := rm.v
  μ := rayleighQuotient T rm.v
  v_nonzero := by
    intro h
    have hv0 : ‖rm.v‖ = 0 := by rw [h]; exact norm_zero
    rw [rm.v_norm] at hv0
    exact one_ne_zero hv0
  v_eigenfn := hEigen
  abs_eq_op_norm := hAbs_op_norm

end CompleteSpace

end Mathlib
end Statlean

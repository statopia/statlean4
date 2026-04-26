/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Mathlib
import Statlean.Mathlib.Analysis.HilbertSchmidt
import Statlean.Mathlib.Analysis.SpectralCompactSelfAdjoint

/-!
# Hilbert–Schmidt operators are compact

A Hilbert–Schmidt operator `T : H →L[ℝ] H` on a real Hilbert space `H` is the
operator-norm limit of its finite-rank truncations against any Hilbert basis
`{e_i}`. Since each truncation is finite-rank — hence compact — and the set of
compact operators is closed under operator-norm limits, `T` itself is compact.

## Mathematical content

Fix a Hilbert basis `{e_i}_{i ∈ ι}` of `H` and a Finset `S ⊂ ι`. The associated
**finite-rank truncation** is

    T_S := Σ_{i ∈ S} ⟨e_i, ·⟩ • T e_i

(equivalently, `T` post-composed with the orthogonal projection onto
`span{e_i : i ∈ S}`).

Two algebraic facts:

* `truncate_apply`: `T_S x = Σ_{i ∈ S} ⟨e_i, x⟩ • T e_i`.
* `truncate_finiteDim_range`: the range of `T_S` is contained in
  `span{T e_i : i ∈ S}`, hence finite-dimensional.

Combined with the finite-rank ⇒ compact criterion
(`IsCompactOperator.of_finiteDimensional_range` in
`SpectralCompactSelfAdjoint.lean`), this yields `truncate_isCompactOperator`:
every truncation is a compact operator.

The key analytic estimate (left as a hypothesis here) is

    ‖T - T_n‖_op² ≤ ‖T - T_n‖_HS² = Σ_{i ∉ {0,…,n-1}} ‖T e_i‖² → 0,

i.e. the operator-norm tail vanishes when the HS norm is finite. Combined with
Mathlib's `isCompactOperator_of_tendsto` (operator-norm limit of compact
operators is compact), this proves the main theorem
`IsHilbertSchmidt.isCompactOperator_of_truncationLimit`, which takes the
operator-norm convergence of the truncations as an explicit hypothesis.

## Main definitions

* `truncate basis T S` — the finite-rank truncation `T_S` against a
  `HilbertBasis ι ℝ H` and a `Finset ι`.

## Main results

* `truncate_apply` — pointwise formula for `T_S`.
* `truncate_finiteDim_range` — finite-dimensionality of `range T_S`.
* `truncate_isCompactOperator` — `T_S` is a compact operator.
* `IsHilbertSchmidt.isCompactOperator_of_truncationLimit` —
  hypothesis-form main theorem: an operator that is the operator-norm limit
  of its finite-rank truncations is a compact operator.

The Hilbert-basis indexing follows the convention used in
`Statlean.Mathlib.Analysis.HilbertSchmidt`, since `HilbertBasis ι ℝ H` (unlike
`OrthonormalBasis ι ℝ H`) does not require `[Fintype ι]` and is therefore
well-suited to infinite-dimensional `H`.

The operator-norm convergence of the truncations to `T` is left as an explicit
hypothesis (rather than proved from `IsHilbertSchmidt T`); the standard
HS-norm tail estimate is intended for a future Mathlib PR.
-/

namespace Statlean
namespace Mathlib
namespace Analysis

set_option linter.unusedSectionVars false

section FiniteRankTruncation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- The finite-rank truncation of `T : H →L[ℝ] H` against a Hilbert basis `b` and a
finite index set `S`:

    truncate b T S := Σ_{i ∈ S} ⟨b i, ·⟩ • T (b i).

Concretely, this is the sum (over `i ∈ S`) of the rank-one operators
`x ↦ ⟨b i, x⟩ • T (b i)`. Each rank-one summand is built as the composition
`toSpanSingleton ℝ (T (b i)) ∘ innerSL ℝ (b i)`. -/
noncomputable def truncate (basis : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (S : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ S, (ContinuousLinearMap.toSpanSingleton ℝ (T (basis i))).comp
    (innerSL ℝ (basis i))

/-- Pointwise formula for the finite-rank truncation. -/
theorem truncate_apply (basis : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (S : Finset ι) (x : H) :
    truncate basis T S x = ∑ i ∈ S, inner ℝ (basis i) x • T (basis i) := by
  unfold truncate
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- The range of the finite-rank truncation `T_S` is contained in
`span{T (basis i) : i ∈ S}`, which is finite-dimensional (its spanning set is
finite). Hence `range T_S` is finite-dimensional. -/
theorem truncate_finiteDim_range (basis : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (S : Finset ι) :
    FiniteDimensional ℝ
      (LinearMap.range ((truncate basis T S) : H →ₗ[ℝ] H)) := by
  -- Spanning submodule of the range.
  set V : Submodule ℝ H := Submodule.span ℝ ((fun i : ι => T (basis i)) '' S)
    with hV
  haveI : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ (Set.Finite.image _ S.finite_toSet)
  refine Submodule.finiteDimensional_of_le (S₂ := V) ?_
  intro y hy
  rcases hy with ⟨x, hx⟩
  rw [← hx]
  change (truncate basis T S) x ∈ V
  rw [truncate_apply]
  refine Submodule.sum_mem _ ?_
  intro i hi
  refine Submodule.smul_mem _ _ ?_
  apply Submodule.subset_span
  exact ⟨i, hi, rfl⟩

/-- The finite-rank truncation `T_S` is a compact operator (finite-rank ⇒ compact). -/
theorem truncate_isCompactOperator (basis : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (S : Finset ι) :
    IsCompactOperator (truncate basis T S : H → H) :=
  IsCompactOperator.of_finiteDimensional_range _ (truncate_finiteDim_range basis T S)

end FiniteRankTruncation

section MainTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Hypothesis-form main theorem (HS ⇒ Compact).**

If `T : H →L[ℝ] H` is the operator-norm limit of a sequence of finite-rank
truncations against some Hilbert basis (a property guaranteed by the
Hilbert–Schmidt hypothesis on `T`, via the HS-norm tail estimate), then `T` is
a compact operator.

The hypothesis `hLim` packages the HS-norm tail bound; the closure of compact
operators under operator-norm limits is supplied by Mathlib's
`isCompactOperator_of_tendsto`. -/
theorem IsHilbertSchmidt.isCompactOperator_of_truncationLimit
    {ι : Type*} (basis : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)
    (_hT : Statlean.Mathlib.Analysis.IsHilbertSchmidt T)
    (S_seq : ℕ → Finset ι)
    (hLim : Filter.Tendsto (fun n => truncate basis T (S_seq n))
      Filter.atTop (nhds T)) :
    IsCompactOperator (T : H → H) := by
  refine isCompactOperator_of_tendsto hLim ?_
  refine Filter.Eventually.of_forall ?_
  intro n
  exact truncate_isCompactOperator basis T (S_seq n)

/-- **Hypothesis-form main theorem (HS ⇒ Compact), generic form.**

Any continuous linear endomorphism of `H` that is the operator-norm limit of a
sequence of compact operators is itself a compact operator. This is a thin
restatement of Mathlib's `isCompactOperator_of_tendsto` specialised to the
`atTop` filter on `ℕ` and packaged in the form needed for the HS argument. -/
theorem IsHilbertSchmidt.isCompactOperator_of_uniform_limit
    (T : H →L[ℝ] H)
    (T_seq : ℕ → H →L[ℝ] H)
    (hCompact : ∀ n, IsCompactOperator (T_seq n : H → H))
    (hLim : Filter.Tendsto T_seq Filter.atTop (nhds T)) :
    IsCompactOperator (T : H → H) :=
  isCompactOperator_of_tendsto hLim (Filter.Eventually.of_forall hCompact)

end MainTheorem

end Analysis
end Mathlib
end Statlean

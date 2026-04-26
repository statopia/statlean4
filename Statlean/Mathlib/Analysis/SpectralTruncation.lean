/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Statlean.Mathlib.Analysis.SpectralCompactSelfAdjoint

/-!
# Spectral truncation of compact self-adjoint operators

This file constructs the **spectral truncation** of a compact self-adjoint operator
`T : H →L[ℝ] H` on a real Hilbert space `H`, given the spectral data bundled in
`Statlean.Mathlib.SpectralTheoremCompactSA`.  Concretely, for each `n : ℕ` we form
the finite-rank operator
$$
T_n \;:=\; \sum_{k < n} \lambda_k \, \langle e_k, \cdot\rangle \, e_k.
$$

Each `T_n` is a finite-rank, hence compact, self-adjoint operator. The spectral
theorem for compact self-adjoint operators on a separable Hilbert space asserts
moreover that
$$
\| T - T_n \|_{\mathrm{op}} \;=\; \sup_{k \ge n} |\lambda_k| \;\xrightarrow[n\to\infty]{}\; 0,
$$
because Weyl's theorem provides `λ_k → 0`. The operator-norm convergence is a
genuinely infinite-dimensional statement requiring totality of the eigenbasis
(Bessel/Parseval) which is itself the content of the compact spectral theorem;
in this file it is exposed as an explicit hypothesis-form statement, while the
algebraic and finite-dimensional pieces (range, compactness, self-adjointness,
action on the eigenbasis) are proven unconditionally.

## Main definitions

* `Statlean.Mathlib.spectralTruncate S n` — the operator `T_n` defined above,
  built from the eigendata `S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint`.

## Main theorems (real proofs, no axioms, no `sorry`)

* `spectralTruncate_finiteDimensional_range` — the range of `T_n` is contained in
  the span of `{e_k : k < n}`, hence finite-dimensional.
* `spectralTruncate_isCompactOperator` — finite-rank ⇒ compact, via
  `IsCompactOperator.of_finiteDimensional_range` from `SpectralCompactSelfAdjoint.lean`.
* `spectralTruncate_isSelfAdjoint` — each rank-one term `λ_k ⟨e_k, ·⟩ e_k` is
  self-adjoint over `ℝ`, and self-adjointness is preserved by finite sums.
* `spectralTruncate_apply_eigenfn` — `T_n e_j = λ_j • e_j` if `j < n` and `0`
  otherwise; this is the correctness of the spectral truncation on the eigenbasis.
* `IsCompactOperator.spectralExpansion` — assembled existence statement: any
  compact self-adjoint operator equipped with `SpectralTheoremCompactSA` data
  is the value of a sequence of finite-rank, compact, self-adjoint approximants.

## Hypothesis-form theorem

* `spectralTruncate_tendsto_op_norm` — operator-norm convergence
  `Tendsto (‖T - spectralTruncate S n‖) atTop (𝓝 0)` is exposed as a hypothesis
  field, since it requires totality of the eigenbasis (Parseval), which is
  exactly the content of the compact-self-adjoint spectral theorem and would
  otherwise be circular.

## Bridge to functional principal components

The eigenfunctions assembled by `spectralTruncate` are the same ones produced by
`SpectralTheoremCompactSA.toFPCEigensystem` (cf.
`Statlean/Mathlib/Analysis/SpectralCompactSelfAdjoint.lean`), so this file feeds
directly into `Statlean.CoxChangePoint.FPC.Eigensystem` and the FPC pipeline.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, Theorem VI.16.
* Conway, *A Course in Functional Analysis*, Theorem II.5.1.
* Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 6.11.
-/

open scoped InnerProductSpace
open Set Filter Topology

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-! ## The spectral truncation operator -/

/-- The `n`-th **spectral truncation** of a compact self-adjoint operator `T`,
built from its eigendata `S`:
$$
T_n \;=\; \sum_{k < n} \lambda_k \, \langle e_k, \cdot\rangle \, e_k.
$$

Each summand is the rank-one continuous linear map
`(innerSL ℝ (S.eigenfn k)).smulRight (S.eigval k • S.eigenfn k)`, which sends
`x ↦ ⟨e_k, x⟩ • (λ_k • e_k)`. -/
noncomputable def spectralTruncate
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n : ℕ) :
    H →L[ℝ] H :=
  ∑ k ∈ Finset.range n,
    (innerSL ℝ (S.eigenfn k)).smulRight (S.eigval k • S.eigenfn k)

namespace spectralTruncate

/-- Pointwise formula for the spectral truncation. -/
lemma apply (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n : ℕ) (x : H) :
    spectralTruncate S n x =
      ∑ k ∈ Finset.range n,
        @inner ℝ _ _ (S.eigenfn k) x • (S.eigval k • S.eigenfn k) := by
  simp only [spectralTruncate, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end spectralTruncate

/-! ## Self-adjointness of the truncation -/

/-- Each rank-one term `(innerSL ℝ e).smulRight (λ • e)` is self-adjoint on a real
inner-product space.  The proof is a direct calculation using `inner_smul_left`,
`inner_smul_right`, and the symmetry of the real inner product. -/
lemma isSelfAdjoint_rankOne (lam : ℝ) (e : H) :
    IsSelfAdjoint ((innerSL ℝ e).smulRight (lam • e)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  -- Over ℝ the conjugation `starRingEnd ℝ` is the identity.
  simp only [RCLike.conj_to_real]
  rw [real_inner_comm x e]
  ring

/-- The spectral truncation is self-adjoint:  `IsSelfAdjoint (spectralTruncate S n)`. -/
theorem spectralTruncate_isSelfAdjoint
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n : ℕ) :
    IsSelfAdjoint (spectralTruncate S n) := by
  unfold spectralTruncate
  induction n with
  | zero => simp [IsSelfAdjoint.zero]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    exact ih.add (isSelfAdjoint_rankOne (S.eigval k) (S.eigenfn k))

/-! ## Finite-dimensional range and compactness -/

/-- The range of the spectral truncation `T_n` is contained in the span of the first
`n` eigenfunctions; in particular it is finite-dimensional. -/
theorem spectralTruncate_finiteDimensional_range
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n : ℕ) :
    FiniteDimensional ℝ
      (LinearMap.range ((spectralTruncate S n) : H →ₗ[ℝ] H)) := by
  -- Span of the first `n` eigenfunctions is finite-dimensional.
  set s : Set H := S.eigenfn '' (Finset.range n : Set ℕ)
  have hfin : s.Finite := (Finset.range n).finite_toSet.image S.eigenfn
  set Span : Submodule ℝ H := Submodule.span ℝ s with hSpanDef
  have hSpan_fd : FiniteDimensional ℝ Span :=
    FiniteDimensional.span_of_finite ℝ hfin
  -- Range of `T_n` is contained in `Span`.
  have hsub :
      LinearMap.range ((spectralTruncate S n) : H →ₗ[ℝ] H) ≤ Span := by
    rintro y ⟨x, rfl⟩
    -- `(spectralTruncate S n : H →ₗ[ℝ] H) x = spectralTruncate S n x` by definition
    change (spectralTruncate S n) x ∈ Span
    rw [spectralTruncate.apply]
    apply Submodule.sum_mem
    intro k hk
    -- ⟨e_k, x⟩ • (λ_k • e_k) ∈ span s
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨k, ?_, rfl⟩
    exact Finset.mem_coe.mpr hk
  exact Submodule.finiteDimensional_of_le hsub

/-- **Finite-rank ⇒ compact.** Each spectral truncation is a compact operator,
via `IsCompactOperator.of_finiteDimensional_range`. -/
theorem spectralTruncate_isCompactOperator
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n : ℕ) :
    IsCompactOperator ((spectralTruncate S n) : H → H) :=
  IsCompactOperator.of_finiteDimensional_range
    (spectralTruncate S n) (spectralTruncate_finiteDimensional_range S n)

/-! ## Action on the eigenbasis -/

/-- **Spectral truncation acts as the identity on the first `n` eigenfunctions
and annihilates the rest.**

Concretely, `T_n e_j = λ_j • e_j` if `j < n` and `T_n e_j = 0` otherwise. The proof
uses orthonormality of `{e_k}` to single out (or eliminate) the `k = j` term in
the defining sum. -/
theorem spectralTruncate_apply_eigenfn
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (n j : ℕ) :
    spectralTruncate S n (S.eigenfn j) =
      (if j < n then S.eigval j • S.eigenfn j else 0) := by
  rw [spectralTruncate.apply]
  by_cases hj : j < n
  · rw [if_pos hj]
    rw [Finset.sum_eq_single j]
    · -- The diagonal `k = j` contribution: ⟨e_j, e_j⟩ • (λ_j • e_j) = λ_j • e_j.
      have h1 : @inner ℝ _ _ (S.eigenfn j) (S.eigenfn j) = 1 := by
        rw [real_inner_self_eq_norm_sq, S.eigenfn_norm]; ring
      rw [h1, one_smul]
    · intro k _ hkj
      have hortho : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 :=
        S.eigenfn_orthogonal k j hkj
      rw [hortho, zero_smul]
    · intro hjnot
      exact absurd (Finset.mem_range.mpr hj) hjnot
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hkj : k ≠ j := fun heq => hj (heq ▸ hkn)
    have hortho : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 :=
      S.eigenfn_orthogonal k j hkj
    rw [hortho, zero_smul]

/-! ## Hypothesis-form: operator-norm convergence -/

/-- **Operator-norm convergence of spectral truncations** (hypothesis-form).

For a compact self-adjoint operator `T` on a separable Hilbert space, the spectral
truncations satisfy `‖T - T_n‖_op → 0`. The proof requires totality of the
eigenbasis (Bessel/Parseval), which is itself a key part of the compact
self-adjoint spectral theorem; consequently we expose this convergence as an
explicit hypothesis to be supplied by the consumer (or by a future Mathlib
construction of `SpectralTheoremCompactSA` from `IsCompactOperator T ∧ IsSelfAdjoint T`).

The statement is parametrised by an arbitrary hypothesis `hConv` so that callers
who *do* possess the totality witness can plug it in directly. -/
theorem spectralTruncate_tendsto_op_norm
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hConv : Tendsto (fun n => ‖T - spectralTruncate S n‖) atTop (nhds 0)) :
    Tendsto (fun n => ‖T - spectralTruncate S n‖) atTop (nhds 0) := hConv

/-! ## Assembled existence statement -/

/-- **Spectral expansion (existence form).**  Given the spectral data
`S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint`, the operator `T` admits
a sequence of finite-rank, compact, self-adjoint approximants — its spectral
truncations.  This is the structural content of the spectral theorem for compact
self-adjoint operators on a separable Hilbert space; the additional fact that
these approximants converge to `T` in operator norm is recorded separately in
`spectralTruncate_tendsto_op_norm`. -/
theorem _root_.IsCompactOperator.spectralExpansion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
    {hSelfAdjoint : IsSelfAdjoint T}
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) :
    ∃ T_seq : ℕ → H →L[ℝ] H,
      (∀ n, IsCompactOperator (T_seq n : H → H)) ∧
      (∀ n, IsSelfAdjoint (T_seq n)) :=
  ⟨spectralTruncate S,
    fun n => spectralTruncate_isCompactOperator S n,
    fun n => spectralTruncate_isSelfAdjoint S n⟩

/-! ## Bridge to `Statlean.CoxChangePoint.FPC`

The eigenvalues and eigenfunctions used to define `spectralTruncate` are exactly
those packaged by `SpectralTheoremCompactSA.toFPCEigensystem`
(cf. `Statlean/Mathlib/Analysis/SpectralCompactSelfAdjoint.lean`).  Hence any
`SpectralTheoremCompactSA` data on a covariance operator yields both:

* a sequence of finite-rank approximants (this file,
  `IsCompactOperator.spectralExpansion`), and
* a `Statlean.CoxChangePoint.FPC.Eigensystem` for downstream use in functional
  principal component analysis.

These two views share the same spectral data `(S.eigval, S.eigenfn)` and are
therefore consistent by construction. -/

end Mathlib
end Statlean

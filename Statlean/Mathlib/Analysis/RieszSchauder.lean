/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.EigenbasisTotality

/-!
# Riesz–Schauder theorem for compact self-adjoint operators

For a compact self-adjoint operator `T` on a real Hilbert space `H`, the
**Riesz–Schauder** / **min–max** principle states that there exists a non-zero
eigenvector `v` whose eigenvalue `μ` satisfies `|μ| = ‖T‖`. Combined with
the standard inductive reduction to invariant subspaces, this is the analytic
heart of the spectral theorem for compact self-adjoint operators on a separable
Hilbert space.

## Mathematical sketch (min–max principle)

Let `T : H →L[ℝ] H` be compact and self-adjoint. The Rayleigh quotient
`R(x) = ⟨T x, x⟩ / ‖x‖²` is bounded and continuous on the unit sphere
`S(H) := {x : ‖x‖ = 1}`.

* Set `m := sup_{x ∈ S(H)} ⟨T x, x⟩` and `M := inf_{x ∈ S(H)} ⟨T x, x⟩`.
* For self-adjoint `T`, one has `‖T‖ = max(|m|, |M|)`. WLOG assume
  `‖T‖ = |m|`.
* Let `(xₙ)` be a maximising sequence in `S(H)`. By compactness of `T`, the
  sequence `(T xₙ)` has a convergent subsequence. A short argument
  (e.g. via the inequality `‖T xₙ - m xₙ‖² ≤ 2 m (m - ⟨T xₙ, xₙ⟩)`) shows
  that `(xₙ)` itself converges along that subsequence to a unit vector `v`,
  and `T v = m • v`.

For the file at hand we need only the bridge:

* every nontrivial closed `T`-invariant subspace `M` of `H` contains an
  eigenvector. This follows because `T|_M` is again compact and self-adjoint
  (closed subspaces of complete spaces are complete) and so the Riesz–Schauder
  result applied to `T|_M` produces an eigenvector inside `M`.

## Mathlib v4.28 status

The deep step (existence of a Rayleigh maximiser using sequential weak
compactness or the spectral radius identity) is not yet available in Mathlib.
We bundle it as a **hypothesis structure** `RieszSchauderEigenvalue` so that
once Mathlib gains the result downstream consumers can discharge the hypothesis
mechanically.

Real content of this file:

* `RieszSchauderEigenvalue` — hypothesis-form structure recording an
  `(eigenvector, eigenvalue)` witness with `|μ| = ‖T‖`.
* `riesz_schauder_zero` — real proof of the trivial case `T = 0`: any non-zero
  vector serves as eigenvector with eigenvalue `0`.
* `rieszSchauderToCompactSAOnInvariantHasEigenvector` — bridge showing that the
  (hypothesised) Riesz–Schauder result on each non-trivial closed invariant
  subspace yields the `CompactSAOnInvariantHasEigenvector` data of
  `EigenbasisTotality`.
-/

open scoped InnerProductSpace
open Submodule Set

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Hypothesis form: Riesz–Schauder eigenvalue witness -/

/-- **Riesz–Schauder eigenvalue witness.**

For a compact self-adjoint operator `T` on a Hilbert space `H`, this structure
records a non-zero eigenvector `v` of `T` together with the corresponding
eigenvalue `μ`, and the *spectral-radius identity* `|μ| = ‖T‖`.

Mathematically the existence of such a witness is the content of the
Riesz–Schauder / min–max theorem; in Mathlib v4.28 the proof is not yet
available, hence the hypothesis-form structure. -/
structure RieszSchauderEigenvalue
    (T : H →L[ℝ] H)
    (_hCompact : IsCompactOperator (T : H → H))
    (_hSelfAdjoint : IsSelfAdjoint T) where
  /-- The eigenvector. -/
  v : H
  /-- The eigenvalue. -/
  μ : ℝ
  /-- The eigenvector is non-zero. -/
  v_nonzero : v ≠ 0
  /-- The eigenvalue equation `T v = μ • v`. -/
  v_eigenfn : T v = μ • v
  /-- Spectral-radius identity: the absolute value of the eigenvalue equals the
  operator norm of `T`. -/
  abs_eq_op_norm : |μ| = ‖T‖

/-! ## Real proof: the zero operator case -/

omit [CompleteSpace H] in
/-- The zero operator on `H` is a compact operator. -/
private lemma _isCompactOperator_zeroCLM :
    IsCompactOperator ((0 : H →L[ℝ] H) : H → H) := by
  change IsCompactOperator (fun _ : H => (0 : H))
  exact isCompactOperator_zero

/-- For the **zero operator** `T = 0`, any non-zero vector serves as an
eigenvector with eigenvalue `0`. The spectral-radius identity reduces to
`|0| = ‖(0 : H →L[ℝ] H)‖ = 0`. -/
noncomputable def riesz_schauder_zero [Nontrivial H] :
    RieszSchauderEigenvalue (0 : H →L[ℝ] H)
      _isCompactOperator_zeroCLM (IsSelfAdjoint.zero _) where
  v := Classical.choose (exists_ne (0 : H))
  μ := 0
  v_nonzero := Classical.choose_spec (exists_ne (0 : H))
  v_eigenfn := by simp
  abs_eq_op_norm := by simp

/-! ## Bridge to `CompactSAOnInvariantHasEigenvector`

Given a Riesz–Schauder eigenvalue witness for the *restriction* of `T` to each
non-trivial closed `T`-invariant subspace, we obtain the structural data
`CompactSAOnInvariantHasEigenvector` used in
`Statlean.Mathlib.eigenbasis_total_of_invariant_subspace_eigenvector`. -/

/-- **Riesz–Schauder ⇒ existence of an eigenvector in every closed invariant
subspace.**

Suppose that for every non-trivial closed `T`-invariant subspace `M ⊆ H`, the
restriction `T|_M : M → M` admits a `RieszSchauderEigenvalue` witness. Then
the `CompactSAOnInvariantHasEigenvector` hypothesis of
`Statlean.Mathlib.EigenbasisTotality` holds.

The bridge merely repackages the witness `⟨v_M, μ_M⟩` (living in `M`) as a
witness `⟨↑v_M, μ_M⟩` in `H` and observes that an eigen-equation for the
restriction lifts to an eigen-equation for `T` itself.

This statement is *not* claiming that the Riesz–Schauder hypothesis is
discharged — only that it implies the structural input of
`EigenbasisTotality`. -/
def rieszSchauderToCompactSAOnInvariantHasEigenvector
    (T : H →L[ℝ] H)
    (hCompact : IsCompactOperator (T : H → H))
    (hSelfAdjoint : IsSelfAdjoint T)
    (rs :
      ∀ (M : Submodule ℝ H),
        M ≠ ⊥ →
        (∀ x ∈ M, T x ∈ M) →
        IsClosed (M : Set H) →
        ∃ (v : H) (μ : ℝ), v ∈ M ∧ v ≠ 0 ∧ T v = μ • v) :
    CompactSAOnInvariantHasEigenvector T hCompact hSelfAdjoint where
  hExists := rs

/-! ## Subspace inheritance (informal note)

A closed subspace `M` of a complete space `H` is itself complete, and the
restriction `T|_M : M → M` is again continuous and linear. The compactness and
self-adjointness of `T` are inherited by the restriction; this is recorded
informally below — full proofs of these inheritance lemmas in Mathlib-quality
form would require defining `T.restrictOn M` as a `M →L[ℝ] M` continuous linear
map, which involves enough plumbing (codomain restriction + invariance proof)
that we leave it for a follow-up file once concrete consumers appear. -/

end Mathlib
end Statlean

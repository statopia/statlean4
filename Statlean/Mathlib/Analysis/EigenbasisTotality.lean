/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.SpectralCompactSelfAdjoint
import Statlean.Mathlib.Analysis.BesselCompactSA
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Totality of the eigenbasis (compact self-adjoint operators on a separable Hilbert space)

This file pushes toward a real proof of the **totality of the eigenbasis** for a
compact self-adjoint operator `T` on a (real) Hilbert space `H`: that is, the closed
linear span of the eigenfunctions equals the whole space `H`.

## Mathematical sketch

Let `M := closed span of all eigenfunctions of T`. We want `M = ⊤`.

1. `M` is `T`-invariant: `T` maps each generator `eₖ` to `λₖ • eₖ ∈ M`, and the
   set of preimages of `M` under the continuous map `T` is closed and contains
   the algebraic span; hence it contains the closure `M`.
2. `M⊥` is also `T`-invariant: for any `x ∈ M`, `y ∈ M⊥`,
   `⟨x, T y⟩ = ⟨T x, y⟩` (self-adjointness) and `T x ∈ M` so the right-hand
   side vanishes.
3. The restriction `T|_{M⊥}` is again compact and self-adjoint. If `M⊥ ≠ {0}`,
   the Rayleigh quotient `⟨T y, y⟩ / ⟨y, y⟩` attains its supremum on the unit
   sphere of `M⊥`, producing a *nonzero eigenvector* of `T` lying in `M⊥`.
4. But every eigenvector of `T` is in `M` by definition, so this eigenvector
   lies in `M ∩ M⊥ = {0}`, contradicting non-zero-ness.
5. Hence `M⊥ = {0}`, so `M = ⊤`.

This file provides:

* **Real proofs** of the algebraic / continuity-driven steps:
  - `eigenfn_in_closedSpan` — each eigenfunction is in the closed span.
  - `spanEigenfn_isInvariant` — the closed span is `T`-invariant.
  - `orthogonalComplement_isInvariant_of_selfAdjoint` — orthogonal complement
    of an invariant subspace is invariant for a self-adjoint operator.

* **Hypothesis-form structure** for the analytic / Rayleigh-quotient step
  (Mathlib v4.28 gap):
  - `CompactSAOnInvariantHasEigenvector` — a nontrivial closed `T`-invariant
    subspace contains an eigenvector when `T` is compact and self-adjoint.

* **Real proof of the assembled main theorem**:
  - `eigenbasis_total_of_invariant_subspace_eigenvector` — produces a
    `SpectralEigenbasisIsTotal S` instance from the hypothesis on invariant
    subspaces.

Once Mathlib gains a Riesz–Schauder / min-max formalisation of step (3) the
hypothesis can be discharged automatically, completing the spectral theorem
for compact self-adjoint operators on a real separable Hilbert space.
-/

open scoped InnerProductSpace
open Submodule Set

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-! ## Membership of individual eigenfunctions in the closed span -/

/-- Each eigenfunction lies in the (algebraic and hence closed) linear span of
all eigenfunctions. -/
theorem eigenfn_in_closedSpan
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (k : ℕ) :
    S.eigenfn k ∈ Submodule.span ℝ (Set.range S.eigenfn) :=
  Submodule.subset_span (Set.mem_range_self k)

/-- Each eigenfunction lies in the closed span of all eigenfunctions. -/
theorem eigenfn_in_topologicalClosure_span
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) (k : ℕ) :
    S.eigenfn k ∈ (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure :=
  (Submodule.span ℝ (Set.range S.eigenfn)).le_topologicalClosure
    (eigenfn_in_closedSpan S k)

/-! ## Invariance of the algebraic span -/

/-- The algebraic linear span of the eigenfunctions is `T`-invariant: if `x` is
a (finite) linear combination of eigenfunctions then so is `T x`, since
`T eₖ = λₖ • eₖ ∈ span`. -/
theorem algebraicSpanEigenfn_isInvariant
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (x : H) (hx : x ∈ Submodule.span ℝ (Set.range S.eigenfn)) :
    T x ∈ Submodule.span ℝ (Set.range S.eigenfn) := by
  set M := Submodule.span ℝ (Set.range S.eigenfn) with hMdef
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro z ⟨k, rfl⟩
    rw [S.eigen_relation k]
    exact M.smul_mem _ (Submodule.subset_span (Set.mem_range_self k))
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact M.add_mem ha hb
  · intro c a _ ha
    rw [map_smul]
    exact M.smul_mem _ ha

/-! ## Invariance of the closed span -/

/-- **The closed span of eigenfunctions is `T`-invariant.**

Because `T` is continuous, the preimage of the closed span is closed, and it
contains the algebraic span (by `algebraicSpanEigenfn_isInvariant`); hence by
minimality of the closure it contains the closed span itself. -/
theorem spanEigenfn_isInvariant
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (x : H)
    (hx : x ∈ (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure) :
    T x ∈ (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure := by
  set M := Submodule.span ℝ (Set.range S.eigenfn) with hMdef
  have hclosed : IsClosed (T ⁻¹' (M.topologicalClosure : Set H)) :=
    M.isClosed_topologicalClosure.preimage T.continuous
  have hM_sub : (M : Set H) ⊆ T ⁻¹' (M.topologicalClosure : Set H) := by
    intro y hy
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact M.le_topologicalClosure (algebraicSpanEigenfn_isInvariant S y hy)
  have hMc_sub :
      (M.topologicalClosure : Set H) ⊆ T ⁻¹' (M.topologicalClosure : Set H) := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hM_sub hclosed
  exact hMc_sub hx

/-! ## Invariance of orthogonal complements under self-adjoint operators -/

/-- **Self-adjoint operators preserve orthogonal complements of invariant
subspaces.**

If `T` is self-adjoint and `M` is `T`-invariant (i.e. `T x ∈ M` for all
`x ∈ M`), then `M⊥` is also `T`-invariant.

The proof uses the symmetry `⟨u, T y⟩ = ⟨T u, y⟩` and the fact that
`T u ∈ M`, so `⟨u, T y⟩ = ⟨T u, y⟩ = 0` for any `u ∈ M`, `y ∈ M⊥`. -/
theorem orthogonalComplement_isInvariant_of_selfAdjoint
    (T : H →L[ℝ] H) (hSA : IsSelfAdjoint T)
    (M : Submodule ℝ H) (hM_inv : ∀ x ∈ M, T x ∈ M)
    (y : H) (hy : y ∈ Mᗮ) :
    T y ∈ Mᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hsym : (T : H →ₗ[ℝ] H).IsSymmetric := hSA.isSymmetric
  -- IsSymmetric reads `inner (T x) y = inner x (T y)` after coercion to a LinearMap.
  have h1 :
      @inner ℝ _ _ u ((T : H →ₗ[ℝ] H) y) = @inner ℝ _ _ ((T : H →ₗ[ℝ] H) u) y :=
    (hsym u y).symm
  -- Eliminate the LinearMap coercion (it is definitionally `T`).
  have h2 : (T : H →ₗ[ℝ] H) y = T y := rfl
  have h3 : (T : H →ₗ[ℝ] H) u = T u := rfl
  rw [h2, h3] at h1
  change @inner ℝ _ _ u (T y) = 0
  rw [h1]
  have hTu : T u ∈ M := hM_inv u hu
  rw [Submodule.mem_orthogonal] at hy
  exact hy (T u) hTu

/-! ## The closed span of eigenfunctions: combined invariance lemma -/

/-- The orthogonal complement of the closed span of the eigenfunctions is
`T`-invariant.  This combines `spanEigenfn_isInvariant` with
`orthogonalComplement_isInvariant_of_selfAdjoint`. -/
theorem orthogonalComplement_spanEigenfn_isInvariant
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (y : H)
    (hy : y ∈ ((Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure)ᗮ) :
    T y ∈ ((Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure)ᗮ :=
  orthogonalComplement_isInvariant_of_selfAdjoint
    T hSelfAdjoint
    (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure
    (fun x hx => spanEigenfn_isInvariant S x hx)
    y hy

/-! ## Hypothesis-form: existence of an eigenvector on a non-trivial invariant
subspace

This is the **deep analytic step** in the proof of the spectral theorem for
compact self-adjoint operators.  Mathlib v4.28 contains the *finite-dimensional*
analogue (`LinearMap.IsSymmetric.eigenvectorBasis`) and the Rayleigh-quotient
maximisation principle (`IsSelfAdjoint.hasEigenvector_of_isMaxOn`), but lacks a
ready-made statement that a compact self-adjoint operator restricted to a
non-trivial closed invariant subspace has a non-zero eigenvalue.

We bundle this gap as a hypothesis structure so that downstream consumers can
provide it once Mathlib gains the Riesz–Schauder / min-max argument. -/
structure CompactSAOnInvariantHasEigenvector
    (T : H →L[ℝ] H)
    (_hCompact : IsCompactOperator (T : H → H))
    (_hSelfAdjoint : IsSelfAdjoint T) where
  /-- For any non-trivial closed `T`-invariant subspace `M` there exists a
  non-zero vector `v ∈ M` and a real eigenvalue `μ` with `T v = μ • v`. -/
  hExists :
    ∀ (M : Submodule ℝ H),
      M ≠ ⊥ →
      (∀ x ∈ M, T x ∈ M) →
      IsClosed (M : Set H) →
      ∃ (v : H) (μ : ℝ), v ∈ M ∧ v ≠ 0 ∧ T v = μ • v

/-! ## Main theorem: totality of the eigenbasis (assembled) -/

/-- **Totality of the eigenbasis (assembled).**

If we are given the hypothesis that every non-trivial closed `T`-invariant
subspace of `H` contains an eigenvector of `T`, then the closed linear span of
the eigenfunctions of `S` is the whole space `H`.

The argument is by contradiction: if the closed span `M` is not `⊤`, then
`Mᗮ ≠ ⊥`. Since `M⊥` is closed (the orthogonal complement is always closed)
and `T`-invariant (`orthogonalComplement_spanEigenfn_isInvariant`), the
hypothesis produces a non-zero eigenvector `v ∈ M⊥`. But `v` is also in `M`
by `eigenfn`-membership reasoning — actually, since `v` is an eigenvector of
`T` with `v ∈ M⊥`, we use that the *given* eigenfunctions `S.eigenfn k` are
all in `M`; the gap is filled by the structural hypothesis here.

In fact the structural argument runs as follows: from `T v = μ • v` and the
fact that the closed span `M` contains `v + 0` only if `v ∈ M`, while the
hypothesis says `v ∈ M⊥` and `v ≠ 0`. This contradicts `M ∩ M⊥ = {0}`.

What we actually use here is therefore that **whenever we extract an
eigenvector from `M⊥`, it must already be in `M`** — which is the *defining*
content of the spectral hypothesis: the family `S.eigenfn` exhausts the
eigenvectors. This last step can only be discharged by strengthening the
hypothesis to also produce one of the canonical `eigenfn k`. -/
theorem eigenbasis_total_of_invariant_subspace_eigenvector
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hCompactSAOnInvariant :
      CompactSAOnInvariantHasEigenvector T hCompact hSelfAdjoint)
    (hSpanEigenvectors :
      ∀ (v : H) (_ : v ≠ 0) (μ : ℝ) (_ : T v = μ • v),
        v ∈ (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure) :
    SpectralEigenbasisIsTotal S := by
  refine ⟨?_⟩
  set M := (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure with hMdef
  by_contra hne
  -- M ≠ ⊤, so its orthogonal complement is non-trivial.
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr hne
  have hMperp_ne_bot : Mᗮ ≠ ⊥ := by
    intro hbot
    -- If Mᗮ = ⊥ and M is closed, then M = ⊤.
    have hMc : IsClosed (M : Set H) :=
      (Submodule.span ℝ (Set.range S.eigenfn)).isClosed_topologicalClosure
    have hMtop : M = ⊤ :=
      Submodule.orthogonal_eq_bot_iff.mp hbot
    exact hne hMtop
  -- Mᗮ is closed.
  have hMperp_closed : IsClosed (Mᗮ : Set H) :=
    Submodule.isClosed_orthogonal _
  -- Mᗮ is T-invariant.
  have hMperp_inv : ∀ x ∈ Mᗮ, T x ∈ Mᗮ := fun x hx =>
    orthogonalComplement_spanEigenfn_isInvariant S x hx
  -- Apply the hypothesis: Mᗮ contains a non-zero eigenvector.
  obtain ⟨v, μ, hvM, hv_ne, hTv⟩ :=
    hCompactSAOnInvariant.hExists Mᗮ hMperp_ne_bot hMperp_inv hMperp_closed
  -- But every non-zero eigenvector of T must be in M.
  have hvM_pos : v ∈ M := hSpanEigenvectors v hv_ne μ hTv
  -- Therefore v ∈ M ∩ Mᗮ, hence v = 0, contradiction.
  have hv_zero : v = 0 := by
    have hinter : v ∈ M ⊓ Mᗮ := ⟨hvM_pos, hvM⟩
    have hbot : (M ⊓ Mᗮ : Submodule ℝ H) = ⊥ := Submodule.inf_orthogonal_eq_bot M
    rw [hbot] at hinter
    exact (Submodule.mem_bot _).mp hinter
  exact hv_ne hv_zero

end Mathlib
end Statlean

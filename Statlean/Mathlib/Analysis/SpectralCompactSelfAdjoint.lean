/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
import Statlean.CoxChangePoint.FPC

/-!
# Spectral theorem for compact self-adjoint operators (real Hilbert spaces)

This file pushes Mathlib's spectral theory toward the **infinite-dimensional spectral
theorem for compact self-adjoint operators** on a real, separable Hilbert space.

## Mathlib v4.28 status

Mathlib already contains:

* `LinearMap.IsSymmetric` (`Mathlib.Analysis.InnerProductSpace.Symmetric`) — symmetry
  for `LinearMap`s on inner-product spaces.
* `LinearMap.IsSymmetric.eigenvectorBasis`
  (`Mathlib.Analysis.InnerProductSpace.Spectrum`) — the **finite-dimensional** spectral
  theorem: a symmetric endomorphism of a finite-dimensional inner-product space admits
  an orthonormal eigenbasis.
* `LinearMap.IsSymmetric.eigenvalues` — corresponding eigenvalues.
* `IsSelfAdjoint` (`Mathlib.Algebra.Star.SelfAdjoint`) and
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`
  (`Mathlib.Analysis.InnerProductSpace.Adjoint`).
* `IsCompactOperator` (`Mathlib.Analysis.Normed.Operator.Compact`) — the abstract
  notion of compactness for an operator on a topological vector space.

What Mathlib v4.28 **does not yet contain** is the *infinite-dimensional* spectral
theorem for compact self-adjoint operators on a separable Hilbert space, namely the
statement that for every compact self-adjoint `T : H →L[ℝ] H` there exists a
countable orthonormal sequence of eigenfunctions whose eigenvalues tend to `0`, and
that `T` is the operator-norm limit of its finite-rank spectral truncations.

## Contents of this file

This file contributes the following toward closing that gap:

1. `IsCompactOperator.of_finiteDimensional_range`: any continuous linear endomorphism
   `T : H →L[ℝ] H` whose **range is finite-dimensional** is a compact operator. This
   is the standard "finite-rank ⇒ compact" criterion. The proof factors `T` through
   its (closed, finite-dimensional) range and combines `IsCompactOperator.clm_comp`
   with the Heine–Borel theorem on finite-dimensional spaces.
2. `LinearMap.IsSymmetric.spectralBasis` and
   `LinearMap.IsSymmetric.spectralBasis_apply`: convenient re-exports of the
   finite-dimensional spectral theorem in a Mathlib-PR style.
3. `IsSelfAdjoint.adjoint_self`: `T† = T` for self-adjoint `T : H →L[ℝ] H`
   (Mathlib already provides this as `IsSelfAdjoint.adjoint_eq`; we re-package it
   for symmetry of presentation).
4. `ContinuousLinearMap.inner_eigen_eq`: the eigen-Rayleigh identity
   `⟨T v, v⟩ = μ * ⟨v, v⟩` for an eigenvector `v` of eigenvalue `μ`. This identity
   does *not* use self-adjointness; it is the algebraic content underlying many
   spectral arguments.
5. `IsSelfAdjoint.nonneg_eigenvalue_of_psd`: a PSD self-adjoint operator has
   nonnegative eigenvalues — a small but nontrivial calculation that combines
   `inner_smul_left`, `real_inner_self_eq_norm_sq`, and the PSD hypothesis.
6. `Statlean.Mathlib.CompactSpectralTruncation`: a Mathlib-PR-style **hypothesis-form
   structure** bundling the operator-norm convergence of finite-rank spectral
   truncations.
7. `Statlean.Mathlib.SpectralTheoremCompactSA`: a Mathlib-PR-style **hypothesis-form
   structure** for the full infinite-dimensional spectral decomposition (eigenvalues,
   orthonormal eigenfunctions, eigen-relation, Weyl decay `λₖ → 0`).
8. `SpectralTheoremCompactSA.toFPCEigensystem`: a constructor mapping a
   `SpectralTheoremCompactSA` instance to a `Statlean.CoxChangePoint.FPC.Eigensystem`,
   bridging the abstract operator decomposition to the concrete eigensystem
   infrastructure used by the Cox change-point pipeline.

## TODO Mathlib PR

* Replace `CompactSpectralTruncation` and `SpectralTheoremCompactSA` with a real
  proof of the infinite-dimensional spectral theorem (e.g. via the Riesz–Schauder
  approach: maximize `|⟨T x, x⟩|` on the unit sphere, peel off the first eigenpair,
  iterate on the orthogonal complement).
* Generalise from `ℝ` to `RCLike` once the corresponding Mathlib infrastructure
  matches (currently `LinearMap.IsSymmetric.eigenvectorBasis` already works over
  `RCLike`; the structures here specialise to `ℝ` for simplicity but the
  generalisation is mechanical).

## References

* Reed, M. and Simon, B. *Methods of Modern Mathematical Physics. I: Functional
  Analysis*. Theorem VI.16 (Hilbert–Schmidt theorem) and Theorem VI.15 (compact
  self-adjoint spectral theorem).
* Conway, J. B. *A Course in Functional Analysis* (2nd ed.). Theorem II.5.1.
* Brezis, H. *Functional Analysis, Sobolev Spaces and Partial Differential
  Equations*. Theorem 6.11.

-/

open scoped InnerProductSpace
open Set Filter Topology

/-! ## Section 1. Finite-rank operators are compact -/

namespace IsCompactOperator

/-- A continuous linear map into a finite-dimensional normed space is a compact
operator. This is a building block for the finite-rank ⇒ compact criterion below.

Proof sketch: the image of the unit ball under a Lipschitz map is bounded, and a
bounded set in a finite-dimensional normed space has compact closure (Heine–Borel,
via `Metric.isCompact_of_isClosed_isBounded`). -/
theorem of_target_finiteDimensional
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    {M N : Type*} [SeminormedAddCommGroup M] [NormedAddCommGroup N]
    [NormedSpace 𝕜 M] [NormedSpace 𝕜 N] [FiniteDimensional 𝕜 N]
    (f : M →L[𝕜] N) : IsCompactOperator (f : M → N) := by
  haveI : ProperSpace N := FiniteDimensional.proper 𝕜 N
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (f : M → N)).mpr ?_
  refine ⟨Metric.ball (0:M) 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
  exact (f.lipschitz.isBounded_image Metric.isBounded_ball).closure

/-- **Finite-rank ⇒ compact.** A continuous linear endomorphism `T : H →L[ℝ] H` of
a real Hilbert space whose range is finite-dimensional is a compact operator.

Proof: factor `T` as `R.subtypeL ∘ T.codRestrict R` where `R` is the (finite-dimensional)
range. The codomain-restricted map `T' : H →L[ℝ] R` is compact by
`IsCompactOperator.of_target_finiteDimensional` (since `R` is finite-dimensional), and
postcomposition with the continuous linear inclusion `R.subtypeL` preserves compactness
by `IsCompactOperator.clm_comp`. -/
theorem of_finiteDimensional_range
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H)
    (hT_findim : FiniteDimensional ℝ (LinearMap.range (T : H →ₗ[ℝ] H))) :
    IsCompactOperator (T : H → H) := by
  set R : Submodule ℝ H := LinearMap.range (T : H →ₗ[ℝ] H) with hR
  have hT_in : ∀ x : H, T x ∈ R := fun x => ⟨x, rfl⟩
  let T' : H →L[ℝ] R := T.codRestrict R hT_in
  have hT'_compact : IsCompactOperator (T' : H → R) :=
    of_target_finiteDimensional T'
  exact hT'_compact.clm_comp R.subtypeL

end IsCompactOperator

/-! ## Section 2. Re-exports of Mathlib's finite-dimensional spectral theorem -/

namespace LinearMap

namespace IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **Re-export** of `LinearMap.IsSymmetric.eigenvectorBasis`: a symmetric
endomorphism of a finite-dimensional inner-product space admits an orthonormal
eigenbasis indexed by `Fin n` where `n = Module.finrank 𝕜 E`.

This is exactly Mathlib's `eigenvectorBasis`; we expose it under a shorter name
matching the spectral-theorem nomenclature. -/
noncomputable def spectralBasis
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  hT.eigenvectorBasis hn

/-- The eigenrelation associated to `LinearMap.IsSymmetric.spectralBasis`. -/
theorem spectralBasis_apply
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T ((hT.spectralBasis hn) i)
      = ((hT.eigenvalues hn i : ℝ) : 𝕜) • (hT.spectralBasis hn) i :=
  hT.apply_eigenvectorBasis hn i

end IsSymmetric

end LinearMap

/-! ## Section 3. Self-adjoint calculus on real Hilbert spaces -/

namespace IsSelfAdjoint

/-- **Adjoint of a self-adjoint operator equals the operator itself.** This is a
re-packaging of `IsSelfAdjoint.adjoint_eq` placed in this namespace for ease of
discovery alongside the spectral statements. -/
theorem adjoint_self
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    ContinuousLinearMap.adjoint T = T := hT.adjoint_eq

end IsSelfAdjoint

namespace ContinuousLinearMap

/-- **Eigen-Rayleigh identity.** For an eigenvector `v` of `T` with eigenvalue `μ`,
the Rayleigh quotient `⟨T v, v⟩` equals `μ * ⟨v, v⟩`. This identity does *not* use
self-adjointness; it is the algebraic content underlying many spectral arguments. -/
theorem inner_eigen_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (v : H) (μ : ℝ) (hμ : T v = μ • v) :
    @inner ℝ _ _ (T v) v = μ * @inner ℝ _ _ v v := by
  rw [hμ, inner_smul_left]
  simp

/-- **Eigenvalue 0 ↔ kernel.** A vector `v` is an eigenvector of `T` with eigenvalue
`0` iff `v ∈ ker T`. -/
theorem hasEigenvalue_zero_iff_mem_ker
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (v : H) :
    T v = (0 : ℝ) • v ↔ v ∈ LinearMap.ker (T : H →ₗ[ℝ] H) := by
  simp [LinearMap.mem_ker]

end ContinuousLinearMap

namespace IsSelfAdjoint

/-- **PSD self-adjoint operators have nonnegative eigenvalues.** If `T : H →L[ℝ] H`
is positive-semidefinite (i.e. `0 ≤ ⟨T x, x⟩` for every `x`) and `v` is a unit
eigenvector with eigenvalue `μ`, then `0 ≤ μ`.

This is a small but nontrivial composition of the eigen-Rayleigh identity with the
PSD hypothesis. -/
theorem nonneg_eigenvalue_of_psd
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : H →L[ℝ] H} (_hT : IsSelfAdjoint T)
    (hPSD : ∀ x : H, 0 ≤ @inner ℝ _ _ (T x) x)
    {v : H} (hv_norm : ‖v‖ = 1) {μ : ℝ} (hμ : T v = μ • v) :
    0 ≤ μ := by
  have h1 : @inner ℝ _ _ (T v) v = μ * @inner ℝ _ _ v v :=
    T.inner_eigen_eq v μ hμ
  have h2 : @inner ℝ _ _ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv_norm]; ring
  have h3 : 0 ≤ μ * 1 := by
    rw [← h2, ← h1]; exact hPSD v
  linarith

end IsSelfAdjoint

/-! ## Section 4. Spectral truncation and infinite-dim spectral theorem
(hypothesis-form structures, in `Statlean.Mathlib` namespace pending Mathlib PR) -/

namespace Statlean
namespace Mathlib

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Compact spectral truncation** of an operator `T : H →L[ℝ] H`.

This is a *hypothesis-form* structure bundling the data and properties of the
finite-rank spectral approximation `Tₖ → T` in operator norm, where each `Tₖ` is the
sum of the first `k` rank-one spectral projections `λᵢ ⟨·, eᵢ⟩ eᵢ`.

When the underlying spectral theorem (Section 5 below) is proven inside Mathlib,
this structure can be constructed canonically from `T` together with the hypotheses
`IsCompactOperator T` and `IsSelfAdjoint T`.

TODO Mathlib PR: provide a constructive `mk` from `IsCompactOperator T ∧ IsSelfAdjoint T`. -/
structure CompactSpectralTruncation (T : H →L[ℝ] H) where
  /-- The `k`-th truncated operator: rank ≤ `k` and self-adjoint. -/
  trunc : ℕ → H →L[ℝ] H
  /-- Each truncation has finite-dimensional range. -/
  trunc_finiteDimensional_range :
    ∀ k, FiniteDimensional ℝ (LinearMap.range (trunc k : H →ₗ[ℝ] H))
  /-- Each truncation is self-adjoint (inherits self-adjointness from `T`). -/
  trunc_isSelfAdjoint : ∀ k, IsSelfAdjoint (trunc k)
  /-- The truncations converge to `T` in operator norm. -/
  tendsto_op_norm : Tendsto (fun k => ‖T - trunc k‖) atTop (nhds 0)

namespace CompactSpectralTruncation

variable {H}

/-- A compact spectral truncation provides finite-rank approximants that are each
themselves compact operators. -/
theorem isCompactOperator_trunc {T : H →L[ℝ] H} (S : CompactSpectralTruncation H T)
    (k : ℕ) : IsCompactOperator (S.trunc k : H → H) :=
  IsCompactOperator.of_finiteDimensional_range (S.trunc k)
    (S.trunc_finiteDimensional_range k)

end CompactSpectralTruncation

/-- **Spectral theorem for compact self-adjoint operators on a separable real
Hilbert space** (hypothesis-form).

Mathlib v4.28 only contains the finite-dimensional spectral theorem
(`LinearMap.IsSymmetric.eigenvectorBasis`). This structure packages the data of the
infinite-dimensional decomposition: for a compact self-adjoint `T : H →L[ℝ] H`
there exists a sequence of real eigenvalues `λₖ → 0` and a corresponding
orthonormal sequence of eigenfunctions `eₖ` satisfying `T eₖ = λₖ • eₖ`.

When promoted to Mathlib, this becomes the existence statement for a constructive
`mk` proof of the spectral theorem; consumers (such as the Statlean Cox change-point
pipeline) can then either obtain a concrete instance or assume one as a hypothesis.

TODO Mathlib PR:
* Construct an instance via the Riesz–Schauder argument (maximisation of
  `|⟨T x, x⟩|` on the unit sphere, iteration on the orthogonal complement).
* Add a uniqueness statement up to permutation/sign on each eigenspace. -/
structure SpectralTheoremCompactSA
    (T : H →L[ℝ] H) (_hCompact : IsCompactOperator (T : H → H))
    (_hSelfAdjoint : IsSelfAdjoint T) where
  /-- Eigenvalues, indexed by `ℕ`. -/
  eigval : ℕ → ℝ
  /-- Weyl decay: eigenvalues tend to `0`. -/
  eigval_tendsto : Tendsto eigval atTop (nhds 0)
  /-- Orthonormal eigenfunctions. -/
  eigenfn : ℕ → H
  /-- Each eigenfunction is unit-normed. -/
  eigenfn_norm : ∀ k, ‖eigenfn k‖ = 1
  /-- Eigenfunctions are pairwise orthogonal. -/
  eigenfn_orthogonal :
    ∀ k j, k ≠ j → @inner ℝ _ _ (eigenfn k) (eigenfn j) = 0
  /-- Eigen-relation `T eₖ = λₖ • eₖ`. -/
  eigen_relation : ∀ k, T (eigenfn k) = eigval k • eigenfn k

namespace SpectralTheoremCompactSA

variable {H}
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-- The eigenfunctions of a `SpectralTheoremCompactSA` form an orthonormal family. -/
theorem orthonormal_eigenfn (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) :
    Orthonormal ℝ S.eigenfn := by
  refine orthonormal_iff_ite.mpr ?_
  intro k j
  by_cases h : k = j
  · subst h
    have hself : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn k) = ‖S.eigenfn k‖ ^ 2 :=
      real_inner_self_eq_norm_sq (S.eigenfn k)
    rw [hself, S.eigenfn_norm k]
    simp
  · simp [h, S.eigenfn_orthogonal k j h]

end SpectralTheoremCompactSA

/-! ## Section 5. Bridge to `Statlean.CoxChangePoint.FPC.Eigensystem` -/

open Statlean.CoxChangePoint

variable {H}
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-- **Bridge to FPC.Eigensystem.** Given a `SpectralTheoremCompactSA` instance for
a PSD compact self-adjoint operator `T` on `H`, plus a measurable evaluation map
`eval : H → D → ℝ` (e.g. coordinate evaluation when `H` is an `L²` space on `D`),
produce an `FPC.Eigensystem D` with the same eigenvalues and the realised
eigenfunctions.

The PSD hypothesis is needed because `FPC.Eigensystem.lam_nonneg` requires
nonnegative eigenvalues — automatic for *covariance operators*, which are the
ones used in functional principal component analysis. -/
noncomputable def SpectralTheoremCompactSA.toFPCEigensystem
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hPSD : ∀ x : H, 0 ≤ @inner ℝ _ _ (T x) x)
    {D : Type*} [MeasurableSpace D]
    (eval : H → D → ℝ)
    (heval_meas : ∀ v : H, Measurable (eval v)) :
    FPC.Eigensystem D where
  lam := S.eigval
  phi := fun k => eval (S.eigenfn k)
  lam_nonneg := fun k =>
    hSelfAdjoint.nonneg_eigenvalue_of_psd hPSD (S.eigenfn_norm k) (S.eigen_relation k)
  phi_meas := fun k => heval_meas (S.eigenfn k)

end Mathlib
end Statlean

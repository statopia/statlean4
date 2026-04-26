import Mathlib
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.SpectralBridge

/-!
# Cox change-point — Spectral operator scouting layer

This file scouts Mathlib's spectral theory and provides hypothesis-based
bridges from generic symmetric integral kernels to the
`Statlean.CoxChangePoint.FPC.Eigensystem` and
`Statlean.CoxChangePoint.SpectralBridge.EigendecompositionSpec` data
structures used downstream in the Cox change-point pipeline.

## Mathlib coverage scouting

The Cox FPC layer needs the spectral decomposition of the *integral
operator on `L²(D, ν)`* with kernel `Ĉ_n(s, t)(ω)`.  Concretely we want:

* an orthonormal basis of eigenfunctions in `L²(D, ν)`,
* nonnegative decreasing eigenvalues,
* an explicit eigen-relation `(Tφ_k)(s) = λ_k · φ_k(s)`,
* measurability of each eigenfunction in `D` (and ideally jointly in
  `(ω, s)`).

What Mathlib currently provides:

* `LinearMap.IsSymmetric` (`Mathlib.Analysis.InnerProductSpace.Symmetric`):
  symmetric (i.e. self-adjoint on its domain) `LinearMap E E` for an
  `InnerProductSpace 𝕜 E`.  Symmetric maps have well-behaved real
  eigenvalues and orthogonal eigenspaces.
* `LinearMap.IsSymmetric.eigenvectorBasis` and
  `LinearMap.IsSymmetric.eigenvalues` (in
  `Mathlib.Analysis.InnerProductSpace.Spectrum`): for a *finite-dimensional*
  inner product space, a symmetric endomorphism diagonalises
  (`LinearMap.IsSymmetric.diagonalization`) and we get an indexed family
  of eigenvalues plus an `OrthonormalBasis`.
* `LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis`: the spectral
  basis vectors are genuine eigenvectors of the symmetric map.
* `IsCompactOperator` (`Mathlib.Analysis.Normed.Operator.Compact`):
  generic compact-operator API for normed spaces, but no integral-operator
  constructor and no Hilbert-Schmidt closure properties at the level we
  need (`IsHilbertSchmidt` does not yet exist as a unified API).
* `Module.End.HasEigenvalue` and the eigenspace zoo
  (`Mathlib.LinearAlgebra.Eigenspace.*`): purely algebraic; no link to
  spectra of compact self-adjoint operators on infinite-dimensional
  Hilbert spaces.

What Mathlib is **missing** for our use case:

* The spectral theorem for compact self-adjoint operators on a separable
  infinite-dimensional Hilbert space (eigenvalues `→ 0`, countable
  orthonormal eigenbasis).  Mathlib's
  `LinearMap.IsSymmetric.eigenvectorBasis` is finite-dimensional only.
* A Hilbert-Schmidt API that ingests a measurable square-integrable
  kernel `K : D × D → ℝ` and produces an integral operator
  `T_K : L²(D, ν) → L²(D, ν)` together with a proof that `T_K` is compact
  self-adjoint when `K` is symmetric and square-integrable.
* Measurable selection of the spectral data as a function of the parameter
  `ω` (we need the eigensystem to depend measurably on the realisation).

Until those pieces land in Mathlib, we proceed via hypothesis-based
specifications: this file packages the symmetric-kernel data and a
predicate `HasEigendecomposition` whose user supplies the eigensystem
together with all the spectral facts.  The bridges
`HasEigendecomposition.toEigensystem` and
`HasEigendecomposition.toEigendecompositionSpec` then deliver the
downstream data structures unchanged.

## Real lemma proved here

`empiricalCovariance_symm` — the empirical covariance kernel
`Ĉ_n(s, t)(ω) = n⁻¹ Σᵢ Xᵢ(ω, s) · Xᵢ(ω, t)` is symmetric in `(s, t)`.
This is a one-line consequence of the commutativity of `*` on `ℝ`.

The remaining `HasEigendecomposition` content is a Prop predicate; its
extraction lemmas are pure data shuffling.
-/

noncomputable section

namespace Statlean.CoxChangePoint
namespace SpectralOperator

open MeasureTheory Statlean.CoxChangePoint.FPC
  Statlean.CoxChangePoint.SpectralBridge

/-! ### Symmetric kernel operator (data-only record) -/

/-- A symmetric measurable kernel `K : D → D → ℝ` on a measurable space
`D`.  This packages just enough data to describe the symbol of an integral
operator on `L²(D, ν)`; we do not (yet) construct the operator itself
because Mathlib lacks the integral-operator/Hilbert-Schmidt API in the
form we need.

* `kernel` — the kernel function `K(s, t)`.
* `symm` — pointwise symmetry `K s t = K t s`.
* `meas_left s` — measurability of `t ↦ K s t`.
* `meas_right t` — measurability of `s ↦ K s t`.

The measurability fields are stated in two directions because Mathlib's
typical use sites either fix `s` and integrate in `t` (eigen-relation) or
swap the roles (Fubini reductions). -/
structure SymmetricKernelOperator (D : Type*) [MeasurableSpace D] where
  /-- The kernel `K : D → D → ℝ`. -/
  kernel : D → D → ℝ
  /-- `K` is symmetric: `K s t = K t s`. -/
  symm : ∀ s t, kernel s t = kernel t s
  /-- For each `s`, the partial map `t ↦ K s t` is measurable. -/
  meas_left : ∀ s, Measurable (fun t => kernel s t)
  /-- For each `t`, the partial map `s ↦ K s t` is measurable. -/
  meas_right : ∀ t, Measurable (fun s => kernel s t)

namespace SymmetricKernelOperator

variable {D : Type*} [MeasurableSpace D]

/-! ### Symmetry of the empirical covariance kernel

This is the only nontrivial proof in this file: the empirical covariance
`Ĉ_n(s, t)(ω) = n⁻¹ Σᵢ Xᵢ(ω, s) · Xᵢ(ω, t)` is symmetric in `(s, t)`,
because each summand `Xᵢ(ω, s) · Xᵢ(ω, t)` is symmetric in `(s, t)` by
commutativity of multiplication on `ℝ`. -/

/-- The empirical covariance kernel is symmetric in its two spatial
arguments. -/
lemma empiricalCovariance_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (X : Fin n → FunctionalSample Ω D) (s t : D) (ω : Ω) :
    empiricalCovariance n X s t ω = empiricalCovariance n X t s ω := by
  unfold empiricalCovariance
  refine congrArg (fun z => (1 / (n : ℝ)) * z) ?_
  refine Finset.sum_congr rfl ?_
  intro i _
  exact mul_comm _ _

/-! ### Wrapper: empirical covariance as a `SymmetricKernelOperator`

For each fixed realisation `ω`, the empirical covariance kernel
`(s, t) ↦ Ĉ_n(s, t)(ω)` is a symmetric measurable kernel on `D`.  The
measurability of the partial maps is requested as hypotheses on `X` (each
`Xᵢ` measurable in the spatial variable `s` for the fixed `ω`); this is
the standard regularity assumption on a `FunctionalSample`. -/

/-- Build a `SymmetricKernelOperator D` from the empirical covariance
kernel at a fixed realisation `ω`, given that each sample `Xᵢ ω : D → ℝ`
is measurable in the spatial variable. -/
def ofEmpiricalCov
    {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (X : Fin n → FunctionalSample Ω D) (ω : Ω)
    (hX : ∀ i, Measurable (fun s => X i ω s)) :
    SymmetricKernelOperator D where
  kernel := fun s t => empiricalCovariance n X s t ω
  symm := fun s t => empiricalCovariance_symm X s t ω
  meas_left := by
    intro s
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ ?_
    intro i _
    exact ((hX i).comp measurable_const).mul (hX i)
  meas_right := by
    intro t
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ ?_
    intro i _
    exact (hX i).mul ((hX i).comp measurable_const)

end SymmetricKernelOperator

/-! ### `HasEigendecomposition` predicate

The contract that whoever supplies a spectral decomposition for a
`SymmetricKernelOperator` must satisfy.  We take this as a `structure`
of `Prop`-valued / data-valued fields, mirroring the shape of
`EigendecompositionSpec` from `SpectralBridge.lean` but keyed on the
abstract symmetric kernel record rather than on the empirical covariance
specifically.

Once Mathlib provides the spectral theorem for compact self-adjoint
operators on `L²` plus a measurable selection of eigenpairs, the
existence of a `HasEigendecomposition` for any square-integrable
symmetric kernel will be a theorem rather than a hypothesis; for now it
is supplied by the user. -/

/-- Spectral decomposition data for a `SymmetricKernelOperator K` on
`L²(D, ν)`.

* `lam` and `phi` are the eigenvalues / eigenfunctions.
* `lam_nonneg` / `phi_meas` give the regularity needed by `Eigensystem`.
* `eigen_relation` is the integral-equation form of `T_K φ_k = λ_k φ_k`.
* `orthonormal` is the standard `L²(D, ν)` orthonormality of `(φ_k)`.
* `lam_decreasing` is the convention that eigenvalues are listed in
  nonincreasing order. -/
structure HasEigendecomposition
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (T : SymmetricKernelOperator D) where
  /-- Eigenvalues. -/
  lam : ℕ → ℝ
  /-- Eigenfunctions. -/
  phi : ℕ → D → ℝ
  /-- Eigenvalues are nonnegative (PSD covariance). -/
  lam_nonneg : ∀ k, 0 ≤ lam k
  /-- Each eigenfunction is measurable. -/
  phi_meas : ∀ k, Measurable (phi k)
  /-- Integral-form eigen-relation
  `∫ t, K(s, t) · φ_k(t) dν(t) = λ_k · φ_k(s)`. -/
  eigen_relation :
    ∀ (k : ℕ) (s : D),
      ∫ t, T.kernel s t * phi k t ∂ν = lam k * phi k s
  /-- `L²(D, ν)` orthonormality of the eigenfunctions. -/
  orthonormal :
    ∀ (k j : ℕ),
      ∫ t, phi k t * phi j t ∂ν = (if k = j then (1 : ℝ) else 0)
  /-- Eigenvalues are nonincreasing. -/
  lam_decreasing : ∀ k, lam (k + 1) ≤ lam k

namespace HasEigendecomposition

variable {D : Type*} [MeasurableSpace D]

/-! ### Bridges to FPC's `Eigensystem` and `EigendecompositionSpec` -/

/-- Extract an `Eigensystem D` from a `HasEigendecomposition` instance.
This forgets the spectral structure (eigen-relation, orthonormality,
ordering) and keeps only the data plus regularity needed by the FPC
layer. -/
def toEigensystem {ν : Measure D} {T : SymmetricKernelOperator D}
    (H : HasEigendecomposition ν T) : Eigensystem D where
  lam := H.lam
  phi := H.phi
  lam_nonneg := H.lam_nonneg
  phi_meas := H.phi_meas

/-- For a sample `X : Fin n → FunctionalSample Ω D` whose every realisation
is measurable in the spatial variable, an `Ω`-indexed family of
`HasEigendecomposition` instances for the empirical covariance kernel
yields an `EigendecompositionSpec` in the sense of `SpectralBridge.lean`.

The `Ω`-family is the standard form of measurable spectral selection
(separately for each realisation `ω`, then bundled). -/
def toEigendecompositionSpec
    {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure D} {n : ℕ} {X : Fin n → FunctionalSample Ω D}
    (hX : ∀ i ω, Measurable (fun s => X i ω s))
    (H : ∀ ω, HasEigendecomposition ν
              (SymmetricKernelOperator.ofEmpiricalCov X ω (fun i => hX i ω))) :
    EigendecompositionSpec ν n X where
  eigsys_of := fun ω => (H ω).toEigensystem
  eigen_relation := by
    intro k ω s
    -- `(toEigensystem (H ω)).phi k = (H ω).phi k` by `rfl`,
    -- and the kernel of `ofEmpiricalCov` at `(s, t)` is exactly
    -- `empiricalCovariance n X s t ω`, again by `rfl`.
    exact (H ω).eigen_relation k s
  orthonormal := by
    intro k j ω
    exact (H ω).orthonormal k j
  lam_decreasing := by
    intro ω k
    exact (H ω).lam_decreasing k

end HasEigendecomposition

end SpectralOperator
end Statlean.CoxChangePoint

end

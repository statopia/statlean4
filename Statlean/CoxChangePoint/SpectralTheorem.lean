import Mathlib
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.SpectralOperator
import Statlean.CoxChangePoint.L2Operator
import Statlean.CoxChangePoint.L2OperatorMap

/-!
# Cox change-point — Spectral theorem bridges

This file connects Mathlib's spectral theory of symmetric / self-adjoint
operators to the `Statlean.CoxChangePoint.FPC.Eigensystem` data type used
by the FPC layer of the CP-FLCRM model.

## Mathlib coverage scouting

What Mathlib (v4.28) currently provides:

* `LinearMap.IsSymmetric` (`Mathlib.Analysis.InnerProductSpace.Symmetric`):
  symmetric linear endomorphisms of an inner product space, defined by
  `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.
* `LinearMap.IsSymmetric.eigenvectorBasis` and
  `LinearMap.IsSymmetric.eigenvalues`
  (`Mathlib.Analysis.InnerProductSpace.Spectrum`):
  the spectral theorem for symmetric endomorphisms of a *finite-dimensional*
  inner product space.  Returns an `OrthonormalBasis (Fin n) ℝ H` of
  eigenvectors plus a `Fin n → ℝ` of eigenvalues sorted in decreasing
  order.
* `LinearMap.IsSymmetric.apply_eigenvectorBasis`: the eigen-relation
  `T (basis i) = (eigenvalues i) • basis i`.
* `IsSelfAdjoint` (in `Mathlib.Analysis.InnerProductSpace.Adjoint`,
  via the `StarRing` structure on `E →L[𝕜] E`): `T† = T` for a
  `ContinuousLinearMap`.
* `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`: the equivalence
  between operator self-adjointness (in the `*`-ring sense) and the
  symmetric inner-product identity.
* `IsCompactOperator` (`Mathlib.Analysis.Normed.Operator.Compact`):
  generic compact-operator API.

What Mathlib *does not* yet provide (relevant to FPC):

* The spectral theorem for compact self-adjoint operators on an
  *infinite-dimensional* separable Hilbert space.  In particular, no
  general statement that the eigenvalues of a compact self-adjoint
  operator tend to zero, or that there exists an orthonormal basis of
  eigenvectors.
* `IsHilbertSchmidt` for L²-integral kernels with the canonical
  Hilbert-Schmidt norm bound.
* Measurable selection of an eigenbasis from a measurably-varying
  family of compact self-adjoint operators (needed for the empirical
  covariance kernel parametrised by `ω`).

This file therefore:

1. Provides a real bridge for the *finite-dimensional* case.
2. Encodes the *infinite-dimensional* spectral theorem as a hypothesis
   structure (`InfiniteDimSpectralData`) until Mathlib catches up.
3. Provides a bridge from `InfiniteDimSpectralData` (on `Lp ℝ 2 ν`)
   plus a measurable-selection witness back to `FPC.Eigensystem D`.
4. Restates the `IsSelfAdjoint` ↔ `IsSymmetric` Mathlib equivalence at
   the namespace level for downstream convenience.
-/

open MeasureTheory Real

namespace Statlean.CoxChangePoint
namespace SpectralTheorem

universe u

/-! ## 1. Self-adjointness ↔ symmetry on a real inner product space

Mathlib provides this equivalence as
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.  We re-export it
in our namespace so downstream files do not need to import the full
adjoint module just to use the symmetry side. -/

section IsSelfAdjoint

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- For a continuous linear endomorphism on a real Hilbert space,
self-adjointness (`A† = A`) is equivalent to symmetry of the underlying
linear map (`⟪A x, y⟫ = ⟪x, A y⟫`). -/
theorem isSelfAdjoint_iff_isSymmetric (A : H →L[ℝ] H) :
    IsSelfAdjoint A ↔ (A : H →ₗ[ℝ] H).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric

/-- Forward direction: a self-adjoint continuous linear endomorphism
has a symmetric underlying linear map. -/
theorem IsSelfAdjoint.isSymmetric {A : H →L[ℝ] H} (hA : IsSelfAdjoint A) :
    (A : H →ₗ[ℝ] H).IsSymmetric :=
  (isSelfAdjoint_iff_isSymmetric A).mp hA

/-- Backward direction: a symmetric continuous linear endomorphism is
self-adjoint. -/
theorem isSelfAdjoint_of_isSymmetric {A : H →L[ℝ] H}
    (hA : (A : H →ₗ[ℝ] H).IsSymmetric) : IsSelfAdjoint A :=
  (isSelfAdjoint_iff_isSymmetric A).mpr hA

end IsSelfAdjoint

/-! ## 2. Finite-dimensional spectral bridge

Take a real, finite-dimensional inner product space `H` equipped with
a Borel σ-algebra (so that continuous functions on `H` are measurable).
Given a symmetric endomorphism `T`, build an `Eigensystem H` whose
`phi k : H → ℝ` is the inner product against the `k`-th eigenvector
(or zero out of range), and whose `lam k` is the corresponding
eigenvalue (or zero out of range).

We do **not** claim the eigen-relation here: the `Eigensystem`
structure intentionally does not bake one in (see
`Statlean/CoxChangePoint/FPC.lean`).  Downstream consumers wanting the
eigen-relation should invoke `LinearMap.IsSymmetric.apply_eigenvectorBasis`
directly. -/

section FiniteDim

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The eigenvalue function used by `FiniteDimSpectralBridge`: the
Mathlib spectral eigenvalues for `k < n`, otherwise zero.  Always
nonnegative is **not** claimed (see the `lam_nonneg` issue handled by
taking the `max` with zero). -/
noncomputable def finiteDimLam {T : H →ₗ[ℝ] H} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ H = n) (k : ℕ) : ℝ :=
  if h : k < n then max 0 (hT.eigenvalues hn ⟨k, h⟩) else 0

set_option linter.unusedSectionVars false in
/-- Nonnegativity of `finiteDimLam`: by construction we take `max 0`. -/
lemma finiteDimLam_nonneg {T : H →ₗ[ℝ] H} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ H = n) (k : ℕ) :
    0 ≤ finiteDimLam hT hn k := by
  unfold finiteDimLam
  split_ifs with h
  · exact le_max_left _ _
  · exact le_refl 0

/-- The `k`-th coordinate function: pair `H` with the `k`-th eigenvector
of `T` (or the zero vector when `k ≥ n`).  This is continuous, hence
Borel-measurable. -/
noncomputable def finiteDimPhi {T : H →ₗ[ℝ] H} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ H = n) (k : ℕ) : H → ℝ :=
  if h : k < n then
    fun x => @inner ℝ _ _ x (hT.eigenvectorBasis hn ⟨k, h⟩)
  else fun _ => 0

/-- Each `finiteDimPhi` is measurable. -/
lemma finiteDimPhi_meas {T : H →ₗ[ℝ] H} (hT : T.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ H = n) (k : ℕ) :
    Measurable (finiteDimPhi hT hn k) := by
  unfold finiteDimPhi
  split_ifs with h
  · exact (continuous_id.inner continuous_const).measurable
  · exact measurable_const

/-- **Finite-dimensional spectral bridge.**  Given a symmetric
endomorphism `T` of a finite-dimensional real Borel inner product
space `H`, package the Mathlib spectral data as an
`FPC.Eigensystem H`. -/
noncomputable def FiniteDimSpectralBridge {T : H →ₗ[ℝ] H}
    (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ H = n) :
    FPC.Eigensystem H where
  lam := finiteDimLam hT hn
  phi := finiteDimPhi hT hn
  lam_nonneg := finiteDimLam_nonneg hT hn
  phi_meas := finiteDimPhi_meas hT hn

end FiniteDim

/-! ## 3. Infinite-dimensional spectral theorem (hypothesis form)

Mathlib v4.28 has no spectral theorem for compact self-adjoint
operators on an infinite-dimensional separable Hilbert space.  Until
that lands, we encode the conclusion as a `structure` so that
downstream files can take it as a hypothesis. -/

/-- **Hypothesis-form spectral theorem.**  For a (compact) self-adjoint
operator `T` on a Hilbert space `H`, this records the existence of an
orthonormal sequence of eigenvectors with eigenvalues tending to zero.

Note: we deliberately do *not* assume completeness of the eigenfamily
(i.e. that they form a basis).  Some downstream uses only need the
weaker form, and a complete formulation would be a follow-up
infrastructure item. -/
structure InfiniteDimSpectralData
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (T : H →L[ℝ] H) where
  /-- Orthonormal eigenfunctions. -/
  eigenfn : ℕ → H
  /-- Corresponding eigenvalues. -/
  eigval : ℕ → ℝ
  /-- Eigen-relation: `T φ_k = λ_k · φ_k`. -/
  eigen_relation : ∀ k, T (eigenfn k) = (eigval k) • (eigenfn k)
  /-- Orthonormality of the eigenfunctions. -/
  orthonormal : ∀ k j,
    @inner ℝ _ _ (eigenfn k) (eigenfn j) = if k = j then (1 : ℝ) else 0
  /-- Eigenvalues tend to zero (compact-operator property). -/
  eigval_tendsto : Filter.Tendsto eigval Filter.atTop (nhds 0)

namespace InfiniteDimSpectralData

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {T : H →L[ℝ] H}

/-- Self inner product of an eigenfunction is one. -/
lemma inner_self_eq_one (S : InfiniteDimSpectralData H T) (k : ℕ) :
    @inner ℝ _ _ (S.eigenfn k) (S.eigenfn k) = 1 := by
  have := S.orthonormal k k
  simpa using this

/-- Distinct eigenfunctions are orthogonal. -/
lemma inner_of_ne (S : InfiniteDimSpectralData H T) {k j : ℕ}
    (hkj : k ≠ j) :
    @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 := by
  have := S.orthonormal k j
  simpa [hkj] using this

end InfiniteDimSpectralData

/-! ## 4. Bridge: `InfiniteDimSpectralData` on `Lp` → `FPC.Eigensystem`

Take an L²-bounded kernel operator data structure
(`L2KernelMapData ν`) — which packages a continuous linear map
`T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν` from a kernel — together with an
`InfiniteDimSpectralData` instance for that operator.  Each
`eigenfn k : Lp ℝ 2 ν` is an equivalence class; we extract a
canonical measurable representative via `AEStronglyMeasurable.mk`.

The eigenvalue is wrapped through `max 0` to satisfy the FPC layer's
`lam_nonneg` requirement; the spectral structure is *not* required to
have nonnegative eigenvalues (only PSD covariance operators do), so
this reflects the FPC layer's intended use rather than the abstract
spectral data. -/

section Bridge

open Statlean.CoxChangePoint.L2Operator

variable {D : Type u} [MeasurableSpace D] {ν : Measure D}

/-- The `k`-th eigenfunction as a measurable representative on `D`. -/
noncomputable def InfiniteDimSpectralData.phiRepr
    (𝓜 : L2KernelMapData ν)
    (S : InfiniteDimSpectralData (Lp ℝ 2 ν) 𝓜.toContinuousLinearMap)
    (k : ℕ) : D → ℝ :=
  (Lp.aestronglyMeasurable (S.eigenfn k)).mk (S.eigenfn k)

/-- `phiRepr` is genuinely measurable. -/
lemma InfiniteDimSpectralData.phiRepr_meas
    (𝓜 : L2KernelMapData ν)
    (S : InfiniteDimSpectralData (Lp ℝ 2 ν) 𝓜.toContinuousLinearMap)
    (k : ℕ) : Measurable (InfiniteDimSpectralData.phiRepr 𝓜 S k) :=
  (Lp.aestronglyMeasurable (S.eigenfn k)).stronglyMeasurable_mk.measurable

/-- The `k`-th nonneg-clipped eigenvalue. -/
noncomputable def InfiniteDimSpectralData.lamClip
    (𝓜 : L2KernelMapData ν)
    (S : InfiniteDimSpectralData (Lp ℝ 2 ν) 𝓜.toContinuousLinearMap)
    (k : ℕ) : ℝ := max 0 (S.eigval k)

lemma InfiniteDimSpectralData.lamClip_nonneg
    (𝓜 : L2KernelMapData ν)
    (S : InfiniteDimSpectralData (Lp ℝ 2 ν) 𝓜.toContinuousLinearMap)
    (k : ℕ) : 0 ≤ InfiniteDimSpectralData.lamClip 𝓜 S k :=
  le_max_left _ _

/-- **Infinite-dim spectral bridge to `FPC.Eigensystem`.**  Given a
kernel operator on `Lp ℝ 2 ν` and an infinite-dim spectral data
instance for it, package the eigenfunctions (as measurable
representatives on `D`) and (clipped, nonneg) eigenvalues into an
`FPC.Eigensystem D`.

Because the FPC layer of `Eigensystem D` does not bake in the
eigen-relation or orthonormality (those are properties of *specific*
eigensystems supplied as additional hypotheses), this bridge transfers
exactly the data the FPC layer needs.  The eigen-relation and
orthonormality remain available on the `S` side. -/
noncomputable def InfiniteDimSpectralData.toEigensystem
    (𝓜 : L2KernelMapData ν)
    (S : InfiniteDimSpectralData (Lp ℝ 2 ν) 𝓜.toContinuousLinearMap) :
    FPC.Eigensystem D where
  lam := InfiniteDimSpectralData.lamClip 𝓜 S
  phi := InfiniteDimSpectralData.phiRepr 𝓜 S
  lam_nonneg := InfiniteDimSpectralData.lamClip_nonneg 𝓜 S
  phi_meas := InfiniteDimSpectralData.phiRepr_meas 𝓜 S

end Bridge

end SpectralTheorem
end Statlean.CoxChangePoint

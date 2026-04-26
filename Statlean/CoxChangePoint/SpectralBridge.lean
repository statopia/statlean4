import Mathlib
import Statlean.CoxChangePoint.FPC

/-!
# Cox change-point — Spectral bridge (specification layer)

This file provides an **abstract specification** for what the spectral theory
layer must provide in order to construct an `EstimatedEigensystem` from the
empirical covariance kernel `Ĉ_n` (defined in `FPC.lean`).

## Why a specification, not a construction

The actual construction of the estimated eigensystem requires solving the
eigenproblem of the integral operator with kernel `Ĉ_n(·, ·)(ω)` on
`L²(D, ν)`.  This is a deep operation that needs:

* spectral theory of compact self-adjoint operators on `L²`;
* Hilbert-Schmidt theory (since the kernel is square-integrable);
* a measurable selection theorem (eigenpairs depend on `ω`).

Mathlib's coverage of these tools is currently insufficient for `L²(D, ν)`
in full generality (the relevant API is `Module.End.Eigenspaces`,
`IsHilbertSchmidt`, `CompactOperator.spectrum` and friends, but they do not
yet compose into the Karhunen-Loève decomposition we need).

Rather than block downstream work, we package what spectral theory *would*
give us as a `structure` of `Prop`-valued hypotheses
(`EigendecompositionSpec`).  Anyone who can later instantiate this
structure (by hand for finite-dimensional `D`, or once Mathlib catches up
in general) automatically gets an `EstimatedEigensystem` and the
perturbation bounds we need.

## Forward links

When Mathlib gains:
* `Module.End.HasEigenvalue` for compact operators on Hilbert spaces,
* an `IsHilbertSchmidt` API closed under the integral-operator construction,
* `CompactOperator.spectrum` over `ℝ` with measurable eigenpair selection,

then `EigendecompositionSpec` should be promoted from a hypothesis to a
theorem, with the field `eigsys_of` constructed from the spectral
decomposition of the empirical covariance integral operator.
-/

noncomputable section

namespace Statlean.CoxChangePoint.SpectralBridge

open MeasureTheory Statlean.CoxChangePoint.FPC

/-! ### Eigendecomposition specification

What the spectral layer must deliver: an `Ω`-indexed eigensystem of the
empirical covariance kernel, together with the eigen-relation,
orthonormality of eigenfunctions, and decreasing eigenvalues.
-/

/-- Specification of the eigendecomposition of the empirical covariance
kernel `empiricalCovariance n X · ·`.

A term of this type packages the data + properties that spectral theory
would produce.  Each field is a hypothesis the user must supply (or that
will eventually be discharged by a Mathlib spectral theorem). -/
structure EigendecompositionSpec
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    (ν : Measure D) (n : ℕ)
    (X : Fin n → FunctionalSample Ω D) where
  /-- For each realisation `ω`, an eigensystem of the empirical covariance
  kernel `Ĉ_n(·, ·)(ω)`. -/
  eigsys_of : Ω → Eigensystem D
  /-- **Eigen-relation.**  For each index `k`, each realisation `ω`, and
  each `s ∈ D`, the integral operator with kernel `Ĉ_n(s, t)(ω)` applied
  to `(eigsys_of ω).phi k` returns `(eigsys_of ω).lam k * (eigsys_of ω).phi k s`.

  In symbols:
  `∫ t, Ĉ_n(s, t)(ω) · φ̂_k(t) dν(t) = λ̂_k · φ̂_k(s)`. -/
  eigen_relation :
    ∀ (k : ℕ) (ω : Ω) (s : D),
      ∫ t, empiricalCovariance n X s t ω * (eigsys_of ω).phi k t ∂ν
        = (eigsys_of ω).lam k * (eigsys_of ω).phi k s
  /-- **Orthonormality** of eigenfunctions in `L²(D, ν)`. -/
  orthonormal :
    ∀ (k j : ℕ) (ω : Ω),
      ∫ t, (eigsys_of ω).phi k t * (eigsys_of ω).phi j t ∂ν
        = (if k = j then (1 : ℝ) else 0)
  /-- **Eigenvalues are nonincreasing** in `k` (standard convention for
  spectral decompositions of compact PSD operators). -/
  lam_decreasing :
    ∀ (ω : Ω) (k : ℕ), (eigsys_of ω).lam (k + 1) ≤ (eigsys_of ω).lam k

/-! ### Bridge to `EstimatedEigensystem` -/

/-- From an `EigendecompositionSpec`, extract the underlying
`EstimatedEigensystem` (as defined in `FPC.lean`).  This is just the
projection `spec.eigsys_of`; the additional hypotheses are discarded at
this stage but remain available to downstream consumers via the spec. -/
def EstimatedEigensystem.fromSpec
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    {ν : Measure D} {n : ℕ}
    {X : Fin n → FunctionalSample Ω D}
    (spec : EigendecompositionSpec ν n X) : EstimatedEigensystem Ω D :=
  spec.eigsys_of

/-! ### Sin-Theta perturbation bound (specification)

Once we have both a true eigensystem `eigsys_true` and an estimated one
`eigsys_est`, the Davis-Kahan / Sin-Theta theorem gives a perturbation
bound of the form
`‖φ̂_k − φ_k‖_{L²}² ≤ C_pert · ‖Ĉ_n − C‖_op²`,
where the operator-norm difference is between integral operators on
`L²(D, ν)`.

We package this as a hypothesis structure rather than a proven theorem. -/

/-- Specification of the Sin-Theta / Davis-Kahan perturbation bound that
links eigenfunction estimation error to operator-norm covariance error.

* `cov_diff_sq ω` is meant to represent `‖Ĉ_n(ω) − C‖_op²`, the squared
  operator-norm difference between the empirical and population covariance
  integral operators (we leave its concrete definition to downstream
  spectral infrastructure).
* The bound says the squared `L²(D, ν)` distance between `φ̂_k(ω, ·)` and
  `φ_k(·)` is controlled by `cov_diff_sq ω`, uniformly in `k` and `ω`. -/
structure PerturbationBound
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    (ν : Measure D)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (cov_diff_sq : Ω → ℝ) where
  /-- Universal perturbation constant (depends on the eigenvalue gaps of
  the true covariance, etc.). -/
  C_pert : ℝ
  /-- The constant is positive. -/
  C_pert_pos : 0 < C_pert
  /-- The squared `L²(D, ν)` distance between the estimated and true
  eigenfunctions is bounded by `C_pert · ‖Ĉ_n − C‖_op²`. -/
  l2_bound :
    ∀ (k : ℕ) (ω : Ω),
      ∫ t, ((eigsys_est ω).phi k t - eigsys_true.phi k t) ^ 2 ∂ν
        ≤ C_pert * cov_diff_sq ω

end Statlean.CoxChangePoint.SpectralBridge

end

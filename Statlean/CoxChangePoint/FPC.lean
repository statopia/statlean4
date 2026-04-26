import Mathlib
import Statlean.CoxChangePoint.Foundation

/-!
# Cox change-point — Functional principal components (FPC) infrastructure

Concrete data model and basic operations for the functional principal
components of the functional covariate `X_i` of the CP-FLCRM model.

The functional covariate `X : Ω → D → ℝ` is a random element of `L²(D, ν)`
for some domain `D` with measure `ν`.  The Karhunen-Loève decomposition
gives `X = Σ_k ξ_k φ_k` where `(λ_k, φ_k)` is the eigensystem of the
covariance operator and `ξ_k = ⟨X, φ_k⟩` are the (uncorrelated) FPC scores.

This file:
* defines the `Eigensystem D` type (countable sequence of eigenpairs);
* the FPC score `ξ_k = ∫ X·φ_k dν`;
* truncated FPC scores as `Fin d → ℝ`;
* the empirical covariance kernel from `n` samples;
* a constructor that builds `CoxObs p d` from a survival observation,
  scalar covariates, and a functional covariate (via FPC truncation).

The construction of the *estimated* eigensystem from sample data is
non-trivial (eigendecomposition of the empirical covariance integral
operator).  We provide it as a *data hypothesis* — `EstimatedEigensystem`
— that whoever instantiates the model must supply.  The Cox layer then
sees both the true and estimated eigensystems and can talk about
`ξ̂_k − ξ_k` (the FPC score estimation error of Lemma S2_supp).
-/

open MeasureTheory Real Finset

namespace Statlean.CoxChangePoint
namespace FPC

/-! ### Eigensystem -/

/-- An eigensystem on the domain `D`: a countable sequence of eigenvalues and
eigenfunctions. We do NOT bake in orthonormality / actual eigenproblem
satisfaction here — those are facts about specific eigensystems, supplied
as additional hypotheses when needed. -/
structure Eigensystem (D : Type*) [MeasurableSpace D] where
  /-- Eigenvalues `lam_k` (typically nonnegative, decreasing). -/
  lam : ℕ → ℝ
  /-- Eigenfunctions `phi_k : D → ℝ`. -/
  phi : ℕ → D → ℝ
  /-- Eigenvalues are nonnegative (covariance operator is PSD). -/
  lam_nonneg : ∀ k, 0 ≤ lam k
  /-- Each eigenfunction is measurable. -/
  phi_meas : ∀ k, Measurable (phi k)

/-! ### Functional sample -/

/-- A random functional covariate: `X : Ω → (D → ℝ)`. -/
def FunctionalSample (Ω : Type*) [MeasurableSpace Ω]
    (D : Type*) [MeasurableSpace D] : Type _ :=
  Ω → D → ℝ

namespace FunctionalSample

variable {Ω : Type*} [MeasurableSpace Ω] {D : Type*} [MeasurableSpace D]

/-- The FPC score `ξ_k(ω) = ∫ X(ω, t) · φ_k(t) dν(t)`. -/
noncomputable def fpcScore (ν : Measure D) (X : FunctionalSample Ω D)
    (eigsys : Eigensystem D) (k : ℕ) (ω : Ω) : ℝ :=
  ∫ t, (X ω t) * (eigsys.phi k t) ∂ν

/-- The truncated FPC scores: the first `d` scores as a function `Fin d → ℝ`. -/
noncomputable def truncatedScores (ν : Measure D) (X : FunctionalSample Ω D)
    (eigsys : Eigensystem D) (d : ℕ) (ω : Ω) : Fin d → ℝ :=
  fun k => fpcScore ν X eigsys k.val ω

/-- The truncation residual `r_d(ω, t) = X(ω, t) − Σ_{k<d} ξ_k(ω) φ_k(t)`. -/
noncomputable def truncationResidual (ν : Measure D) (X : FunctionalSample Ω D)
    (eigsys : Eigensystem D) (d : ℕ) (ω : Ω) (t : D) : ℝ :=
  X ω t - ∑ k ∈ Finset.range d, fpcScore ν X eigsys k ω * eigsys.phi k t

end FunctionalSample

/-! ### Empirical covariance and estimated eigensystem -/

/-- The empirical covariance kernel `Ĉ_n(s, t)(ω) = n⁻¹ Σᵢ Xᵢ(ω, s)·Xᵢ(ω, t)`,
viewed as a function `D × D → Ω → ℝ` (or equivalently `D → D → Ω → ℝ`).

`X` is supplied as `Fin n → Ω → D → ℝ`. -/
noncomputable def empiricalCovariance {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (n : ℕ)
    (X : Fin n → FunctionalSample Ω D) (s t : D) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω s) * (X i ω t)

/-- The estimated eigensystem (as a function of ω): for each realisation,
an eigensystem of the empirical covariance kernel.

In the actual Cox pipeline, `EstimatedEigensystem` is constructed by solving
the eigenproblem for the integral operator with kernel `Ĉ_n(·,·)(ω)` —
a deep operation requiring spectral theory of compact self-adjoint
operators on `L²(D, ν)`.  We take it as a data hypothesis here. -/
def EstimatedEigensystem (Ω : Type*) [MeasurableSpace Ω]
    (D : Type*) [MeasurableSpace D] : Type _ :=
  Ω → Eigensystem D

/-! ### Building Cox observations from functional data -/

/-- Construct a single `CoxObs p d` from survival data, scalar covariates,
a functional covariate, and a (true OR estimated) eigensystem.

If the eigensystem is the *true* one, this gives observations with the
true (population) FPC scores `ξ_{ik}`.  If it is the *estimated* one,
we get the estimated scores `ξ̂_{ik}` used in the empirical objective. -/
noncomputable def CoxObs.ofFunctional
    {p d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (T : Ω → ℝ) (δ : Ω → Bool) (Z₁ : Ω → Fin p → ℝ) (Z₂ : Ω → ℝ)
    (X : FunctionalSample Ω D) (eigsys : Eigensystem D)
    (ω : Ω) : CoxObs p d :=
  { T := T ω
    δ := δ ω
    Z₁ := Z₁ ω
    Z₂ := Z₂ ω
    ξ := FunctionalSample.truncatedScores ν X eigsys d ω }

/-- The FPC score estimation error `v_k = ξ̂_k − ξ_k` for each subject.

Given a single subject's functional covariate `X_i`, the true eigensystem
`eigsys_true`, and the estimated (ω-dependent) eigensystem `eigsys_est`,
returns the difference in the k-th score. -/
noncomputable def fpcScoreError {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (X : FunctionalSample Ω D)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (k : ℕ) (ω : Ω) : ℝ :=
  FunctionalSample.fpcScore ν X (eigsys_est ω) k ω
    - FunctionalSample.fpcScore ν X eigsys_true k ω

/-- Sup over a parameter space and a subject set of the absolute FPC score error
weighted by the change-point coefficients. This is the `vᵢ` quantity in the
paper's Lemma S2_supp:
  `vᵢ(θ) = Σ_{k=1}^{d_n} (ξ̂_{ik} − ξ_{ik})·[α_k I(Z₂ᵢ ≤ η) + β_k I(Z₂ᵢ > η)]`. -/
noncomputable def vScoreError {p d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (X : FunctionalSample Ω D) (Z₂ : Ω → ℝ)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (θ : CoxParam p d) (ω : Ω) : ℝ :=
  ∑ k : Fin d,
    fpcScoreError ν X eigsys_true eigsys_est k.val ω *
      (if Z₂ ω ≤ θ.η then θ.α k else θ.β k)

/-! ### Wiring into Foundation's `Sample` -/

/-- Build a `Foundation.Sample Ω p d` (cf. `Statlean/CoxChangePoint/Foundation.lean`)
    from `n`-indexed survival/covariate data plus a functional covariate and
    a (true) eigensystem.  The truncation level `d` is fixed.

    For the *estimated* version (Cox empirical objective uses estimated FPC scores),
    pass `eigsys_est ω` instead of a fixed `eigsys`. -/
noncomputable def buildSample
    {p d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (T : ℕ → ℕ → Ω → ℝ) (δ : ℕ → ℕ → Ω → Bool)
    (Z₁ : ℕ → ℕ → Ω → Fin p → ℝ) (Z₂ : ℕ → ℕ → Ω → ℝ)
    (X : ℕ → ℕ → FunctionalSample Ω D) (eigsys : Eigensystem D) :
    Statlean.CoxChangePoint.Sample Ω p d :=
  fun n i ω =>
    CoxObs.ofFunctional (d := d) ν
      (T n i) (δ n i) (Z₁ n i) (Z₂ n i) (X n i) eigsys ω

end FPC
end Statlean.CoxChangePoint

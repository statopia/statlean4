import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# High-dimensional mediation analysis — Assumption (A1)

This file formalizes **Assumption (A1)** from Section 3.1 of the paper on
testing the overall mediation effect in high-dimensional settings.

The assumption is a *structural predicate* bundling:

* i.i.d. centered sub-Gaussian design vectors `X_i = (A_i, M_i) ∈ ℝ^{q+p}`
  with covariance eigenvalues in `[c₀, C₀]`;
* i.i.d. mediator-equation errors `E_i ∈ ℝ^p` satisfying the conditional
  moment conditions `𝔼[E_i|A_i] = 0`, `Var[E_i|A_i] = Σ_E`, and
  norm-sub-Gaussianity with parameter `σ`;
* i.i.d. sub-Gaussian scalar residuals `Z_i` with `𝔼[Z_i|X_i] = 0`
  and `𝔼[Z_i²|X_i] = σ_Z²`.

Because the assumption is purely definitional, no theorem is proved here;
all fields are mathematical hypotheses that downstream results consume.
-/

namespace Statlean.HDMediation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section SubGaussianity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `l2norm x = √(∑ xᵢ²)` — the Euclidean (L²) norm of a real Fin-indexed
vector, stated with no dependence on `EuclideanSpace` instances. -/
noncomputable def l2norm {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- A scalar random variable `Y : Ω → ℝ` is **sub-Gaussian with parameter
`σ`** if it has sub-Gaussian tail decay from its mean:
`ℙ(|Y - 𝔼Y| ≥ t) ≤ 2 exp(-t² / (2 σ²))` for all `t`.

This is the form used in Section 3.1 of the paper. -/
def IsSubGaussianScalar (μ : Measure Ω) (Y : Ω → ℝ) (σ : ℝ) : Prop :=
  ∃ eY : ℝ, ∀ t : ℝ,
    μ {ω | t ≤ |Y ω - eY|} ≤
      2 * ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * σ ^ 2)))

/-- A random vector `S : Ω → Fin d → ℝ` is **(componentwise) sub-Gaussian
with parameter `σ`** if every unit-norm linear combination `vᵀ S` is a
scalar sub-Gaussian with the same parameter. -/
def IsVectorSubGaussian {d : ℕ} (μ : Measure Ω)
    (S : Ω → Fin d → ℝ) (σ : ℝ) : Prop :=
  ∀ v : Fin d → ℝ, (∑ i, v i ^ 2) = 1 →
    IsSubGaussianScalar μ (fun ω => ∑ i, v i * S ω i) σ

/-- A random vector `S : Ω → Fin d → ℝ` is **norm-sub-Gaussian with
parameter `σ`** (in the sense of Jin–Netrapalli–Ge, 2019):
`ℙ(‖S - 𝔼S‖₂ ≥ t) ≤ 2 exp(-t² / (2 σ²))` for all `t`. -/
def IsNormSubGaussian {d : ℕ} (μ : Measure Ω)
    (S : Ω → Fin d → ℝ) (σ : ℝ) : Prop :=
  ∃ eS : Fin d → ℝ, ∀ t : ℝ,
    μ {ω | t ≤ l2norm (fun i => S ω i - eS i)} ≤
      2 * ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * σ ^ 2)))

end SubGaussianity

/-- **Assumption (A1)** from Section 3.1 of the high-dimensional mediation
paper.

The predicate bundles the i.i.d. structure, centering, sub-Gaussian
tails and eigenvalue control of the design `X = (A, M)`, together with
the conditional moment / tail assumptions on the mediator-equation error
`E` and the outcome-equation residual `Z`. -/
structure AssumptionA1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q p n : ℕ)
    (A : Fin n → Ω → Fin q → ℝ)
    (M : Fin n → Ω → Fin p → ℝ)
    (E : Fin n → Ω → Fin p → ℝ)
    (Z : Fin n → Ω → ℝ)
    (σ σZ c₀ C₀ : ℝ)
    (SigmaX : Matrix (Fin (q + p)) (Fin (q + p)) ℝ)
    (SigmaE : Matrix (Fin p) (Fin p) ℝ) : Prop where
  -- ── constants ──
  c₀_pos      : 0 < c₀
  c₀_le_C₀    : c₀ ≤ C₀
  σ_pos       : 0 < σ
  σZ_sq_pos   : 0 < σZ ^ 2
  -- ── covariance Σ_X : eigenvalue sandwich c₀ ≤ λⱼ(Σ_X) ≤ C₀ ──
  SigmaX_hermitian : SigmaX.IsHermitian
  SigmaX_eig_lower : ∀ j, c₀ ≤ SigmaX_hermitian.eigenvalues j
  SigmaX_eig_upper : ∀ j, SigmaX_hermitian.eigenvalues j ≤ C₀
  -- ── X_i := (A_i, M_i) i.i.d. centered sub-Gaussian ──
  X_iid : ∀ i j, IdentDistrib
    (fun ω => Fin.append (A i ω) (M i ω))
    (fun ω => Fin.append (A j ω) (M j ω)) μ μ
  X_independent : iIndepFun (fun (i : Fin n) (ω : Ω) => Fin.append (A i ω) (M i ω)) μ
  X_centered : ∀ i k, ∫ ω, Fin.append (A i ω) (M i ω) k ∂μ = 0
  X_subGaussian : ∀ i, IsVectorSubGaussian μ
    (fun ω => Fin.append (A i ω) (M i ω)) σ
  -- ── mediator-equation error E_i : i.i.d. & conditional on A_i ──
  E_iid : ∀ i j, IdentDistrib (E i) (E j) μ μ
  E_cond_mean : ∀ i j,
    μ[(fun ω => E i ω j) |
        MeasurableSpace.comap (A i) inferInstance]
      =ᵐ[μ] 0
  E_cond_var : ∀ i j k,
    μ[(fun ω => E i ω j * E i ω k) |
        MeasurableSpace.comap (A i) inferInstance]
      =ᵐ[μ] (fun _ => SigmaE j k)
  -- ── Σ_E is symmetric positive semi-definite ──
  SigmaE_posSemidef : SigmaE.PosSemidef
  -- ── conditional on A_i, each E_i is norm-sub-Gaussian with parameter σ ──
  E_normSubG : ∀ i, IsNormSubGaussian μ (E i) σ
  -- ── outcome-equation residual Z_i : i.i.d. sub-Gaussian, conditional on X_i ──
  Z_iid : ∀ i j, IdentDistrib (Z i) (Z j) μ μ
  Z_subGaussian : ∀ i, IsSubGaussianScalar μ (Z i) σZ
  Z_cond_mean : ∀ i,
    μ[Z i |
        MeasurableSpace.comap (fun ω => Fin.append (A i ω) (M i ω)) inferInstance]
      =ᵐ[μ] 0
  Z_cond_sq_mean : ∀ i,
    μ[(fun ω => (Z i ω) ^ 2) |
        MeasurableSpace.comap (fun ω => Fin.append (A i ω) (M i ω)) inferInstance]
      =ᵐ[μ] (fun _ => σZ ^ 2)

end Statlean.HDMediation

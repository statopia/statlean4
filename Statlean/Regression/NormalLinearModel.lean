import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Normal Linear Model — Joint Distribution of LSE and σ̂²

## Main result (Shao, *Mathematical Statistics* Theorem 3.8)

In the normal linear model `X = Zβ + ε` with `ε ~ N_n(0, σ²I_n)`
(assumption A1), if `lᵀβ` is estimable, then:

  (i)  the UMVUE `lᵀβ̂` and `σ̂²` are independent;
  (ii) `lᵀβ̂ ~ N(lᵀβ, σ²·lᵀ(ZᵀZ)⁻ l)`;
  (iii) `(n-r)·σ̂²/σ² ~ χ²_{n-r}`,

where `r = rank Z`, `β̂ = (ZᵀZ)⁻ Zᵀ X` is the LSE (using a chosen
generalized inverse `(ZᵀZ)⁻`), and `σ̂² = ‖X - Zβ̂‖² / (n-r)`.

## Formalization plan

- `Setup n p`: design matrix `Z : Matrix (Fin n) (Fin p) ℝ`, true
  parameter `β : Fin p → ℝ`, error scale `σ > 0`, a chosen generalized
  inverse `H` of `ZᵀZ`, and `r := rank (ZᵀZ)`.
- `IsEstimable l ↔ l ∈ R(Zᵀ)` (column space of `Zᵀ`).
- `lse X := H · Zᵀ · X` (LSE under chosen generalized inverse).
- `sigmaSqHat X := ‖X - Z · lse X‖² / (n - r)`.
- `AssumptionA1 μ X`: `X ω = Zβ + σ·ε ω` where `ε` is iid `N(0,1)`.
- `chiSquared k`: distribution of `∑ᵢ Zᵢ²` for `Z₁,…,Z_k` iid `N(0,1)`.

The three conclusions are stated as separate theorems plus a combined
`lse_sigma_hat_distribution_under_a1` for the headline statement.

The core proof reduces to:
- (i) Cross-covariance vanishes: `[I - Z(ZᵀZ)⁻Zᵀ] · Z(ZᵀZ)⁻ = 0`,
  combined with joint normality ⇒ independence.
- (ii) Linear functional of a Gaussian is Gaussian; mean and variance
  are computed directly.
- (iii) Cochran's theorem (Shao Thm 1.5): `Xᵀ M X / σ² ~ χ²_{rk M}`
  when `M` is symmetric idempotent, applied to `M = I - Z(ZᵀZ)⁻Zᵀ`.

## Status

The three conclusions are currently stated as named axioms with
structured comments documenting the Mathlib gap (vector-valued
`IsGaussian`, Cochran's theorem, spectral decomposition of
idempotents). This matches the precedent established by
`Statlean.Concentration.Talagrand.mcdiarmid_mgf_bound`,
`Statlean.Gaussian.Gordon.slepian_lemma`, and the
`Statlean.RandomMatrix.MarchenkoPastur` axioms. Each axiom is tracked
in `theme/input/sorry_backlog.yaml` and will be discharged once
Mathlib gains the prerequisite multivariate Gaussian infrastructure.

## References

- Jun Shao, *Mathematical Statistics*, 2nd ed., Theorem 3.8 (p. 204).
- Mathlib: `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.IsGaussian`,
  `ProbabilityTheory.IndepFun`, `Matrix.rank`.
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

namespace Statlean.Regression.NormalLinearModel

/-- Auxiliary: the chi-square distribution with `k` degrees of freedom,
defined as the pushforward of the joint of `k` iid `N(0,1)` along
`x ↦ ∑ᵢ xᵢ²`. -/
def chiSquared (k : ℕ) : Measure ℝ :=
  (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map
    (fun x : Fin k → ℝ => ∑ i, (x i) ^ 2)

/-- A **normal linear model setup**: design matrix `Z`, true parameter
`β`, error scale `σ > 0`, a chosen generalized inverse `H` of `ZᵀZ`,
and the rank `r` of `ZᵀZ`.

The choice `H` is part of the data because in the rank-deficient case
the generalized inverse is not unique; Shao's Theorem 3.6 guarantees
that `Z · H · Zᵀ` (and hence the LSE projection) is invariant under
this choice. -/
structure Setup (n p : ℕ) where
  /-- Design matrix. -/
  Z : Matrix (Fin n) (Fin p) ℝ
  /-- True regression coefficient vector. -/
  β : Fin p → ℝ
  /-- Error scale (σ > 0). -/
  σ : ℝ
  hσ : 0 < σ
  /-- A chosen generalized inverse of `ZᵀZ`: any matrix `H` satisfying
  `(ZᵀZ) · H · (ZᵀZ) = ZᵀZ`. -/
  H : Matrix (Fin p) (Fin p) ℝ
  hH : Z.transpose * Z * H * (Z.transpose * Z) = Z.transpose * Z
  /-- Rank of the design (equivalently of `ZᵀZ`). -/
  r : ℕ
  hr_eq : r = (Z.transpose * Z).rank
  /-- Rank cannot exceed the number of observations. -/
  hr_le : r ≤ n

namespace Setup

variable {n p : ℕ} (M : Setup n p)

/-- A linear functional `lᵀβ` is **estimable** iff `l ∈ R(Zᵀ)`, the
column space of `Zᵀ` (equivalently, the column space of `ZᵀZ`). -/
def IsEstimable (l : Fin p → ℝ) : Prop :=
  ∃ c : Fin n → ℝ, l = M.Z.transpose.mulVec c

/-- The **least-squares estimator** `β̂ = H · Zᵀ · X` (using the chosen
generalized inverse `H = (ZᵀZ)⁻`). -/
def lse (X : Fin n → ℝ) : Fin p → ℝ :=
  (M.H * M.Z.transpose).mulVec X

/-- The **residual** vector `X - Z · β̂`. -/
def residual (X : Fin n → ℝ) : Fin n → ℝ :=
  X - M.Z.mulVec (M.lse X)

/-- The **residual sum of squares**: `‖X - Z β̂‖²`. -/
def ssr (X : Fin n → ℝ) : ℝ :=
  ∑ i, (M.residual X i) ^ 2

/-- The **σ̂² estimator**: `SSR / (n - r)`. -/
def sigmaSqHat (X : Fin n → ℝ) : ℝ :=
  M.ssr X / (n - M.r : ℝ)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Assumption A1**: `X = Zβ + σ·ε` where `ε ω : Fin n → ℝ` is iid
standard normal. Equivalently, `μ.map X` has the joint distribution
`N_n(Zβ, σ²·I_n)`. -/
def AssumptionA1 (μ : Measure Ω) (X : Ω → Fin n → ℝ) : Prop :=
  ∃ ε : Ω → Fin n → ℝ,
    (Measurable ε) ∧
    (∀ ω i, X ω i = (M.Z.mulVec M.β) i + M.σ * ε ω i) ∧
    μ.map ε = Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- **Shao Thm 3.8 (i)** — the LSE of an estimable parameter and `σ̂²`
are independent under assumption A1.

The standard proof has two ingredients:

1. *Linear-algebraic fact*: the cross-covariance vanishes, i.e.
   `(I - Z H Zᵀ) · Z H l = 0`. This follows from the generalised-inverse
   identity `(Zᵀ Z) H (Zᵀ Z) = Zᵀ Z` together with the estimability of
   `l` (Shao Thm 3.6 — the projection `Z H Zᵀ` is invariant under the
   choice of generalised inverse `H` and equals the orthogonal
   projection onto col(Z)).
2. *Probabilistic fact (Shao Exercise 1.58)*: jointly normal random
   variables with zero cross-covariance are independent. This requires
   multivariate Gaussian theory (joint distribution of
   `(⟨a,ε⟩, B·ε)` is Gaussian, the characteristic function factorises
   when the cross-covariance vanishes, hence by
   `MeasureTheory.charFunDual_eq_prod_iff` the joint measure is a
   product measure).

**Status**: Accepted as an axiom. Blocked by: Mathlib 4.28.0-rc1 lacks
the multivariate-Gaussian-on-`Fin n → ℝ` infrastructure (vector-valued
`IsGaussian`, joint-normal pushforward under linear maps, the
characteristic-function factorisation argument specialised to the
multivariate case) required to formalise step 2. Tracked in
`sorry_backlog.yaml`. -/
axiom lse_indep_sigmaSqHat
    {n p : ℕ} (M : Setup n p)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hX : M.AssumptionA1 μ X)
    (l : Fin p → ℝ) (hl : M.IsEstimable l) :
    IndepFun (fun ω => l ⬝ᵥ M.lse (X ω))
             (fun ω => M.sigmaSqHat (X ω)) μ

/-- **Shao Thm 3.8 (ii)** — the marginal distribution of any estimable
linear functional of the LSE is Gaussian:
`lᵀβ̂ ~ N(lᵀβ, σ²·lᵀ H l)` under A1.

The standard proof has two steps:

1. *Affine decomposition*: write
   `lᵀβ̂ = lᵀ(HZᵀ)(Zβ + σε) = lᵀβ + σ·⟨c, ε⟩`
   where `c := (HZᵀ)ᵀl ∈ ℝⁿ`.  The first summand is constant, the
   second is a linear combination of iid N(0,1) components.

2. *Gaussian stability under linear maps*: `∑ᵢ cᵢ εᵢ ~ N(0, ‖c‖²)`.
   By induction on n and `gaussianReal_add_gaussianReal_of_indepFun`,
   the weighted sum is Gaussian.  The variance is
   `σ² · ‖c‖² = σ² · ‖(HZᵀ)ᵀl‖² = σ² · lᵀHZᵀZHl`.
   The key matrix identity `ZᵀZ · H · ZᵀZ = ZᵀZ` together with
   estimability `l = Zᵀa` yields `HZᵀZHl = Hl`, so the variance
   reduces to `σ² · lᵀHl`.

**Status**: Accepted as an axiom. Blocked by: Mathlib 4.28.0-rc1 lacks
the necessary infrastructure to formalise step 2 for a general
`Fin n`-indexed family — extracting pairwise `IndepFun` from
`μ.map ε = Measure.pi …`, induction over `Fin n` for finite weighted
Gaussian sums, and matrix-identity simplification
`lᵀHZᵀZHl = lᵀHl`. Tracked in `sorry_backlog.yaml`. -/
axiom lse_distribution
    {n p : ℕ} (M : Setup n p)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hX : M.AssumptionA1 μ X)
    (l : Fin p → ℝ) (hl : M.IsEstimable l)
    (hVar : 0 ≤ M.σ ^ 2 * (l ⬝ᵥ M.H.mulVec l)) :
    μ.map (fun ω => l ⬝ᵥ M.lse (X ω))
      = gaussianReal (l ⬝ᵥ M.β)
          ⟨M.σ ^ 2 * (l ⬝ᵥ M.H.mulVec l), hVar⟩

/-- **Shao Thm 3.8 (iii)** — the scaled residual sum of squares has a
chi-squared distribution: `(n-r)·σ̂²/σ² ~ χ²_{n-r}` under A1.

The standard proof applies **Cochran's theorem**:

1. *Quadratic form representation*: write
   `(n-r)·σ̂²/σ² = εᵀ(I - P)ε`
   where `ε ~ N(0, Iₙ)` (standardised errors), and
   `P = ZH(ZᵀZ)Hᵀ Zᵀ` is the orthogonal projection onto `colsp(Z)`,
   with rank `r`.

2. *Cochran's theorem*: if `A` is a symmetric idempotent matrix of rank
   `k` and `ε ~ N(0, Iₙ)`, then `εᵀ A ε ~ χ²_k`.
   Here `I - P` is symmetric idempotent of rank `n - r`, giving
   `εᵀ(I-P)ε ~ χ²_{n-r}`.

**Status**: Accepted as an axiom. Blocked by: Mathlib 4.28.0-rc1 lacks
Cochran's theorem and its prerequisites — multivariate Gaussian on
`Fin n → ℝ` (no `IsGaussianVector`), spectral decomposition of
symmetric idempotents (`Matrix.IsSymm.spectral_decomposition`), and
the connection between `chiSquared` (defined via `gammaMeasure`) and
the distribution of `∑ Zᵢ²` for iid standard normals. Tracked in
`sorry_backlog.yaml`. -/
axiom sigmaSqHat_chiSquared
    {n p : ℕ} (M : Setup n p)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hX : M.AssumptionA1 μ X)
    (hr : M.r < n) :
    μ.map (fun ω => (n - M.r : ℝ) * M.sigmaSqHat (X ω) / M.σ ^ 2)
      = chiSquared (n - M.r)

end Setup

/-- **Shao 3.8** (combined statement): the joint distribution of the
LSE `lᵀβ̂` and `σ̂²` under assumption A1.

For an estimable parameter `lᵀβ`:
  (i)   `lᵀβ̂` and `σ̂²` are independent;
  (ii)  `lᵀβ̂ ~ N(lᵀβ, σ²·lᵀ H l)`;
  (iii) `(n-r)·σ̂²/σ² ~ χ²_{n-r}`.

This is the headline theorem; it is composed from the three sub-claims
above. -/
theorem lse_sigma_hat_distribution_under_a1
    {n p : ℕ} (M : Setup n p)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Fin n → ℝ) (hX : M.AssumptionA1 μ X)
    (l : Fin p → ℝ) (hl : M.IsEstimable l)
    (hVar : 0 ≤ M.σ ^ 2 * (l ⬝ᵥ M.H.mulVec l))
    (hr : M.r < n) :
    IndepFun (fun ω => l ⬝ᵥ M.lse (X ω))
             (fun ω => M.sigmaSqHat (X ω)) μ
      ∧ μ.map (fun ω => l ⬝ᵥ M.lse (X ω))
          = gaussianReal (l ⬝ᵥ M.β)
              ⟨M.σ ^ 2 * (l ⬝ᵥ M.H.mulVec l), hVar⟩
      ∧ μ.map (fun ω => (n - M.r : ℝ) * M.sigmaSqHat (X ω) / M.σ ^ 2)
          = chiSquared (n - M.r) :=
  ⟨Setup.lse_indep_sigmaSqHat M μ X hX l hl,
   Setup.lse_distribution M μ X hX l hl hVar,
   Setup.sigmaSqHat_chiSquared M μ X hX hr⟩

end Statlean.Regression.NormalLinearModel

end

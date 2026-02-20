import Statlean.Concentration.Density

/-! # Gaussian Log-Sobolev Inequality (Theorems 3.5 & 3.6)

## Statement (Theorem 3.5)
Let γⁿ be the standard n-dimensional Gaussian measure. For any f ∈ W^{1,2}(γⁿ):

  Ent_γⁿ(f²) ≤ 2 · E_γⁿ[‖∇f‖²]

where Ent_μ(g) = E_μ[g log g] - E_μ[g] log E_μ[g] is the entropy functional.

## Tensorization (Theorem 3.6)
If μ = μ₁ ⊗ ... ⊗ μₙ is a product measure and each μᵢ satisfies LSI(cᵢ),
then μ satisfies LSI(max cᵢ). For standard Gaussian, each factor satisfies
LSI(2), so the product also satisfies LSI(2).

## Proof strategy
1. Prove 1D Gaussian LSI from Gaussian Poincaré via the Rothaus-Simon lemma:
   LSI follows from Poincaré + uniform bound on the defect
2. Prove tensorization of LSI (Theorem 3.6)
3. Extend from C_c^∞ to W^{1,2}(γⁿ) using the density result (Theorem 3.3)
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- **Entropy functional**: Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)
for a nonneg measurable function g. -/
def entropy (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- Entropy functional on a product space. -/
def entropyPi {n : ℕ} (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- A measure μ satisfies a **log-Sobolev inequality** with constant c if
    Ent_μ(f²) ≤ c · E_μ[f'²] for all smooth f. -/
def SatisfiesLSI (μ : Measure ℝ) (c : ℝ) : Prop :=
  ∀ f f' : ℝ → ℝ,
    MemLp f 2 μ → MemLp f' 2 μ →
    (∀ x, HasDerivAt f (f' x) x) →
    entropy μ (fun x => f x ^ 2) ≤ c * ∫ x, f' x ^ 2 ∂μ

/-- Tensorized LSI statement at fixed dimension `n` and constant `c`
for products of the standard Gaussian measure. -/
def TensorizationLSIAt (n : ℕ) (c : ℝ) : Prop :=
  SatisfiesLSI stdGaussian c →
    ∀ f : (Fin n → ℝ) → ℝ,
    ∀ gradf : Fin n → (Fin n → ℝ) → ℝ,
    MemLp f 2 (stdGaussianPi n) →
    (∀ i, MemLp (gradf i) 2 (stdGaussianPi n)) →
    (∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) →
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)

/-- Universal tensorization interface across all dimensions and constants. -/
def UniversalTensorizationLSI : Prop :=
  ∀ n : ℕ, ∀ c : ℝ, TensorizationLSIAt n c

/-- Regularity package for a function and its coordinate derivatives
on `stdGaussianPi n`. -/
structure GaussianSobolevRegularity
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  hf : MemLp f 2 (stdGaussianPi n)
  hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n)
  hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)

/-- **1D Gaussian LSI core** (sorry):
The standard Gaussian `N(0,1)` satisfies `LSI(2)`:
  `Ent_γ(f²) ≤ 2 · E_γ[(f')²]` for all smooth `f`.

**Proof sketch** (Rothaus-Simon, using 1D Gaussian Poincaré):
- The Rothaus-Simon lemma: if μ satisfies Poincaré(1) then it satisfies LSI(2).
- Apply the 1D Gaussian Poincaré inequality (spectral gap = 1).
- Alternatively: direct proof via Gross's Bonami-Beckner hypercontractivity.
-/
theorem gaussian_lsi_1d_core : SatisfiesLSI stdGaussian 2 := by
  sorry

/-- **1D Gaussian LSI**: The standard Gaussian N(0,1) satisfies LSI(2).
Delegates to `gaussian_lsi_1d_core`. -/
theorem gaussian_lsi_1d : SatisfiesLSI stdGaussian 2 :=
  gaussian_lsi_1d_core

/-- **Tensorization of LSI core** (sorry):
If the 1D Gaussian satisfies `LSI(c)`, then the n-dimensional product
`stdGaussianPi n` satisfies `LSI(c)` (constant independent of dimension).

**Proof sketch** (tensorization argument):
By induction on n, using: if μ₁ satisfies LSI(c) and μ₂ satisfies LSI(c),
then μ₁ ⊗ μ₂ satisfies LSI(c).
Key identity: `Ent_{μ₁⊗μ₂}(f²) = E₁[Ent₂(f²)] + Ent₁(E₂[f²])`.
Apply LSI to each term using the product structure.
-/
theorem tensorization_lsi_core (n : ℕ) (c : ℝ) : TensorizationLSIAt n c := by
  sorry

/-- **Theorem 3.6** (Tensorization of LSI):
If each μᵢ satisfies LSI(c), then the product ⊗ᵢ μᵢ satisfies LSI(c)
(the constant does not grow with dimension). -/
theorem tensorization_lsi
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hTensorAt : TensorizationLSIAt n c) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hTensorAt h f gradf hf hgradf hgrad

/-- Use a fixed `(n,c)` tensorization statement to obtain the target inequality. -/
theorem tensorization_lsi_of_at
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (hTensorAt : TensorizationLSIAt n c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi n c h f gradf hf hgradf hgrad hTensorAt

/-- Turn a universal tensorization interface into the fixed `(n,c)` one. -/
lemma tensorization_lsi_at_of_universal
    (hTensor : UniversalTensorizationLSI) (n : ℕ) (c : ℝ) :
    TensorizationLSIAt n c := by
  exact hTensor n c

/-- Gaussian log-Sobolev from a fixed `(n,2)` tensorization statement. -/
theorem gaussian_log_sobolev_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi_of_at n 2 hLSI1d hTensorAt f gradf hf hgradf hgrad

/-- Gaussian log-Sobolev from the universal tensorization interface. -/
theorem gaussian_log_sobolev_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hf hgradf hgrad hLSI1d
    (tensorization_lsi_at_of_universal hTensor n 2)

/-- Structured regularity version of `gaussian_log_sobolev_of_tensorization_at`. -/
theorem gaussian_log_sobolev_structured_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensorAt

/-- Structured regularity version of `gaussian_log_sobolev_of_universal_tensorization`. -/
theorem gaussian_log_sobolev_structured_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_universal_tensorization n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensor

/-- **Theorem 3.5** (Gaussian Log-Sobolev Inequality):
For `f ∈ W^{1,2}(γⁿ)` with partial derivatives `gradf i`:
  `Ent_γⁿ(f²) ≤ 2 · E_γⁿ[‖∇f‖²] = 2 · Σᵢ E_γⁿ[(∂f/∂xᵢ)²]`

This version requires no external hypothesis: `SatisfiesLSI stdGaussian 2`
comes from `gaussian_lsi_1d_core` (sorry) and tensorization from
`tensorization_lsi_core` (sorry). -/
theorem gaussian_log_sobolev
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) :=
  gaussian_log_sobolev_of_tensorization_at n f gradf hf hgradf hgrad
    gaussian_lsi_1d_core
    (tensorization_lsi_core n 2)

end

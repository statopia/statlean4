import Statlean.Gaussian.Basic

/-! # Entropy Functional and Log-Sobolev Definitions

## Main definitions
- `entropy` — Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)
- `entropyPi` — entropy on product space
- `SatisfiesLSI` — log-Sobolev inequality with constant c
- `TensorizationLSIAt`, `UniversalTensorizationLSI` — tensorization interfaces
- `GaussianSobolevRegularity` — regularity package for Gaussian Sobolev
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- **Entropy functional**: Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ). -/
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

/-- Tensorized LSI statement at fixed dimension `n` and constant `c`. -/
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

/-- Regularity package for a function and its coordinate derivatives. -/
structure GaussianSobolevRegularity
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  hf : MemLp f 2 (stdGaussianPi n)
  hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n)
  hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)

end

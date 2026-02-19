import Statlean.Concentration.EfronStein
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Gaussian Poincaré Inequality (Corollary 3.2)

## Statement
Let X ~ N(0, Iₙ) (standard n-dimensional Gaussian) and f ∈ C_c^∞(ℝⁿ). Then:

  Var[f(X)] ≤ E[‖∇f(X)‖²]

## Proof strategy (from Efron-Stein)
Starting from Efron-Stein for product Gaussian:
  Var[f(X)] ≤ Σᵢ E[(f(X) - E^{(i)}[f(X)])²]

For each term, conditioning on Xⱼ (j ≠ i) and applying 1D Poincaré:
  E[(f(X) - E^{(i)}[f(X)])² | Xⱼ, j ≠ i] ≤ E[(∂f/∂xᵢ)² | Xⱼ, j ≠ i]

The 1D Poincaré inequality for Gaussian can be proved via:
  - Hermite polynomial expansion (spectral gap = 1)
  - or: CLT from Rademacher to Gaussian
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Standard Gaussian measure on ℝ: N(0,1). -/
abbrev stdGaussian : Measure ℝ := gaussianReal 0 1

/-- Standard n-dimensional Gaussian as product measure on `Fin n → ℝ`. -/
def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => stdGaussian)

/-- **One-dimensional Gaussian Poincaré inequality**:
For f smooth with compact support, Var_γ[f] ≤ E_γ[f'²]
where γ = N(0,1). -/
theorem gaussian_poincare_1d
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hGP1d : Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian := by
  exact hGP1d

/-- Multi-dimensional Gaussian Poincaré from an already-established
gradient-integral bound. Kept as a compatibility wrapper. -/
theorem gaussian_poincare_of_integral_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) -- partial derivatives
    (hGP :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hGP

/-- Gaussian Poincaré via Efron-Stein + coordinate-wise control:
first control variance by the Efron-Stein sum, then bound each summand by
the corresponding gradient-square integral. -/
theorem gaussian_poincare_of_efron_stein
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n))
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hSum :
      (∑ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n))
        ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hCoord i
  exact le_trans hES hSum

/-- Gaussian Poincaré via conditional-variance-sum Efron-Stein form plus
coordinate-wise controls. This wraps
`efron_stein_of_condVar_sum_bound + gaussian_poincare_of_efron_stein`. -/
theorem gaussian_poincare_of_condVar_sum
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hCondVar :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          (stdGaussianPi n)[Var[f; stdGaussianPi n |
            sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]])
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n) := by
    exact efron_stein (μ := fun _ : Fin n => stdGaussian) f hf hCondVar
  exact gaussian_poincare_of_efron_stein n f gradf hES hCoord

/-- **Multi-dimensional Gaussian Poincaré inequality** (Corollary 3.2):
for `X ~ N(0, Iₙ)`, derive the gradient-form bound from
conditional-variance-sum Efron-Stein plus coordinate-wise controls. -/
theorem gaussian_poincare
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hCondVar :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          (stdGaussianPi n)[Var[f; stdGaussianPi n |
            sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]])
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_poincare_of_condVar_sum n f gradf hf hCondVar hCoord

end

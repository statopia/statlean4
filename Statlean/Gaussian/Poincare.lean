import Statlean.Variance.EfronStein
import Statlean.Gaussian.Hermite

/-! # Gaussian Poincaré Inequality

## Proved (zero sorry)
- `gaussian_poincare_of_integral_bound` — wrapper
- `gaussian_poincare_of_efron_stein` — via Efron-Stein + coordinate bound
- `gaussian_poincare_of_condVar_sum` — via conditional variance sum

## Sorry gaps
- `gaussian_poincare_1d_core` — needs Hermite coefficient relation + Parseval
- `gaussian_poincare_coord_bound_core` — needs Fubini + 1D Poincaré
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

/-! ## Clean wrappers (zero sorry) -/

theorem gaussian_poincare_of_integral_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hGP :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hGP

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
            ∂(stdGaussianPi n) :=
    efron_stein_of_condVar_sum_bound (μ := fun _ : Fin n => stdGaussian) f hf hCondVar
  exact gaussian_poincare_of_efron_stein n f gradf hES hCoord

/-! ## Sorry-dependent declarations -/

/-- **1D Gaussian Poincaré core** (sorry — needs Hermite completeness/Parseval). -/
theorem gaussian_poincare_1d_core
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian := by
  sorry

theorem gaussian_poincare_1d
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian :=
  gaussian_poincare_1d_core f f' hf hf' hderiv

/-- **Per-coordinate Poincaré bound core** (sorry — needs Fubini + 1D Poincaré). -/
theorem gaussian_poincare_coord_bound_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    ∀ i : Fin n,
      ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
        ∂(stdGaussianPi n)
        ≤
      ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  sorry

/-- **Multi-dimensional Gaussian Poincaré inequality** (Corollary 3.2). -/
theorem gaussian_poincare
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) :=
  gaussian_poincare_of_efron_stein n f gradf
    (efron_stein (μ := fun _ : Fin n => stdGaussian) f hf)
    (gaussian_poincare_coord_bound_core n f gradf hf hgradf hderiv)

end

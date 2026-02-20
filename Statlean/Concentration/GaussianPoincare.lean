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

/-- **1D Gaussian Poincaré core** (sorry):
For `f ∈ W^{1,2}(N(0,1))` with derivative `f'`, `Var_γ[f] ≤ E_γ[(f')²]`.

**Proof sketch** (Hermite expansion):
The Hermite polynomials `Hₙ` form an orthonormal basis of L²(γ).
Write `f = Σₙ aₙ Hₙ` and `f' = Σₙ aₙ H'ₙ = Σₙ aₙ n Hₙ₋₁`.
Then:
  `Var_γ[f] = Σₙ≥1 aₙ²` (since `E[Hₙ] = 0` for `n ≥ 1`)
  `E_γ[(f')²] = Σₙ≥1 n aₙ²`
Since `n ≥ 1` for all terms, `Var_γ[f] ≤ E_γ[(f')²]`.

Alternative: via Stein's identity `E_γ[f'(X)] = E_γ[X·f(X)]`
and integration by parts on the Gaussian density.
-/
theorem gaussian_poincare_1d_core
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian := by
  sorry

/-- **One-dimensional Gaussian Poincaré inequality** (Corollary of 1D core):
For `f` with derivative `f'`, `Var_γ[f] ≤ E_γ[(f')²]` where `γ = N(0,1)`.
Delegates to `gaussian_poincare_1d_core`. -/
theorem gaussian_poincare_1d
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian :=
  gaussian_poincare_1d_core f f' hf hf' hderiv

/-- **Per-coordinate Poincaré bound core** (sorry):
For each coordinate `i`, the Efron-Stein summand is bounded by the
expected squared partial derivative:
  `∫(f(x) - E^{(i)}[f](x))² ∂μ ≤ ∫(∂f/∂xᵢ(x))² ∂μ`

**Proof sketch** (Fubini + 1D Poincaré):
Fix the coordinates `x_{-i} = (xⱼ)_{j≠i}` and apply the 1D Gaussian
Poincaré inequality to `g : t ↦ f(update x i t)` with derivative `gradf i`.
By Fubini, integrating over `x_{-i}` gives the result.
-/
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
            ∂(stdGaussianPi n) :=
    efron_stein_of_condVar_sum_bound (μ := fun _ : Fin n => stdGaussian) f hf hCondVar
  exact gaussian_poincare_of_efron_stein n f gradf hES hCoord

/-- **Multi-dimensional Gaussian Poincaré inequality** (Corollary 3.2):
For `X ~ N(0, Iₙ)` and `f` with coordinate partial derivatives `gradf i`:
  `Var[f(X)] ≤ Σᵢ E[(∂f/∂xᵢ(X))²]`

This version requires no external hypothesis: Efron-Stein comes from
`efron_stein_core` and the per-coordinate bound from
`gaussian_poincare_coord_bound_core` (both marked sorry). -/
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

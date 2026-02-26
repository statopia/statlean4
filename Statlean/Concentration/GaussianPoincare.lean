import Statlean.Concentration.GaussianPoincareProved
import Statlean.Concentration.EfronStein

/-! # Gaussian Poincaré Inequality — Sorry-dependent Declarations

This file re-exports `GaussianPoincareProved` (all zero-sorry infrastructure
including `stein_identity`, `memLp_polynomial_gaussianReal`, etc.) and adds
the declarations that still contain `sorry`:

- `gaussian_poincare_1d_core` (sorry — needs Hermite completeness / Parseval)
- `gaussian_poincare_1d` (depends on `gaussian_poincare_1d_core`)
- `gaussian_poincare_coord_bound_core` (sorry — needs Fubini + 1D Poincaré)
- `gaussian_poincare` (depends on `efron_stein` (sorry) + coord bound (sorry))
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

/-- **1D Gaussian Poincaré core**:
For `f ∈ W^{1,2}(N(0,1))` with derivative `f'`, `Var_γ[f] ≤ E_γ[(f')²]`.

**Status**: sorry — genuine core gap requiring Hermite completeness.

**What we have proved** (zero sorry):
- `stein_identity`: `E_γ[x·h(x)] = E_γ[h'(x)]`
- `hermite_orthogonality`: `E_γ[Hₘ·Hₙ] = n! · δ_{mn}`
- `derivative_hermite`: `H'_{n+1} = (n+1)·Hₙ`
- `memLp_polynomial_gaussianReal`: all polynomials in all Lp(γ)

**What remains** (the spectral gap):
The forward Poincaré `Var[f] ≤ E[(f')²]` cannot be derived from Stein's
identity alone (Stein + Cauchy-Schwarz gives only `(E[f'])² ≤ Var[f]`,
the REVERSE direction). The essential missing piece is:

  **Hermite completeness (Parseval)**: `‖f‖²_{L²(γ)} = Σₙ aₙ² · n!`
  where `aₙ = E_γ[f · Hₙ] / n!`.

This, combined with `hermite_orthogonality` (proved), yields:
  `Var[f] = Σ_{n≥1} aₙ²·n!  ≤  Σ_{n≥1} n·aₙ²·n! = E[(f')²]`

**Possible proof routes for completeness**:
1. Smooth compact-support density (`Lp.dense_hasCompactSupport_contDiff`,
   in Mathlib) + Weierstrass on compacts + Hermite orthogonality
2. Ornstein-Uhlenbeck semigroup spectral theory (not in Mathlib)
3. Brascamp-Lieb inequality (not in Mathlib)
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

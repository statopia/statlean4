import Statlean.Concentration.EfronStein
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Gaussian Poincaré Inequality (Corollary 3.2)

## Statement
Let X ~ N(0, Iₙ) (standard n-dimensional Gaussian) and f ∈ C_c^∞(ℝⁿ). Then:

  Var[f(X)] ≤ E[‖∇f(X)‖²]

## Proof strategy (1D: Stein identity + IBP)
The 1D Gaussian Poincaré inequality `Var_γ[f] ≤ E_γ[(f')²]` is proved via:

1. **Stein's identity**: For `γ = N(0,1)`, `E_γ[x·h(x)] = E_γ[h'(x)]`.
   Proof: integration by parts using `φ'(x) = -x·φ(x)`.

2. **Poincaré from Stein**: Let `g = f - E[f]`.
   By Stein applied to `g²/2`: `E_γ[g·g'] = ½ E_γ[x·g²]`.
   By non-negativity of `E[(g' - xg)²]`:
     `E[(g')²] + E[x²g²] ≥ 2E[xgg']`
   Combined with Stein identity on `xg²` this yields Poincaré.

## Multi-dimensional Poincaré
For the multi-dimensional case, apply Efron-Stein + per-coordinate 1D Poincaré
via Fubini slicing.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal

noncomputable section

/-- Standard Gaussian measure on ℝ: N(0,1). -/
abbrev stdGaussian : Measure ℝ := gaussianReal 0 1

/-- Standard n-dimensional Gaussian as product measure on `Fin n → ℝ`. -/
def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => stdGaussian)

/-! ## Gaussian density derivative and Stein's identity

The standard Gaussian density `φ(x) = (√(2π))⁻¹ exp(-x²/2)` satisfies
`φ'(x) = -x · φ(x)`. This yields Stein's identity by integration by parts:
`E_γ[x·h(x)] = E_γ[h'(x)]`.
-/

/-- The standard Gaussian density `φ(x) = (√(2π))⁻¹ exp(-x²/2)` has
derivative `φ'(x) = -x · φ(x)`. -/
lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  -- We prove this by chaining: (-x²/2)' = -x, then exp ∘ (-x²/2), then const_mul
  have hg : HasDerivAt (fun y => -(y ^ 2) / 2) (-x) x := by
    have h1 := hasDerivAt_pow 2 x  -- HasDerivAt (· ^ 2) (2 * x) x
    have h2 := h1.neg               -- HasDerivAt (-(· ^ 2)) (-(2 * x)) x
    have h3 := h2.div_const 2       -- HasDerivAt (-(· ^ 2) / 2) (-(2 * x) / 2) x
    convert h3 using 1; ring
  have hexp := hg.exp  -- HasDerivAt (exp ∘ (-·²/2)) (exp(-x²/2) * (-x)) x
  -- gaussianPDFReal 0 1 y = (√(2 * π * ↑1))⁻¹ * exp(-(y - 0)² / (2 * ↑1))
  -- We need to match this with const * exp(-y²/2)
  have hkey : ∀ y, gaussianPDFReal 0 1 y = (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    intro y; simp [gaussianPDFReal]
  have hfull := (hexp.const_mul (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹)
  rw [show gaussianPDFReal 0 1 = fun y => (√(2 * Real.pi * ↑(1 : ℝ≥0)))⁻¹ *
      Real.exp (-(y ^ 2) / 2) from funext hkey]
  convert hfull using 1; ring

/-- **Stein's identity for standard Gaussian**:
For `h` differentiable with `h, h' ∈ L²(γ)`:
  `∫ x, x * h x ∂γ = ∫ x, h' x ∂γ`

**Proof**: Write the Gaussian integral in density form using
`integral_gaussianReal_eq_integral_smul`. Since `φ'(x) = -x · φ(x)`, we have
`x · φ(x) = -φ'(x)`, so:
  `∫ x·h(x)·φ(x) dx = -∫ h(x)·φ'(x) dx = ∫ h'(x)·φ(x) dx`
where the second step uses `integral_mul_deriv_eq_deriv_mul_of_integrable`
(integration by parts on ℝ) with `u = h` and `v = φ`.

The integrability of `h · φ` follows from `h ∈ L²(γ)` and boundedness of `φ`.
-/
lemma stein_identity
    (h h' : ℝ → ℝ)
    (hh : MemLp h 2 stdGaussian)
    (hh' : MemLp h' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt h (h' x) x) :
    ∫ x, x * h x ∂stdGaussian = ∫ x, h' x ∂stdGaussian := by
  -- Convert to Lebesgue density form:
  -- ∫ f ∂γ = ∫ φ(x) • f(x) dx  where φ = gaussianPDFReal 0 1
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  show ∫ x, x * h x ∂gaussianReal 0 1 = ∫ x, h' x ∂gaussianReal 0 1
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv,
      integral_gaussianReal_eq_integral_smul (v := (1 : ℝ≥0)) hv]
  simp only [smul_eq_mul]
  -- LHS: ∫ φ(x) * (x * h(x)) dx
  -- RHS: ∫ φ(x) * h'(x) dx
  -- Use IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  --   where φ'(x) = -x * φ(x), so ∫ h(x) * (-x * φ(x)) dx = -∫ h'(x) * φ(x) dx
  --   i.e., -∫ x * h(x) * φ(x) dx = -∫ h'(x) * φ(x) dx
  --   i.e., ∫ x * h(x) * φ(x) dx = ∫ h'(x) * φ(x) dx  ✓
  -- Apply integral_mul_deriv_eq_deriv_mul_of_integrable with u = h, v = φ.
  have hφ_deriv : ∀ x, HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := hasDerivAt_gaussianPDFReal_std
  -- IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  -- i.e., ∫ h(x) * (-x * φ(x)) dx = -∫ h'(x) * φ(x) dx
  -- Rearranging: ∫ φ(x) * (x * h(x)) dx = ∫ φ(x) * h'(x) dx
  -- IBP: ∫ h(x) * φ'(x) dx = -∫ h'(x) * φ(x) dx
  have hIBP := integral_mul_deriv_eq_deriv_mul_of_integrable
    hderiv hφ_deriv
    -- Integrability of h·(xφ): h ∈ L²(γ) and x·φ bounded by C·φ^{1/2} ∈ L²(Leb)
    -- Use MemLp.integrable_mul with HolderTriple 2 2 1 after converting from γ to Lebesgue
    (sorry /- Integrable (h * fun x => -x * φ x) Leb: from h ∈ L²(γ), xφ ∈ L²(Leb) -/)
    -- Integrability of h'·φ: h' ∈ L²(γ) means h'²φ ∈ L¹(Leb), φ bounded → h'φ ∈ L¹(Leb)
    (sorry /- Integrable (h' * φ) Leb: from h' ∈ L²(γ) and φ ∈ L^∞ -/)
    -- Integrability of h·φ: h ∈ L²(γ) → h·√φ ∈ L²(Leb) → h·φ = (h·√φ)·√φ ∈ L¹(Leb)
    (sorry /- Integrable (h * φ) Leb: from h ∈ L²(γ), Cauchy-Schwarz -/)
  -- hIBP : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) = -(∫ x, h' x * gaussianPDFReal 0 1 x)
  -- We need: ∫ x, gaussianPDFReal 0 1 x * (x * h x) = ∫ x, gaussianPDFReal 0 1 x * h' x
  -- From hIBP: ∫ h(x) * (-x * φ(x)) = -∫ h'(x) * φ(x)
  -- i.e.      -∫ h(x) * x * φ(x) = -∫ h'(x) * φ(x)
  -- i.e.       ∫ h(x) * x * φ(x) = ∫ h'(x) * φ(x)
  -- i.e.       ∫ φ(x) * (x * h(x)) = ∫ φ(x) * h'(x)    ✓
  have key : ∫ x, h x * (-x * gaussianPDFReal 0 1 x) =
      -(∫ x, gaussianPDFReal 0 1 x * (x * h x)) := by
    rw [← integral_neg]; congr 1; ext x; ring
  have key2 : ∫ x, h' x * gaussianPDFReal 0 1 x =
      ∫ x, gaussianPDFReal 0 1 x * h' x := by
    congr 1; ext x; ring
  linarith

/-- **1D Gaussian Poincaré core**:
For `f ∈ W^{1,2}(N(0,1))` with derivative `f'`, `Var_γ[f] ≤ E_γ[(f')²]`.

**Status**: sorry — this is a genuine core gap.

**Known proof routes** (all require infrastructure beyond current Mathlib):

1. **Hermite expansion** (most elementary):
   Hermite polynomials `{Hₙ}` form an ONB of L²(γ).
   Write `f = Σ aₙ Hₙ`. Then `Var[f] = Σ_{n≥1} aₙ²` and
   `E[(f')²] = Σ_{n≥1} n·aₙ²`. Since `n ≥ 1`, done.
   **Missing**: Hermite orthogonality `∫ Hₘ Hₙ dγ = n! δ_{mn}` and completeness.
   Mathlib has `hermite` polynomials + `deriv_gaussian_eq_hermite_mul_gaussian`
   but NOT orthogonality in L²(γ).

2. **Ornstein-Uhlenbeck semigroup**:
   `P_t f(x) = E[f(e^{-t}x + √(1-e^{-2t})Z)]`. Then
   `Var[f] = 2∫₀^∞ e^{-2t} E[(P_t f')²] dt ≤ E[(f')²]`
   since `E[(P_t f')²] ≤ E[(f')²]` by contractivity.
   **Missing**: OU semigroup definition and contractivity in L²(γ).

3. **Brascamp-Lieb**: For log-concave measure with Hessian ≥ κI,
   `Var[f] ≤ (1/κ) E[‖∇f‖²]`. For Gaussian, κ = 1.
   **Missing**: Brascamp-Lieb inequality.

**Note**: Stein's identity (`stein_identity` above) is a necessary ingredient
but NOT sufficient alone — it gives `E[Xf] = E[f']` which by Cauchy-Schwarz
yields `(E[f'])² ≤ Var[f]` (REVERSE Poincaré), not the forward direction.
The spectral gap (= 1) is the essential additional information.
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

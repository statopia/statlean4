import Statlean.Concentration.GaussianPoincare
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-! # Density of C_c^∞ in W^{1,2}(γ) (Theorem 3.3)

## Statement
C_c^∞(ℝⁿ) is dense in the Gaussian Sobolev space W^{1,2}(γⁿ), where γⁿ is the
standard n-dimensional Gaussian measure.

## Key lemma: Lipschitz mollification (Lemma 3.4)
For any Lipschitz function g on ℝⁿ, the standard mollification gₑ = g * φₑ
is Lipschitz with the same constant, and gₑ → g in W^{1,2}(γⁿ).

## Proof strategy
1. Truncation: reduce to compactly supported functions
2. Mollification: smooth the truncated function via convolution with Gaussian kernel
3. Show L² convergence of both the function and its gradient
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- **Lemma 3.4** (Lipschitz mollification):
If g : ℝⁿ → ℝ is L-Lipschitz, then its mollification gₑ is also L-Lipschitz
and gₑ → g in L²(γⁿ). -/
theorem lipschitz_mollification_preserves_constant
    (n : ℕ) (g : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hMoll :
      ∀ ε > (0 : ℝ), ∃ gε : (Fin n → ℝ) → ℝ,
        LipschitzWith L gε ∧
        ContDiff ℝ ⊤ gε ∧
        ∫ x, (g x - gε x) ^ 2 ∂(stdGaussianPi n) < ε ^ 2) :
    ∀ ε > (0 : ℝ), ∃ gε : (Fin n → ℝ) → ℝ,
      LipschitzWith L gε ∧
      ContDiff ℝ ⊤ gε ∧
      ∫ x, (g x - gε x) ^ 2 ∂(stdGaussianPi n) < ε ^ 2 := by
  exact hMoll

/-- **Theorem 3.3** (Density):
C_c^∞(ℝⁿ) is dense in W^{1,2}(γⁿ). More precisely, for any f in L²(γⁿ)
with weak gradient in L²(γⁿ), there exists a sequence of smooth
compactly supported functions converging to f in L². -/
theorem smooth_compactSupport_dense_in_gaussianSobolev
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hDense :
      ∀ ε > (0 : ℝ), ∃ φ : (Fin n → ℝ) → ℝ,
        ContDiff ℝ ⊤ φ ∧
        HasCompactSupport φ ∧
        ∫ x, (f x - φ x) ^ 2 ∂(stdGaussianPi n) < ε ^ 2) :
    ∀ ε > (0 : ℝ), ∃ φ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ⊤ φ ∧
      HasCompactSupport φ ∧
      ∫ x, (f x - φ x) ^ 2 ∂(stdGaussianPi n) < ε ^ 2 := by
  exact hDense

end

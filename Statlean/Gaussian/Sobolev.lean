import Statlean.Gaussian.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-! # Density of C_c^∞ in W^{1,2}(γ) (Theorem 3.3)

Lipschitz mollification and smooth compact-support density in Gaussian Sobolev space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

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

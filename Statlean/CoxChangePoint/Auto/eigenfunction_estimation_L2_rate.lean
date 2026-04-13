import Mathlib

/-!
# eigenfunction_estimation_L2_rate

Source: paper Lemma_S1_supp (Appendix A)

(Zhou et al., 2023). Under Assumptions (A8)–(A10), E(‖φ̂k − φk‖²) ≤ k² / n.
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory

/-- Assumptions (A8)–(A10) for eigenfunction estimation (Zhou et al., 2023). -/
structure CovarianceAssumptions (Ω D : Type*) [MeasurableSpace Ω] [MeasurableSpace D] where
  P : Measure Ω
  hP : IsProbabilityMeasure P
  ν : Measure D
  hν : SigmaFinite ν
  n : ℕ
  hn : 0 < n
  φ : ℕ → D → ℝ
  φ_hat : Ω → ℕ → D → ℝ
  lam_eig : ℕ → ℝ
  -- (A8) Eigenvalues positive and strictly decreasing
  eigenval_pos : ∀ k, 0 < lam_eig k
  eigenval_decreasing : StrictAnti lam_eig
  -- (A9) True eigenfunctions are L²(ν)-orthonormal
  eigfun_orthonormal : ∀ i j, ∫ t, φ i t * φ j t ∂ν = if i = j then 1 else 0
  -- (A10) Process fourth-moment bound
  fourth_moment_bound : ∃ M : ℝ, 0 < M ∧
    ∀ k, ∫ ω, (∫ t, (φ_hat ω k t) ^ 2 ∂ν) ^ 2 ∂P ≤ M
  -- Measurability of the L² error
  l2_error_measurable : ∀ k,
    Measurable (fun ω => ∫ t, (φ_hat ω k t - φ k t) ^ 2 ∂ν)

variable {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]

theorem eigenfunction_estimation_L2_rate
    (A : CovarianceAssumptions Ω D)
    (k : ℕ) (hk : 0 < k) :
    ∫ ω, (∫ t, (A.φ_hat ω k t - A.φ k t) ^ 2 ∂A.ν) ∂A.P
      ≤ (k : ℝ) ^ 2 / (A.n : ℝ) := by sorry

end Statlean.CoxChangePoint.Auto
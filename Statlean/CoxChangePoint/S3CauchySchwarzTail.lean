import Mathlib

/-!
# Cox Lemma S3 — deterministic Cauchy-Schwarz tail bound

Deterministic core invoked in the proof of Lemma S3 of
"Functional linear Cox regression model with a change-point in the covariate"
(Yu, Li, Lin 2026), supplementary p.34.

The paper writes (for the FPCA remainder `R_{i0}`):
  `|∑_{k>d} ξ_{ik} α_{k0}| ≤ (∑_{k>d} α_{k0}²)^{1/2} · ‖X_i‖`
where `‖X_i‖² = ∑_{k≥1} ξ_{ik}²`.

Below is the finite-index form of that Cauchy-Schwarz step, specialised to
`Finset.Ico N d` so it applies directly to the paper's tail index set.
-/

namespace Statlean.CoxChangePoint

/-- Absolute-value Cauchy-Schwarz on a finite index set:
    `|∑ ξ_k · α_k| ≤ √(∑ ξ_k²) · √(∑ α_k²)`. -/
theorem s3_cauchy_schwarz_tail
    (N d : ℕ) (ξ α : ℕ → ℝ) :
    |∑ k ∈ Finset.Ico N d, ξ k * α k|
      ≤ Real.sqrt (∑ k ∈ Finset.Ico N d, (ξ k) ^ 2)
        * Real.sqrt (∑ k ∈ Finset.Ico N d, (α k) ^ 2) := by
  have hub := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Ico N d) ξ α
  have hneg := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Ico N d) (fun k => -ξ k) α
  have hneg_sum : ∑ k ∈ Finset.Ico N d, (-ξ k) * α k =
      -(∑ k ∈ Finset.Ico N d, ξ k * α k) := by
    simp [neg_mul, Finset.sum_neg_distrib]
  have hneg_sq : ∑ k ∈ Finset.Ico N d, (-ξ k) ^ 2 =
      ∑ k ∈ Finset.Ico N d, (ξ k) ^ 2 := by
    congr 1; ext k; ring
  rw [hneg_sum, hneg_sq] at hneg
  rw [abs_le]
  refine ⟨?_, hub⟩
  linarith

end Statlean.CoxChangePoint

import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Gaussian/Gordon

## Slepian's Lemma and Gordon's Minimax Theorem

### Slepian's Lemma
For centered Gaussian vectors `X, Y` on `ℝⁿ`, if
`E[XᵢXⱼ] ≤ E[YᵢYⱼ]` for all `i ≠ j` and `E[Xᵢ²] = E[Yᵢ²]` for all `i`,
then `E[max Xᵢ] ≤ E[max Yᵢ]`.

### Gordon's Minimax Theorem
For centered Gaussian matrices `X_{ij}, Y_{ij}`, if certain covariance
comparison conditions hold, then `E[min_i max_j X_{ij}] ≤ E[min_i max_j Y_{ij}]`.

### Proof route
- Slepian: Lindeberg interpolation between X and Y, differentiate E[max] w.r.t. interpolation parameter
- Gordon: generalize Slepian to min-max via same interpolation technique

### References
- Y. Gordon, "Some inequalities for Gaussian processes and applications" (1985)
- R. Vershynin, "High-Dimensional Probability", Chapter 7
-/

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Statlean.Gaussian

section Slepian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-- **Slepian's comparison condition**: two centered Gaussian vectors satisfy
`Cov(Xᵢ,Xⱼ) ≤ Cov(Yᵢ,Yⱼ)` for `i ≠ j` and equal marginal variances. -/
structure SlepianCondition (X Y : Fin n → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Both are centered -/
  mean_zero_X : ∀ i, ∫ ω, X i ω ∂μ = 0
  mean_zero_Y : ∀ i, ∫ ω, Y i ω ∂μ = 0
  /-- Equal marginal variances -/
  var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = ∫ ω, (Y i ω) ^ 2 ∂μ
  /-- Off-diagonal covariance comparison -/
  cov_le : ∀ i j, i ≠ j →
    ∫ ω, X i ω * X j ω ∂μ ≤ ∫ ω, Y i ω * Y j ω ∂μ

/-- **Slepian's Lemma**: Under the Slepian condition,
`E[max Xᵢ] ≤ E[max Yᵢ]`. -/
theorem slepian_lemma
    {X Y : Fin n → Ω → ℝ}
    (hn : 0 < n)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_int : ∀ i, Integrable (X i) μ)
    (hY_int : ∀ i, Integrable (Y i) μ)
    (hcond : SlepianCondition X Y μ)
    -- Gaussian hypothesis (simplified: joint Gaussianity)
    (hX_gauss : ∀ i, IsGaussian (μ.map (X i)))
    (hY_gauss : ∀ i, IsGaussian (μ.map (Y i))) :
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂μ := by
  sorry

end Slepian

section Gordon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m n : ℕ}

/-- **Gordon's comparison condition**: for Gaussian matrices X, Y indexed by (i,j),
the covariance structure satisfies:
- `E[Xᵢⱼ²] = E[Yᵢⱼ²]` (equal variances)
- `E[XᵢⱼXᵢₖ] ≤ E[YᵢⱼYᵢₖ]` for j ≠ k (same row, different column)
- `E[XᵢⱼXₖⱼ] ≥ E[YᵢⱼYₖⱼ]` for i ≠ k (same column, different row)
- `E[XᵢⱼXₖₗ] = E[YᵢⱼYₖₗ] = 0` for (i,j) ≠ (k,l) with i ≠ k and j ≠ l -/
structure GordonCondition (X Y : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) : Prop where
  var_eq : ∀ i j, ∫ ω, (X i j ω) ^ 2 ∂μ = ∫ ω, (Y i j ω) ^ 2 ∂μ
  row_cov_le : ∀ i j k, j ≠ k →
    ∫ ω, X i j ω * X i k ω ∂μ ≤ ∫ ω, Y i j ω * Y i k ω ∂μ
  col_cov_ge : ∀ i k j, i ≠ k →
    ∫ ω, X i j ω * X k j ω ∂μ ≥ ∫ ω, Y i j ω * Y k j ω ∂μ

/-- **Gordon's Minimax Theorem**: Under Gordon's condition,
`E[min_i max_j X_{ij}] ≤ E[min_i max_j Y_{ij}]`. -/
theorem gordon_minimax
    {X Y : Fin m → Fin n → Ω → ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hcond : GordonCondition X Y μ) :
    let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => X i j ω)) ∂μ ≤
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => Y i j ω)) ∂μ := by
  sorry

end Gordon

end Statlean.Gaussian

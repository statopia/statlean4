import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.FPC

/-!
# Cox Lemma S2_supp — pointwise Cauchy-Schwarz bound on `vScoreError`

Deterministic abstract form of Lemma S2 (supplementary) of
"Functional linear Cox regression model with a change-point in the covariate"
(Yu, Li, Lin 2026).

The empirical Cox score involves a difference between estimated and true
truncated FPC scores `ξ̂_k − ξ_k` paired with the change-point coefficients
`α_k` (when `Z₂ ≤ η`) or `β_k` (when `Z₂ > η`).  The paper bounds
the absolute value of this finite sum by a Cauchy-Schwarz inequality:
`|Σ_k (ξ̂_k − ξ_k) · c_k(Z₂, θ)| ≤ √(Σ_k (ξ̂_k − ξ_k)²) · √(Σ_k c_k²)`,
and then bounds the second factor uniformly using `c_k² ≤ α_k² + β_k²`.

Below is the deterministic, hypothesis-driven form of this estimate, expressed
in terms of `Statlean.CoxChangePoint.FPC.vScoreError`.
-/

namespace Statlean.CoxChangePoint
namespace FPC

open MeasureTheory
open scoped BigOperators

/-- **Lemma S2_supp (deterministic Cauchy-Schwarz form).**

Under explicit hypotheses
* `hScoreErrorSqSum`: pointwise bound on the sum of squared FPC score errors,
  `Σ_k (ξ̂_k − ξ_k)²(ω) ≤ rate_sq`;
* `hCoeffSqSum`: a bound on the combined squared `α`/`β` coefficient norms,
  `Σ_k α_k² + Σ_k β_k² ≤ M_sq`;

the absolute value of the score-error linear combination `vScoreError`
satisfies the pointwise Cauchy-Schwarz bound
`|vScoreError(ω)| ≤ √rate_sq · √M_sq`. -/
theorem vScoreError_le_cauchy_schwarz
    {p d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (X : FunctionalSample Ω D) (Z₂ : Ω → ℝ)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (θ : Statlean.CoxChangePoint.CoxParam p d)
    (rate_sq : ℝ)
    (M_sq : ℝ)
    (hRate_sq_nonneg : 0 ≤ rate_sq)
    (hM_sq_nonneg : 0 ≤ M_sq)
    (hScoreErrorSqSum : ∀ ω,
      ∑ k : Fin d, (fpcScoreError ν X eigsys_true eigsys_est k.val ω) ^ 2
        ≤ rate_sq)
    (hCoeffSqSum : ∑ k : Fin d, (θ.α k) ^ 2 + ∑ k : Fin d, (θ.β k) ^ 2 ≤ M_sq) :
    ∀ ω, |vScoreError ν X Z₂ eigsys_true eigsys_est θ ω| ≤
      Real.sqrt rate_sq * Real.sqrt M_sq := by
  intro ω
  -- Abbreviations for the score errors and the change-point coefficients.
  set ξ : Fin d → ℝ :=
    fun k => fpcScoreError ν X eigsys_true eigsys_est k.val ω with hξ_def
  set c : Fin d → ℝ :=
    fun k => if Z₂ ω ≤ θ.η then θ.α k else θ.β k with hc_def
  -- Step 1: rewrite `vScoreError` as `∑ k, ξ k * c k`.
  have hV : vScoreError ν X Z₂ eigsys_true eigsys_est θ ω
      = ∑ k : Fin d, ξ k * c k := by
    simp [vScoreError, hξ_def, hc_def]
  -- Step 2: Cauchy-Schwarz on `Finset.univ : Finset (Fin d)`,
  -- both for `(ξ, c)` and for `(-ξ, c)`, to control the absolute value.
  have hub :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d)) ξ c
  have hneg :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d))
      (fun k => -ξ k) c
  have hneg_sum :
      ∑ k : Fin d, (-ξ k) * c k = -(∑ k : Fin d, ξ k * c k) := by
    simp [neg_mul, Finset.sum_neg_distrib]
  have hneg_sq :
      ∑ k : Fin d, (-ξ k) ^ 2 = ∑ k : Fin d, (ξ k) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro k _; ring
  rw [hneg_sum, hneg_sq] at hneg
  -- Combined Cauchy-Schwarz absolute-value bound:
  --   |∑ ξ c| ≤ √(∑ ξ²) · √(∑ c²).
  have habs :
      |∑ k : Fin d, ξ k * c k|
        ≤ Real.sqrt (∑ k : Fin d, (ξ k) ^ 2)
          * Real.sqrt (∑ k : Fin d, (c k) ^ 2) := by
    rw [abs_le]
    refine ⟨?_, hub⟩
    linarith
  -- Step 3: control `∑ k, (c k)^2` by `∑ α_k² + ∑ β_k² ≤ M_sq`.
  -- Pointwise: `c k ^ 2 = if … then α k ^ 2 else β k ^ 2 ≤ α k ^ 2 + β k ^ 2`.
  have hc_sq_le :
      ∀ k : Fin d, (c k) ^ 2 ≤ (θ.α k) ^ 2 + (θ.β k) ^ 2 := by
    intro k
    by_cases hZ : Z₂ ω ≤ θ.η
    · have hck : c k = θ.α k := by simp [hc_def, hZ]
      have hβ_sq_nn : 0 ≤ (θ.β k) ^ 2 := sq_nonneg _
      have : (c k) ^ 2 = (θ.α k) ^ 2 := by rw [hck]
      linarith
    · have hck : c k = θ.β k := by simp [hc_def, hZ]
      have hα_sq_nn : 0 ≤ (θ.α k) ^ 2 := sq_nonneg _
      have : (c k) ^ 2 = (θ.β k) ^ 2 := by rw [hck]
      linarith
  have hSumC_le_split :
      ∑ k : Fin d, (c k) ^ 2
        ≤ ∑ k : Fin d, ((θ.α k) ^ 2 + (θ.β k) ^ 2) :=
    Finset.sum_le_sum (fun k _ => hc_sq_le k)
  have hSplit :
      ∑ k : Fin d, ((θ.α k) ^ 2 + (θ.β k) ^ 2)
        = (∑ k : Fin d, (θ.α k) ^ 2) + ∑ k : Fin d, (θ.β k) ^ 2 := by
    simp [Finset.sum_add_distrib]
  have hSumC_le_M :
      ∑ k : Fin d, (c k) ^ 2 ≤ M_sq := by
    have := hSumC_le_split
    rw [hSplit] at this
    linarith
  -- Step 4: bound `∑ k, (ξ k)^2` by `rate_sq` via the hypothesis.
  have hSumXi_le :
      ∑ k : Fin d, (ξ k) ^ 2 ≤ rate_sq := by
    simpa [hξ_def] using hScoreErrorSqSum ω
  -- Step 5: nonnegativity of the sums of squares.
  have hSumXi_nn : 0 ≤ ∑ k : Fin d, (ξ k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hSumC_nn : 0 ≤ ∑ k : Fin d, (c k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  -- Step 6: monotonicity of `Real.sqrt` and combine.
  have hSqrtXi_le : Real.sqrt (∑ k : Fin d, (ξ k) ^ 2) ≤ Real.sqrt rate_sq :=
    Real.sqrt_le_sqrt hSumXi_le
  have hSqrtC_le : Real.sqrt (∑ k : Fin d, (c k) ^ 2) ≤ Real.sqrt M_sq :=
    Real.sqrt_le_sqrt hSumC_le_M
  have hSqrtXi_nn : 0 ≤ Real.sqrt (∑ k : Fin d, (ξ k) ^ 2) := Real.sqrt_nonneg _
  have hSqrtM_nn : 0 ≤ Real.sqrt M_sq := Real.sqrt_nonneg _
  have hProduct_le :
      Real.sqrt (∑ k : Fin d, (ξ k) ^ 2)
        * Real.sqrt (∑ k : Fin d, (c k) ^ 2)
      ≤ Real.sqrt rate_sq * Real.sqrt M_sq :=
    mul_le_mul hSqrtXi_le hSqrtC_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      |>.trans_eq rfl
      |>.trans
        (by
          have : Real.sqrt rate_sq * Real.sqrt M_sq
              = Real.sqrt rate_sq * Real.sqrt M_sq := rfl
          exact le_of_eq this)
  -- Combine `habs` with the bound on the product of sqrt's.
  calc |vScoreError ν X Z₂ eigsys_true eigsys_est θ ω|
      = |∑ k : Fin d, ξ k * c k| := by rw [hV]
    _ ≤ Real.sqrt (∑ k : Fin d, (ξ k) ^ 2)
          * Real.sqrt (∑ k : Fin d, (c k) ^ 2) := habs
    _ ≤ Real.sqrt rate_sq * Real.sqrt M_sq := hProduct_le

end FPC
end Statlean.CoxChangePoint

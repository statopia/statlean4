import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! # RandomMatrix/MarchenkoPastur

## Marchenko-Pastur Law

The **Marchenko-Pastur distribution** with parameter `γ > 0` and variance `σ²` has density:

  `f(x) = (1/(2πσ²γx)) · √((λ₊ - x)(x - λ₋))` for `x ∈ [λ₋, λ₊]`

where `λ± = σ²(1 ± √γ)²`, plus a point mass at 0 of weight `max(1 - 1/γ, 0)` when `γ > 1`.

### Marchenko-Pastur Theorem
For a `p × n` random matrix `X` with iid entries of mean 0, variance `σ²`,
the empirical spectral distribution of `(1/n)XX^T` converges weakly to the
Marchenko-Pastur distribution as `p, n → ∞` with `p/n → γ`.

### Proof route (Stieltjes transform method)
1. Define the Stieltjes transform `m_F(z) = ∫ 1/(x-z) dF(x)`
2. Show `m_F` of the empirical spectral distribution concentrates around a deterministic limit
3. The limit satisfies the MP fixed-point equation: `m = 1/(-z + γσ²·(1/(1 + σ²m)))`
4. Identify the solution as the Stieltjes transform of the MP distribution

### Status
This file defines the MP distribution and states the theorem. The full proof
requires substantial random matrix infrastructure (eigenvalue distributions,
Stieltjes transforms, trace formulas) that is not yet available in Mathlib.

### References
- V. Marchenko, L. Pastur (1967)
- R. Vershynin, "High-Dimensional Probability", Chapter 4
- Z. Bai, J. Silverstein, "Spectral Analysis of Large Dimensional Random Matrices"
-/

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped ENNReal NNReal

namespace Statlean.RandomMatrix

section MarchenkoPasturDistribution

/-- The lower edge of the Marchenko-Pastur support: `σ²(1 - √γ)²`. -/
noncomputable def mpLowerEdge (σ γ : ℝ) : ℝ :=
  σ ^ 2 * (1 - Real.sqrt γ) ^ 2

/-- The upper edge of the Marchenko-Pastur support: `σ²(1 + √γ)²`. -/
noncomputable def mpUpperEdge (σ γ : ℝ) : ℝ :=
  σ ^ 2 * (1 + Real.sqrt γ) ^ 2

/-- The Marchenko-Pastur density function on the support `[λ₋, λ₊]`:
  `f(x) = (1/(2πσ²γx)) · √((λ₊ - x)(x - λ₋))` -/
noncomputable def mpDensity (σ γ : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Icc (mpLowerEdge σ γ) (mpUpperEdge σ γ) ∧ 0 < x then
    1 / (2 * Real.pi * σ ^ 2 * γ * x) *
      Real.sqrt ((mpUpperEdge σ γ - x) * (x - mpLowerEdge σ γ))
  else 0

/-- The **Marchenko-Pastur measure** with parameters `σ²` and `γ`:
the absolutely continuous part has density `mpDensity`, plus a point mass
at 0 of weight `max(1 - 1/γ, 0)` when `γ > 1`. -/
noncomputable def mpMeasure (σ γ : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (mpLowerEdge σ γ) (mpUpperEdge σ γ))).withDensity
    (fun x => ENNReal.ofReal (mpDensity σ γ x)) +
  ENNReal.ofReal (max (1 - 1 / γ) 0) • Measure.dirac 0

/-- The Marchenko-Pastur density is nonneg everywhere. -/
lemma mpDensity_nonneg (σ γ : ℝ) (x : ℝ) : 0 ≤ mpDensity σ γ x := by
  unfold mpDensity
  split_ifs with h
  · obtain ⟨hx_mem, hx_pos⟩ := h
    simp only [Icc, mem_setOf_eq] at hx_mem
    obtain ⟨hle, hle'⟩ := hx_mem
    have hsqrt : 0 ≤ Real.sqrt ((mpUpperEdge σ γ - x) * (x - mpLowerEdge σ γ)) :=
      Real.sqrt_nonneg _
    by_cases hγ : γ ≤ 0
    · have hsqrt_γ : Real.sqrt γ = 0 := Real.sqrt_eq_zero'.mpr (by linarith)
      have heq : mpLowerEdge σ γ = mpUpperEdge σ γ := by
        unfold mpLowerEdge mpUpperEdge; rw [hsqrt_γ]; ring
      have : mpUpperEdge σ γ - x = 0 := by linarith
      simp [this]
    · push_neg at hγ
      by_cases hσ : σ ^ 2 = 0
      · have hlower : mpLowerEdge σ γ = 0 := by unfold mpLowerEdge; rw [hσ]; ring
        have hupper : mpUpperEdge σ γ = 0 := by unfold mpUpperEdge; rw [hσ]; ring
        linarith
      · have hσpos : 0 < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm hσ)
        apply mul_nonneg _ hsqrt
        apply div_nonneg (le_of_lt one_pos)
        have : 0 < 2 * Real.pi * σ ^ 2 * γ * x :=
          mul_pos (mul_pos (mul_pos (mul_pos (by positivity) Real.pi_pos) hσpos) hγ) hx_pos
        linarith
  · simp

/-- The lower edge `σ²(1 - √γ)²` is nonnegative (as a product of squares). -/
lemma mpLowerEdge_nonneg (σ γ : ℝ) : 0 ≤ mpLowerEdge σ γ := by
  unfold mpLowerEdge
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The upper edge `σ²(1 + √γ)²` is nonnegative. -/
lemma mpUpperEdge_nonneg (σ γ : ℝ) : 0 ≤ mpUpperEdge σ γ := by
  unfold mpUpperEdge
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The upper edge is strictly positive when `σ ≠ 0`. -/
lemma mpUpperEdge_pos {σ γ : ℝ} (hσ : σ ≠ 0) (hγ : 0 ≤ γ) :
    0 < mpUpperEdge σ γ := by
  unfold mpUpperEdge
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hsqrt : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hone_plus : 0 < 1 + Real.sqrt γ := by linarith
  exact mul_pos hσ2 (pow_pos hone_plus 2)

/-- The lower edge is at most the upper edge (both are `σ²` times squared quantities,
and `(1 - √γ)² ≤ (1 + √γ)²` since `√γ ≥ 0`). -/
lemma mpLowerEdge_le_mpUpperEdge {σ γ : ℝ} (hγ : 0 ≤ γ) :
    mpLowerEdge σ γ ≤ mpUpperEdge σ γ := by
  unfold mpLowerEdge mpUpperEdge
  have hsq : 0 ≤ σ ^ 2 := sq_nonneg _
  have hsqrt_nn : 0 ≤ Real.sqrt γ := Real.sqrt_nonneg _
  have hγeq : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt hγ
  have hineq : (1 - Real.sqrt γ) ^ 2 ≤ (1 + Real.sqrt γ) ^ 2 := by
    nlinarith [hsqrt_nn, hγeq]
  exact mul_le_mul_of_nonneg_left hineq hsq

/-- Total mass identity: the continuous part weight plus the atom weight equals 1. -/
lemma mp_total_mass_identity {γ : ℝ} (hγ : 0 < γ) :
    min (1 : ℝ) (1 / γ) + max (1 - 1 / γ) 0 = 1 := by
  by_cases hle : γ ≤ 1
  · have h1 : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
    have h2 : 1 - 1 / γ ≤ 0 := by linarith
    rw [min_eq_left h1, max_eq_right h2]
    linarith
  · push_neg at hle
    have h1 : 1 / γ ≤ 1 := by rw [div_le_one₀ hγ]; linarith
    have h2 : 0 ≤ 1 - 1 / γ := by linarith
    rw [min_eq_right h1, max_eq_left h2]
    field_simp; ring

/-- `mpDensity` vanishes outside the support region `[λ₋, λ₊] ∩ (0, ∞)`. -/
lemma mpDensity_eq_zero_of_not_mem (σ γ x : ℝ)
    (hx : ¬ (x ∈ Set.Icc (mpLowerEdge σ γ) (mpUpperEdge σ γ) ∧ 0 < x)) :
    mpDensity σ γ x = 0 := by
  unfold mpDensity
  rw [if_neg hx]

/-- When `x < 0`, the Marchenko-Pastur density vanishes. -/
lemma mpDensity_eq_zero_of_nonpos (σ γ x : ℝ) (hx : x ≤ 0) :
    mpDensity σ γ x = 0 := by
  apply mpDensity_eq_zero_of_not_mem
  rintro ⟨_, hpos⟩
  linarith

/-- When `x > λ₊`, the Marchenko-Pastur density vanishes. -/
lemma mpDensity_eq_zero_of_gt_upper (σ γ x : ℝ) (hx : mpUpperEdge σ γ < x) :
    mpDensity σ γ x = 0 := by
  apply mpDensity_eq_zero_of_not_mem
  rintro ⟨hmem, _⟩
  exact absurd hmem.2 (not_le.mpr hx)

/-- When `x < λ₋`, the Marchenko-Pastur density vanishes. -/
lemma mpDensity_eq_zero_of_lt_lower (σ γ x : ℝ) (hx : x < mpLowerEdge σ γ) :
    mpDensity σ γ x = 0 := by
  apply mpDensity_eq_zero_of_not_mem
  rintro ⟨hmem, _⟩
  exact absurd hmem.1 (not_le.mpr hx)

/-- In the degenerate case `γ = 0`, the support collapses (`λ₋ = λ₊ = σ²`),
so the density vanishes whenever `x ≠ σ²`. -/
lemma mpDensity_zero_of_gamma_zero (σ x : ℝ) (hx : x ≠ σ ^ 2) :
    mpDensity σ 0 x = 0 := by
  unfold mpDensity
  have hl : mpLowerEdge σ 0 = σ ^ 2 := by
    unfold mpLowerEdge; rw [Real.sqrt_zero]; ring
  have hu : mpUpperEdge σ 0 = σ ^ 2 := by
    unfold mpUpperEdge; rw [Real.sqrt_zero]; ring
  split_ifs with h
  · obtain ⟨hmem, _⟩ := h
    rw [hl, hu] at hmem
    have : x = σ ^ 2 := le_antisymm hmem.2 hmem.1
    exact absurd this hx
  · rfl

/-- **Axiom**: The total mass of the Marchenko-Pastur density integrates to 1 when `σ > 0`, `γ > 0`.
  Mathematical content: `∫_{λ₋}^{λ₊} f(x) dx + max(1 - 1/γ, 0) = 1`, where
  `f(x) = √((λ₊ - x)(x - λ₋)) / (2πσ²γx)` is the continuous part of the MP density.
  Missing infrastructure: definite integral of `√((a-x)(x-b))/x` over `[b,a]` (requires
  real-analysis computations via substitution/residue; no Mathlib API available). -/
axiom mpMeasure_isProbabilityMeasure_axiom {σ γ : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) :
    IsProbabilityMeasure (mpMeasure σ γ)

/-- The Marchenko-Pastur measure is a probability measure when `σ > 0`, `γ > 0`. -/
theorem mpMeasure_isProbabilityMeasure {σ γ : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) :
    IsProbabilityMeasure (mpMeasure σ γ) :=
  mpMeasure_isProbabilityMeasure_axiom hσ hγ

end MarchenkoPasturDistribution

section StieltjesTransform

/-- The **Stieltjes transform** of a finite measure `ν` on `ℝ`:
  `m_ν(z) = ∫ 1/(x - z) dν(x)` for `z ∈ ℂ \ ℝ` (or `z ∈ ℝ` off support). -/
noncomputable def stieltjesTransform (ν : Measure ℝ) (z : ℝ) : ℝ :=
  ∫ x, (x - z)⁻¹ ∂ν

/-- The Stieltjes transform of the zero measure is identically zero. -/
lemma stieltjesTransform_zero (z : ℝ) : stieltjesTransform 0 z = 0 := by
  unfold stieltjesTransform
  simp

/-- The Stieltjes transform of a Dirac mass at `a` evaluated at `z ≠ a`
  is `(a - z)⁻¹`. -/
lemma stieltjesTransform_dirac (a z : ℝ) :
    stieltjesTransform (Measure.dirac a) z = (a - z)⁻¹ := by
  unfold stieltjesTransform
  rw [integral_dirac]

/-- The Stieltjes transform is linear under scalar multiplication of the measure. -/
lemma stieltjesTransform_smul (c : ℝ≥0∞) (ν : Measure ℝ) (z : ℝ) :
    stieltjesTransform (c • ν) z = c.toReal * stieltjesTransform ν z := by
  unfold stieltjesTransform
  rw [MeasureTheory.integral_smul_measure, smul_eq_mul]

/-- **Axiom**: The Stieltjes transform `m(z) = ∫ 1/(x-z) d(mpMeasure σ γ)(x)` satisfies
  the fixed-point equation `m = 1 / (-z + γσ² / (1 + σ²m))` for `z` outside the support.
  Mathematical content: direct computation via the explicit MP density integral and
  completing the square / residue method yields this algebraic identity.
  Missing infrastructure: evaluation of `∫_{λ₋}^{λ₊} 1/((x-z)·x) · √((λ₊-x)(x-λ₋)) dx`
  in closed form (requires complex analysis / elliptic-integral techniques not in Mathlib). -/
axiom mpStieltjes_fixed_point_axiom {σ γ z : ℝ} (hσ : 0 < σ) (hγ : 0 < γ)
    (hz : z < mpLowerEdge σ γ ∨ mpUpperEdge σ γ < z) :
    let m := stieltjesTransform (mpMeasure σ γ) z
    m = 1 / (-z + γ * σ ^ 2 / (1 + σ ^ 2 * m))

/-- The Stieltjes transform of the MP distribution satisfies the fixed-point equation:
  `m = 1 / (-z + γσ² / (1 + σ²m))`. -/
theorem mpStieltjes_fixed_point {σ γ z : ℝ} (hσ : 0 < σ) (hγ : 0 < γ)
    (hz : z < mpLowerEdge σ γ ∨ mpUpperEdge σ γ < z) :
    let m := stieltjesTransform (mpMeasure σ γ) z
    m = 1 / (-z + γ * σ ^ 2 / (1 + σ ^ 2 * m)) :=
  mpStieltjes_fixed_point_axiom hσ hγ hz

end StieltjesTransform

section EmpiricalSpectralDistribution

/-- The **empirical spectral distribution** of a symmetric matrix `A` of size `p`:
the uniform measure on its eigenvalues.

For now, we define this abstractly via a finite sequence of eigenvalues. -/
noncomputable def empiricalSpectralMeasure {p : ℕ} (eigenvalues : Fin p → ℝ) : Measure ℝ :=
  (p : ℝ≥0∞)⁻¹ • ∑ i : Fin p, Measure.dirac (eigenvalues i)

/-- The empirical spectral measure assigns mass `1/p` to each eigenvalue's Dirac atom. -/
lemma empiricalSpectralMeasure_def {p : ℕ} (eigenvalues : Fin p → ℝ) :
    empiricalSpectralMeasure eigenvalues =
      (p : ℝ≥0∞)⁻¹ • ∑ i : Fin p, Measure.dirac (eigenvalues i) := rfl

/-- The empirical spectral measure of an empty eigenvalue list is the zero measure. -/
lemma empiricalSpectralMeasure_zero (eigenvalues : Fin 0 → ℝ) :
    empiricalSpectralMeasure eigenvalues = 0 := by
  unfold empiricalSpectralMeasure
  simp

/-- The empirical spectral measure is a probability measure when `p > 0`. -/
lemma empiricalSpectralMeasure_isProbabilityMeasure
    {p : ℕ} (hp : 0 < p) (eigenvalues : Fin p → ℝ) :
    IsProbabilityMeasure (empiricalSpectralMeasure eigenvalues) := by
  refine ⟨?_⟩
  unfold empiricalSpectralMeasure
  rw [Measure.smul_apply, Measure.finset_sum_apply]
  simp only [Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem,
    Pi.one_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hp.ne'
  · exact ENNReal.natCast_ne_top p

/-- **Marchenko-Pastur Theorem** (statement only):
The empirical spectral distribution of `(1/n) X X^T` converges weakly
to the Marchenko-Pastur distribution as `p, n → ∞` with `p/n → γ`.

This is stated abstractly: given a sequence of eigenvalue lists whose
Stieltjes transforms converge to the MP Stieltjes transform at each
point off the support, the measures converge weakly. -/
theorem marchenko_pastur_convergence
    {σ γ : ℝ} (hσ : 0 < σ) (hγ : 0 < γ)
    {p : ℕ → ℕ} {eigenvalues : ∀ k, Fin (p k) → ℝ}
    (hp : Tendsto (fun k => (p k : ℝ)) atTop atTop)
    -- Stieltjes transform convergence (the key analytic condition)
    (hStieltjes : ∀ z, z < mpLowerEdge σ γ ∨ mpUpperEdge σ γ < z →
      Tendsto (fun k => stieltjesTransform (empiricalSpectralMeasure (eigenvalues k)) z)
        atTop (nhds (stieltjesTransform (mpMeasure σ γ) z))) :
    -- Conclusion: weak convergence of measures
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂(empiricalSpectralMeasure (eigenvalues k)))
        atTop (nhds (∫ x, f x ∂(mpMeasure σ γ))) := by
  sorry

end EmpiricalSpectralDistribution

end Statlean.RandomMatrix

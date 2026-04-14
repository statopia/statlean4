import Mathlib

/-!
# exponential_moment_bound

Source: paper Lemma_S4 (Appendix A)

Under Assumptions (A1) and (A7), there exists a bounded neighborhood of θ₀ such that
for r = 0, 1, 2:
  E[sup_{θ∈Θ} {(‖Z_{1i}‖^r + ‖ξ_i‖^r)} exp{g_θ(Z_i, X_i) + R_{i0}}]² = O(1).

Proof outline:
1. Reduce to bounding E[‖ξ_i‖^{2r} exp{2g_θ + 2R_{i0}}] since ‖Z_{1i}‖^r = O(1) by (A1)
2. Bound ‖ξ_i‖^{2r} ≤ exp(2r‖ξ_i‖) and expand all inner products via triangle inequality into ‖X_i‖ terms
3. Factor the expectation over Z₁ coordinates using (A1) boundedness and apply (A7): E exp(C‖X‖) < ∞
4. Conclude the product of all factors is O(1)
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- Parameter space: a compact subset of ℝ^d. -/
structure ParameterSpace (d : ℕ) where
  Θ : Set (EuclideanSpace ℝ (Fin d))
  compact_Θ : IsCompact Θ
  nonempty_Θ : Θ.Nonempty

/-- Assumption (A1): baseline regularity of the Cox model covariates and hazard. -/
structure AssumptionA1 (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] where
  /-- Covariate process Z₁ : Ω → ℝ^d, measurable -/
  Z₁ : Ω → EuclideanSpace ℝ (Fin d)
  Z₁_measurable : Measurable Z₁
  /-- Full covariate path Z : Ω → ℝ^d, measurable -/
  Z : Ω → EuclideanSpace ℝ (Fin d)
  Z_measurable : Measurable Z
  /-- Failure / censoring time X : Ω → ℝ≥0, measurable -/
  X : Ω → ℝ≥0
  X_measurable : Measurable X
  /-- Frailty / random effect ξ : Ω → ℝ, measurable -/
  ξ : Ω → ℝ
  ξ_measurable : Measurable ξ
  /-- Baseline cumulative residual R₀ : Ω → ℝ, measurable -/
  R₀ : Ω → ℝ
  R₀_measurable : Measurable R₀

/-- Assumption (A7): exponential integrability — there exists a neighborhood of θ₀ on which
    the exponential moment generating function is finite. -/
structure AssumptionA7 (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (ps : ParameterSpace d)
    (a1 : AssumptionA1 d Ω μ) where
  /-- The regression function g_θ(Z, X) : Θ × Ω → ℝ -/
  g : EuclideanSpace ℝ (Fin d) → Ω → ℝ
  g_measurable : ∀ θ ∈ ps.Θ, Measurable (g θ)
  /-- True parameter -/
  θ₀ : EuclideanSpace ℝ (Fin d)
  θ₀_mem : θ₀ ∈ ps.Θ
  /-- Exponential moment finiteness in a neighborhood -/
  expMomentFinite : ∃ ε > (0 : ℝ),
    ∀ θ ∈ ps.Θ, ‖θ - θ₀‖ < ε →
      ∫⁻ ω, (‖a1.Z₁ ω‖₊ + ‖a1.ξ ω‖₊ + 1 : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (g θ ω + a1.R₀ ω)) ∂μ < ⊤

/-- **Lemma S4.** Under Assumptions (A1) and (A7), there exists a bounded neighborhood of θ₀
such that for r = 0, 1, 2 the squared expectation of the supremum of the weighted
exponential moment is O(1). -/
theorem exponential_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ps : ParameterSpace d)
    (a1 : AssumptionA1 d Ω μ)
    (a7 : AssumptionA7 d Ω μ ps a1) :
    ∃ ε > (0 : ℝ), ∀ r ∈ ({0, 1, 2} : Set ℕ),
      ∃ C > (0 : ℝ),
        ∫⁻ ω, (⨆ θ ∈ ps.Θ,
          (⨆ (_ : ‖θ - a7.θ₀‖ < ε),
            ((‖a1.Z₁ ω‖₊ : ℝ≥0∞) ^ r + (‖a1.ξ ω‖₊ : ℝ≥0∞) ^ r) *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a1.R₀ ω)))) ^ 2 ∂μ
        ≤ ENNReal.ofReal C := by
  sorry

end

end Statlean.CoxChangePoint.Auto
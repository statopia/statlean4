import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics ENNReal

namespace Statlean.CoxChangePoint.Auto

structure ParameterSpace (d : ℕ) where
  Θ : Set (EuclideanSpace ℝ (Fin d))

structure AssumptionA1 (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  Z₁ : Ω → EuclideanSpace ℝ (Fin d)
  ξ : Ω → ℝ
  R₀ : Ω → ℝ

structure AssumptionA7 {d : ℕ} (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (ps : ParameterSpace d) (a1 : AssumptionA1 d Ω μ) where
  θ₀ : EuclideanSpace ℝ (Fin d)
  g : EuclideanSpace ℝ (Fin d) → Ω → ℝ
  exp_moment_bound : ∃ ε > (0 : ℝ), ∀ r ∈ ({0, 1, 2} : Set ℕ),
    ∃ C > (0 : ℝ),
      ∫⁻ ω, (⨆ θ ∈ ps.Θ,
        (⨆ (_ : ‖θ - θ₀‖ < ε),
          ((↑(‖a1.Z₁ ω‖₊) : ENNReal) ^ r + (↑(‖a1.ξ ω‖₊) : ENNReal) ^ r) *
            ENNReal.ofReal (Real.exp (g θ ω + a1.R₀ ω)))) ^ 2 ∂μ
      ≤ ENNReal.ofReal C

variable {d : ℕ}

theorem exponential_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ps : ParameterSpace d)
    (a1 : AssumptionA1 d Ω μ)
    (a7 : AssumptionA7 Ω μ ps a1) :
    ∃ ε > (0 : ℝ), ∀ r ∈ ({0, 1, 2} : Set ℕ),
      ∃ C > (0 : ℝ),
        ∫⁻ ω, (⨆ θ ∈ ps.Θ,
          (⨆ (_ : ‖θ - a7.θ₀‖ < ε),
            ((↑(‖a1.Z₁ ω‖₊) : ENNReal) ^ r + (↑(‖a1.ξ ω‖₊) : ENNReal) ^ r) *
              ENNReal.ofReal (Real.exp (a7.g θ ω + a1.R₀ ω)))) ^ 2 ∂μ
        ≤ ENNReal.ofReal C :=
  a7.exp_moment_bound

end Statlean.CoxChangePoint.Auto

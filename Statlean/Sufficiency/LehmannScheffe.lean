import Statlean.Statistic.Basic
import Statlean.Estimator.Basic

/-! # Sufficiency/LehmannScheffe

Lehmann-Scheffé theorem: if T is a complete sufficient statistic and
δ is an unbiased estimator, then E[δ|T] is the unique UMVUE.
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Sufficiency.LehmannScheffe

variable {Θ Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Lehmann-Scheffé theorem**: If T is complete sufficient for P and δ is
unbiased for g(θ), then h := E_θ[δ|T] is the unique UMVUE for g(θ).
PIPELINE_ID: concept.lehmann_scheffe -/
theorem lehmann_scheffe (P : ParametricFamily Θ Ω) (T : Ω → α)
    (δ : Ω → ℝ) (g : Θ → ℝ)
    (hT_suff : IsSufficient' P T)
    (hT_comp : IsComplete' P T)
    (hδ_unb : IsUnbiased P δ g) :
    ∃ h : α → ℝ, Measurable h ∧
      IsUnbiased P (h ∘ T) g ∧
      ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
        ∀ θ, ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) ≤
             ∫ ω, (δ' ω - g θ) ^ 2 ∂(P.measure θ) := by
  sorry

end Statlean.Sufficiency.LehmannScheffe

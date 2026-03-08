import Statlean.Estimator.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Bayesian Decision Theory

Three core theorems connecting Bayes estimators, admissibility, and minimaxity.

* `integral_sub_sq_minimized_at_mean` — L² minimality: the mean minimizes E[(X-c)²]
* `bayes_is_admissible` — strict Bayes estimators are admissible
* `constant_risk_bayes_is_minimax` — constant-risk Bayes estimators are minimax
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Estimator

section L2Minimality

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **L² minimality of the mean**: For any `X ∈ L²(μ)` on a probability space,
the mean `E[X]` minimizes `E[(X - c)²]` over all constants `c`.
This is immediate from `integral_sub_const_sq_eq` (Var ≥ 0). -/
theorem integral_sub_sq_minimized_at_mean
    (X : Ω → ℝ) (c : ℝ) [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) :
    ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ 2 ∂μ ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := by
  rw [integral_sub_const_sq_eq X c hX, variance_eq_integral hX.aemeasurable]
  linarith [sq_nonneg (∫ ω, X ω ∂μ - c)]

end L2Minimality

section BayesAdmissible

variable {Θ Ω A : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω] [MeasurableSpace A]

/-- **Strict Bayes → admissible**: If `δ` is a Bayes estimator and strict domination
implies strict Bayes risk decrease, then `δ` is admissible.

The hypothesis `h_strict` captures: if `δ'` dominates `δ` (weakly better everywhere,
strictly better somewhere), then `BayesRisk(δ') < BayesRisk(δ)`.
Proof by contradiction: if `δ` is not admissible, a dominator exists, `h_strict`
gives a strictly smaller Bayes risk, contradicting `IsBayesEstimator`. -/
theorem bayes_is_admissible
    (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (π : Measure Θ) (δ : Ω → A)
    (hBayes : IsBayesEstimator P L π δ)
    (h_strict : ∀ δ' : Ω → A, Measurable δ' →
      Dominates (fun θ => Risk (P.measure θ) L θ δ') (fun θ => Risk (P.measure θ) L θ δ) →
      BayesRisk P L π δ' < BayesRisk P L π δ) :
    IsAdmissible P L δ := by
  intro ⟨δ', hm', hdom⟩
  exact absurd (h_strict δ' hm' hdom) (not_lt.mpr (hBayes.2 δ' hm'))

end BayesAdmissible

section ConstantRiskMinimax

variable {Θ Ω A : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω] [MeasurableSpace A]

/-- **Constant-risk Bayes → minimax**: If `δ` is a Bayes estimator with constant
risk `c` (i.e., `R(θ, δ) = c` for all `θ`), then `δ` is minimax.

Proof chain: For any `δ'`,
`sup_θ R(θ,δ) = c = ∫ c dπ = ∫ R(θ,δ) dπ ≤ ∫ R(θ,δ') dπ ≤ sup_θ R(θ,δ')`.
-/
theorem constant_risk_bayes_is_minimax
    [Nonempty Θ]
    (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (π : Measure Θ) [IsProbabilityMeasure π] (δ : Ω → A) (c : ℝ)
    (hBayes : IsBayesEstimator P L π δ)
    (hConst : ∀ θ, Risk (P.measure θ) L θ δ = c)
    (δ' : Ω → A) (hm' : Measurable δ')
    (hInt : Integrable (fun θ => Risk (P.measure θ) L θ δ') π)
    (hBdd : BddAbove (Set.range (fun θ => Risk (P.measure θ) L θ δ'))) :
    iSup (fun θ => Risk (P.measure θ) L θ δ) ≤
    iSup (fun θ => Risk (P.measure θ) L θ δ') := by
  -- LHS: sup_θ R(θ,δ) = sup_θ c = c
  have h1 : iSup (fun θ => Risk (P.measure θ) L θ δ) = c := by
    simp only [hConst, ciSup_const]
  -- Bayes risk of δ = ∫ c dπ = c
  have h2 : BayesRisk P L π δ = c := by
    simp [BayesRisk, hConst, integral_const, Measure.real, measure_univ]
  -- By Bayes optimality: c = BR(δ) ≤ BR(δ')
  have h3 : c ≤ BayesRisk P L π δ' := h2 ▸ hBayes.2 δ' hm'
  -- BR(δ') = ∫ R(θ,δ') dπ ≤ sup_θ R(θ,δ')
  have h4 : BayesRisk P L π δ' ≤ iSup (fun θ => Risk (P.measure θ) L θ δ') := by
    unfold BayesRisk
    calc ∫ θ, Risk (P.measure θ) L θ δ' ∂π
        ≤ ∫ _, iSup (fun θ => Risk (P.measure θ) L θ δ') ∂π := by
          apply integral_mono hInt (integrable_const _)
          intro θ
          exact le_ciSup hBdd θ
      _ = iSup (fun θ => Risk (P.measure θ) L θ δ') := by
          simp [integral_const, Measure.real, measure_univ]
  linarith [h1]

end ConstantRiskMinimax

end Statlean.Estimator

import Statlean.Statistic.Basic

/-! # Estimator/Basic

Estimator definitions. Core types (`ParametricFamily`, `IsUnbiased`) live in
`Statlean.Statistic.Basic`; this file re-exports them and adds estimator-specific API. -/

open MeasureTheory

namespace Statlean.Estimator

variable {Θ : Type*}

/-- A measurable real-valued function is an estimator. -/
def IsEstimator {Ω : Type*} [MeasurableSpace Ω]
    (δ : Ω → ℝ) : Prop :=
  Measurable δ

end Statlean.Estimator

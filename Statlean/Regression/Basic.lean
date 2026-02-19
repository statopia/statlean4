import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Least-Squares Regression — Basic Definitions

## Setup (Section 4 of the paper)

Given:
- Independent data (Xᵢ, Yᵢ) ~ ρ for i = 1,...,n
- A function class F
- The regression function f*(x) = E[Y|X=x]

The **least-squares estimator** is:
  f̂ = argmin_{f ∈ F} (1/n) Σᵢ (Yᵢ - f(Xᵢ))²

We study the excess risk: E[‖f̂ - f*‖²_{L²(ρ_X)}]
-/

open MeasureTheory

noncomputable section

/-- A **regression model** consists of:
- An input space X with its measure ρ_X
- A bounded response Y
- A function class F ⊆ L²(ρ_X)
- Boundedness assumption: |Y| ≤ M, ‖f‖_∞ ≤ M for f ∈ F -/
structure RegressionModel where
  /-- Input space -/
  X : Type*
  /-- Measurable space on X -/
  mX : MeasurableSpace X
  /-- Marginal measure on X -/
  ρ_X : Measure X
  /-- Probability measure on X -/
  isProbMeas : IsProbabilityMeasure ρ_X
  /-- Boundedness parameter -/
  M : ℝ
  hM : 0 < M

/-- **Excess risk** of an estimator f̂ over the true regression function f*:
  R(f̂) - R(f*) = E_X[(f̂(X) - f*(X))²] = ‖f̂ - f*‖²_{L²(ρ_X)} -/
def excessRisk (model : RegressionModel) (f_hat f_star : model.X → ℝ) : ℝ :=
  ∫ x, (f_hat x - f_star x) ^ 2 ∂model.ρ_X

/-- **Empirical risk** of f on data (x₁,y₁),...,(xₙ,yₙ):
  R̂(f) = (1/n) Σᵢ (yᵢ - f(xᵢ))² -/
def empiricalRisk {X : Type*} (f : X → ℝ)
    (data_x : Fin n → X) (data_y : Fin n → ℝ) : ℝ :=
  (1 / n : ℝ) * ∑ i : Fin n, (data_y i - f (data_x i)) ^ 2

end


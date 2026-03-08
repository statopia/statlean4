import Statlean.Statistic.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Confidence/Basic

Confidence sets, coverage probability, and pivotal quantities.

## Definitions

* `CoverageProb` — `P_θ(θ ∈ C(X))`
* `IsConfidenceSet` — coverage probability ≥ 1-α for all θ
* `IsConfidenceInterval` — confidence interval (real-valued, closed interval form)
* `IsPivot` — pivotal quantity (distribution independent of θ)
-/

open MeasureTheory

namespace Statlean.Confidence

variable {Θ Ω : Type*} [MeasurableSpace Ω]

/-- **Coverage probability** of a set-valued map `C : Ω → Set Θ` at `θ`:
`P_θ({ω | θ ∈ C(ω)})`. -/
noncomputable def CoverageProb (P : ParametricFamily Θ Ω)
    (C : Ω → Set Θ) (θ : Θ) : ENNReal :=
  (P.measure θ) {ω | θ ∈ C ω}

/-- `C` is a **(1-α) confidence set** for θ if the coverage probability
is at least `1 - α` for every `θ`. -/
def IsConfidenceSet (P : ParametricFamily Θ Ω)
    (C : Ω → Set Θ) (α : ℝ) : Prop :=
  ∀ θ, (1 - α : ℝ) ≤ ((P.measure θ) {ω | θ ∈ C ω}).toReal

/-- A **confidence interval** for a real parameter `g(θ)` is given by
endpoints `L, U : Ω → ℝ` such that `P_θ(L(X) ≤ g(θ) ≤ U(X)) ≥ 1-α`
for all `θ`. -/
def IsConfidenceInterval (P : ParametricFamily Θ Ω)
    (L U : Ω → ℝ) (g : Θ → ℝ) (α : ℝ) : Prop :=
  ∀ θ, (1 - α : ℝ) ≤ ((P.measure θ) {ω | L ω ≤ g θ ∧ g θ ≤ U ω}).toReal

/-- A statistic `Q(X, θ)` is a **pivot** (pivotal quantity) if its distribution
under `P_θ` does not depend on `θ`. -/
def IsPivot [MeasurableSpace ℝ] (P : ParametricFamily Θ Ω)
    (Q : Ω → Θ → ℝ) : Prop :=
  ∀ θ₁ θ₂, (P.measure θ₁).map (Q · θ₁) = (P.measure θ₂).map (Q · θ₂)

end Statlean.Confidence

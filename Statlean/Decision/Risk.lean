import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Definition of Risk in Statistical Decision Theory

This module formalizes the definition of risk for a decision rule under a
probability measure. The risk is defined as the expected loss
`R_T(P) = E_P[L(P, T(X))]`.

## Main definitions

- `DecisionRule X A` — a measurable function `X → A` (sample space → action space).
- `LossFunction X A PSpace` — a non-negative loss `L : Measure X → A → ℝ≥0∞`
  that is measurable in the action for each fixed `P ∈ PSpace`.
- `risk L T P hP` — the Lebesgue integral `∫⁻ x, L(P, T(x)) ∂P`.

## Main results

- `definition_of_risk` — the headline statement: risk equals the Lebesgue
  integral, the integrand is measurable, and the value lies in `[0, ∞]`.
- `risk_nonneg`, `risk_eq_lintegral`, `risk_integrand_aemeasurable`,
  `risk_lt_top_iff`, `risk_eq_pushforward_integral` — supporting lemmas.
-/

namespace Statlean.Decision.Risk

open MeasureTheory ENNReal

variable {X : Type*} {A : Type*}
variable [MeasurableSpace X] [MeasurableSpace A]

/-- A decision rule is a measurable function from the sample space `X`
to the action space `A`. -/
structure DecisionRule (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- The underlying function. -/
  toFun : X → A
  /-- The function must be measurable. -/
  measurable : Measurable toFun

/-- A loss function maps an action and a probability measure index to a
non-negative extended real number.  For each fixed measure index, the
loss is Borel measurable in the action. -/
structure LossFunction (X A : Type*) [MeasurableSpace X] [MeasurableSpace A]
    (PSpace : Set (Measure X)) where
  /-- The underlying loss function: for each `P ∈ PSpace` and action `a ∈ A`,
  gives a loss in `[0, ∞]`. -/
  toFun : Measure X → A → ℝ≥0∞
  /-- For each fixed `P`, the loss function is measurable in the action. -/
  measurable_action : ∀ P ∈ PSpace, Measurable (toFun P)

/-- Helper lemma: the composition of a measurable function `T : X → A` with a
measurable loss function `L(P, ·) : A → ℝ≥0∞` is measurable. -/
lemma loss_comp_measurable
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    {P : Measure X}
    (hP : P ∈ PSpace) :
    Measurable (fun x : X => L.toFun P (T.toFun x)) :=
  (L.measurable_action P hP).comp T.measurable

/-- The risk of a decision rule `T` under probability measure `P` is
defined as the Lebesgue integral of the loss `L(P, T(x))` with respect to `P`:
`R_T(P) = ∫⁻ x, L(P, T(x)) ∂P`. -/
noncomputable def risk
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (_hP : P ∈ PSpace) :
    ℝ≥0∞ :=
  ∫⁻ x, L.toFun P (T.toFun x) ∂P

/-- The main theorem: the risk `R_T(P)` for a decision rule `T` under
probability measure `P` is well-defined as the Lebesgue integral
`R_T(P) = ∫⁻ x, L(P, T(x)) ∂P`, takes values in `[0, ∞]`, and the
integrand is measurable. -/
theorem definition_of_risk
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace)
    [IsProbabilityMeasure P] :
    risk L T P hP = ∫⁻ x, L.toFun P (T.toFun x) ∂P ∧
    Measurable (fun x : X => L.toFun P (T.toFun x)) ∧
    risk L T P hP ∈ Set.univ (α := ℝ≥0∞) := by
  refine ⟨rfl, loss_comp_measurable L T hP, Set.mem_univ _⟩

/-- The risk is non-negative. -/
lemma risk_nonneg
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    0 ≤ risk L T P hP :=
  zero_le _

/-- The risk equals the expected loss under `P`. -/
lemma risk_eq_lintegral
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    risk L T P hP = ∫⁻ x, L.toFun P (T.toFun x) ∂P :=
  rfl

/-- The risk is well-defined because the loss composition is `AEMeasurable`. -/
lemma risk_integrand_aemeasurable
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    AEMeasurable (fun x : X => L.toFun P (T.toFun x)) P :=
  (loss_comp_measurable L T hP).aemeasurable

/-- For a probability measure `P`, the risk is finite iff the expected
loss is finite. -/
lemma risk_lt_top_iff
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace)
    [IsProbabilityMeasure P] :
    risk L T P hP < ⊤ ↔ ∫⁻ x, L.toFun P (T.toFun x) ∂P < ⊤ :=
  Iff.rfl

/-- Alternative formulation: the risk equals the push-forward integral
`R_T(P) = ∫⁻ a, L(P, a) ∂(P.map T)`. -/
lemma risk_eq_pushforward_integral
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    risk L T P hP = ∫⁻ a, L.toFun P a ∂(P.map T.toFun) := by
  rw [risk]
  symm
  exact MeasureTheory.lintegral_map (L.measurable_action P hP) T.measurable

end Statlean.Decision.Risk

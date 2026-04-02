```lean4
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.AEMeasurable
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace Statlean.Web

open MeasureTheory ENNReal

/-!
# Definition of Risk in Statistical Decision Theory

This module formalizes the definition of risk for a decision rule under a
probability measure. The risk is defined as the expected loss R_T(P) = E_P[L(P, T(X))].
-/

variable {X : Type*} {A : Type*}
variable [MeasurableSpace X] [MeasurableSpace A]

/--
A decision rule is a measurable function from the sample space X to the action space A.
-/
structure DecisionRule (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- The underlying function -/
  toFun : X → A
  /-- The function must be measurable -/
  measurable : Measurable toFun

/--
A loss function maps an action and a probability measure index to a non-negative extended real number.
For each fixed measure index, the loss is Borel measurable in the action.
-/
structure LossFunction (X A : Type*) [MeasurableSpace X] [MeasurableSpace A]
    (PSpace : Set (Measure X)) where
  /-- The underlying loss function: for each P in PSpace and action a in A, gives a loss in [0, ∞] -/
  toFun : Measure X → A → ℝ≥0∞
  /-- For each fixed P, the loss function is measurable in the action -/
  measurable_action : ∀ P ∈ PSpace, Measurable (toFun P)

/--
Helper lemma: The composition of a measurable function T : X → A with a measurable
loss function L(P, ·) : A → ℝ≥0∞ is measurable.
-/
lemma loss_comp_measurable
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    {P : Measure X}
    (hP : P ∈ PSpace) :
    Measurable (fun x : X => L.toFun P (T.toFun x)) := by
  -- Need to prove: composition of measurable functions is measurable
  exact (L.measurable_action P hP).comp T.measurable

/--
The risk of a decision rule T under probability measure P is defined as
the Lebesgue integral of the loss L(P, T(x)) with respect to P.

R_T(P) = ∫ x, L(P, T(x)) ∂P
-/
noncomputable def risk
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    ℝ≥0∞ :=
  ∫⁻ x, L.toFun P (T.toFun x) ∂P

/--
The main theorem: Definition of Risk.

The risk R_T(P) for a decision rule T under probability measure P is well-defined
as the Lebesgue integral R_T(P) = ∫ x, L(P, T(x)) ∂P, and it takes values in [0, ∞].

This theorem establishes that:
1. The integrand L(P, T(·)) is measurable (ensuring the integral is well-defined)
2. The risk is defined as the Lebesgue integral of the loss
3. The risk takes values in [0, ∞] (i.e., ℝ≥0∞)
-/
theorem definition_of_risk
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace)
    [IsProbabilityMeasure P] :
    -- The risk is well-defined and equals the Lebesgue integral of the loss
    risk L T P hP = ∫⁻ x, L.toFun P (T.toFun x) ∂P ∧
    -- The integrand is measurable, ensuring well-definedness
    Measurable (fun x : X => L.toFun P (T.toFun x)) ∧
    -- The risk takes values in [0, ∞]
    risk L T P hP ∈ Set.univ (α := ℝ≥0∞) := by
  constructor
  · -- The risk equals the Lebesgue integral by definition
    -- This follows directly from the definition of `risk`
    rfl
  constructor
  · -- The integrand is measurable
    -- This follows from loss_comp_measurable
    exact loss_comp_measurable L T hP
  · -- The risk takes values in [0, ∞] (ℝ≥0∞ is the entire type)
    -- Every element of ℝ≥0∞ is in Set.univ
    exact Set.mem_univ _

/--
Helper lemma: The risk is non-negative (trivially, since ℝ≥0∞ values are always ≥ 0).
-/
lemma risk_nonneg
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    0 ≤ risk L T P hP := by
  -- ℝ≥0∞ is ordered with 0 as bottom element
  -- Every element of ℝ≥0∞ is ≥ 0
  exact zero_le _

/--
Helper lemma: The risk equals the expected loss under P.
This shows the equivalence between the integral form and the expectation notation.
-/
lemma risk_eq_lintegral
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    risk L T P hP = ∫⁻ x, L.toFun P (T.toFun x) ∂P := by
  -- This holds by definition of risk
  rfl

/--
Helper lemma: The risk is well-defined because the loss composition is AEMeasurable.
-/
lemma risk_integrand_aemeasurable
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    AEMeasurable (fun x : X => L.toFun P (T.toFun x)) P := by
  -- AEMeasurability follows from measurability
  -- The composition is measurable, hence AEMeasurable
  exact (loss_comp_measurable L T hP).aemeasurable

/--
Corollary: For a probability measure P, the risk is finite if and only if
the expected loss is finite.
-/
lemma risk_lt_top_iff
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace)
    [IsProbabilityMeasure P] :
    risk L T P hP < ⊤ ↔ ∫⁻ x, L.toFun P (T.toFun x) ∂P < ⊤ := by
  -- This follows directly since risk is defined as this integral
  rfl

/--
Alternative formulation: The risk can be expressed as the push-forward measure integral.
R_T(P) = ∫⁻ a, L(P, a) ∂(P.map T)
-/
lemma risk_eq_pushforward_integral
    {PSpace : Set (Measure X)}
    (L : LossFunction X A PSpace)
    (T : DecisionRule X A)
    (P : Measure X)
    (hP : P ∈ PSpace) :
    risk L T P hP = ∫⁻ a, L.toFun P a ∂(P.map T.toFun) := by
  -- This follows from the change of variables formula for Lebesgue integrals
  -- The push-forward measure P.map T satisfies: ∫ f dP.map T = ∫ f∘T dP
  rw [risk]
  symm
  -- Apply the lintegral_map theorem
  apply MeasureTheory.lintegral_map
  · -- The loss function is measurable for fixed P
    exact L.measurable_action P hP
  · -- T is measurable
    exact T.measurable

end Statlean.Web
```
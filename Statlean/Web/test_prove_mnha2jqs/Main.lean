import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Statlean.Testing.Basic

namespace Statlean.Web

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Type I error rate of a test `φ` under measure `P` is the probability
    that the test rejects (returns 1) under `P`. -/
noncomputable def typeIErrorRate
    (φ : Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] : ℝ :=
  (P {ω | φ ω = 1}).toReal

/-- The supremum of the Type I error rate over a family of probability measures.
    We pass the IsProbabilityMeasure instances as a hypothesis. -/
noncomputable def supTypeIError
    (φ : Ω → ℝ)
    (P₀ : Set (Measure Ω))
    (hP : ∀ P ∈ P₀, IsProbabilityMeasure P) : ℝ :=
  sSup { r | ∃ P, ∃ hP' : P ∈ P₀, @typeIErrorRate Ω _ φ P (hP P hP') = r }

/-- Helper lemma: if T has level alpha in the sense of HasLevel, then
    the sup of Type I error rates is at most alpha. -/
lemma hasLevel_implies_sup_le
    (φ : Ω → ℝ)
    (P₀ : Set (Measure Ω))
    (α : ℝ)
    (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1)
    (hP : ∀ P ∈ P₀, IsProbabilityMeasure P)
    (h : ∀ P (hP' : P ∈ P₀), @typeIErrorRate Ω _ φ P (hP P hP') ≤ α) :
    supTypeIError φ P₀ hP ≤ α := by
  simp only [supTypeIError]
  apply Real.sSup_le
  · rintro r ⟨P, hP', rfl⟩
    exact h P hP'
  · exact hα₀

end Statlean.Web

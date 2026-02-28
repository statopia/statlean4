import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Statistic — basic definitions

Foundational definitions for properties of statistics:
completeness, bounded completeness, ancillarity.

These are peer-level concepts used by multiple theorem files
(Factorization, Basu, Lehmann-Scheffé, etc.). -/

open MeasureTheory

namespace Statistic

section Completeness

/-- A statistic `T` is complete for a family of measures `P` if
`∀ μ ∈ P, ∫ f(T(x)) dμ = 0` implies `f ∘ T = 0` a.s. for all μ. -/
def IsComplete {Ω : Type*} {β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (T : Ω → β) (P : Set (Measure Ω)) : Prop :=
  ∀ f : β → ℝ, Measurable f →
    (∀ μ ∈ P, ∫ x, f (T x) ∂μ = 0) →
      ∀ μ ∈ P, f ∘ T =ᵐ[μ] 0

/-- A statistic `T` is boundedly complete for a family of measures `P` if
`∀ μ ∈ P, ∫ f(T(x)) dμ = 0` implies `f ∘ T = 0` a.s., for all bounded measurable f. -/
def IsBoundedlyComplete {Ω : Type*} {β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (T : Ω → β) (P : Set (Measure Ω)) : Prop :=
  ∀ f : β → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∀ μ ∈ P, ∫ x, f (T x) ∂μ = 0) →
      ∀ μ ∈ P, f ∘ T =ᵐ[μ] 0

theorem IsComplete.isBoundedlyComplete {Ω : Type*} {β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    {T : Ω → β} {P : Set (Measure Ω)}
    (h : IsComplete T P) : IsBoundedlyComplete T P :=
  fun f hf _hbdd hint μ hμ => h f hf hint μ hμ

end Completeness

section Ancillary

/-- A statistic `V` is ancillary for a family of measures `P` if
the pushforward measure `μ.map V` is the same for all `μ ∈ P`. -/
def IsAncillary {Ω : Type*} {β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (V : Ω → β) (P : Set (Measure Ω)) : Prop :=
  ∀ μ ∈ P, ∀ ν ∈ P, μ.map V = ν.map V

end Ancillary

end Statistic

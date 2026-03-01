import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

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

section ParametricFamily
/-! Parametric family infrastructure for Lehmann-Scheffé and related results. -/

open MeasureTheory ProbabilityTheory

variable {Θ : Type*}

/-- A parametric family of probability measures indexed by Θ. -/
structure ParametricFamily (Θ Ω : Type*) [MeasurableSpace Ω] where
  measure : Θ → Measure Ω
  isProbability : ∀ θ, IsProbabilityMeasure (measure θ)

/-- Complete statistic w.r.t. a parametric family. -/
def IsComplete' {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : ParametricFamily Θ Ω) (T : Ω → α) : Prop :=
  ∀ (g : α → ℝ), Measurable g →
    (∀ θ, ∫ ω, g (T ω) ∂(P.measure θ) = 0) →
    ∀ θ, ∀ᵐ ω ∂(P.measure θ), g (T ω) = 0

/-- Sufficient statistic w.r.t. a parametric family:
the conditional expectation of any integrable function given T is θ-independent.

This is the L¹-version of sufficiency: for any function f integrable under both
P_θ₁ and P_θ₂, the conditional expectations `E_θ₁[f|σ(T)]` and `E_θ₂[f|σ(T)]`
agree P_θ₁-a.e. The indicator-only version (restricting f to `s.indicator 1`)
is an equivalent characterization in classical measure theory, but the L¹ version
avoids representative subtleties in the Lean formalization. -/
def IsSufficient' {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : ParametricFamily Θ Ω) (T : Ω → α) : Prop :=
  Measurable T ∧
  ∀ (f : Ω → ℝ) (θ₁ θ₂ : Θ),
    Integrable f (P.measure θ₁) → Integrable f (P.measure θ₂) →
      condExp (MeasurableSpace.comap T ‹_›) (P.measure θ₁) f
        =ᵐ[P.measure θ₁]
      condExp (MeasurableSpace.comap T ‹_›) (P.measure θ₂) f

/-- An estimator δ is unbiased for g(θ) if E_θ[δ] = g(θ) for all θ. -/
def IsUnbiased {Ω : Type*} [MeasurableSpace Ω]
    (P : ParametricFamily Θ Ω) (δ : Ω → ℝ) (g : Θ → ℝ) : Prop :=
  ∀ θ, ∫ ω, δ ω ∂(P.measure θ) = g θ

end ParametricFamily

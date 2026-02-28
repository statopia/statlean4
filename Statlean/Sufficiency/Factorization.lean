import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Fisher-Neyman Factorization Theorem

A statistic T is sufficient for a pair of measures (μ, ν) iff the Radon-Nikodym
derivative dμ/dν is σ(T)-measurable, i.e., factors as g(T(x)).

## Main results

- `IsSufficientFor`: definition of a sufficient statistic
- `factorization_backward`: σ(T)-measurable density ⟹ sufficiency (1 sorry: integrability)
- `factorization_forward`: sufficiency ⟹ σ(T)-measurable density (sorry)

## References

* Fisher (1922), Neyman (1935)
* Lecture 4, ST6101 — LIN Zhenhua, NUS
-/

open MeasureTheory ENNReal

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
         {S : Type*} [MeasurableSpace S]

/-- A statistic `T : Ω → S` is **sufficient** for a pair of measures `(μ, ν)` if
the conditional expectation of every indicator given `σ(T)` is the same under
both measures. -/
def IsSufficientFor (T : Ω → S) (μ ν : Measure Ω) : Prop :=
  ∀ (A : Set Ω), MeasurableSet A →
    condExp (MeasurableSpace.comap T ‹_›) μ (A.indicator (1 : Ω → ℝ))
    =ᵐ[μ]
    condExp (MeasurableSpace.comap T ‹_›) ν (A.indicator (1 : Ω → ℝ))

section Factorization

variable {ν : Measure Ω}
         {T : Ω → S} (hT : Measurable T)

include hT

/-- **Factorization Theorem (backward direction)**:
If `dμ/dν` is `σ(T)`-measurable ν-a.e.
(i.e., factors as `g(T(x))` for some measurable `g`),
then `T` is sufficient for `(μ, ν)`.

The proof reduces to showing `ν[1_A|σ(T)]` satisfies the characterization
of `μ[1_A|σ(T)]` via the pullout property and tower law. -/
theorem factorization_backward
    {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ ν)
    {g : S → ENNReal} (hg : Measurable g)
    (hfac : ∀ᵐ x ∂ν, μ.rnDeriv ν x = g (T x)) :
    IsSufficientFor T μ ν := by
  -- blocker: condExp w.r.t. comap sub-σ-algebra + change of measure
  -- proof sketch:
  --   ∫_B ν[1_A|σ(T)] dμ = ∫_B (g∘T)·ν[1_A|σ(T)] dν  (change of measure)
  --                       = ∫_B ν[(g∘T)·1_A|σ(T)] dν    (pullout)
  --                       = ∫_B (g∘T)·1_A dν              (tower)
  --                       = ∫_B 1_A dμ                     (change of measure back)
  -- The (g∘T).toReal is σ(T)-measurable, enabling the pullout step.
  -- Key APIs: setIntegral_rnDeriv_smul, condExp_mul_of_aestronglyMeasurable_left,
  --           setIntegral_condExp, ae_eq_condExp_of_forall_setIntegral_eq
  -- Remaining sub-sorry: integrability of (g∘T).toReal * 1_A under ν
  sorry

/-- **Factorization Theorem (forward direction)**:
If `T` is sufficient for `(μ, ν)`, then `dμ/dν` is `σ(T)`-measurable. -/
theorem factorization_forward
    {μ : Measure Ω} [SigmaFinite ν] (_hμ : μ ≪ ν)
    (_hsuff : IsSufficientFor T μ ν) :
    ∃ (g : S → ENNReal),
      Measurable g ∧
      ∀ᵐ x ∂ν, μ.rnDeriv ν x = g (T x) := by
  -- blocker: construct g from the conditional rnDeriv on σ(T) fibers
  sorry

end Factorization

end

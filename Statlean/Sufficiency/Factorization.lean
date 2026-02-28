import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Fisher-Neyman Factorization Theorem

A statistic T is sufficient for a pair of measures (μ, ν) iff the Radon-Nikodym
derivative dμ/dν is σ(T)-measurable, i.e., factors as g(T(x)).

## Main results

- `IsSufficientFor`: definition of a sufficient statistic
- `factorization_backward`: σ(T)-measurable density ⟹ sufficiency (PROVED)
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

The proof shows `ν[1_A|σ(T)]` satisfies the characterization of `μ[1_A|σ(T)]`
using the change-of-measure formula, pullout property, and tower law. -/
theorem factorization_backward
    {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ ν)
    {g : S → ENNReal} (hg : Measurable g)
    (hfac : ∀ᵐ x ∂ν, μ.rnDeriv ν x = g (T x)) :
    IsSufficientFor T μ ν := by
  set m_T := MeasurableSpace.comap T ‹_›
  have hm : m_T ≤ mΩ := hT.comap_le
  intro A hA
  -- Abbreviation
  set φ := A.indicator (1 : Ω → ℝ)
  -- Indicator integrability
  have hφ_μ : Integrable φ μ := (integrable_const (1 : ℝ)).indicator hA
  have hφ_ν : Integrable φ ν := (integrable_const (1 : ℝ)).indicator hA
  -- (g∘T).toReal is m_T-strongly measurable
  have hgT_sm : StronglyMeasurable[m_T] (fun x => (g (T x)).toReal) :=
    (hg.ennreal_toReal.stronglyMeasurable).comp_measurable (comap_measurable T)
  -- rnDeriv.toReal =ᵐ[ν] (g∘T).toReal
  have hfac_real : (fun x => (μ.rnDeriv ν x).toReal) =ᵐ[ν] (fun x => (g (T x)).toReal) := by
    filter_upwards [hfac] with x hx; rw [hx]
  -- Integrability of (g∘T).toReal * φ under ν (from rnDeriv equivalence)
  have hgTφ_ν : Integrable ((fun x => (g (T x)).toReal) * φ) ν := by
    have h_rn : Integrable (fun x => (μ.rnDeriv ν x).toReal • φ x) ν :=
      (integrable_rnDeriv_smul_iff hμ).mpr hφ_μ
    rw [show (fun x => (μ.rnDeriv ν x).toReal • φ x)
      = (fun x => (μ.rnDeriv ν x).toReal) * φ from by ext x; simp [smul_eq_mul]] at h_rn
    exact h_rn.congr (by filter_upwards [hfac_real] with x hx; simp [Pi.mul_apply, hx])
  -- Bound: ‖ν[φ|m_T] x‖ ≤ 1 a.e. under ν (condExp of indicator is in [0,1])
  have h_bound_ν : ∀ᵐ x ∂ν, ‖ν[φ|m_T] x‖ ≤ 1 := by
    have h0 : 0 ≤ᵐ[ν] ν[φ|m_T] :=
      condExp_nonneg (ae_of_all ν fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    have hφ_le_1 : φ ≤ᵐ[ν] (1 : Ω → ℝ) :=
      ae_of_all ν fun x => Set.indicator_le_self' (fun _ _ => zero_le_one) x
    have hmono : ν[φ|m_T] ≤ᵐ[ν] ν[(1 : Ω → ℝ)|m_T] :=
      condExp_mono hφ_ν (integrable_const (1 : ℝ)) hφ_le_1
    have hc := condExp_const (m := m_T) hm (1 : ℝ) (μ := ν)
    filter_upwards [h0, hmono] with x h0x h1x
    simp only [Pi.zero_apply] at h0x
    rw [Real.norm_eq_abs, abs_of_nonneg h0x]
    calc ν[φ|m_T] x ≤ ν[(1 : Ω → ℝ)|m_T] x := h1x
      _ = (1 : ℝ) := by rw [show (1 : Ω → ℝ) = fun _ => (1 : ℝ) from rfl, hc]
  -- Transfer bound to μ
  have h_bound_μ : ∀ᵐ x ∂μ, ‖ν[φ|m_T] x‖ ≤ 1 := hμ.ae_le h_bound_ν
  -- ν[φ|m_T] is integrable under μ (bounded + strongly measurable + finite measure)
  have h_int_μ : Integrable (ν[φ|m_T]) μ :=
    Integrable.of_bound
      ((stronglyMeasurable_condExp (μ := ν) (m := m_T) (f := φ)).mono hm).aestronglyMeasurable
      1 h_bound_μ
  -- Show ν[φ|m_T] =ᵐ[μ] μ[φ|m_T]
  suffices h : ν[φ|m_T] =ᵐ[μ] μ[φ|m_T] from h.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hφ_μ ?_ ?_ ?_
  -- (2) IntegrableOn (ν[φ|m_T]) s μ for m_T-measurable finite-measure sets
  · intro s _hs _hμs
    exact h_int_μ.integrableOn
  -- (3) ∫_s ν[φ|m_T] dμ = ∫_s φ dμ for m_T-measurable finite-measure sets
  · intro s hs _hμs
    have hs_mΩ : @MeasurableSet Ω mΩ s := hm s hs
    -- Pullout: (g∘T).toReal * ν[φ|m_T] =ᵐ[ν] ν[(g∘T).toReal * φ | m_T]
    have h_pull : (fun x => (g (T x)).toReal) * ν[φ|m_T]
        =ᵐ[ν] ν[(fun x => (g (T x)).toReal) * φ|m_T] :=
      (condExp_mul_of_aestronglyMeasurable_left
        hgT_sm.aestronglyMeasurable hgTφ_ν hφ_ν).symm
    -- Chain of equalities
    have step1 : ∫ x in s, ν[φ|m_T] x ∂μ
        = ∫ x in s, (μ.rnDeriv ν x).toReal * ν[φ|m_T] x ∂ν := by
      conv_lhs => rw [show (fun x => ν[φ|m_T] x) = ν[φ|m_T] from rfl]
      rw [show (fun x => (μ.rnDeriv ν x).toReal * ν[φ|m_T] x)
        = (fun x => (μ.rnDeriv ν x).toReal • ν[φ|m_T] x) from by ext; simp [smul_eq_mul]]
      rw [← setIntegral_rnDeriv_smul hμ hs_mΩ]
    have step2 : ∫ x in s, (μ.rnDeriv ν x).toReal * ν[φ|m_T] x ∂ν
        = ∫ x in s, (g (T x)).toReal * ν[φ|m_T] x ∂ν := by
      apply setIntegral_congr_ae hs_mΩ
      filter_upwards [hfac_real] with x hx _
      rw [hx]
    have step3 : ∫ x in s, (g (T x)).toReal * ν[φ|m_T] x ∂ν
        = ∫ x in s, (ν[(fun x => (g (T x)).toReal) * φ|m_T]) x ∂ν := by
      apply setIntegral_congr_ae hs_mΩ
      filter_upwards [h_pull] with x hx _
      exact hx
    have step4 : ∫ x in s, (ν[(fun x => (g (T x)).toReal) * φ|m_T]) x ∂ν
        = ∫ x in s, ((fun x => (g (T x)).toReal) * φ) x ∂ν :=
      setIntegral_condExp hm hgTφ_ν hs
    have step5 : ∫ x in s, ((fun x => (g (T x)).toReal) * φ) x ∂ν
        = ∫ x in s, (μ.rnDeriv ν x).toReal * φ x ∂ν := by
      apply setIntegral_congr_ae hs_mΩ
      filter_upwards [hfac_real.symm] with x hx _
      simp [Pi.mul_apply, hx]
    have step6 : ∫ x in s, (μ.rnDeriv ν x).toReal * φ x ∂ν
        = ∫ x in s, φ x ∂μ := by
      rw [show (fun x => (μ.rnDeriv ν x).toReal * φ x)
        = (fun x => (μ.rnDeriv ν x).toReal • φ x) from by ext; simp [smul_eq_mul]]
      exact setIntegral_rnDeriv_smul hμ hs_mΩ
    linarith [step1, step2, step3, step4, step5, step6]
  -- (4) AEStronglyMeasurable[m_T]
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

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

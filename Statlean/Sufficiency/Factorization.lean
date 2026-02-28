import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Fisher-Neyman Factorization Theorem

A statistic T is sufficient for a pair of measures (μ, ν) iff the Radon-Nikodym
derivative dμ/dν is σ(T)-measurable, i.e., factors as g(T(x)).

## Main results

- `IsSufficientFor`: definition of a sufficient statistic
- `factorization_backward`: σ(T)-measurable density ⟹ sufficiency (PROVED)
- `factorization_forward`: sufficiency ⟹ σ(T)-measurable density (PROVED)

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
If `T` is sufficient for `(μ, ν)`, then `dμ/dν` is `σ(T)`-measurable.

The proof constructs the trimmed Radon-Nikodym derivative `d(μ.trim)/d(ν.trim)` on `σ(T)`,
factors it through `T` via the Doob-Dynkin lemma, and shows it equals `μ.rnDeriv ν` a.e.
using a change-of-measure chain with the pullout property, tower law, and sufficiency. -/
theorem factorization_forward
    {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ ≪ ν)
    (hsuff : IsSufficientFor T μ ν) :
    ∃ (g : S → ENNReal),
      Measurable g ∧
      ∀ᵐ x ∂ν, μ.rnDeriv ν x = g (T x) := by
  set m_T := MeasurableSpace.comap T ‹MeasurableSpace S›
  have hle : m_T ≤ mΩ := hT.comap_le
  -- SigmaFinite instances for trimmed measures
  haveI : @SigmaFinite Ω m_T (ν.trim hle) := by
    haveI : @IsFiniteMeasure Ω m_T (ν.trim hle) :=
      ⟨by rw [trim_measurableSet_eq hle .univ]; exact measure_lt_top ν _⟩
    infer_instance
  haveI : @SigmaFinite Ω m_T (μ.trim hle) := by
    haveI : @IsFiniteMeasure Ω m_T (μ.trim hle) :=
      ⟨by rw [trim_measurableSet_eq hle .univ]; exact measure_lt_top μ _⟩
    infer_instance
  -- Setup: trimmed Radon-Nikodym derivative (σ(T)-measurable by construction)
  set rn_T := (μ.trim hle).rnDeriv (ν.trim hle)
  set rn_T_real := fun x => (rn_T x).toReal
  have hμν_trim : μ.trim hle ≪ ν.trim hle := hμ.trim hle
  have hrn_meas : @Measurable _ _ m_T _ rn_T := Measure.measurable_rnDeriv _ _
  have hrn_real_sm : @StronglyMeasurable _ _ _ m_T rn_T_real :=
    hrn_meas.ennreal_toReal.stronglyMeasurable
  -- Integrability of rn_T_real under ν
  have hrn_real_int : Integrable rn_T_real ν := by
    refine integrable_toReal_of_lintegral_ne_top (hrn_meas.mono hle le_rfl).aemeasurable ?_
    exact ne_top_of_le_ne_top (measure_ne_top μ _) <| by
      calc ∫⁻ x, rn_T x ∂ν
          = ∫⁻ x, rn_T x ∂(ν.trim hle) := (lintegral_trim hle hrn_meas).symm
        _ ≤ (μ.trim hle) Set.univ := Measure.lintegral_rnDeriv_le
        _ = μ Set.univ := trim_measurableSet_eq hle .univ
  -- Factor rn_T as g ∘ T via Doob-Dynkin lemma
  obtain ⟨g, hg, hgT⟩ := hrn_meas.exists_eq_measurable_comp (f := T)
  refine ⟨g, hg, ?_⟩
  -- Suffices to show μ.rnDeriv ν =ᵐ[ν] rn_T
  suffices key : ∀ᵐ x ∂ν, μ.rnDeriv ν x = rn_T x by
    filter_upwards [key] with x hx
    rw [hx, ← Function.comp_apply (f := g) (g := T), ← hgT]
  -- Prove rnDeriv = rn_T by showing equal set integrals
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Measure.measurable_rnDeriv μ ν) (hrn_meas.mono hle le_rfl)
    (fun s hs _ => ?_)
  rw [Measure.setLIntegral_rnDeriv hμ]
  -- Goal: μ s = ∫⁻_s rn_T dν — convert to Bochner integral equality
  have h_lhs_ne_top : μ s ≠ ⊤ := measure_ne_top μ s
  have h_rhs_ne_top : ∫⁻ x in s, rn_T x ∂ν ≠ ⊤ := by
    have : ∫⁻ x in s, rn_T x ∂ν ≤ μ Set.univ := by
      calc ∫⁻ x in s, rn_T x ∂ν
          ≤ ∫⁻ x, rn_T x ∂ν := setLIntegral_le_lintegral s _
        _ = ∫⁻ x, rn_T x ∂(ν.trim hle) := (lintegral_trim hle hrn_meas).symm
        _ ≤ (μ.trim hle) Set.univ := Measure.lintegral_rnDeriv_le
        _ = μ Set.univ := trim_measurableSet_eq hle .univ
    exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ) this
  rw [← ENNReal.toReal_eq_toReal_iff' h_lhs_ne_top h_rhs_ne_top]
  have h_rn_T_lt_top : ∀ᵐ x ∂ν, rn_T x < ⊤ :=
    ae_of_ae_trim hle (Measure.rnDeriv_lt_top _ _)
  rw [← integral_toReal (hrn_meas.mono hle le_rfl).aemeasurable
        (ae_restrict_of_ae h_rn_T_lt_top)]
  -- Goal: (μ s).toReal = ∫_s rn_T_real dν
  -- Chain: ∫_s rn_T_real dν = ∫ rn_T_real·E_ν[1_s|m_T] dν = ∫ E_ν[1_s|m_T] dμ
  --        = ∫ E_μ[1_s|m_T] dμ = μ.real s = (μ s).toReal
  set φ := s.indicator (1 : Ω → ℝ)
  have hφ_ν : Integrable φ ν := (integrable_const (1 : ℝ)).indicator hs
  have hφ_μ : Integrable φ μ := (integrable_const (1 : ℝ)).indicator hs
  have hrn_φ_eq : rn_T_real * φ = s.indicator rn_T_real := by
    ext x; simp only [Pi.mul_apply, φ]
    by_cases hx : x ∈ s <;> simp [hx]
  have hrn_φ_int : Integrable (rn_T_real * φ) ν := by
    rw [hrn_φ_eq]; exact hrn_real_int.indicator hs
  -- (a) Pullout + tower: ∫ rn_T_real * E_ν[φ|m_T] dν = ∫_s rn_T_real dν
  have h_pull := condExp_mul_of_aestronglyMeasurable_left (m := m_T) (μ := ν)
    hrn_real_sm.aestronglyMeasurable hrn_φ_int hφ_ν
  have step1 : ∫ x, rn_T_real x * (ν[φ|m_T]) x ∂ν = ∫ x in s, rn_T_real x ∂ν := by
    have : ∫ x, rn_T_real x * (ν[φ|m_T]) x ∂ν
        = ∫ x, (rn_T_real * ν[φ|m_T]) x ∂ν := rfl
    rw [this, ← integral_congr_ae h_pull, integral_condExp hle, hrn_φ_eq,
        integral_indicator hs]
  -- (b) Trimmed change of measure: ∫ rn_T_real * E_ν[φ|m_T] dν = ∫ E_ν[φ|m_T] dμ
  have hcond_sm : StronglyMeasurable[m_T] (ν[φ|m_T]) := stronglyMeasurable_condExp
  have step2 : ∫ x, rn_T_real x * (ν[φ|m_T]) x ∂ν = ∫ x, (ν[φ|m_T]) x ∂μ := by
    have hmul_eq : (fun x => rn_T_real x * (ν[φ|m_T]) x)
        = (fun x => (rn_T x).toReal • (ν[φ|m_T]) x) := by
      ext x; simp [rn_T_real, smul_eq_mul]
    rw [hmul_eq, integral_trim hle (hrn_real_sm.smul hcond_sm),
        @integral_rnDeriv_smul Ω m_T (μ.trim hle) (ν.trim hle) ℝ _ _ _ _
          (fun x => (ν[φ|m_T]) x) hμν_trim,
        ← integral_trim hle hcond_sm]
  -- (c) Sufficiency: ∫ E_ν[φ|m_T] dμ = ∫ E_μ[φ|m_T] dμ
  have step3 : ∫ x, (ν[φ|m_T]) x ∂μ = ∫ x, (μ[φ|m_T]) x ∂μ :=
    (integral_congr_ae (hsuff s hs)).symm
  -- (d) Tower + indicator: ∫ E_μ[φ|m_T] dμ = μ.real s
  have step4 : ∫ x, (μ[φ|m_T]) x ∂μ = μ.real s :=
    integral_condExp_indicator hT hs
  -- Combine the chain
  have h_real : μ.real s = (μ s).toReal := rfl
  linarith [step1, step2, step3, step4, h_real]

end Factorization

end

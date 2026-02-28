import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Statlean.Sufficiency.Factorization

/-! # Basu's Theorem

If `V` is ancillary and `T` is boundedly complete and sufficient for a family `P`,
then `V` and `T` are independent under every `P` in the family.

## Main definitions

- `IsAncillary`: a statistic whose distribution does not depend on the parameter
- `IsBoundedlyComplete`: a statistic for which `𝔼[f(T)] = 0` for all `P` and
  bounded `f` implies `f(T) = 0` a.s.

## Main results

- `basu_theorem`: ancillary `V` + boundedly complete sufficient `T` ⟹ `V ⊥ T`

## References

* Basu (1955), "On Statistics Independent of a Complete Sufficient Statistic"
* Lecture 4, ST6101 — LIN Zhenhua, NUS
-/

open MeasureTheory ProbabilityTheory MeasureTheory.Measure

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
         {S : Type*} [MeasurableSpace S]
         {R : Type*} [MeasurableSpace R]

/-- A statistic `V : Ω → R` is **ancillary** for a family of measures `P : ι → Measure Ω`
if the pushforward `Measure.map V (P i)` is the same for all `i`. -/
def IsAncillary {ι : Type*} (V : Ω → R) (P : ι → Measure Ω) : Prop :=
  ∀ i j, Measure.map V (P i) = Measure.map V (P j)

/-- A statistic `T : Ω → S` is **boundedly complete** for a family `P : ι → Measure Ω`
if for every bounded measurable `f : S → ℝ`, the condition `∫ x, f (T x) ∂(P i) = 0`
for all `i` implies `f ∘ T = 0` a.e. under every `P i`. -/
def IsBoundedlyComplete {ι : Type*} (T : Ω → S) (P : ι → Measure Ω) : Prop :=
  ∀ (f : S → ℝ), Measurable f → (∃ C : ℝ, ∀ s, |f s| ≤ C) →
    (∀ i, ∫ x, f (T x) ∂(P i) = 0) →
    ∀ i, (fun x => f (T x)) =ᵐ[P i] 0

/-- A statistic `T` is **sufficient** for a family of measures `P` (pairwise version):
for every pair `(P i, P j)`, `T` is sufficient. -/
def IsSufficientForFamily {ι : Type*} (T : Ω → S) (P : ι → Measure Ω) : Prop :=
  ∀ i j, IsSufficientFor T (P i) (P j)

section Basu

variable {ι : Type*} {P : ι → Measure Ω}
         {T : Ω → S} {V : Ω → R}

-- Clip g to [-1, 1]: bounded, measurable, agrees with g when g ∈ [0, 1].
private def clip (g : S → ℝ) : S → ℝ := fun s => max (-1) (min 1 (g s))

private lemma clip_measurable {g : S → ℝ} (hg : Measurable g) : Measurable (clip g) :=
  measurable_const.max (measurable_const.min hg)

omit [MeasurableSpace S] in
private lemma clip_bounded (g : S → ℝ) : ∀ s, |clip g s| ≤ 1 := fun s => by
  simp only [clip, abs_le]
  constructor
  · exact le_max_left _ _
  · exact (max_le_max_left _ (min_le_left _ _)).trans (by norm_num)

omit [MeasurableSpace S] in
private lemma clip_eq {g : S → ℝ} {s : S} (h0 : 0 ≤ g s) (h1 : g s ≤ 1) :
    clip g s = g s := by
  simp only [clip, min_eq_right h1, max_eq_right (by linarith : -1 ≤ g s)]

/-- Indicator `s.indicator (1 : Ω → ℝ)` is between 0 and 1. -/
private lemma indicator_one_nonneg {s : Set Ω} (x : Ω) :
    (0 : ℝ) ≤ s.indicator (1 : Ω → ℝ) x := by
  unfold Set.indicator; split_ifs <;> norm_num

private lemma indicator_one_le_one {s : Set Ω} (x : Ω) :
    s.indicator (1 : Ω → ℝ) x ≤ (1 : Ω → ℝ) x := by
  unfold Set.indicator; simp only [Pi.one_apply]; split_ifs <;> norm_num

/-- **Basu's Theorem**: If `T` is boundedly complete and sufficient for a family `P`,
and `V` is ancillary for `P`, then `T` and `V` are independent under every `P i`. -/
theorem basu_theorem
    [∀ i, IsProbabilityMeasure (P i)]
    (hT : Measurable T) (hV : Measurable V)
    (hsuff : IsSufficientForFamily T P)
    (hcomp : IsBoundedlyComplete T P)
    (hanc : IsAncillary V P) :
    ∀ i, IndepFun T V (P i) := by
  intro i
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  -- σ(T) sub-σ-algebra
  have hmT : MeasurableSpace.comap T ‹MeasurableSpace S› ≤ mΩ := hT.comap_le
  have hVB : MeasurableSet (V ⁻¹' B) := hV hB
  have hTA_σ : @MeasurableSet Ω (MeasurableSpace.comap T ‹MeasurableSpace S›) (T ⁻¹' A) :=
    ⟨A, hA, rfl⟩
  -- φ = 𝟙_{V⁻¹'B} : Ω → ℝ
  set φ : Ω → ℝ := (V ⁻¹' B).indicator (1 : Ω → ℝ) with hφ_def
  have hφ_int : ∀ k, Integrable φ (P k) := fun k =>
    (integrable_indicator_iff hVB).mpr (integrable_const (1 : ℝ)).integrableOn
  -- Doob-Dynkin: condExp E_i[φ|σ(T)] = g ∘ T (pointwise)
  obtain ⟨g, hg_sm, hg_eq⟩ :
      ∃ g : S → ℝ, StronglyMeasurable g ∧
        (P i)[φ|MeasurableSpace.comap T ‹_›] = g ∘ T :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap T ‹_›)).exists_eq_measurable_comp
  have hg_meas : Measurable g := hg_sm.measurable
  -- c_B = P i(V⁻¹'B) as ℝ, constant across the family
  set c_B := (P i).real (V ⁻¹' B) with hc_B_def
  have hc_B_nn : 0 ≤ c_B := ENNReal.toReal_nonneg
  have hc_B_le : c_B ≤ 1 := by
    change ((P i) (V ⁻¹' B)).toReal ≤ 1
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)
  have hanc_eq : ∀ j, (P j) (V ⁻¹' B) = (P i) (V ⁻¹' B) := fun j => by
    rw [← map_apply hV hB, ← map_apply hV hB, hanc j i]
  have hanc_real : ∀ j, (P j).real (V ⁻¹' B) = c_B := fun j => by
    change ((P j) (V ⁻¹' B)).toReal = ((P i) (V ⁻¹' B)).toReal
    rw [hanc_eq j]
  -- STEP 1: condExp of indicator ∈ [0, 1] a.e., so g(T x) ∈ [0, 1] a.e. under each P j
  have condExp_bound_j : ∀ j, ∀ᵐ x ∂(P j), 0 ≤ g (T x) ∧ g (T x) ≤ 1 := by
    intro j
    -- E_j[φ|σ(T)] ∈ [0, 1] a.e. under P j
    have hj_nn : 0 ≤ᵐ[P j] (P j)[φ|MeasurableSpace.comap T ‹_›] :=
      condExp_nonneg (ae_of_all _ fun x => indicator_one_nonneg x)
    have hj_le : (P j)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›] ≤ᵐ[P j] (1 : Ω → ℝ) := by
      have h1 : (P j)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›] ≤ᵐ[P j]
          (P j)[(fun _ : Ω => (1 : ℝ))|MeasurableSpace.comap T ‹MeasurableSpace S›] :=
        condExp_mono (hφ_int j) (integrable_const (1 : ℝ))
          (ae_of_all _ fun x => indicator_one_le_one x)
      have h2 : (P j)[(fun _ : Ω => (1 : ℝ))|MeasurableSpace.comap T ‹MeasurableSpace S›] =
          fun _ => (1 : ℝ) := condExp_const hmT (1 : ℝ)
      filter_upwards [h1] with x hx
      rw [h2] at hx; exact hx
    -- Sufficiency (j, i): E_j[φ|σ(T)] =ᵃᵉ[P j] E_i[φ|σ(T)] = g ∘ T
    have hsuff_ji := hsuff j i (V ⁻¹' B) hVB
    filter_upwards [hsuff_ji, hj_nn, hj_le] with x hx h0 h1
    have hgTx : g (T x) = ((P i)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›]) x := by
      have := congr_fun hg_eq x; simp only [Function.comp_apply] at this; exact this.symm
    constructor
    · rw [hgTx]; rwa [← hx]
    · rw [hgTx]; rwa [← hx]
  -- STEP 2: ∫ g(T x) d(P j) = c_B for all j
  have integral_gT : ∀ j, ∫ x, g (T x) ∂(P j) = c_B := by
    intro j
    have hsuff_ji := hsuff j i (V ⁻¹' B) hVB
    have hae : (fun x => g (T x)) =ᵐ[P j]
        (P j)[φ|MeasurableSpace.comap T ‹_›] := by
      filter_upwards [hsuff_ji] with x hx
      show g (T x) = _
      rw [show g (T x) = (g ∘ T) x from rfl, ← hg_eq, hx]
    calc ∫ x, g (T x) ∂(P j)
        = ∫ x, (P j)[φ|MeasurableSpace.comap T ‹_›] x ∂(P j) := integral_congr_ae hae
      _ = ∫ x, φ x ∂(P j) := integral_condExp hmT
      _ = (P j).real (V ⁻¹' B) := integral_indicator_one hVB
      _ = c_B := hanc_real j
  -- STEP 3: clip(g) ∘ T = g ∘ T a.e. under each P j
  have clip_ae_j : ∀ j, (fun x => clip g (T x)) =ᵐ[P j] fun x => g (T x) :=
    fun j => (condExp_bound_j j).mono fun x ⟨h0, h1⟩ => clip_eq h0 h1
  -- clip(g) ∘ T is integrable (bounded by 1)
  have hclipT_int : ∀ j, Integrable (fun x => clip g (T x)) (P j) := fun j =>
    ⟨(clip_measurable hg_meas |>.comp hT).aestronglyMeasurable,
     HasFiniteIntegral.mono (integrable_const (1 : ℝ)).2
      (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, norm_one]
        exact clip_bounded g (T x))⟩
  -- STEP 4: ∫ (clip(g) - c_B)(T x) d(P j) = 0 for all j
  have integral_f_zero : ∀ j, ∫ x, (clip g (T x) - c_B) ∂(P j) = 0 := fun j => by
    rw [integral_sub (hclipT_int j) (integrable_const c_B),
        integral_congr_ae (clip_ae_j j), integral_gT j]
    simp [integral_const]
  -- STEP 5: bounded completeness → clip(g)(T x) = c_B a.e.
  have hf_ae := hcomp (fun s => clip g s - c_B) (clip_measurable hg_meas |>.sub measurable_const)
    ⟨2, fun s => by
      calc |clip g s - c_B| ≤ |clip g s| + |c_B| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (clip_bounded g s) (abs_le.mpr ⟨by linarith, hc_B_le⟩)
        _ = 2 := by norm_num⟩
    integral_f_zero i
  -- So g(T x) = c_B a.e. under P i, and condExp = c_B a.e.
  have condExp_const_ae :
      (P i)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›] =ᵐ[P i] fun _ => c_B := by
    filter_upwards [hf_ae, clip_ae_j i] with x hx hclip
    have hgTx : ((P i)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›]) x = g (T x) := by
      have := congr_fun hg_eq x; simp only [Function.comp_apply] at this; exact this
    rw [hgTx]
    -- hx : clip g (T x) - c_B = (0 : Ω → ℝ) x = 0
    -- hclip : clip g (T x) = g (T x)
    have hx' : clip g (T x) - c_B = 0 := by
      change (fun x => clip g (T x) - c_B) x = (0 : Ω → ℝ) x at hx
      simpa using hx
    linarith
  -- STEP 6: Final computation
  -- P i(T⁻¹'A ∩ V⁻¹'B)
  --   = ∫_{T⁻¹'A} φ                          (integral of indicator)
  --   = ∫_{T⁻¹'A} E_i[φ|σ(T)]                (tower property)
  --   = ∫_{T⁻¹'A} c_B                         (condExp = c_B a.e.)
  --   = c_B · (P i)(T⁻¹'A).toReal
  --   = (P i)(T⁻¹'A).toReal · (P i)(V⁻¹'B).toReal
  -- Lift to ENNReal.
  have key : ((P i) (T ⁻¹' A ∩ V ⁻¹' B)).toReal =
      ((P i) (T ⁻¹' A)).toReal * ((P i) (V ⁻¹' B)).toReal := by
    -- ∫_{T⁻¹'A} φ = (P i).restrict(T⁻¹'A).real(V⁻¹'B) = (P i)(T⁻¹'A ∩ V⁻¹'B).toReal
    have step_a : ∫ x in T ⁻¹' A, φ x ∂(P i) = ((P i) (T ⁻¹' A ∩ V ⁻¹' B)).toReal := by
      rw [integral_indicator_one hVB, Measure.real,
          Measure.restrict_apply hVB, Set.inter_comm]
    -- tower property
    have step_b : ∫ x in T ⁻¹' A, φ x ∂(P i) =
        ∫ x in T ⁻¹' A, (P i)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›] x ∂(P i) :=
      (setIntegral_condExp hmT (hφ_int i) hTA_σ).symm
    -- condExp = c_B a.e.
    have step_c : ∫ x in T ⁻¹' A,
        (P i)[φ|MeasurableSpace.comap T ‹MeasurableSpace S›] x ∂(P i) =
        ∫ x in T ⁻¹' A, c_B ∂(P i) :=
      setIntegral_congr_ae (hmT _ hTA_σ)
        (condExp_const_ae.mono fun x hx _ => hx)
    -- integral of constant
    have step_d : ∫ x in T ⁻¹' A, c_B ∂(P i) = c_B * ((P i) (T ⁻¹' A)).toReal := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
    -- chain: step_a.symm ▸ step_b ▸ step_c ▸ step_d ▸ mul_comm
    have h1 : ((P i) (T ⁻¹' A ∩ V ⁻¹' B)).toReal = c_B * ((P i) (T ⁻¹' A)).toReal := by
      linarith [step_a, step_b, step_c, step_d]
    rw [h1, hc_B_def, Measure.real]; ring
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
      ENNReal.toReal_mul]
  exact key

end Basu

end

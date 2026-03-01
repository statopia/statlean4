import Statlean.Statistic.Basic
import Statlean.Estimator.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Sufficiency/LehmannScheffe

Lehmann-Scheffé theorem: if T is a complete sufficient statistic and
δ is an unbiased estimator, then E[δ|T] is the unique UMVUE.
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Sufficiency.LehmannScheffe

variable {Θ Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-! ## Completeness uniqueness -/

/-- If T is complete, any two unbiased σ(T)-measurable estimators of g(θ) agree a.e. -/
theorem complete_unbiased_ae_unique
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (hT_comp : IsComplete' P T)
    (f₁ f₂ : α → ℝ) (g : Θ → ℝ)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h₁_unb : ∀ θ, ∫ ω, f₁ (T ω) ∂(P.measure θ) = g θ)
    (h₂_unb : ∀ θ, ∫ ω, f₂ (T ω) ∂(P.measure θ) = g θ)
    (h₁_int : ∀ θ, Integrable (f₁ ∘ T) (P.measure θ))
    (h₂_int : ∀ θ, Integrable (f₂ ∘ T) (P.measure θ)) :
    ∀ θ, f₁ ∘ T =ᵐ[P.measure θ] f₂ ∘ T := by
  have hd_meas : Measurable (f₁ - f₂) := hf₁.sub hf₂
  have hd_zero : ∀ θ, ∫ ω, (f₁ - f₂) (T ω) ∂(P.measure θ) = 0 := by
    intro θ; simp only [Pi.sub_apply]
    have : ∫ ω, (f₁ (T ω) - f₂ (T ω)) ∂(P.measure θ) =
        ∫ ω, f₁ (T ω) ∂(P.measure θ) - ∫ ω, f₂ (T ω) ∂(P.measure θ) :=
      integral_sub (h₁_int θ) (h₂_int θ)
    rw [this, h₁_unb θ, h₂_unb θ, sub_self]
  intro θ
  have h_ae := hT_comp (f₁ - f₂) hd_meas hd_zero θ
  filter_upwards [h_ae] with ω hω
  simp only [Pi.sub_apply, Function.comp_apply] at hω ⊢
  linarith

/-! ## Sufficiency → condExp invariance

The key technical lemma: if T is sufficient, then `E_θ[f|σ(T)]` does not
depend on θ (as an a.e. statement). This extends the indicator-based
definition of sufficiency to general integrable functions.

Proof sketch: IsSufficient' says `E_θ₁[1_s|σ(T)] =ᵃᵉ E_θ₂[1_s|σ(T)]` for
all measurable s. By linearity this extends to simple functions, and by
monotone class / dominated convergence to all integrable f.

This is a standard measure theory result but requires significant
formalization effort (simple function approximation + DCT in Lean). -/
theorem condExp_eq_of_sufficient
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (hT_suff : IsSufficient' P T)
    (f : Ω → ℝ) (θ₁ θ₂ : Θ)
    (hf₁ : Integrable f (P.measure θ₁))
    (hf₂ : Integrable f (P.measure θ₂)) :
    condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ₁) f
      =ᵐ[P.measure θ₁]
    condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ₂) f := by
  -- blocker: extending from indicators to general functions
  -- requires simple function approximation + DCT
  sorry

/-! ## Conditional expectation MSE reduction -/

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- **L² projection**: conditioning reduces MSE.

`∫(E[f|m] - c)² ≤ ∫(f - c)²` by the orthogonal decomposition
`f - c = (E[f|m] - c) + (f - E[f|m])` with vanishing cross term. -/
theorem condExp_reduces_mse
    {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure Ω}
    [SigmaFinite (μ.trim hm)] [IsFiniteMeasure μ]
    (f : Ω → ℝ) (c : ℝ)
    (hf : Integrable f μ)
    (hf_sq : Integrable (fun ω => (f ω - c) ^ 2) μ) :
    ∫ ω, ((μ[f|m]) ω - c) ^ 2 ∂μ ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := by
  -- Abbreviations: ψ = μ[f|m]
  set ψ := μ[f|m] with hψ_def
  -- Integrability
  have hfc_int : Integrable (fun ω => f ω - c) μ := hf.sub (integrable_const c)
  have hψ_int : Integrable ψ μ := integrable_condExp
  have hΔ_int : Integrable (fun ω => f ω - ψ ω) μ := hf.sub hψ_int
  -- f - c ∈ L²
  have hfc_memLp : MemLp (fun ω => f ω - c) 2 μ := by
    rwa [memLp_two_iff_integrable_sq hfc_int.aestronglyMeasurable]
  -- condExp of (f - c) equals ψ - c a.e.
  have h_condExp_fc : μ[fun ω => f ω - c|m] =ᵐ[μ] fun ω => ψ ω - c := by
    -- condExp_sub gives μ[f - (fun _ => c)|m] =ᵐ μ[f|m] - μ[(fun _ => c)|m]
    -- We need to bridge lambda vs Pi.sub
    have h1 := condExp_sub hf (integrable_const c) m
    have h2 : μ[(fun _ => c)|m] = fun _ => c := condExp_const hm c
    have h_eq : (fun ω => f ω - c) = f - (fun _ => c) := rfl
    rw [h_eq]
    filter_upwards [h1] with ω hω
    simp only [Pi.sub_apply] at hω
    rw [hω, h2]
  -- ψ - c ∈ L² (by L² contraction of condExp + a.e. equality)
  have hψc_memLp : MemLp (fun ω => ψ ω - c) 2 μ :=
    hfc_memLp.condExp.ae_eq h_condExp_fc
  -- f - ψ ∈ L²
  have hΔ_memLp : MemLp (fun ω => f ω - ψ ω) 2 μ := by
    have hae : (fun ω => f ω - ψ ω) =ᵐ[μ] (fun ω => (f ω - c) - (ψ ω - c)) :=
      ae_of_all _ (fun ω => by ring)
    exact (hfc_memLp.sub hψc_memLp).ae_eq hae.symm
  -- Integrability of squares
  have hψc_sq : Integrable (fun ω => (ψ ω - c) ^ 2) μ := hψc_memLp.integrable_sq
  have hΔ_sq : Integrable (fun ω => (f ω - ψ ω) ^ 2) μ := hΔ_memLp.integrable_sq
  -- Cross term integrable
  have hcross_int : Integrable (fun ω => (ψ ω - c) * (f ω - ψ ω)) μ :=
    hψc_memLp.integrable_mul hΔ_memLp
  -- Step 1: Algebraic decomposition of (f-c)²
  have h_expand : ∀ ω, (f ω - c) ^ 2 = (ψ ω - c) ^ 2 + 2 * ((ψ ω - c) * (f ω - ψ ω))
      + (f ω - ψ ω) ^ 2 := fun ω => by ring
  -- Step 2: Integrate both sides
  have h_int_eq : ∫ ω, (f ω - c) ^ 2 ∂μ =
      ∫ ω, (ψ ω - c) ^ 2 ∂μ + 2 * ∫ ω, (ψ ω - c) * (f ω - ψ ω) ∂μ
      + ∫ ω, (f ω - ψ ω) ^ 2 ∂μ := by
    have h1 : ∫ ω, (f ω - c) ^ 2 ∂μ = ∫ ω, ((ψ ω - c) ^ 2 + 2 * ((ψ ω - c) * (f ω - ψ ω))
        + (f ω - ψ ω) ^ 2) ∂μ := integral_congr_ae (ae_of_all _ h_expand)
    rw [h1]
    -- Use explicit have for each integral_add (computed with correct Pi form)
    have hi12 : Integrable (fun ω => (ψ ω - c) ^ 2 + 2 * ((ψ ω - c) * (f ω - ψ ω))) μ :=
      hψc_sq.add (hcross_int.const_mul 2)
    have h2 := integral_add hi12 hΔ_sq
    have h3 := integral_add hψc_sq (hcross_int.const_mul 2)
    -- h2 : ∫ (a+b) = ∫ a + ∫ b, but uses Pi.add form
    -- Convert: the integrand is (fun ω => ...) which is defeq to Pi.add applied
    calc ∫ ω, ((ψ ω - c) ^ 2 + 2 * ((ψ ω - c) * (f ω - ψ ω)) + (f ω - ψ ω) ^ 2) ∂μ
        = ∫ ω, ((ψ ω - c) ^ 2 + 2 * ((ψ ω - c) * (f ω - ψ ω))) ∂μ +
          ∫ ω, (f ω - ψ ω) ^ 2 ∂μ := integral_add hi12 hΔ_sq
      _ = (∫ ω, (ψ ω - c) ^ 2 ∂μ + ∫ ω, 2 * ((ψ ω - c) * (f ω - ψ ω)) ∂μ) +
          ∫ ω, (f ω - ψ ω) ^ 2 ∂μ := by
          have := integral_add hψc_sq (hcross_int.const_mul 2)
          linarith
      _ = ∫ ω, (ψ ω - c) ^ 2 ∂μ + 2 * ∫ ω, (ψ ω - c) * (f ω - ψ ω) ∂μ +
          ∫ ω, (f ω - ψ ω) ^ 2 ∂μ := by
          have : ∫ ω, 2 * ((ψ ω - c) * (f ω - ψ ω)) ∂μ =
              2 * ∫ ω, (ψ ω - c) * (f ω - ψ ω) ∂μ :=
            integral_const_mul 2 _
          linarith
  -- Step 3: Cross term vanishes
  have h_cross_zero : ∫ ω, (ψ ω - c) * (f ω - ψ ω) ∂μ = 0 := by
    -- E[f-ψ|m] =ᵃᵉ 0
    have hψ_ae_sm : AEStronglyMeasurable[m] ψ μ :=
      stronglyMeasurable_condExp.aestronglyMeasurable
    have h_Δ_condExp : μ[fun ω => f ω - ψ ω|m] =ᵐ[μ] 0 := by
      have h1 := condExp_sub hf hψ_int m
      have h2 := condExp_of_aestronglyMeasurable' hm hψ_ae_sm hψ_int
      filter_upwards [h1, h2] with ω hω1 hω2
      simp only [Pi.sub_apply, Pi.zero_apply] at hω1 ⊢
      -- hω1 : μ[f - ψ|m] ω = μ[f|m] ω - μ[ψ|m] ω
      -- hω2 : μ[ψ|m] ω = ψ ω
      -- Goal: μ[fun ω => f ω - ψ ω|m] ω = 0
      -- condExp doesn't distinguish lambda vs Pi.sub, so goal is same as hω1 context
      -- μ[f|m] = ψ by definition, μ[ψ|m] =ᵃᵉ ψ by hω2
      show μ[fun ω => f ω - ψ ω|m] ω = 0
      -- We need: μ[fun ω => f ω - ψ ω|m] = μ[f - ψ|m] (they should be defeq)
      -- Then use hω1 and hω2
      change μ[f - ψ|m] ω = 0
      rw [hω1, hψ_def, hω2, sub_self]
    -- ∫ (ψ-c)(f-ψ) dμ = ∫ E[(ψ-c)(f-ψ)|m] dμ  (tower)
    --                   = ∫ (ψ-c)·E[f-ψ|m] dμ    (pullout)
    --                   = ∫ (ψ-c)·0 dμ = 0
    have hψc_ae_sm : AEStronglyMeasurable[m] (fun ω => ψ ω - c) μ :=
      (stronglyMeasurable_condExp.sub stronglyMeasurable_const).aestronglyMeasurable
    -- Use tower + pullout in one step:
    -- ∫ g·h dμ = ∫ E[g·h|m] dμ = ∫ g·E[h|m] dμ  when g is m-sm
    -- Then E[h|m] =ᵃᵉ 0 gives ∫ g·0 = 0
    have : ∫ ω, (ψ ω - c) * (f ω - ψ ω) ∂μ =
        ∫ ω, (ψ ω - c) * (μ[fun ω => f ω - ψ ω|m]) ω ∂μ := by
      rw [← integral_condExp hm (f := fun ω => (ψ ω - c) * (f ω - ψ ω))]
      refine integral_congr_ae ?_
      exact condExp_mul_of_aestronglyMeasurable_left hψc_ae_sm hcross_int hΔ_int
    rw [this]
    have : (fun ω => (ψ ω - c) * (μ[fun ω => f ω - ψ ω|m]) ω) =ᵐ[μ]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_Δ_condExp] with ω hω
      simp only [Pi.zero_apply] at hω
      rw [hω, mul_zero]
    rw [integral_congr_ae this, integral_zero]
  -- Step 4: ∫(f-ψ)² ≥ 0
  have h_Δ_sq_nonneg : 0 ≤ ∫ ω, (f ω - ψ ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith [h_int_eq, h_cross_zero, h_Δ_sq_nonneg]

/-! ## Main theorem -/

variable [Nonempty α] [StandardBorelSpace α]

omit [Nonempty α] [StandardBorelSpace α] in
/-- **Lehmann-Scheffé theorem**: If T is complete sufficient for P and δ is
unbiased for g(θ), then there exists a measurable h such that h ∘ T is the
unique UMVUE for g(θ).

Proof:
1. Doob-Dynkin: `E_θ₀[δ|σ(T)]` is σ(T)-measurable, hence `= h ∘ T`.
2. Sufficiency: `E_θ[δ|σ(T)] =ᵃᵉ E_θ₀[δ|σ(T)] = h ∘ T` for all θ.
   Tower: `∫(h∘T)dP_θ = ∫E_θ[δ|σ(T)]dP_θ = ∫δdP_θ = g(θ)`.
3. For unbiased δ', MSE reduction + completeness uniqueness:
   `∫(δ'-gθ)² ≥ ∫(E_θ[δ'|σ(T)]-gθ)² = ∫((h∘T)-gθ)²`.
PIPELINE_ID: concept.lehmann_scheffe -/
theorem lehmann_scheffe [Nonempty Θ]
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (δ : Ω → ℝ) (g : Θ → ℝ)
    (hT_suff : IsSufficient' P T)
    (hT_comp : IsComplete' P T)
    (hδ_unb : IsUnbiased P δ g)
    (hδ_int : ∀ θ, Integrable δ (P.measure θ))
    (hδ'_int : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable δ' (P.measure θ))
    (hδ'_sq : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable (fun ω => (δ' ω - g θ) ^ 2) (P.measure θ)) :
    ∃ h : α → ℝ, Measurable h ∧
      IsUnbiased P (h ∘ T) g ∧
      ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
        ∀ θ, ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) ≤
             ∫ ω, (δ' ω - g θ) ^ 2 ∂(P.measure θ) := by
  have hT_meas := hT_suff.1
  have hm_le := hT_meas.comap_le
  -- Reference parameter θ₀
  obtain ⟨θ₀⟩ := ‹Nonempty Θ›
  haveI : IsProbabilityMeasure (P.measure θ₀) := P.isProbability θ₀
  haveI : IsFiniteMeasure (P.measure θ₀) := inferInstance
  haveI : SigmaFinite ((P.measure θ₀).trim hm_le) := inferInstance
  -- Step 1: E_θ₀[δ|σ(T)] factors through T (Doob-Dynkin)
  have hψ_sm : StronglyMeasurable[MeasurableSpace.comap T ‹MeasurableSpace α›]
      (condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ₀) δ) :=
    stronglyMeasurable_condExp
  obtain ⟨h, hh_meas, hψ_eq⟩ := hψ_sm.measurable.exists_eq_measurable_comp (f := T)
  -- hψ_eq : condExp σ(T) μ₀ δ = h ∘ T
  -- Step 2: h ∘ T is unbiased for g
  have h_unb : IsUnbiased P (h ∘ T) g := by
    intro θ
    haveI : IsProbabilityMeasure (P.measure θ) := P.isProbability θ
    haveI : SigmaFinite ((P.measure θ).trim hm_le) := inferInstance
    -- By sufficiency: E_θ[δ|σ(T)] =ᵃᵉ E_θ₀[δ|σ(T)] = h∘T
    have h_inv := condExp_eq_of_sufficient P T hT_suff δ θ θ₀ (hδ_int θ) (hδ_int θ₀)
    -- Tower property for θ: ∫ E_θ[δ|σ(T)] dP_θ = ∫ δ dP_θ = g(θ)
    have h_tower : ∫ ω, (condExp (MeasurableSpace.comap T ‹_›) (P.measure θ) δ) ω
        ∂(P.measure θ) = g θ := by
      rw [integral_condExp hm_le]
      exact hδ_unb θ
    -- h∘T =ᵃᵉ E_θ₀[δ|σ(T)] =ᵃᵉ E_θ[δ|σ(T)]
    rw [← h_tower]
    refine integral_congr_ae ?_
    filter_upwards [h_inv] with ω hω
    -- hω : E_θ[δ|σ(T)] ω = E_θ₀[δ|σ(T)] ω
    -- hψ_eq : E_θ₀[δ|σ(T)] = h ∘ T
    -- goal: (h ∘ T) ω = E_θ[δ|σ(T)] ω
    rw [hω, ← congr_fun hψ_eq ω]
  -- Step 3: MSE optimality
  have h_opt : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) ≤
           ∫ ω, (δ' ω - g θ) ^ 2 ∂(P.measure θ) := by
    intro δ' hδ'_unb θ
    haveI : IsProbabilityMeasure (P.measure θ) := P.isProbability θ
    haveI : IsFiniteMeasure (P.measure θ) := inferInstance
    haveI : SigmaFinite ((P.measure θ).trim hm_le) := inferInstance
    -- (a) MSE reduction: ∫(E_θ[δ'|σ(T)] - gθ)² ≤ ∫(δ' - gθ)²
    have h_mse : ∫ ω,
        (condExp (MeasurableSpace.comap T ‹_›) (P.measure θ) δ' ω - g θ) ^ 2 ∂(P.measure θ) ≤
        ∫ ω, (δ' ω - g θ) ^ 2 ∂(P.measure θ) :=
      condExp_reduces_mse hm_le δ' (g θ) (hδ'_int δ' hδ'_unb θ) (hδ'_sq δ' hδ'_unb θ)
    -- (b) E_θ[δ'|σ(T)] factors through T as h_θ'∘T (Doob-Dynkin)
    have hψ'_sm : StronglyMeasurable[MeasurableSpace.comap T ‹MeasurableSpace α›]
        (condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ) δ') :=
      stronglyMeasurable_condExp
    obtain ⟨h', hh'_meas, hψ'_eq⟩ := hψ'_sm.measurable.exists_eq_measurable_comp (f := T)
    -- (c) h'∘T is unbiased for all θ' (via sufficiency + tower)
    have h'_unb : ∀ θ', ∫ ω, h' (T ω) ∂(P.measure θ') = g θ' := by
      intro θ'
      haveI : IsProbabilityMeasure (P.measure θ') := P.isProbability θ'
      haveI : SigmaFinite ((P.measure θ').trim hm_le) := inferInstance
      -- Sufficiency: E_θ'[δ'|σ(T)] =ᵃᵉ E_θ[δ'|σ(T)] = h'∘T
      have h_inv := condExp_eq_of_sufficient P T hT_suff δ' θ' θ
        (hδ'_int δ' hδ'_unb θ') (hδ'_int δ' hδ'_unb θ)
      -- Tower: ∫ E_θ'[δ'|σ(T)] dP_θ' = ∫ δ' dP_θ' = g(θ')
      have h_tower : ∫ ω, (condExp (MeasurableSpace.comap T ‹_›) (P.measure θ') δ') ω
          ∂(P.measure θ') = g θ' := by
        rw [integral_condExp hm_le]; exact hδ'_unb θ'
      rw [← h_tower]
      refine integral_congr_ae ?_
      filter_upwards [h_inv] with ω hω
      -- hω : E_θ'[δ'|σ(T)] ω = E_θ[δ'|σ(T)] ω
      -- hψ'_eq : E_θ[δ'|σ(T)] = h' ∘ T
      -- goal : h' (T ω) = E_θ'[δ'|σ(T)] ω
      rw [hω]; exact (congr_fun hψ'_eq ω).symm
    -- (d) Completeness: h∘T =ᵃᵉ h'∘T (both unbiased, σ(T)-measurable)
    have h_eq_ae := complete_unbiased_ae_unique P T hT_comp h h' g
      hh_meas hh'_meas h_unb h'_unb
      (fun θ' => (hδ'_int (h ∘ T) h_unb θ'))
      (fun θ' => (hδ'_int (h' ∘ T) (fun θ'' => h'_unb θ'') θ'))
      θ
    -- (e) ∫(h∘T - gθ)² = ∫(h'∘T - gθ)² (by ae equality)
    have h_mse_eq : ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) =
        ∫ ω, ((h' ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) := by
      refine integral_congr_ae ?_
      filter_upwards [h_eq_ae] with ω hω
      rw [hω]
    -- (f) ∫(h'∘T - gθ)² = ∫(E_θ[δ'|σ(T)] - gθ)² (since h'∘T = E_θ[δ'|σ(T)])
    have h_mse_eq' : ∫ ω, ((h' ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) =
        ∫ ω, (condExp (MeasurableSpace.comap T ‹_›) (P.measure θ) δ' ω - g θ) ^ 2
          ∂(P.measure θ) := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      congr 1; congr 1; exact congr_fun hψ'_eq.symm ω
    -- Combine: ∫(h∘T-gθ)² = ∫(h'∘T-gθ)² = ∫(E_θ[δ'|σ(T)]-gθ)² ≤ ∫(δ'-gθ)²
    linarith [h_mse_eq, h_mse_eq', h_mse]
  exact ⟨h, hh_meas, h_unb, h_opt⟩

end Statlean.Sufficiency.LehmannScheffe

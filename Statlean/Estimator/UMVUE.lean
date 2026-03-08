import Statlean.Estimator.Basic
import Statlean.Information.CramerRao
import Statlean.Sufficiency.LehmannScheffe

/-! # Estimator/UMVUE

UMVUE theorems: uniqueness, efficient ⇒ UMVUE, Rao-Blackwell bridge,
exponential family construction, and unestimability.

## Main results

* `umvue_ae_unique` — UMVUE is a.e. unique
* `efficient_is_umvue` — efficient estimator is UMVUE
* `rao_blackwell_umvue` — Lehmann-Scheffé packaged as IsUMVUE
* `expfamily_umvue` — unbiased function of complete sufficient T is UMVUE
* `unestimable_of_complete_no_function` — completeness negative side

### sorry inventory (2 sorry)
- `umvue_ae_unique`: parallelogram identity for L² → ae equality (~30 lines)
- `unestimable_of_complete_no_function`: Doob-Dynkin + sufficiency (~40 lines)
-/

open MeasureTheory ProbabilityTheory Filter

namespace Statlean.Estimator

variable {Θ : Type*}
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## UMVUE uniqueness -/

/-- **UMVUE uniqueness**: if two estimators are both UMVUE for `g(θ)`,
they agree a.e. under every `P_θ`.

Proof sketch: both are unbiased, so `δ_avg = (δ₁+δ₂)/2` is also unbiased.
By the parallelogram identity, `MSE(δ_avg) = (MSE(δ₁)+MSE(δ₂))/2 - E[(δ₁-δ₂)²]/4`.
Since `MSE(δ₁) = MSE(δ₂) ≤ MSE(δ_avg)`, we get `E[(δ₁-δ₂)²] = 0`, hence `δ₁ =ᵃᵉ δ₂`.

-- blocker: integral_add integrability threading
-- estimated effort: ~30 lines -/
theorem umvue_ae_unique (P : ParametricFamily Θ Ω)
    (δ₁ δ₂ : Ω → ℝ) (g : Θ → ℝ)
    (h₁ : IsUMVUE P δ₁ g) (h₂ : IsUMVUE P δ₂ g)
    (h₁_int : ∀ θ, Integrable δ₁ (P.measure θ))
    (h₂_int : ∀ θ, Integrable δ₂ (P.measure θ))
    (h₁_sq : ∀ θ, Integrable (fun ω => (δ₁ ω - g θ) ^ 2) (P.measure θ))
    (h₂_sq : ∀ θ, Integrable (fun ω => (δ₂ ω - g θ) ^ 2) (P.measure θ))
    (hδ_sq : ∀ θ, Integrable (fun ω => (δ₁ ω - δ₂ ω) ^ 2) (P.measure θ)) :
    ∀ θ, δ₁ =ᵐ[P.measure θ] δ₂ := by
  intro θ
  set μ := P.measure θ
  set c := g θ
  -- Step 1: Both achieve the same MSE
  have h_mse_eq : MSE P δ₁ g θ = MSE P δ₂ g θ :=
    le_antisymm (h₁.2 δ₂ h₂.1 θ) (h₂.2 δ₁ h₁.1 θ)
  -- Step 2: δ_avg = (δ₁+δ₂)/2 is unbiased
  set δ_avg : Ω → ℝ := fun ω => (δ₁ ω + δ₂ ω) / 2
  have h_avg_unb : IsUnbiased P δ_avg g := by
    intro θ'
    change ∫ ω, (δ₁ ω + δ₂ ω) / 2 ∂(P.measure θ') = g θ'
    have : ∫ ω, (δ₁ ω + δ₂ ω) / 2 ∂(P.measure θ') =
        (1/2 : ℝ) * ∫ ω, (δ₁ ω + δ₂ ω) ∂(P.measure θ') := by
      rw [show (fun ω => (δ₁ ω + δ₂ ω) / 2) = fun ω => (1/2 : ℝ) * (δ₁ ω + δ₂ ω) from
        funext fun ω => by ring]
      exact integral_const_mul _ _
    rw [this, integral_add (h₁_int θ') (h₂_int θ'), h₁.1 θ', h₂.1 θ']
    ring
  -- Step 3: Parallelogram identity (pointwise)
  have h_para : ∀ ω, (δ_avg ω - c) ^ 2 =
      ((δ₁ ω - c) ^ 2 + (δ₂ ω - c) ^ 2) / 2 - (δ₁ ω - δ₂ ω) ^ 2 / 4 :=
    fun ω => by simp only [δ_avg]; ring
  -- Step 4: Integrate the parallelogram identity
  -- Rewrite as linear combination for integral_add / integral_const_mul
  have h_para' : ∀ ω, (δ_avg ω - c) ^ 2 =
      (1/2 : ℝ) * ((δ₁ ω - c) ^ 2 + (δ₂ ω - c) ^ 2) +
      (-1/4 : ℝ) * (δ₁ ω - δ₂ ω) ^ 2 :=
    fun ω => by simp only [δ_avg]; ring
  have hi12 : Integrable (fun ω => (δ₁ ω - c) ^ 2 + (δ₂ ω - c) ^ 2) μ :=
    (h₁_sq θ).add (h₂_sq θ)
  have h_avg_sq : Integrable (fun ω => (δ_avg ω - c) ^ 2) μ :=
    (hi12.const_mul _).add ((hδ_sq θ).const_mul _) |>.congr
      (ae_of_all _ (fun ω => by
        show 1 / 2 * ((δ₁ ω - c) ^ 2 + (δ₂ ω - c) ^ 2) +
          -1 / 4 * (δ₁ ω - δ₂ ω) ^ 2 = (δ_avg ω - c) ^ 2
        simp only [δ_avg]; ring))
  set I₁₂ := ∫ ω, (δ₁ ω - δ₂ ω) ^ 2 ∂μ
  have h_int_para : ∫ ω, (δ_avg ω - c) ^ 2 ∂μ =
      (∫ ω, (δ₁ ω - c) ^ 2 ∂μ + ∫ ω, (δ₂ ω - c) ^ 2 ∂μ) / 2 - I₁₂ / 4 := by
    rw [integral_congr_ae (ae_of_all _ h_para')]
    rw [integral_add (hi12.const_mul _) ((hδ_sq θ).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_add (h₁_sq θ) (h₂_sq θ)]
    ring
  -- Step 5: MSE(δ₁) ≤ MSE(δ_avg), combined with the identity
  have h_umvue_le : MSE P δ₁ g θ ≤ MSE P δ_avg g θ := h₁.2 δ_avg h_avg_unb θ
  -- MSE(δ_avg) = MSE(δ₁) - I₁₂/4  (since MSE₁ = MSE₂)
  -- Step 6: I₁₂ ≤ 0 (from UMVUE + parallelogram identity)
  -- h_int_para : ∫(δ_avg-c)² = (∫(δ₁-c)² + ∫(δ₂-c)²)/2 - I₁₂/4
  -- h_umvue_le : MSE₁ ≤ MSE(δ_avg)  i.e. ∫(δ₁-c)² ≤ ∫(δ_avg-c)²
  -- h_mse_eq : ∫(δ₁-c)² = ∫(δ₂-c)²
  -- So: ∫(δ₁-c)² ≤ (∫(δ₁-c)² + ∫(δ₁-c)²)/2 - I₁₂/4 = ∫(δ₁-c)² - I₁₂/4
  -- Hence I₁₂/4 ≤ 0, i.e. I₁₂ ≤ 0
  have h_le_zero : I₁₂ ≤ 0 := by
    -- h_int_para + h_mse_eq gives MSE(δ_avg) = MSE(δ₁) - I₁₂/4
    -- h_umvue_le gives MSE(δ₁) ≤ MSE(δ_avg), hence I₁₂ ≤ 0
    have hmse1 : MSE P δ₁ g θ = ∫ ω, (δ₁ ω - c) ^ 2 ∂μ := rfl
    have hmse2 : MSE P δ₂ g θ = ∫ ω, (δ₂ ω - c) ^ 2 ∂μ := rfl
    have hmse_avg : MSE P δ_avg g θ = ∫ ω, (δ_avg ω - c) ^ 2 ∂μ := rfl
    rw [hmse_avg] at h_umvue_le
    rw [hmse1, hmse2] at h_mse_eq
    linarith [h_int_para]
  -- Step 7: I₁₂ ≥ 0 (always)
  have h_ge_zero : 0 ≤ I₁₂ := integral_nonneg (fun ω => sq_nonneg _)
  -- Step 8: I₁₂ = 0
  have h_eq_zero : I₁₂ = 0 := le_antisymm h_le_zero h_ge_zero
  -- Step 9: (δ₁-δ₂)² =ᵃᵉ 0, hence δ₁ =ᵃᵉ δ₂
  have h_ae_sq := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun ω => sq_nonneg (δ₁ ω - δ₂ ω))) (hδ_sq θ)).mp h_eq_zero
  filter_upwards [h_ae_sq] with ω hω
  have : (δ₁ ω - δ₂ ω) ^ 2 = 0 := hω
  have := sq_eq_zero_iff.mp this
  linarith

/-! ## Efficient ⇒ UMVUE -/

/-- **Efficient implies UMVUE**: if an unbiased estimator attains the
Cramér–Rao lower bound, it is UMVUE.

For any competing unbiased `δ'`, the CR bound gives
`MSE(δ') ≥ g'(θ)²/I(θ) = MSE(δ)`. -/
theorem efficient_is_umvue (P : ParametricFamily ℝ Ω)
    (logDensity : ℝ → Ω → ℝ)
    (δ : Ω → ℝ) (g : ℝ → ℝ)
    (hδ : IsEfficient P logDensity δ g)
    (hI_pos : ∀ θ, fisherInformation P logDensity θ > 0)
    (h_reg : ∀ (δ' : Ω → ℝ) (θ : ℝ), IsUnbiased P δ' g →
      Integrable (fun ω => (δ' ω - g θ) ^ 2) (P.measure θ) →
      Integrable (fun ω => (scoreFunction logDensity θ ω) ^ 2) (P.measure θ) →
      Integrable (fun ω => (δ' ω - g θ) * scoreFunction logDensity θ ω) (P.measure θ) →
      deriv g θ = ∫ ω, (δ' ω - g θ) * scoreFunction logDensity θ ω ∂(P.measure θ))
    (h_sq : ∀ (δ' : Ω → ℝ) (θ : ℝ), IsUnbiased P δ' g →
      Integrable (fun ω => (δ' ω - g θ) ^ 2) (P.measure θ))
    (hS_sq : ∀ θ, Integrable (fun ω => (scoreFunction logDensity θ ω) ^ 2) (P.measure θ))
    (hTS : ∀ (δ' : Ω → ℝ) (θ : ℝ), IsUnbiased P δ' g →
      Integrable (fun ω => (δ' ω - g θ) * scoreFunction logDensity θ ω) (P.measure θ)) :
    IsUMVUE P δ g := by
  refine ⟨hδ.1, fun δ' hδ'_unb θ => ?_⟩
  rw [hδ.2 θ (hI_pos θ)]
  exact (cramer_rao P logDensity δ' g θ (hI_pos θ)
    (h_reg δ' θ hδ'_unb (h_sq δ' θ hδ'_unb) (hS_sq θ) (hTS δ' θ hδ'_unb))
    (h_sq δ' θ hδ'_unb) (hS_sq θ) (hTS δ' θ hδ'_unb)).le

/-! ## Rao-Blackwell / Lehmann-Scheffé bridge -/

/-- **Rao-Blackwell improvement is UMVUE** (bridge theorem):
conditioning an unbiased estimator on a complete sufficient statistic
yields a UMVUE. This packages `lehmann_scheffe` into the `IsUMVUE` predicate. -/
theorem rao_blackwell_umvue {α : Type*} [MeasurableSpace α]
    [Nonempty Θ]
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
    ∃ h : α → ℝ, Measurable h ∧ IsUMVUE P (h ∘ T) g := by
  obtain ⟨h, hh_meas, h_unb, h_opt⟩ :=
    Statlean.Sufficiency.LehmannScheffe.lehmann_scheffe P T δ g
      hT_suff hT_comp hδ_unb hδ_int hδ'_int hδ'_sq
  exact ⟨h, hh_meas, h_unb, fun δ' hδ'_unb θ => h_opt δ' hδ'_unb θ⟩

/-! ## Exponential family UMVUE -/

/-- **Exponential family UMVUE construction**: in a natural exponential family,
the sufficient statistic `T` is complete, so any unbiased function of `T`
is the unique UMVUE.

Given that `T` is both sufficient and complete (which holds for minimal NEFs),
any `h ∘ T` that is unbiased for `g(θ)` is automatically UMVUE. -/
theorem expfamily_umvue {α : Type*} [MeasurableSpace α]
    [Nonempty Θ]
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (h : α → ℝ) (g : Θ → ℝ)
    (hT_suff : IsSufficient' P T)
    (hT_comp : IsComplete' P T)
    (hh_meas : Measurable h)
    (h_unb : IsUnbiased P (h ∘ T) g)
    (hδ'_int : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable δ' (P.measure θ))
    (hδ'_sq : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable (fun ω => (δ' ω - g θ) ^ 2) (P.measure θ)) :
    IsUMVUE P (h ∘ T) g := by
  obtain ⟨h', hh'_meas, h'_umvue⟩ := rao_blackwell_umvue P T (h ∘ T) g
    hT_suff hT_comp h_unb (fun θ => hδ'_int _ h_unb θ) hδ'_int hδ'_sq
  -- By completeness, h ∘ T =ᵃᵉ h' ∘ T (both unbiased functions of T)
  have h_ae_eq := Statlean.Sufficiency.LehmannScheffe.complete_unbiased_ae_unique
    P T hT_comp h h' g hh_meas hh'_meas h_unb h'_umvue.1
    (fun θ => hδ'_int _ h_unb θ) (fun θ => hδ'_int _ h'_umvue.1 θ)
  refine ⟨h_unb, fun δ' hδ'_unb θ => ?_⟩
  -- MSE(h ∘ T) = MSE(h' ∘ T) ≤ MSE(δ')
  have hmse_eq : MSE P (h ∘ T) g θ = MSE P (h' ∘ T) g θ := by
    show ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) =
         ∫ ω, ((h' ∘ T) ω - g θ) ^ 2 ∂(P.measure θ)
    exact integral_congr_ae ((h_ae_eq θ).mono fun ω hω => by
      simp only [Function.comp_apply] at hω; simp only [Function.comp_apply, hω])
  rw [hmse_eq]
  exact h'_umvue.2 δ' hδ'_unb θ

/-! ## Unestimability -/

/-- A parametric function `g(θ)` is **unestimable** (has no unbiased estimator)
if no measurable function is unbiased for it. -/
def IsUnestimable (P : ParametricFamily Θ Ω) (g : Θ → ℝ) : Prop :=
  ¬∃ δ : Ω → ℝ, Measurable δ ∧ IsUnbiased P δ g

/-- If T is a complete sufficient statistic and `g(θ)` has no unbiased estimator
that is a function of T, then `g(θ)` has no unbiased estimator at all
(among integrable estimators).

This is the negative side of completeness: if `g(θ)` were unbiasedly estimable
by some δ, then `E[δ|σ(T)]` factors through T (Doob-Dynkin) and is unbiased
(tower + sufficiency), contradicting the hypothesis.

-- blocker: needs Doob-Dynkin + tower + sufficiency argument
-- estimated effort: ~40 lines -/
theorem unestimable_of_complete_no_function {α : Type*} [MeasurableSpace α]
    [Nonempty Θ]
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (g : Θ → ℝ)
    (hT_comp : IsComplete' P T)
    (hT_suff : IsSufficient' P T)
    (hno_func : ∀ h : α → ℝ, Measurable h →
      (∀ θ, Integrable (h ∘ T) (P.measure θ)) →
      ¬IsUnbiased P (h ∘ T) g) :
    ∀ δ : Ω → ℝ, (∀ θ, Integrable δ (P.measure θ)) →
      ¬IsUnbiased P δ g := by
  intro δ hδ_int hδ_unb
  obtain ⟨θ₀⟩ := ‹Nonempty Θ›
  haveI : IsProbabilityMeasure (P.measure θ₀) := P.isProbability θ₀
  haveI : IsFiniteMeasure (P.measure θ₀) := inferInstance
  have hT_meas := hT_suff.1
  have hm_le := hT_meas.comap_le
  haveI : SigmaFinite ((P.measure θ₀).trim hm_le) := inferInstance
  -- Doob-Dynkin: E_θ₀[δ|σ(T)] = h ∘ T for some measurable h
  have hψ_sm : StronglyMeasurable[MeasurableSpace.comap T ‹MeasurableSpace α›]
      (condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ₀) δ) :=
    stronglyMeasurable_condExp
  obtain ⟨h, hh_meas, hψ_eq⟩ := hψ_sm.measurable.exists_eq_measurable_comp (f := T)
  -- h ∘ T is integrable (condExp is in L¹, h∘T =ᵃᵉ condExp via sufficiency)
  have h_int : ∀ θ, Integrable (h ∘ T) (P.measure θ) := by
    intro θ
    haveI : IsProbabilityMeasure (P.measure θ) := P.isProbability θ
    haveI : SigmaFinite ((P.measure θ).trim hm_le) := inferInstance
    have h_inv := Statlean.Sufficiency.LehmannScheffe.condExp_eq_of_sufficient P T hT_suff δ θ θ₀ (hδ_int θ) (hδ_int θ₀)
    exact integrable_condExp.congr (h_inv.trans (ae_of_all _ (congr_fun hψ_eq)))
  -- h ∘ T is unbiased for g (tower + sufficiency)
  have h_unb : IsUnbiased P (h ∘ T) g := by
    intro θ
    haveI : IsProbabilityMeasure (P.measure θ) := P.isProbability θ
    haveI : SigmaFinite ((P.measure θ).trim hm_le) := inferInstance
    have h_inv := Statlean.Sufficiency.LehmannScheffe.condExp_eq_of_sufficient P T hT_suff δ θ θ₀ (hδ_int θ) (hδ_int θ₀)
    have h_tower : ∫ ω,
        (condExp (MeasurableSpace.comap T ‹MeasurableSpace α›) (P.measure θ) δ) ω
        ∂(P.measure θ) = g θ := by
      rw [integral_condExp hm_le]; exact hδ_unb θ
    rw [← h_tower]
    exact integral_congr_ae (h_inv.trans (ae_of_all _ (congr_fun hψ_eq))).symm
  exact hno_func h hh_meas h_int h_unb

end Statlean.Estimator

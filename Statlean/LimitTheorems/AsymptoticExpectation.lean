import Mathlib
import Statlean.LimitTheorems.Convergence
import Statlean.LimitTheorems.Slutsky

/-!
# Asymptotic Expectation (Shao, Mathematical Statistics, Def 2.11 & Prop 2.3)

This file formalizes the concept of *asymptotic expectation* of a sequence of random
variables (Shao §2.5.2, Definition 2.11(i), p.135) and proves that it is essentially
unique (Proposition 2.3, p.136):

given two sequences of positive normalizers `{aₙ}` and `{bₙ}` for the same
sequence `{ξₙ}`, with `aₙξₙ →d ξ` and `bₙξₙ →d η`
(both with finite absolute expectation), then a trichotomy holds on `(Eξ, Eη)`:

* `(a)` `Eξ = Eη = 0`; or
* `(b)` exactly one of `Eξ`, `Eη` is zero and the corresponding ratio of
  normalizers tends to zero; or
* `(c)` both are nonzero and `(Eξ/aₙ)/(Eη/bₙ) → 1`.

## Book proof sketch

The book proof splits into three cases based on whether the limits `ξ`, `η`
are (a.s.) constants or have non-degenerate c.d.f.s:

* Case (i): both non-degenerate ⇒ **Khinchin's convergence-of-types theorem**
  (`b_n/a_n → c > 0` with `η =d c·ξ`). *Not yet in Mathlib, see §R6 route below.*
* Case (ii): one non-degenerate, one constant ⇒ Slutsky + subsequence argument.
* Case (iii): both constants ⇒ Slutsky (division) on constant limits.

## R6 route for Khinchin's convergence-of-types theorem

Khinchin's theorem: if `Xₙ →d X` (non-degenerate) and `aₙXₙ + bₙ →d Y` (non-degenerate)
with `aₙ > 0` real, `bₙ` real, then `aₙ → a > 0` and `bₙ → b` and `Y =d aX + b`.

For our restricted form `aₙXₙ →d X` and `bₙXₙ →d Y` both non-degenerate, the
conclusion is `bₙ/aₙ → c > 0` and `Y =d cX`.

Engineering route (to unblock case (i), not attempted in this session):
1. Tightness of `{bₙ/aₙ}`: show the family of laws of `aₙXₙ` is tight, so `bₙXₙ`
   is too (by Helly extraction), and all sub-sequential limits are laws of `cX`
   for some `c`.
2. Non-degeneracy transfer: `X` non-degenerate ⟹ the `c` is unique (via cdf
   matching on continuity points).
3. Assemble using Prokhorov + sub-sequential limit uniqueness.

Estimated: ~200 lines, depending on Mathlib's Prokhorov coverage.

## References

* Shao, *Mathematical Statistics* (2nd ed., Springer 2003), §2.5.2, p.135–136.
* Billingsley, *Convergence of Probability Measures*, §14 (Khinchin).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Statlean.AsymptoticExpectation

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Definition 2.11(i): asymptotic expectation -/

section Definitions

/-- **Shao Definition 2.11(i)**.

A pair `(aₙ, ξ)` is a witness that `E[ξ]/aₙ` is an *asymptotic expectation* of the
sequence `ξₙ` if:

* `aₙ > 0` for each `n`;
* `aₙ → ∞` or `aₙ → a > 0` (the normalizers cannot collapse to `0`);
* `aₙ ξₙ →d ξ` (in distribution, under `μ`);
* `E|ξ| < ∞` (so that `E[ξ]` is well-defined). -/
structure IsAsymptoticExpectation (ξn : ℕ → Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (an : ℕ → ℝ) (ξ : Ω → ℝ) : Prop where
  pos : ∀ n, 0 < an n
  nondeg : Filter.Tendsto an Filter.atTop Filter.atTop
           ∨ ∃ a > 0, Filter.Tendsto an Filter.atTop (𝓝 a)
  convD : TendstoInDistribution (fun n ω => an n * ξn n ω) Filter.atTop ξ μ
  integrable : Integrable ξ μ

/-- A random variable is *almost surely constant* under `μ` if it agrees a.e. with
some constant (equivalently: has a degenerate c.d.f.). -/
def IsAlmostSurelyConstant (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  ∃ c : ℝ, f =ᵐ[μ] fun _ => c

end Definitions

/-! ## Proposition 2.3: uniqueness of asymptotic expectation -/

section Proposition23

variable [IsProbabilityMeasure μ]

/-- **Missing-in-Mathlib bridge**: convergence in distribution to a *constant* implies
convergence in probability.

Mathlib has `TendstoInMeasure.tendstoInDistribution` (the converse) but not this
direction. The general direction `→d` ⇒ `→ᵖ` is false (continuous mapping breaks),
but it is true when the limit is degenerate (a constant).

Proof sketch: For each `ε > 0`, apply `tendsto_iff_forall_lipschitz_integral_tendsto`
to the bounded 1-Lipschitz test function `F(x) = min(ε, |x - c|)`. Then
`ε · 𝟙{|X n - c| ≥ ε}(ω) ≤ F(X n ω)` pointwise, so
`μ {|X n - c| ≥ ε} ≤ (1/ε) · ∫ F ∘ X n dμ`. The right-hand side tends to
`(1/ε) · ∫ F(c) dμ = 0` since `F(c) = 0`. -/
lemma tendstoInDistribution_const_to_measure
    {ξn : ℕ → Ω → ℝ} {c : ℝ}
    (h : TendstoInDistribution ξn Filter.atTop (fun _ => c) μ) :
    TendstoInMeasure μ ξn Filter.atTop (fun _ => c) := by
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  -- Define the test function `F(x) = min ε |x - c|`. This function is `1`-Lipschitz,
  -- bounded by `ε`, nonnegative, and vanishes at `c`. The crucial property used below
  -- is the indicator-style bound `F(x) ≥ ε ↔ |x - c| ≥ ε`.
  set F : ℝ → ℝ := fun x => min ε |x - c| with hF_def
  have hF_nonneg : ∀ x, 0 ≤ F x := fun x => le_min hε.le (abs_nonneg _)
  have hF_le_eps : ∀ x, F x ≤ ε := fun x => min_le_left _ _
  have hF_continuous : Continuous F :=
    continuous_const.min (continuous_abs.comp (continuous_id.sub continuous_const))
  have hF_lipschitz : ∃ L, LipschitzWith L F := by
    refine ⟨1, ?_⟩
    have h0 : LipschitzWith 1 (fun x : ℝ => x - c) := by
      have := (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).sub (LipschitzWith.const c)
      simpa using this
    have h1 : LipschitzWith 1 (fun x : ℝ => |x|) := by
      intro x y
      simp only [edist_dist, Real.dist_eq, ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub x y)
    have h2 : LipschitzWith (1 * 1) (fun x : ℝ => |x - c|) := h1.comp h0
    simpa [hF_def] using h2.const_min ε
  have hF_bounded : ∃ C, ∀ x y : ℝ, dist (F x) (F y) ≤ C := by
    refine ⟨ε, ?_⟩
    intro x y
    have h1 : F x ≤ ε := hF_le_eps x
    have h2 : F y ≤ ε := hF_le_eps y
    have h3 : 0 ≤ F x := hF_nonneg x
    have h4 : 0 ≤ F y := hF_nonneg y
    rw [Real.dist_eq, abs_le]
    refine ⟨by linarith, by linarith⟩
  -- Apply the Lipschitz characterisation of weak convergence to obtain
  -- `∫ F d(μ.map (ξn n)) → ∫ F d(μ.map (fun _ => c))`.
  have hint_tendsto : Tendsto
      (fun n => ∫ x, F x ∂(Measure.map (ξn n) μ)) atTop
      (𝓝 (∫ x, F x ∂(Measure.map (fun _ : Ω => c) μ))) :=
    (MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mp h.tendsto)
              F hF_bounded hF_lipschitz
  -- The limit integral is `0`: `μ.map (fun _ => c) = δ_c` (Dirac), and `F(c) = 0`.
  have hlim_zero : ∫ x, F x ∂(Measure.map (fun _ : Ω => c) μ) = 0 := by
    rw [Measure.map_const]
    simp [hF_def, hε.le]
  rw [hlim_zero] at hint_tendsto
  -- Rewrite each `∫ F d(μ.map (ξn n))` as `∫ F ∘ ξn n dμ` via `integral_map`.
  have hF_aem : ∀ n, AEMeasurable (ξn n) μ := h.forall_aemeasurable
  have hint_eq : ∀ n, ∫ x, F x ∂(Measure.map (ξn n) μ) = ∫ ω, F (ξn n ω) ∂μ := fun n =>
    integral_map (hF_aem n) hF_continuous.aestronglyMeasurable
  have hint_tendsto' : Tendsto (fun n => ∫ ω, F (ξn n ω) ∂μ) atTop (𝓝 0) := by
    have := hint_tendsto
    simp_rw [hint_eq] at this
    exact this
  -- Each `F ∘ ξn n` is integrable since it is bounded by `ε` on a probability space.
  have hF_integrable : ∀ n, Integrable (fun ω => F (ξn n ω)) μ := by
    intro n
    have h_aem : AEMeasurable (fun ω => F (ξn n ω)) μ :=
      hF_continuous.aemeasurable.comp_aemeasurable (hF_aem n)
    refine Integrable.mono' (integrable_const ε) h_aem.aestronglyMeasurable ?_
    refine ae_of_all _ (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg _)]
    exact hF_le_eps _
  have hF_nn_ae : ∀ n, 0 ≤ᶠ[ae μ] (fun ω => F (ξn n ω)) :=
    fun n => ae_of_all _ (fun ω => hF_nonneg _)
  -- Markov: `ε · μ.real {F ∘ ξn n ≥ ε} ≤ ∫ F ∘ ξn n dμ`.
  have hMarkov : ∀ n, ε * μ.real {ω | ε ≤ F (ξn n ω)} ≤ ∫ ω, F (ξn n ω) ∂μ :=
    fun n => mul_meas_ge_le_integral_of_nonneg (hF_nn_ae n) (hF_integrable n) ε
  -- The level set of `F ≥ ε` coincides with `|· - c| ≥ ε`.
  have hset_eq : ∀ n, {ω | ε ≤ F (ξn n ω)} = {ω | ε ≤ |ξn n ω - c|} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, hF_def]
    refine ⟨fun hle => le_trans hle (min_le_right _ _), fun hle => le_min le_rfl hle⟩
  -- Hence `μ.real {|· - c| ≥ ε} ≤ ε⁻¹ · ∫ F ∘ ξn n dμ → 0`.
  have hmreal_bound : ∀ n, μ.real {ω | ε ≤ |ξn n ω - c|} ≤ ε⁻¹ * ∫ ω, F (ξn n ω) ∂μ := by
    intro n
    have hM := hMarkov n
    rw [hset_eq] at hM
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hε).mpr (by linarith [hM])
  have hRHS_to_zero : Tendsto (fun n => ε⁻¹ * ∫ ω, F (ξn n ω) ∂μ) atTop (𝓝 0) := by
    have := hint_tendsto'.const_mul (ε⁻¹)
    simpa using this
  have hmreal_to_zero : Tendsto (fun n => μ.real {ω | ε ≤ |ξn n ω - c|}) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n; exact measureReal_nonneg
    · intro n; exact hmreal_bound n
    · exact hRHS_to_zero
  -- Convert the convergence in `μ.real` (i.e. `μ.toReal`) to convergence in `μ` itself,
  -- using `ENNReal.tendsto_toReal_iff` (the measures are bounded by `μ Set.univ < ∞`).
  have h_ne_top : ∀ n, μ {ω | ε ≤ |ξn n ω - c|} ≠ ⊤ := fun n => measure_ne_top μ _
  have hiff := @ENNReal.tendsto_toReal_iff ℕ atTop
                  (fun n => μ {ω | ε ≤ |ξn n ω - c|}) h_ne_top 0 ENNReal.zero_ne_top
  simp only [ENNReal.toReal_zero] at hiff
  have h_target : Tendsto (fun n => μ {ω | ε ≤ |ξn n ω - c|}) atTop (𝓝 0) :=
    hiff.mp hmreal_to_zero
  -- Finally, identify `‖ξn n ω - c‖` with `|ξn n ω - c|` (norm = abs in ℝ).
  have hsets : ∀ n, {x | ε ≤ ‖ξn n x - (fun _ : Ω => c) x‖} = {ω | ε ≤ |ξn n ω - c|} := by
    intro n
    ext ω
    simp [Real.norm_eq_abs]
  simp_rw [hsets]
  exact h_target

/-- Trichotomy conclusion of Shao Proposition 2.3, abstracted to a predicate on
the pair `(p, q)` of means and the normalizer sequences. Factored out so the
three sub-cases below can share the target. -/
def Prop23Conclusion (an bn : ℕ → ℝ) (p q : ℝ) : Prop :=
  (p = 0 ∧ q = 0)
  ∨ (p ≠ 0 ∧ q = 0 ∧ Filter.Tendsto (fun n => bn n / an n) Filter.atTop (𝓝 0))
  ∨ (p = 0 ∧ q ≠ 0 ∧ Filter.Tendsto (fun n => an n / bn n) Filter.atTop (𝓝 0))
  ∨ (p ≠ 0 ∧ q ≠ 0 ∧
      Filter.Tendsto (fun n => (p / an n) / (q / bn n)) Filter.atTop (𝓝 1))

/-- The trichotomy conclusion is symmetric in `(aₙ, p) ↔ (bₙ, q)`. -/
lemma Prop23Conclusion.swap {an bn : ℕ → ℝ} {p q : ℝ}
    (h : Prop23Conclusion bn an q p) : Prop23Conclusion an bn p q := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq, hlim⟩ | ⟨hp, hq, hlim⟩ | ⟨hp, hq, hlim⟩
  · exact Or.inl ⟨hq, hp⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hq, hp, hlim⟩))
  · exact Or.inr (Or.inl ⟨hq, hp, hlim⟩)
  · refine Or.inr (Or.inr (Or.inr ⟨hq, hp, ?_⟩))
    -- hlim : (q/bn n) / (p/an n) → 1, want (p/an n)/(q/bn n) → 1
    have hinv : Filter.Tendsto
        (fun n => ((q / bn n) / (p / an n))⁻¹) Filter.atTop (𝓝 (1 : ℝ)⁻¹) :=
      Filter.Tendsto.inv₀ hlim (by norm_num : (1 : ℝ) ≠ 0)
    have heq : (fun n => ((q / bn n) / (p / an n))⁻¹)
                = (fun n => (p / an n) / (q / bn n)) := by
      funext n; rw [inv_div]
    simpa [heq] using hinv

/-- **Case (i) — both limits non-degenerate.**

Given two asymptotic-expectation witnesses for the same sequence, if both
limits `ξ, η` have non-degenerate c.d.f.s, then the Prop 2.3 trichotomy holds.

**Blocker**: reduces to Khinchin's convergence-of-types theorem
(Exercise 1.129 in Shao), which is not yet in Mathlib — see file docstring for
the engineering route. -/
theorem shao_prop_2_3_case_both_nondeg
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_nondeg : ¬ IsAlmostSurelyConstant μ ξ)
    (hη_nondeg : ¬ IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  -- Depends on Khinchin's convergence-of-types theorem (Exercise 1.129 Shao).
  -- See R6 route in file docstring.
  sorry

/-- **Case (ii) — one non-degenerate, one constant.**

If `ξ` has a non-degenerate c.d.f. and `η` is a.s. constant `= q`, then:

* `q ≠ 0` is impossible (forces `aₙ/bₙ → ξ/q`, contradicting non-degeneracy of `ξ`);
* hence `q = 0` and `bₙ/aₙ → 0` (via a sub-sequential Slutsky argument).

**Blocker (partial)**: requires a sub-sequential limit extraction on `bₙ/aₙ`.
Not attempted in this session. -/
theorem shao_prop_2_3_case_ii
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_nondeg : ¬ IsAlmostSurelyConstant μ ξ)
    (hη_const : IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  sorry

/-- **Case (iii) — both limits a.s. constant.**

If both `ξ = p` a.s. and `η = q` a.s., then the trichotomy follows from Slutsky
division applied to the constant limits (no Khinchin needed).

**Blocker (partial)**: still requires a sub-sequential argument to show
`bₙ/aₙ → q/p` when `p ≠ 0`. Not attempted in this session. -/
theorem shao_prop_2_3_case_both_const
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_const : IsAlmostSurelyConstant μ ξ)
    (hη_const : IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  sorry

/-- **Proposition 2.3 (Shao, p.136) — uniqueness of asymptotic expectation.**

Given two asymptotic-expectation witnesses `(aₙ, ξ)` and `(bₙ, η)` for the same
sequence `{ξₙ}`, one of the following three disjuncts must hold on the means
`p = E[ξ]`, `q = E[η]`:

* `p = q = 0`;
* exactly one of `p`, `q` is zero, with `bₙ/aₙ → 0` (if `q = 0`) or
  `aₙ/bₙ → 0` (if `p = 0`);
* both nonzero, with `(p/aₙ)/(q/bₙ) → 1`.

The proof reduces to three sub-cases according to whether `ξ` and `η` are a.s.
constants; these are isolated as
`shao_prop_2_3_case_both_nondeg`, `shao_prop_2_3_case_ii`, and
`shao_prop_2_3_case_both_const` and currently all contain `sorry`
(see their individual docstrings for the blockers). -/
theorem shao_prop_2_3
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  by_cases hξ : IsAlmostSurelyConstant μ ξ
  · by_cases hη : IsAlmostSurelyConstant μ η
    · exact shao_prop_2_3_case_both_const hA hB hξ hη
    · -- ξ constant, η non-degenerate: apply case (ii) with roles swapped then flip.
      exact Prop23Conclusion.swap (shao_prop_2_3_case_ii hB hA hη hξ)
  · by_cases hη : IsAlmostSurelyConstant μ η
    · exact shao_prop_2_3_case_ii hA hB hξ hη
    · exact shao_prop_2_3_case_both_nondeg hA hB hξ hη

end Proposition23

end Statlean.AsymptoticExpectation

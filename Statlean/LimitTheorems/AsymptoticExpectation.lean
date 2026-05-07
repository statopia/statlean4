import Mathlib
import Statlean.LimitTheorems.Convergence
import Statlean.LimitTheorems.Slutsky
import Statlean.LimitTheorems.DeltaMethod

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

omit [IsProbabilityMeasure μ] in
/-- **Helper**: a deterministic sequence `a : ℕ → ℝ` converging to `c` lifts to
convergence in measure of the constant random variables `(fun n _ => a n)` to
`fun _ => c`. Used by `shao_prop_2_3_case_ii` sub-cases (A) and (C). -/
private lemma tendstoInMeasure_const_of_tendsto
    (a : ℕ → ℝ) (c : ℝ) (h : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure μ (fun n (_ : Ω) => a n) atTop (fun _ => c) := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hε_top
  obtain ⟨ε_r, hε_r_pos, hε_r_lt⟩ : ∃ r : ℝ, 0 < r ∧ (ENNReal.ofReal r) ≤ ε := by
    refine ⟨ε.toReal / 2, ?_, ?_⟩
    · have : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      linarith
    · rw [ENNReal.ofReal_le_iff_le_toReal hε_top]
      have : 0 ≤ ε.toReal := ENNReal.toReal_nonneg
      linarith
  rw [Metric.tendsto_atTop] at h
  rcases h ε_r hε_r_pos with ⟨N, hN⟩
  refine tendsto_atTop_of_eventually_const (i₀ := N) ?_
  intro n hn
  have hempty : {ω : Ω | ε ≤ edist (a n) c} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro habs
    have hdist : dist (a n) c < ε_r := hN n hn
    have h1 : edist (a n) c < ε := by
      rw [edist_dist]
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hdist).trans_le hε_r_lt
    exact absurd habs (not_le.mpr h1)
  rw [hempty]; simp

omit [IsProbabilityMeasure μ] in
/-- **Helper**: if `μ.map ξ = δ_c` (with `ξ` a.e.-measurable), then `ξ` is
a.s. equal to the constant `c`. Used by `shao_prop_2_3_case_ii` sub-cases (A)
and (C) to extract the contradiction with `hξ_nondeg`. -/
private lemma ae_eq_const_of_map_eq_dirac
    {ξ : Ω → ℝ} (hf : AEMeasurable ξ μ) (c : ℝ)
    (hmap : μ.map ξ = Measure.dirac c) : ξ =ᵐ[μ] (fun _ => c) := by
  rw [Filter.EventuallyEq, ae_iff]
  have hpre : {ω | ¬ ξ ω = (fun _ => c) ω} = ξ ⁻¹' ({c}ᶜ) := by
    ext ω; simp
  rw [hpre]
  rw [← Measure.map_apply_of_aemeasurable hf
      (MeasurableSet.compl (measurableSet_singleton c))]
  rw [hmap]
  rw [Measure.dirac_apply' _ (MeasurableSet.compl (measurableSet_singleton c))]
  simp

/-- **Case (i) — both limits non-degenerate.**

Given two asymptotic-expectation witnesses for the same sequence, if both
limits `ξ, η` have non-degenerate c.d.f.s, then the Prop 2.3 trichotomy holds.

**R6 Axiom Discharge**: This statement reduces to **Khinchin's convergence-of-types
theorem** (Exercise 1.129 in Shao), which is a classical result not yet available
in Mathlib. The full mathematical content is:

> If `Xₙ →d X` and `aₙXₙ + bₙ →d Y` with `X, Y` non-degenerate, then there exist
> `a > 0, b ∈ ℝ` such that `aₙ → a`, `bₙ → b`, and `Y = aX + b` in distribution.

**References**:
* J. Shao, *Mathematical Statistics* (2nd ed.), Springer 2003, Exercise 1.129
* Khinchin, A. Y. (1937). *Limit Distributions for Sums of Independent Random Variables*.
* Gnedenko-Kolmogorov, *Limit Distributions for Sums of Independent Random Variables*,
  Addison-Wesley 1954, §10.

**Engineering route to remove this axiom** (≈300-500 lines, blocked on Mathlib):
1. Tightness of `{aₙ}, {bₙ}` from non-degeneracy + Prokhorov-style argument
2. Helly extraction along subsequences in `[0,∞]` (we have a partial version
   in `case_ii` sub-case D)
3. Sub-sequence uniqueness via characteristic functions + Lévy's continuity theorem
   (which IS in Mathlib as `levy_continuity`)
4. Pass-to-limit using `tendstoInDistribution` Slutsky stability

Once Khinchin is in Mathlib (or built locally), replace `axiom` with `theorem`
and the proof body. All downstream code (`shao_prop_2_3`) consumes only the
statement, so no client changes are needed. -/
axiom shao_prop_2_3_case_both_nondeg
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_nondeg : ¬ IsAlmostSurelyConstant μ ξ)
    (hη_nondeg : ¬ IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ)

/-- **Case (ii) — one non-degenerate, one constant.**

If `ξ` has a non-degenerate c.d.f. and `η` is a.s. constant `= q`, then:

* `q ≠ 0` is impossible (forces `aₙ/bₙ → ξ/q`, contradicting non-degeneracy of `ξ`);
* hence `q = 0` and `bₙ/aₙ → 0` (via a sub-sequential Slutsky argument).

**Status**: structural skeleton in place. The setup steps (extract `q`, identify
`∫ η dμ = q`, lift `bₙξₙ →d η` to `bₙξₙ →ᵖ q`) are proved in full. The case-split
on `p = 0?` is also resolved, depending only on the conjunction
`q = 0 ∧ bₙ/aₙ → 0`. The conjunction is left as a single `sorry` (see comments
in the proof body for the Slutsky + Helly + distribution-uniqueness route). -/
theorem shao_prop_2_3_case_ii
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_nondeg : ¬ IsAlmostSurelyConstant μ ξ)
    (hη_const : IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  -- Step 1: Extract q = (a.s.) value of η, identify ∫ η dμ with q.
  obtain ⟨q, hη_eq⟩ := hη_const
  have hq_eq : ∫ ω, η ω ∂μ = q := by rw [integral_congr_ae hη_eq]; simp
  rw [hq_eq]
  set p := ∫ ω, ξ ω ∂μ with hp_def
  -- Step 2: Lift `bn ξn →d η` to `bn ξn →d (const q)` then to `bn ξn →ᵖ q`.
  -- (Inlined version of `td_to_const_of_ae_eq`, defined later in this file.)
  have hB_const : TendstoInDistribution (fun n ω => bn n * ξn n ω) atTop
      (fun _ : Ω => q) μ := by
    refine ⟨hB.convD.forall_aemeasurable, aemeasurable_const, ?_⟩
    have hmap : μ.map η = μ.map (fun _ : Ω => q) :=
      MeasureTheory.Measure.map_congr hη_eq
    have h1 := hB.convD.tendsto
    convert h1 using 2
    exact Subtype.ext hmap.symm
  have hB_meas : TendstoInMeasure μ (fun n ω => bn n * ξn n ω) atTop (fun _ => q) :=
    tendstoInDistribution_const_to_measure hB_const
  -- Step 3: The structural conclusion: `q = 0 ∧ bn/an → 0`.
  --
  -- **Phase 1 decomposition (4-way rcases on `hA.nondeg` × `hB.nondeg`)**:
  -- The monolithic sorry is split into 4 named sub-stubs.  Sub-case (B)'s
  -- deterministic part `bₙ/aₙ → 0` is closed directly via `Tendsto.div_atTop`.
  -- The remaining analytical content (q = 0 in B; vacuity of A, C; Helly in D)
  -- lives in 4 small sorries below, ready for individual attack.
  have h_main : q = 0 ∧ Tendsto (fun n => bn n / an n) atTop (𝓝 0) := by
    rcases hA.nondeg with hA_inf | ⟨a, ha_pos, ha_lim⟩
    · -- aₙ → ∞.  Split on bₙ behavior.
      rcases hB.nondeg with hB_inf | ⟨b, hb_pos, hb_lim⟩
      · -- **Sub-case (D)** : aₙ → ∞ AND bₙ → ∞.
        -- Strategy:
        -- 1. Prove `bn/an → 0` by contradiction.  Suppose not: `∃ε > 0, ∃ᶠ n, ε ≤ bn/an`.
        --    Extract subseq φ with `bn(φk)/an(φk) ≥ ε`, so `an(φk)/bn(φk) ≤ ε⁻¹`.
        --    The seq `r := an/bn` lives in `[0, ε⁻¹]` along φ, compact.
        --    Sub-sub ψ gives `r ∘ (φ ∘ ψ) → σ ∈ [0, ε⁻¹]`.
        --    * Case σ = 0: `(an/bn)·(bn ξn) = an ξn →d 0·q = 0` along subseq.
        --                  Also `an ξn →d ξ` along subseq (subseq stability).
        --                  Uniqueness ⟹ ξ =ᵐ 0, contradicting hξ_nondeg.
        --    * Case σ > 0: `bn(φ(ψk))/an(φ(ψk)) → σ⁻¹ > 0`.  Slutsky-mul:
        --                  `(bn/an)·(an ξn) = bn ξn →d σ⁻¹ · ξ` along subseq.
        --                  Also `bn ξn →d const q` along subseq.
        --                  Uniqueness ⟹ σ⁻¹ · ξ =ᵐ q ⟹ ξ =ᵐ σq, contradicting hξ_nondeg.
        -- 2. Derive `q = 0` from `bn/an → 0` via slutsky_mul on `(bn/an)(an ξn) = bn ξn`.
        have hξ_aemeas : AEMeasurable ξ μ := hA.convD.aemeasurable_limit
        have h_ratio_zero : Tendsto (fun n => bn n / an n) atTop (𝓝 (0 : ℝ)) := by
          by_contra h_not
          rw [Metric.tendsto_atTop] at h_not
          push_neg at h_not
          obtain ⟨ε, hε_pos, h_freq_in⟩ := h_not
          -- Extract a strictly monotone subseq with `bn(φk)/an(φk) ≥ ε`.
          have h_freq : ∃ᶠ n in atTop, ε ≤ bn n / an n := by
            rw [Filter.frequently_atTop]
            intro N
            obtain ⟨n, hN, hd⟩ := h_freq_in N
            refine ⟨n, hN, ?_⟩
            rw [Real.dist_eq, sub_zero] at hd
            have h_an_pos := hA.pos n
            have h_bn_pos := hB.pos n
            have h_ratio_pos : 0 < bn n / an n := div_pos h_bn_pos h_an_pos
            rw [abs_of_pos h_ratio_pos] at hd
            exact hd
          obtain ⟨φ, hφ_mono, hφ_ε⟩ := Filter.extraction_of_frequently_atTop h_freq
          -- Along φ, `an/bn ≤ ε⁻¹`, so `an/bn ∈ [0, ε⁻¹]`.
          have hε_inv_pos : 0 < ε⁻¹ := inv_pos.mpr hε_pos
          have h_r_in_Icc : ∀ k, an (φ k) / bn (φ k) ∈ Set.Icc (0 : ℝ) ε⁻¹ := by
            intro k
            have h_an_pos := hA.pos (φ k)
            have h_bn_pos := hB.pos (φ k)
            have h_r_pos : 0 ≤ an (φ k) / bn (φ k) := le_of_lt (div_pos h_an_pos h_bn_pos)
            have h_r_le : an (φ k) / bn (φ k) ≤ ε⁻¹ := by
              have h_ε_le := hφ_ε k
              rw [le_div_iff₀ h_an_pos] at h_ε_le
              rw [div_le_iff₀ h_bn_pos, le_inv_mul_iff₀ hε_pos]
              linarith
            exact ⟨h_r_pos, h_r_le⟩
          -- Compact extraction: `an(φ(ψk))/bn(φ(ψk)) → σ ∈ [0, ε⁻¹]`.
          have h_compact : IsCompact (Set.Icc (0 : ℝ) ε⁻¹) := isCompact_Icc
          obtain ⟨σ, hσ_mem, ψ, hψ_mono, hψ_lim⟩ :=
            h_compact.tendsto_subseq h_r_in_Icc
          -- Define χ := φ ∘ ψ
          set χ := φ ∘ ψ with hχ_def
          have hχ_mono : StrictMono χ := hφ_mono.comp hψ_mono
          have hχ_top : Tendsto χ atTop atTop := StrictMono.tendsto_atTop hχ_mono
          -- hψ_lim : Tendsto ((fun k => an (φ k) / bn (φ k)) ∘ ψ) atTop (𝓝 σ)
          have hr_lim : Tendsto (fun k => an (χ k) / bn (χ k)) atTop (𝓝 σ) := by
            simpa [hχ_def, Function.comp] using hψ_lim
          have hσ_nn : 0 ≤ σ := hσ_mem.1
          -- Case split on σ
          by_cases hσ : σ = 0
          · -- σ = 0: `an/bn` along χ → 0.  Then `(an/bn)·(bn ξn) = an ξn →d 0`.
            have hr_meas : TendstoInMeasure μ
                (fun k (_ : Ω) => an (χ k) / bn (χ k)) atTop (fun _ => (0 : ℝ)) := by
              rw [hσ] at hr_lim
              exact tendstoInMeasure_const_of_tendsto _ 0 hr_lim
            have hr_aemeas : ∀ i, AEMeasurable
                (fun (_ : Ω) => an (χ i) / bn (χ i)) μ := fun _ => aemeasurable_const
            -- Subseq of hB_const: `bn(χk) ξn(χk) →d const q`
            have hB_const_sub : TendstoInDistribution
                (fun k ω => bn (χ k) * ξn (χ k) ω) atTop (fun _ : Ω => q) μ :=
              ⟨fun i => hB_const.forall_aemeasurable _, hB_const.aemeasurable_limit,
                hB_const.tendsto.comp hχ_top⟩
            -- Slutsky-mul: `(an/bn)·(bn ξn) →d 0·q = 0` along χ.
            have hkey : TendstoInDistribution
                (fun k ω => (an (χ k) / bn (χ k)) * (bn (χ k) * ξn (χ k) ω)) atTop
                (fun _ : Ω => (0 : ℝ) * q) μ :=
              Statlean.LimitTheorems.slutsky_mul hB_const_sub hr_meas hr_aemeas
            -- Rewrite: `(an/bn)·(bn ξn) = an ξn` (since bn ≠ 0).
            have hbn_ne : ∀ k, bn (χ k) ≠ 0 := fun k => ne_of_gt (hB.pos (χ k))
            have hkey' : TendstoInDistribution
                (fun k ω => an (χ k) * ξn (χ k) ω) atTop
                (fun _ : Ω => (0 : ℝ) * q) μ := by
              refine ⟨fun i => hA.convD.forall_aemeasurable _, aemeasurable_const, ?_⟩
              have ht := hkey.tendsto
              have hmap_eq : ∀ k,
                  μ.map (fun ω => (an (χ k) / bn (χ k)) * (bn (χ k) * ξn (χ k) ω)) =
                  μ.map (fun ω => an (χ k) * ξn (χ k) ω) := by
                intro k
                apply Measure.map_congr
                apply ae_of_all
                intro ω
                have hbk : bn (χ k) ≠ 0 := hbn_ne k
                field_simp
              apply ht.congr'
              apply Filter.Eventually.of_forall
              intro k
              apply Subtype.ext
              simp [hmap_eq]
            -- `an ξn` along χ also tends to ξ (subseq).
            have hA_sub : TendstoInDistribution
                (fun k ω => an (χ k) * ξn (χ k) ω) atTop ξ μ :=
              ⟨fun i => hA.convD.forall_aemeasurable _, hA.convD.aemeasurable_limit,
                hA.convD.tendsto.comp hχ_top⟩
            -- Uniqueness ⟹ μ.map ξ = δ_(0·q) = δ_0
            have hunique := tendstoInDistribution_unique
              (fun k ω => an (χ k) * ξn (χ k) ω) hA_sub hkey'
            rw [Measure.map_const] at hunique
            have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
            rw [h_univ, one_smul] at hunique
            have hξ_const : ξ =ᵐ[μ] (fun _ => (0 : ℝ) * q) :=
              ae_eq_const_of_map_eq_dirac hξ_aemeas ((0 : ℝ) * q) hunique
            exact hξ_nondeg ⟨(0 : ℝ) * q, hξ_const⟩
          · -- σ > 0: `bn(χk)/an(χk) → σ⁻¹`.
            have hσ_pos : 0 < σ := lt_of_le_of_ne hσ_nn (Ne.symm hσ)
            have hσ_ne : σ ≠ 0 := hσ
            -- `bn(χk)/an(χk) = (an(χk)/bn(χk))⁻¹ → σ⁻¹`
            have hbn_an_lim : Tendsto (fun k => bn (χ k) / an (χ k)) atTop (𝓝 σ⁻¹) := by
              have h_eq : ∀ k, bn (χ k) / an (χ k) = (an (χ k) / bn (χ k))⁻¹ := by
                intro k
                rw [inv_div]
              simp_rw [h_eq]
              exact hr_lim.inv₀ hσ_ne
            have hbn_an_meas : TendstoInMeasure μ
                (fun k (_ : Ω) => bn (χ k) / an (χ k)) atTop (fun _ => σ⁻¹) :=
              tendstoInMeasure_const_of_tendsto _ σ⁻¹ hbn_an_lim
            have hbn_an_aemeas : ∀ i, AEMeasurable
                (fun (_ : Ω) => bn (χ i) / an (χ i)) μ := fun _ => aemeasurable_const
            -- Subseq of hA.convD
            have hA_sub : TendstoInDistribution
                (fun k ω => an (χ k) * ξn (χ k) ω) atTop ξ μ :=
              ⟨fun i => hA.convD.forall_aemeasurable _, hA.convD.aemeasurable_limit,
                hA.convD.tendsto.comp hχ_top⟩
            -- Slutsky-mul: `(bn/an)·(an ξn) →d σ⁻¹ · ξ` along χ.
            have hkey : TendstoInDistribution
                (fun k ω => (bn (χ k) / an (χ k)) * (an (χ k) * ξn (χ k) ω)) atTop
                (fun ω => σ⁻¹ * ξ ω) μ :=
              Statlean.LimitTheorems.slutsky_mul hA_sub hbn_an_meas hbn_an_aemeas
            -- Rewrite: `(bn/an)·(an ξn) = bn ξn` (since an ≠ 0).
            have han_ne : ∀ k, an (χ k) ≠ 0 := fun k => ne_of_gt (hA.pos (χ k))
            have hkey' : TendstoInDistribution
                (fun k ω => bn (χ k) * ξn (χ k) ω) atTop
                (fun ω => σ⁻¹ * ξ ω) μ := by
              refine ⟨fun i => hB.convD.forall_aemeasurable _, hkey.aemeasurable_limit, ?_⟩
              have ht := hkey.tendsto
              have hmap_eq : ∀ k,
                  μ.map (fun ω => (bn (χ k) / an (χ k)) * (an (χ k) * ξn (χ k) ω)) =
                  μ.map (fun ω => bn (χ k) * ξn (χ k) ω) := by
                intro k
                apply Measure.map_congr
                apply ae_of_all
                intro ω
                have hak : an (χ k) ≠ 0 := han_ne k
                field_simp
              apply ht.congr'
              apply Filter.Eventually.of_forall
              intro k
              apply Subtype.ext
              simp [hmap_eq]
            -- Subseq of hB_const: `bn(χk) ξn(χk) →d const q`
            have hB_const_sub : TendstoInDistribution
                (fun k ω => bn (χ k) * ξn (χ k) ω) atTop (fun _ : Ω => q) μ :=
              ⟨fun i => hB_const.forall_aemeasurable _, hB_const.aemeasurable_limit,
                hB_const.tendsto.comp hχ_top⟩
            -- Uniqueness ⟹ `μ.map (σ⁻¹ · ξ) = δ_q`, hence ξ =ᵐ σ·q.
            have hunique := tendstoInDistribution_unique
              (fun k ω => bn (χ k) * ξn (χ k) ω) hkey' hB_const_sub
            rw [Measure.map_const] at hunique
            have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
            rw [h_univ, one_smul] at hunique
            -- hunique : μ.map (fun ω => σ⁻¹ * ξ ω) = Measure.dirac q
            -- We want ξ =ᵐ σ * q
            have hξ_aemeas_scaled : AEMeasurable (fun ω => σ⁻¹ * ξ ω) μ :=
              hξ_aemeas.const_mul σ⁻¹
            have h_scaled_const : (fun ω => σ⁻¹ * ξ ω) =ᵐ[μ] (fun _ => q) :=
              ae_eq_const_of_map_eq_dirac hξ_aemeas_scaled q hunique
            -- From σ⁻¹ * ξ =ᵐ q, multiply by σ: ξ =ᵐ σ * q.
            have hξ_const : ξ =ᵐ[μ] (fun _ => σ * q) := by
              filter_upwards [h_scaled_const] with ω hω
              have : σ * (σ⁻¹ * ξ ω) = σ * q := by rw [hω]
              rw [← this]
              field_simp
            exact hξ_nondeg ⟨σ * q, hξ_const⟩
        -- Step 2: Derive q = 0 from h_ratio_zero.
        have h_ratio_meas : TendstoInMeasure μ
            (fun n (_ : Ω) => bn n / an n) atTop (fun _ => (0 : ℝ)) :=
          tendstoInMeasure_const_of_tendsto _ 0 h_ratio_zero
        have h_ratio_aemeas : ∀ i, AEMeasurable
            (fun (_ : Ω) => bn i / an i) μ := fun _ => aemeasurable_const
        -- Slutsky-mul: `(bn/an)·(an ξn) →d 0·ξ`.
        have hslut : TendstoInDistribution
            (fun n ω => (bn n / an n) * (an n * ξn n ω)) atTop
            (fun ω => (0 : ℝ) * ξ ω) μ :=
          Statlean.LimitTheorems.slutsky_mul hA.convD h_ratio_meas h_ratio_aemeas
        have han_ne_all : ∀ n, an n ≠ 0 := fun n => ne_of_gt (hA.pos n)
        -- Rewrite to `bn ξn →d 0·ξ`
        have hbnξn_to_zero_fun : TendstoInDistribution
            (fun n ω => bn n * ξn n ω) atTop (fun ω => (0 : ℝ) * ξ ω) μ := by
          refine ⟨fun i => hB.convD.forall_aemeasurable _, hslut.aemeasurable_limit, ?_⟩
          have ht := hslut.tendsto
          have hmap_eq : ∀ n,
              μ.map (fun ω => (bn n / an n) * (an n * ξn n ω)) =
              μ.map (fun ω => bn n * ξn n ω) := by
            intro n
            apply Measure.map_congr
            apply ae_of_all
            intro ω
            have han_n : an n ≠ 0 := han_ne_all n
            field_simp
          apply ht.congr'
          apply Filter.Eventually.of_forall
          intro n
          apply Subtype.ext
          simp [hmap_eq]
        -- Lift `0·ξ =ᵐ 0` to const 0 limit.
        have h_zero_eq : (fun ω => (0 : ℝ) * ξ ω) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
          apply ae_of_all; intro ω; ring
        have hbnξn_to_const_zero : TendstoInDistribution
            (fun n ω => bn n * ξn n ω) atTop (fun _ : Ω => (0 : ℝ)) μ := by
          refine ⟨fun i => hB.convD.forall_aemeasurable _, aemeasurable_const, ?_⟩
          have ht := hbnξn_to_zero_fun.tendsto
          convert ht using 2
          apply Subtype.ext
          exact (Measure.map_congr h_zero_eq).symm
        -- Uniqueness with hB_const: const 0 = const q.
        have hunique := tendstoInDistribution_unique
          (fun n ω => bn n * ξn n ω) hbnξn_to_const_zero hB_const
        rw [Measure.map_const, Measure.map_const] at hunique
        have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
        rw [h_univ, one_smul, one_smul] at hunique
        -- hunique : Measure.dirac 0 = Measure.dirac q ⟹ q = 0
        have h_q_zero : q = 0 := by
          by_contra hq_ne
          have h_dirac : (Measure.dirac (0 : ℝ)) {(0 : ℝ)} =
              (Measure.dirac q) {(0 : ℝ)} := by rw [hunique]
          rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)] at h_dirac
          rw [Measure.dirac_apply' _ (measurableSet_singleton _)] at h_dirac
          rw [Set.indicator_of_notMem
              (by simp [Set.mem_singleton_iff]; exact hq_ne) _] at h_dirac
          exact one_ne_zero h_dirac
        exact ⟨h_q_zero, h_ratio_zero⟩
      · -- **Sub-case (B)** : aₙ → ∞ AND bₙ → b > 0.
        -- `bₙ/aₙ → 0` directly (deterministic; `b/∞ = 0`).
        -- For `q = 0`: from `bₙξₙ →ᵖ q` and `bₙ → b > 0`, slutsky-div gives
        -- `ξₙ →ᵖ q/b`.  If `q/b ≠ 0`, then `aₙξₙ` is non-tight (its values
        -- diverge to ±∞ on a fixed-positive-probability set), contradicting
        -- `aₙξₙ →d ξ` (which forces tightness).  Tightness-from-→d is the
        -- genuine analytical step (~50 lines).
        refine ⟨?_, ?_⟩
        · -- (b2) q = 0
          -- Path 1: from `aₙ ξₙ →d ξ` and `aₙ → ∞`, deduce `ξₙ →ᵖ 0`.
          have hξn_aemeas : ∀ i, AEMeasurable (ξn i) μ := by
            intro i
            have h_ai_pos : an i ≠ 0 := ne_of_gt (hA.pos i)
            have h_prod_aemeas : AEMeasurable (fun ω => an i * ξn i ω) μ :=
              hA.convD.forall_aemeasurable i
            have hξni : ξn i = fun ω => (an i)⁻¹ * (an i * ξn i ω) := by
              funext ω; field_simp
            rw [hξni]
            exact h_prod_aemeas.const_mul ((an i)⁻¹)
          have hA_conv_sub :
              TendstoInDistribution (fun n ω => an n * (ξn n ω - 0)) atTop ξ μ := by
            refine ⟨?_, hA.convD.aemeasurable_limit, ?_⟩
            · intro i
              have : (fun ω => an i * (ξn i ω - 0)) = (fun ω => an i * ξn i ω) := by
                funext ω; ring
              rw [this]; exact hA.convD.forall_aemeasurable i
            · have htendsto := hA.convD.tendsto
              convert htendsto using 2
              apply Subtype.ext
              apply Measure.map_congr
              apply ae_of_all
              intro ω; ring_nf
          have hξn_to_zero_meas : TendstoInMeasure μ ξn atTop (fun _ : Ω => (0 : ℝ)) :=
            Statlean.LimitTheorems.tendstoInMeasure_const_of_rescaled_tendstoInDistribution
              (Filter.Eventually.of_forall (fun n => hA.pos n)) hA_inf hA_conv_sub hξn_aemeas
          have hξn_to_zero_dist :
              TendstoInDistribution ξn atTop (fun _ : Ω => (0 : ℝ)) μ :=
            hξn_to_zero_meas.tendstoInDistribution hξn_aemeas
          -- Path 2: from `bₙ ξₙ →d q` and `bₙ → b ≠ 0`, slutsky-div gives `ξₙ →d q/b`.
          have hbn_meas :
              TendstoInMeasure μ (fun n (_ : Ω) => bn n) atTop (fun _ => b) :=
            tendstoInMeasure_const_of_tendsto bn b hb_lim
          have hbn_const_aemeas : ∀ i, AEMeasurable (fun (_ : Ω) => bn i) μ :=
            fun _ => aemeasurable_const
          have hb_ne : b ≠ 0 := ne_of_gt hb_pos
          have hdiv : TendstoInDistribution
              (fun n ω => (bn n * ξn n ω) / bn n) atTop
              (fun _ : Ω => q / b) μ :=
            Statlean.LimitTheorems.slutsky_div hb_ne hB_const hbn_meas hbn_const_aemeas
          have hbn_ne_eventually : ∀ᶠ n in atTop, bn n ≠ 0 := by
            have hb_half_pos : 0 < b / 2 := by linarith
            have h := (Metric.tendsto_atTop.mp hb_lim) (b / 2) hb_half_pos
            rcases h with ⟨N, hN⟩
            refine eventually_atTop.mpr ⟨N, fun n hn h0 => ?_⟩
            have h1 := hN n hn
            rw [h0, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hb_pos] at h1
            linarith
          have hξn_to_qb : TendstoInDistribution ξn atTop (fun _ : Ω => q / b) μ := by
            refine ⟨hξn_aemeas, aemeasurable_const, ?_⟩
            have htendsto := hdiv.tendsto
            have hmap_eq : ∀ᶠ n in atTop,
                μ.map (fun ω => (bn n * ξn n ω) / bn n) = μ.map (ξn n) := by
              filter_upwards [hbn_ne_eventually] with n hn
              apply Measure.map_congr
              apply ae_of_all
              intro ω
              field_simp
            apply htendsto.congr'
            filter_upwards [hmap_eq] with n hn
            apply Subtype.ext
            simp [hn]
          -- Combine via uniqueness of distribution limit.
          have hunique := tendstoInDistribution_unique
            ξn hξn_to_zero_dist hξn_to_qb
          rw [Measure.map_const, Measure.map_const] at hunique
          have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
          rw [h_univ, one_smul, one_smul] at hunique
          -- `Measure.dirac 0 = Measure.dirac (q/b)` ⟹ `q/b = 0`.
          have h_qb_zero : q / b = 0 := by
            by_contra hne
            -- Evaluate both sides on the singleton {q/b}.
            have h_dirac : (Measure.dirac (0 : ℝ)) {q / b} =
                (Measure.dirac (q / b)) {q / b} := by rw [hunique]
            rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)] at h_dirac
            rw [Measure.dirac_apply' _ (measurableSet_singleton _)] at h_dirac
            -- h_dirac : ({q/b}.indicator 1) 0 = 1
            rw [Set.indicator_of_notMem
                (by simp [Set.mem_singleton_iff]; exact fun h => hne h.symm) _] at h_dirac
            exact zero_ne_one h_dirac
          rcases (div_eq_zero_iff.mp h_qb_zero) with hq | hb0
          · exact hq
          · exact absurd hb0 hb_ne
        · -- (b1) bn/an → 0: deterministic, since aₙ → ∞ and bₙ → b finite.
          exact hb_lim.div_atTop hA_inf
    · -- aₙ → a > 0.  Both remaining sub-cases are vacuous via `hξ_nondeg`.
      rcases hB.nondeg with hB_inf | ⟨b, hb_pos, hb_lim⟩
      · -- **Sub-case (C)** : aₙ → a > 0 AND bₙ → ∞.  VACUOUS via `hξ_nondeg`.
        -- `1/bₙ → 0` deterministic, so `(1/bₙ) · (bnξn) →d 0 · q = 0` by slutsky_mul.
        -- Eventually `bn ≠ 0`, so this rewrites to `ξn →d 0`.
        -- Then `aₙ · ξn →d a · 0 = 0`, and uniqueness with `aₙ ξₙ →d ξ` forces
        -- `μ.map ξ = δ_0`, hence `ξ =ᵐ 0`, contradicting `hξ_nondeg`.
        exfalso
        have h_inv_bn : Tendsto (fun n => (bn n)⁻¹) atTop (𝓝 0) :=
          Filter.Tendsto.inv_tendsto_atTop hB_inf
        have h_inv_meas :
            TendstoInMeasure μ (fun n (_ : Ω) => (bn n)⁻¹) atTop (fun _ => (0 : ℝ)) :=
          tendstoInMeasure_const_of_tendsto (fun n => (bn n)⁻¹) 0 h_inv_bn
        have h_inv_aemeas : ∀ i, AEMeasurable (fun (_ : Ω) => (bn i)⁻¹) μ :=
          fun _ => aemeasurable_const
        have hkey : TendstoInDistribution
            (fun n ω => (bn n)⁻¹ * (bn n * ξn n ω)) atTop
            (fun _ : Ω => (0 : ℝ) * q) μ :=
          Statlean.LimitTheorems.slutsky_mul hB_const h_inv_meas h_inv_aemeas
        have hbn_ne_eventually : ∀ᶠ n in atTop, bn n ≠ 0 := by
          have := tendsto_atTop.mp hB_inf 1
          filter_upwards [this] with n hn h0
          rw [h0] at hn; linarith
        have han_meas :
            TendstoInMeasure μ (fun n (_ : Ω) => an n) atTop (fun _ => a) :=
          tendstoInMeasure_const_of_tendsto an a ha_lim
        have han_const_aemeas : ∀ i, AEMeasurable (fun (_ : Ω) => an i) μ :=
          fun _ => aemeasurable_const
        have hmul : TendstoInDistribution
            (fun n ω => an n * ((bn n)⁻¹ * (bn n * ξn n ω))) atTop
            (fun _ : Ω => a * ((0 : ℝ) * q)) μ :=
          Statlean.LimitTheorems.slutsky_mul hkey han_meas han_const_aemeas
        have hmul' : TendstoInDistribution (fun n ω => an n * ξn n ω) atTop
            (fun _ : Ω => a * ((0 : ℝ) * q)) μ := by
          refine ⟨hA.convD.forall_aemeasurable, aemeasurable_const, ?_⟩
          have htendsto := hmul.tendsto
          have hmap_eq : ∀ᶠ n in atTop,
              μ.map (fun ω => an n * ((bn n)⁻¹ * (bn n * ξn n ω))) =
              μ.map (fun ω => an n * ξn n ω) := by
            filter_upwards [hbn_ne_eventually] with n hn
            apply Measure.map_congr
            apply ae_of_all
            intro ω
            field_simp
          apply htendsto.congr'
          filter_upwards [hmap_eq] with n hn
          apply Subtype.ext
          simp [hn]
        have hunique := tendstoInDistribution_unique
          (fun n ω => an n * ξn n ω) hA.convD hmul'
        rw [Measure.map_const] at hunique
        have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
        rw [h_univ, one_smul] at hunique
        have hξ_aemeas : AEMeasurable ξ μ := hA.convD.aemeasurable_limit
        have hξ_const : ξ =ᵐ[μ] (fun _ => a * ((0 : ℝ) * q)) :=
          ae_eq_const_of_map_eq_dirac hξ_aemeas (a * ((0 : ℝ) * q)) hunique
        exact hξ_nondeg ⟨a * ((0 : ℝ) * q), hξ_const⟩
      · -- **Sub-case (A)** : aₙ → a > 0 AND bₙ → b > 0.  VACUOUS via `hξ_nondeg`.
        -- Slutsky-div on `bₙξₙ →d const q` and `bn → b ≠ 0` gives
        -- `(bnξn)/bn →d const (q/b)`.  Then slutsky-mul with `aₙ → a` gives
        -- `aₙ · ((bnξn)/bn) →d const (a·q/b)`.  Eventually `bn ≠ 0`, so the
        -- LHS rewrites to `aₙ ξn`, and uniqueness with `aₙ ξₙ →d ξ` forces
        -- `μ.map ξ = δ_(a·q/b)`, hence `ξ =ᵐ a·q/b`, contradicting `hξ_nondeg`.
        exfalso
        have hbn_meas :
            TendstoInMeasure μ (fun n (_ : Ω) => bn n) atTop (fun _ => b) :=
          tendstoInMeasure_const_of_tendsto bn b hb_lim
        have hbn_const_aemeas : ∀ i, AEMeasurable (fun (_ : Ω) => bn i) μ :=
          fun _ => aemeasurable_const
        have hb_ne : b ≠ 0 := ne_of_gt hb_pos
        have hdiv : TendstoInDistribution
            (fun n ω => (bn n * ξn n ω) / bn n) atTop
            (fun _ : Ω => q / b) μ :=
          Statlean.LimitTheorems.slutsky_div hb_ne hB_const hbn_meas hbn_const_aemeas
        have han_meas :
            TendstoInMeasure μ (fun n (_ : Ω) => an n) atTop (fun _ => a) :=
          tendstoInMeasure_const_of_tendsto an a ha_lim
        have han_const_aemeas : ∀ i, AEMeasurable (fun (_ : Ω) => an i) μ :=
          fun _ => aemeasurable_const
        have hmul : TendstoInDistribution
            (fun n ω => an n * ((bn n * ξn n ω) / bn n)) atTop
            (fun _ : Ω => a * (q / b)) μ :=
          Statlean.LimitTheorems.slutsky_mul hdiv han_meas han_const_aemeas
        have hbn_ne_eventually : ∀ᶠ n in atTop, bn n ≠ 0 := by
          have hb_half_pos : 0 < b / 2 := by linarith
          have h := (Metric.tendsto_atTop.mp hb_lim) (b / 2) hb_half_pos
          rcases h with ⟨N, hN⟩
          refine eventually_atTop.mpr ⟨N, fun n hn h0 => ?_⟩
          have h1 := hN n hn
          rw [h0, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hb_pos] at h1
          linarith
        have hmul' : TendstoInDistribution (fun n ω => an n * ξn n ω) atTop
            (fun _ : Ω => a * (q / b)) μ := by
          refine ⟨hA.convD.forall_aemeasurable, aemeasurable_const, ?_⟩
          have htendsto := hmul.tendsto
          have hmap_eq : ∀ᶠ n in atTop,
              μ.map (fun ω => an n * ((bn n * ξn n ω) / bn n)) =
              μ.map (fun ω => an n * ξn n ω) := by
            filter_upwards [hbn_ne_eventually] with n hn
            apply Measure.map_congr
            apply ae_of_all
            intro ω
            field_simp
          apply htendsto.congr'
          filter_upwards [hmap_eq] with n hn
          apply Subtype.ext
          simp [hn]
        have hunique := tendstoInDistribution_unique
          (fun n ω => an n * ξn n ω) hA.convD hmul'
        rw [Measure.map_const] at hunique
        have h_univ : (μ Set.univ : ENNReal) = 1 := measure_univ
        rw [h_univ, one_smul] at hunique
        have hξ_aemeas : AEMeasurable ξ μ := hA.convD.aemeasurable_limit
        have hξ_const : ξ =ᵐ[μ] (fun _ => a * (q / b)) :=
          ae_eq_const_of_map_eq_dirac hξ_aemeas (a * (q / b)) hunique
        exact hξ_nondeg ⟨a * (q / b), hξ_const⟩
  obtain ⟨h_q_zero, h_ratio⟩ := h_main
  subst h_q_zero
  -- Step 4: Case-split on `p = 0?`.
  by_cases hp : p = 0
  · -- (a): p = 0 and q = 0 → first disjunct.
    exact Or.inl ⟨hp, rfl⟩
  · -- (b): p ≠ 0 and q = 0 → second disjunct, using `h_ratio`.
    exact Or.inr (Or.inl ⟨hp, rfl, h_ratio⟩)

/-- Lift `TendstoInDistribution` from `→d ξ` to `→d (const c)` when `ξ =ᵐ const c`.

Used in the `case_both_const` proof: a.s. constant limits agree with their constant
in distribution because `μ.map ξ = μ.map (fun _ => c)` by `Measure.map_congr`. -/
private lemma td_to_const_of_ae_eq
    {ξn : ℕ → Ω → ℝ} {ξ : Ω → ℝ} {c : ℝ}
    (hcv : TendstoInDistribution ξn atTop ξ μ)
    (hξ_eq : ξ =ᵐ[μ] (fun _ => c)) :
    TendstoInDistribution ξn atTop (fun _ : Ω => c) μ := by
  refine ⟨hcv.forall_aemeasurable, aemeasurable_const, ?_⟩
  have hmap : μ.map ξ = μ.map (fun _ : Ω => c) :=
    MeasureTheory.Measure.map_congr hξ_eq
  have h1 := hcv.tendsto
  convert h1 using 2
  exact Subtype.ext hmap.symm

/-- **Deterministic ratio limit lemma**: if `aₙ ξₙ →ᵖ p ≠ 0` and `bₙ ξₙ →ᵖ q`, then
`bₙ / aₙ → q / p`.

This is the technical core of Case (iii) of Shao Proposition 2.3. The proof uses a
two-set indicator argument: pick thresholds `δ_A`, `δ_B` and `n` large enough that
both `μ{|aₙξₙ - p| ≥ δ_A}` and `μ{|bₙξₙ - q| ≥ δ_B}` are `≤ 1/3`. The complement of
the union has measure `> 1 - 2/3 = 1/3 > 0`, hence is non-empty. Pick a witness
`ω₀` and use the deterministic estimates `|aₙξₙω₀| > |p|/2` and the algebraic
decomposition `(bnξnω₀)/(anξnω₀) - q/p = (bnξnω₀ - q)/anξnω₀ - q(anξnω₀ - p)/(p·anξnω₀)`
to bound `|bₙ/aₙ - q/p|` by `ε`. -/
private lemma aux_ratio_limit
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {p q : ℝ} (hp : p ≠ 0)
    (hA : TendstoInMeasure μ (fun n ω => an n * ξn n ω) atTop (fun _ => p))
    (hB : TendstoInMeasure μ (fun n ω => bn n * ξn n ω) atTop (fun _ => q)) :
    Tendsto (fun n => bn n / an n) atTop (𝓝 (q / p)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [MeasureTheory.tendstoInMeasure_iff_norm] at hA hB
  have hp_pos : 0 < |p| := abs_pos.mpr hp
  have hp_half_pos : 0 < |p| / 2 := by linarith
  have hq_one_pos : 0 < |q| + 1 := by positivity
  -- Threshold radii: δA controls `aₙξₙ → p`; δB controls `bₙξₙ → q`.
  -- Tight enough that the algebraic decomposition gives `< ε/2 + ε/2`.
  set δA : ℝ := min (|p|/2) (ε * |p|^2 / (4 * (|q|+1))) with hδA_def
  set δB : ℝ := ε * |p| / 4 with hδB_def
  have hδA_pos : 0 < δA := by
    refine lt_min hp_half_pos ?_
    have hp_sq_pos : 0 < |p|^2 := by positivity
    positivity
  have hδB_pos : 0 < δB := by positivity
  have hAtmp : Tendsto (fun n => μ {x | δA ≤ ‖an n * ξn n x - p‖}) atTop (𝓝 0) :=
    hA δA hδA_pos
  have hBtmp : Tendsto (fun n => μ {x | δB ≤ ‖bn n * ξn n x - q‖}) atTop (𝓝 0) :=
    hB δB hδB_pos
  -- Both bad sets eventually have measure `≤ 1/3`, so the union is `< 1`.
  have h13_pos : (0 : ENNReal) < 1 / 3 := by
    rw [ENNReal.div_pos_iff]
    exact ⟨one_ne_zero, ENNReal.natCast_ne_top 3⟩
  obtain ⟨N₁, hN₁⟩ := (ENNReal.tendsto_atTop_zero.mp hAtmp) (1/3) h13_pos
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp hBtmp) (1/3) h13_pos
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hnA : N₁ ≤ n := le_of_max_le_left hn
  have hnB : N₂ ≤ n := le_of_max_le_right hn
  have hbA := hN₁ n hnA
  have hbB := hN₂ n hnB
  set badA : Set Ω := {x | δA ≤ ‖an n * ξn n x - p‖} with hbadA_def
  set badB : Set Ω := {x | δB ≤ ‖bn n * ξn n x - q‖} with hbadB_def
  have hunion_lt : μ (badA ∪ badB) < 1 := by
    have h1 : μ (badA ∪ badB) ≤ μ badA + μ badB := measure_union_le _ _
    have h2 : μ badA + μ badB ≤ 1/3 + 1/3 := add_le_add hbA hbB
    have h3 : (1 : ENNReal)/3 + 1/3 < 1 := by
      have h1' : (2 : ENNReal)/3 < 1 := by
        rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (3 : ENNReal) ≠ 0))
            (Or.inl (by norm_num : (3 : ENNReal) ≠ ⊤))]
        rw [one_mul]; norm_num
      have h2' : (1 : ENNReal)/3 + 1/3 = 2/3 := by
        rw [ENNReal.div_add_div_same]; norm_num
      rw [h2']; exact h1'
    exact lt_of_le_of_lt (le_trans h1 h2) h3
  -- Hence the complement has positive measure, in particular is non-empty.
  have hgood_pos : 0 < μ (badA ∪ badB)ᶜ := by
    have h_compl_ne_zero : μ (badA ∪ badB)ᶜ ≠ 0 := by
      intro h
      have h_total : μ (badA ∪ badB) + μ (badA ∪ badB)ᶜ ≥ μ Set.univ := by
        rw [← Set.union_compl_self (badA ∪ badB)]
        exact measure_union_le _ _
      rw [measure_univ, h, add_zero] at h_total
      exact absurd hunion_lt (not_lt.mpr h_total)
    exact pos_iff_ne_zero.mpr h_compl_ne_zero
  have hgood_nonempty : (badA ∪ badB)ᶜ.Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty] at h'
    rw [h'] at hgood_pos
    simp at hgood_pos
  obtain ⟨ω₀, hω₀⟩ := hgood_nonempty
  rw [Set.mem_compl_iff, Set.mem_union] at hω₀
  push_neg at hω₀
  obtain ⟨hω₀A, hω₀B⟩ := hω₀
  rw [hbadA_def, Set.mem_setOf_eq, not_le] at hω₀A
  rw [hbadB_def, Set.mem_setOf_eq, not_le] at hω₀B
  rw [Real.norm_eq_abs] at hω₀A hω₀B
  -- Derive `|aₙ ξₙ ω₀| > |p|/2` from the triangle inequality.
  have hδA_le_half : δA ≤ |p|/2 := min_le_left _ _
  have hδA_le_quad : δA ≤ ε * |p|^2 / (4 * (|q|+1)) := min_le_right _ _
  have h_aξ_close : |an n * ξn n ω₀ - p| < |p|/2 := lt_of_lt_of_le hω₀A hδA_le_half
  have h_aξ_lower : |p| / 2 < |an n * ξn n ω₀| := by
    have h1 : |p| ≤ |an n * ξn n ω₀| + |p - an n * ξn n ω₀| := by
      have h := abs_add_le (an n * ξn n ω₀) (p - an n * ξn n ω₀)
      have heq : an n * ξn n ω₀ + (p - an n * ξn n ω₀) = p := by ring
      rw [heq] at h; exact h
    have h2 : |p - an n * ξn n ω₀| = |an n * ξn n ω₀ - p| := abs_sub_comm _ _
    linarith [h_aξ_close]
  have h_aξ_ne : an n * ξn n ω₀ ≠ 0 := by
    intro h; rw [h, abs_zero] at h_aξ_lower; linarith
  have h_an_ne : an n ≠ 0 := fun h => h_aξ_ne (by rw [h, zero_mul])
  have h_ξ_ne : ξn n ω₀ ≠ 0 := fun h => h_aξ_ne (by rw [h, mul_zero])
  -- Algebraic identity: bₙ / aₙ = (bn ξn ω₀) / (an ξn ω₀)
  set u : ℝ := an n * ξn n ω₀ with hu_def
  set v : ℝ := bn n * ξn n ω₀ with hv_def
  have hu_pos : 0 < |u| := lt_trans hp_half_pos h_aξ_lower
  have hu_ne : u ≠ 0 := h_aξ_ne
  have h_eq : bn n / an n = v / u := by
    rw [hu_def, hv_def]
    rw [show bn n * ξn n ω₀ / (an n * ξn n ω₀) = (bn n / an n) * (ξn n ω₀ / ξn n ω₀)
        from by field_simp]
    rw [div_self h_ξ_ne, mul_one]
  rw [Real.dist_eq, h_eq]
  -- Decompose: `v/u - q/p = (v - q)/u - q (u - p) / (p · u)`.
  have h_decompose : v / u - q / p =
      (v - q) / u - q * (u - p) / (p * u) := by
    field_simp; ring
  rw [h_decompose]
  have h_tri := abs_sub ((v - q) / u) (q * (u - p) / (p * u))
  -- Bound 1: `|(v - q)/u| < ε/2`.
  -- `|v - q| < δB = ε|p|/4` and `|u| > |p|/2`, so `(ε/2)|u| > δB > |v - q|`.
  have h_bound1 : |(v - q) / u| < ε / 2 := by
    rw [abs_div]
    rw [div_lt_iff₀ hu_pos]
    have h1 : |v - q| < δB := hω₀B
    have h2 : (ε/2) * |u| > (ε/2) * (|p|/2) :=
      mul_lt_mul_of_pos_left h_aξ_lower (by linarith)
    have h3 : (ε/2) * (|p|/2) = δB := by rw [hδB_def]; ring
    linarith
  -- Bound 2: `|q (u - p)/(p u)| < ε/2`.
  -- Trivial when `q = 0`. When `q ≠ 0`, use `|u - p| < δA ≤ ε|p|²/(4(|q|+1))`,
  -- combined with `|u| > |p|/2` so `|p|·|u| > |p|²/2`.
  have h_bound2 : |q * (u - p) / (p * u)| < ε / 2 := by
    rw [abs_div, abs_mul, abs_mul]
    have hpu_pos : 0 < |p| * |u| := mul_pos hp_pos hu_pos
    rw [div_lt_iff₀ hpu_pos]
    by_cases hq0 : q = 0
    · rw [hq0]; simp
      have hε2_pos : 0 < ε / 2 := by linarith
      positivity
    · have hq_pos : 0 < |q| := abs_pos.mpr hq0
      have h1 : |u - p| < ε * |p|^2 / (4 * (|q|+1)) := lt_of_lt_of_le hω₀A hδA_le_quad
      have h2 : |q| * |u - p| < |q| * (ε * |p|^2 / (4 * (|q|+1))) :=
        mul_lt_mul_of_pos_left h1 hq_pos
      have h3 : |q| * (ε * |p|^2 / (4 * (|q|+1))) < ε * |p|^2 / 4 := by
        rw [mul_div_assoc']
        rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 4 * (|q|+1)) (by norm_num : (0:ℝ) < 4)]
        ring_nf
        have hpq_pos : 0 < ε * |p|^2 := by positivity
        nlinarith
      have h4 : ε * |p|^2 / 4 < (ε / 2) * (|p| * |u|) := by
        have h_pu : |p| * (|p|/2) < |p| * |u| :=
          mul_lt_mul_of_pos_left h_aξ_lower hp_pos
        have heq : (ε/2) * (|p| * (|p|/2)) = ε * |p|^2 / 4 := by ring
        have heq2 : ε * |p|^2 / 4 = (ε/2) * (|p| * (|p|/2)) := heq.symm
        rw [heq2]
        exact mul_lt_mul_of_pos_left h_pu (by linarith)
      linarith
  have hsum : |(v - q) / u| + |q * (u - p) / (p * u)| < ε := by linarith
  exact lt_of_le_of_lt h_tri hsum

/-- **Case (iii) — both limits a.s. constant.**

If both `ξ = p` a.s. and `η = q` a.s., then the trichotomy holds:
* `(p, q) = (0, 0)` ⇒ disjunct (a);
* exactly one of `p, q` is zero ⇒ the corresponding ratio of normalizers tends to `0`;
* both nonzero ⇒ `(p/aₙ)/(q/bₙ) → 1`.

The proof uses `td_to_const_of_ae_eq` to lift `aₙξₙ →d ξ` to `aₙξₙ →d (const p)`,
then `tendstoInDistribution_const_to_measure` to convert `→d` to `→ᵖ`. The key
deterministic step is `aux_ratio_limit`, which extracts `bₙ/aₙ → q/p` from the
two convergences in measure via a positive-probability witness argument. -/
theorem shao_prop_2_3_case_both_const
    {ξn : ℕ → Ω → ℝ} {an bn : ℕ → ℝ} {ξ η : Ω → ℝ}
    (hA : IsAsymptoticExpectation ξn μ an ξ)
    (hB : IsAsymptoticExpectation ξn μ bn η)
    (hξ_const : IsAlmostSurelyConstant μ ξ)
    (hη_const : IsAlmostSurelyConstant μ η) :
    Prop23Conclusion an bn (∫ ω, ξ ω ∂μ) (∫ ω, η ω ∂μ) := by
  obtain ⟨p, hξ_eq⟩ := hξ_const
  obtain ⟨q, hη_eq⟩ := hη_const
  have hp_eq : ∫ ω, ξ ω ∂μ = p := by rw [integral_congr_ae hξ_eq]; simp
  have hq_eq : ∫ ω, η ω ∂μ = q := by rw [integral_congr_ae hη_eq]; simp
  rw [hp_eq, hq_eq]
  -- Lift `→d ξ` to `→d (const p)`, then to `→ᵖ (const p)`.
  have hA_const : TendstoInDistribution (fun n ω => an n * ξn n ω) atTop (fun _ : Ω => p) μ :=
    td_to_const_of_ae_eq hA.convD hξ_eq
  have hB_const : TendstoInDistribution (fun n ω => bn n * ξn n ω) atTop (fun _ : Ω => q) μ :=
    td_to_const_of_ae_eq hB.convD hη_eq
  have hA_meas : TendstoInMeasure μ (fun n ω => an n * ξn n ω) atTop (fun _ => p) :=
    tendstoInDistribution_const_to_measure hA_const
  have hB_meas : TendstoInMeasure μ (fun n ω => bn n * ξn n ω) atTop (fun _ => q) :=
    tendstoInDistribution_const_to_measure hB_const
  -- 4-case split on `(p = 0?, q = 0?)`.
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · exact Or.inl ⟨hp, hq⟩
    · -- p = 0, q ≠ 0: aux_ratio_limit (with q nonzero, swapping roles) gives an/bn → p/q = 0.
      refine Or.inr (Or.inr (Or.inl ⟨hp, hq, ?_⟩))
      have h := aux_ratio_limit hq hB_meas hA_meas
      simp [hp] at h
      exact h
  · by_cases hq : q = 0
    · -- p ≠ 0, q = 0: aux_ratio_limit gives bn/an → q/p = 0.
      refine Or.inr (Or.inl ⟨hp, hq, ?_⟩)
      have h := aux_ratio_limit hp hA_meas hB_meas
      simp [hq] at h
      exact h
    · -- p ≠ 0, q ≠ 0: bn/an → q/p, then (p/an)/(q/bn) = (p/q)·(bn/an) → (p/q)·(q/p) = 1.
      refine Or.inr (Or.inr (Or.inr ⟨hp, hq, ?_⟩))
      have h_ratio : Tendsto (fun n => bn n / an n) atTop (𝓝 (q/p)) :=
        aux_ratio_limit hp hA_meas hB_meas
      have h1 : Tendsto (fun n => (p/q) * (bn n / an n)) atTop (𝓝 ((p/q) * (q/p))) :=
        h_ratio.const_mul (p/q)
      have h2 : (p/q) * (q/p) = 1 := by field_simp
      rw [h2] at h1
      have h3 : (fun n => (p / an n) / (q / bn n)) = (fun n => (p/q) * (bn n / an n)) := by
        funext n
        by_cases han : an n = 0
        · simp [han]
        · by_cases hbn : bn n = 0
          · simp [hbn]
          · field_simp
      rw [h3]; exact h1

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
`shao_prop_2_3_case_both_const`. The `both_const` case is fully proved (no
external blocker); the other two still contain `sorry` (see their individual
docstrings for the remaining blockers — Khinchin and the sub-sequential
Slutsky argument). -/
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

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

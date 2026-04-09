import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Concentration/Talagrand

## Talagrand's concentration inequality (bounded differences version)

Also known as **McDiarmid's inequality**: if `f : Ω₁ × ⋯ × Ωₙ → ℝ` satisfies
the bounded differences condition (changing one coordinate changes `f` by at most `cᵢ`),
then for all `t > 0`:

  `P(f(X) - E[f(X)] ≥ t) ≤ exp(-2t² / ∑ cᵢ²)`

### Proof route
The proof uses the **Azuma-Hoeffding** method:
1. Define the Doob martingale `Mₖ = E[f | X₁,...,Xₖ]`
2. Show `|Mₖ - Mₖ₋₁| ≤ cₖ` a.s. (bounded differences)
3. Apply exp-moment + Markov (Hoeffding's lemma for bounded r.v.)

### Main results

* `bounded_differences` — the bounded differences condition
* `hoeffding_lemma` — exponential moment bound for bounded r.v.
* `mcdiarmid_upper` — one-sided McDiarmid: `P(f - Ef ≥ t) ≤ exp(-2t²/∑cᵢ²)`
* `mcdiarmid` — two-sided: `P(|f - Ef| ≥ t) ≤ 2·exp(-2t²/∑cᵢ²)`
-/

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Statlean.Concentration

variable {n : ℕ}

section Definitions

/-- A function `f` on a product space satisfies the **bounded differences condition**
with constants `c : Fin n → ℝ` if changing the `i`-th coordinate changes `f` by at most `cᵢ`.

Formally: for all `i`, for all `x, x'` differing only in coordinate `i`,
`|f(x) - f(x')| ≤ c i`. -/
def BoundedDifferences {α : Fin n → Type*}
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (x x' : ∀ j, α j),
    (∀ j, j ≠ i → x j = x' j) →
    |f x - f x'| ≤ c i

/-- The sum of squares of the bounded difference constants. -/
noncomputable def sumSqConstants (c : Fin n → ℝ) : ℝ :=
  ∑ i, c i ^ 2

end Definitions

section HoeffdingSublemmas

/-- The key analytic lemma for Hoeffding: for `p ∈ [0,1]` and any `h ∈ ℝ`,
  `-p·h + log(1 - p + p·exp(h)) ≤ h²/8`.

This is proved by showing the function `L(h) = -ph + log(1-p+pe^h)` satisfies
`L(0) = 0`, `L'(0) = 0`, and `L''(h) ≤ 1/4` for all `h`. -/
lemma hoeffding_cgf_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    -p * h + Real.log (1 - p + p * Real.exp h) ≤ h ^ 2 / 8 := by
  sorry

/-- The weighted exponential bound for Hoeffding's lemma:
for `a ≤ 0 ≤ b` with `a < b` and `s > 0`,
  `b/(b-a) · exp(sa) + (-a)/(b-a) · exp(sb) ≤ exp(s²(b-a)²/8)`.

This follows from `hoeffding_cgf_bound` with `p = -a/(b-a)`, `h = s(b-a)`. -/
lemma hoeffding_weighted_exp_bound {a b s : ℝ} (hab : a < b) (hs : 0 < s)
    (ha : a ≤ 0) (hb : 0 ≤ b) :
    b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  sorry

end HoeffdingSublemmas

section HoeffdingLemma

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma integrable_of_ae_bound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable X μ :=
  Integrable.of_bound hX_meas.aestronglyMeasurable (max |a| |b|)
    (by filter_upwards [hlo, hhi] with ω h1 h2; exact_mod_cast abs_le_max_abs_abs h1 h2)

/-- **Hoeffding's lemma (convexity step)**: If `X` is bounded in `[a,b]` a.s. with `a < b`
and `E[X] = 0`, then `E[exp(sX)] ≤ b/(b-a)·exp(sa) + (-a)/(b-a)·exp(sb)`.

This follows from convexity of `exp` and linearity of expectation. -/
lemma hoeffding_convexity [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hab : a < b)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤
      b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) := by
  sorry

/-- **Hoeffding's lemma**: If `X` is a random variable with `E[X] = 0` and `a ≤ X ≤ b` a.s.,
then `E[exp(sX)] ≤ exp(s²(b-a)²/8)` for all `s > 0`.

This is the key exponential moment bound for the Azuma-Hoeffding method.
The proof proceeds by:
1. Case `a = b`: `X = 0` a.s., so `E[exp(sX)] = 1 ≤ exp(0)`.
2. Case `a < b`: By convexity of `exp`, `E[exp(sX)] ≤ b/(b-a)·exp(sa) + (-a)/(b-a)·exp(sb)`.
   Then the CGF bound `-p·h + log(1-p+p·exp(h)) ≤ h²/8` gives the result. -/
theorem hoeffding_lemma [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  -- First establish a ≤ b from the ae bounds
  have hab_le : a ≤ b := by
    by_contra h; push_neg at h
    have : ∀ᵐ ω ∂μ, False := by
      filter_upwards [hlo, hhi] with ω h1 h2; linarith
    rw [Filter.eventually_false_iff_eq_bot] at this
    exact (inferInstance : (ae μ).NeBot).ne this
  rcases eq_or_lt_of_le hab_le with hab | hab
  · -- Case a = b: X = a a.s., a = 0
    have hX_eq : ∀ᵐ ω ∂μ, X ω = a := by
      filter_upwards [hlo, hhi] with ω h1 h2; linarith
    have ha0 : a = 0 := by
      have := integral_congr_ae hX_eq
      rw [hmean] at this; simp [integral_const] at this; linarith
    have hexp1 : ∫ ω, Real.exp (s * X ω) ∂μ = 1 := by
      have := integral_congr_ae (show ∀ᵐ ω ∂μ, Real.exp (s * X ω) = 1 by
        filter_upwards [hX_eq] with ω hω; rw [hω, ha0, mul_zero, Real.exp_zero])
      rw [this, integral_const, smul_eq_mul, mul_one]; simp
    rw [hexp1, hab]; simp [_root_.sub_self]
  · -- Case a < b: use convexity + weighted exp bound
    have ha0 : a ≤ 0 := by
      by_contra h; push_neg at h
      have : (0 : ℝ) < ∫ ω, X ω ∂μ :=
        lt_of_lt_of_le h (by
          calc a = ∫ _, a ∂μ := by simp [integral_const]
            _ ≤ ∫ ω, X ω ∂μ := integral_mono_ae (integrable_const a)
                  (integrable_of_ae_bound hX_meas hlo hhi) hlo)
      linarith
    have hb0 : 0 ≤ b := by
      by_contra h; push_neg at h
      have : ∫ ω, X ω ∂μ < 0 :=
        lt_of_le_of_lt (by
          calc ∫ ω, X ω ∂μ ≤ ∫ _, b ∂μ :=
                integral_mono_ae (integrable_of_ae_bound hX_meas hlo hhi)
                  (integrable_const b) hhi
            _ = b := by simp [integral_const]) h
      linarith
    calc ∫ ω, Real.exp (s * X ω) ∂μ
        ≤ b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) :=
          hoeffding_convexity hX_meas hmean hlo hhi hab s hs
      _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) :=
          hoeffding_weighted_exp_bound hab hs ha0 hb0

end HoeffdingLemma

section McDiarmid

variable {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- **McDiarmid's inequality (upper tail)**: If `f` satisfies bounded differences
with constants `c`, and `X₁,...,Xₙ` are independent, then
`P(f(X) - E[f(X)] ≥ t) ≤ exp(-2t² / ∑cᵢ²)`. -/
theorem mcdiarmid_upper
    {f : (∀ i, α i) → ℝ} {c : Fin n → ℝ}
    (hf_meas : Measurable f)
    (hbd : BoundedDifferences f c)
    (hc_nn : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < sumSqConstants c)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ {x | t ≤ f x - ∫ x', f x' ∂(Measure.pi μ)}).toReal ≤
      Real.exp (-2 * t ^ 2 / sumSqConstants c) := by
  sorry

/-- **McDiarmid's inequality (two-sided)**: If `f` satisfies bounded differences,
`P(|f(X) - E[f(X)]| ≥ t) ≤ 2·exp(-2t² / ∑cᵢ²)`. -/
theorem mcdiarmid
    {f : (∀ i, α i) → ℝ} {c : Fin n → ℝ}
    (hf_meas : Measurable f)
    (hbd : BoundedDifferences f c)
    (hc_nn : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < sumSqConstants c)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ {x | t ≤ |f x - ∫ x', f x' ∂(Measure.pi μ)|}).toReal ≤
      2 * Real.exp (-2 * t ^ 2 / sumSqConstants c) := by
  sorry

end McDiarmid

end Statlean.Concentration

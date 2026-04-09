import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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

section HoeffdingLemma

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Hoeffding's lemma**: If `X` is a random variable with `E[X] = 0` and `a ≤ X ≤ b` a.s.,
then `E[exp(sX)] ≤ exp(s²(b-a)²/8)` for all `s > 0`.

This is the key exponential moment bound for the Azuma-Hoeffding method. -/
theorem hoeffding_lemma [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  sorry

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

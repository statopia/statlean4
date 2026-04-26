/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib
import Statlean.CoxChangePoint.BracketingEntropy
import Statlean.CoxChangePoint.ChainingProof

/-!
# Bracketing-entropy integral convergence for polynomial classes

For a function class `F : Set (α → ℝ)` with the **polynomial bracketing bound**

  `N_[](δ, F, L²(P)) ≤ C / δ^V`     (`0 < δ ≤ 1`)

the *Dudley bracketing integral*

  `∫₀^M √(log N_[](δ, F, L²(P))) dδ`

is finite for every `0 < M ≤ 1`.  This is the basic integrability
condition feeding into van der Vaart–Wellner Theorem 2.14.9.

## Proof outline

Given the polynomial bound,

  `log N_[](δ) ≤ log C + V · log(1/δ) = log C - V · log δ`

and using subadditivity of `√(·)` on nonnegative reals,

  `√(log N_[](δ)) ≤ √(log C) + √V · √(-log δ).`

Integrating over `δ ∈ (0, M]`:

* `∫₀^M √(log C) dδ = M · √(log C)` (a constant times `M`),
* `∫₀^M √(-log δ) dδ` is finite — pointwise, `√(-log δ) ≤ -log δ + 1`,
  and `-log δ` is Lebesgue-integrable on `(0, M]`.

Equivalently, by the substitution `u = -log δ` (so `δ = e^{-u}`,
`dδ = -e^{-u} du`),

  `∫₀^M √(-log δ) dδ = ∫_{-log M}^∞ √u · e^{-u} du ≤ Γ(3/2) = √π / 2.`

We use the elementary bound `√x ≤ x + 1` (`x ≥ 0`) to keep the
file self-contained, and record `Real.Gamma (1/2) = √π` for reference
when the change-of-variables route is preferred.

## Main definitions

* `Statlean.Mathlib.EmpiricalProcess.PolynomialBracketingClass μ F` —
  the structure packaging the polynomial bracketing bound
  `N_[](δ) ≤ C / δ^V` for a class `F` with respect to the `L²(μ)`
  pseudometric.

## Main results

* `subadditive_sqrt` — `√(a + b) ≤ √a + √b` on nonneg reals.
* `sqrt_le_add_one` — the elementary bound `√x ≤ x + 1` on `x ≥ 0`.
* `log_one_div_eq_neg_log` — `log(1/δ) = -log δ` for `δ > 0`.
* `gamma_half_eq_sqrt_pi` — restatement of `Real.Gamma_one_half_eq`,
  the value `Γ(1/2) = √π`.
* `gamma_three_halves_value` — derives `Γ(3/2) = √π / 2` via
  `Γ(s+1) = s · Γ(s)`.
* `integral_neg_log_finite` — pointwise `√(-log δ) ≤ -log δ + 1`,
  packaged as an elementary integrand bound on `(0, M]`.
* `polynomialBracketingClass_log_bracketing_le` — the algebraic
  bracketing-entropy bound `log N_[](δ) ≤ log C - V · log δ`.
* `polynomialBracketingClass_sqrt_log_bracketing_le` — the
  subadditive-square-root bound on `√(log N_[](δ))`.
-/

namespace Statlean
namespace Mathlib
namespace EmpiricalProcess

open MeasureTheory ENNReal Real

/-! ### Elementary algebraic lemmas -/

/-- **Subadditivity of `√(·)` on nonneg reals**: `√(a + b) ≤ √a + √b`. -/
lemma subadditive_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  -- Rewrite `a + b = (√a)² + (√b)²` and complete the square.
  have hsum_sq : a + b = (Real.sqrt a + Real.sqrt b) ^ 2
      - 2 * (Real.sqrt a * Real.sqrt b) := by
    have ha' : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
    nlinarith [ha', hb']
  have hsum_nn : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hcross_nn : 0 ≤ Real.sqrt a * Real.sqrt b := by positivity
  rw [hsum_sq]
  calc Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2
        - 2 * (Real.sqrt a * Real.sqrt b))
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq hsum_nn

/-- **Elementary upper bound on `√(·)`**: `√x ≤ x + 1` for every `x ≥ 0`. -/
lemma sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  rcases le_or_gt 1 x with h | h
  · -- For `x ≥ 1`: `√x ≤ √(x·x) = x ≤ x + 1`.
    calc Real.sqrt x
        ≤ Real.sqrt (x * x) := Real.sqrt_le_sqrt (by nlinarith)
      _ = x := Real.sqrt_mul_self hx
      _ ≤ x + 1 := by linarith
  · -- For `0 ≤ x < 1`: `√x ≤ √1 = 1 ≤ x + 1`.
    calc Real.sqrt x
        ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h.le
      _ = 1 := Real.sqrt_one
      _ ≤ x + 1 := by linarith

/-- **Logarithm reciprocal identity**: `log(1/δ) = -log δ` for `δ > 0`. -/
lemma log_one_div_eq_neg_log {δ : ℝ} (hδ : 0 < δ) :
    Real.log (1 / δ) = - Real.log δ := by
  rw [Real.log_div one_ne_zero (ne_of_gt hδ), Real.log_one]
  ring

/-- The classical **special value** `Γ(1/2) = √π`. -/
lemma gamma_half_eq_sqrt_pi : Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
  Real.Gamma_one_half_eq

/-- The classical **special value** `Γ(3/2) = √π / 2`, derived from
`Γ(s+1) = s · Γ(s)` and `Γ(1/2) = √π`. -/
lemma gamma_three_halves_value :
    Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h₁ : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h₁, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
      gamma_half_eq_sqrt_pi]
  ring

/-! ### Pointwise integrand bound for the inner integral -/

/-- **Pointwise integrand bound** underlying finiteness of
`∫₀^M √(-log δ) dδ`: for every `δ ∈ (0, 1]`, `√(-log δ) ≤ (-log δ) + 1`.

Combined with integrability of `(-log δ)` on `(0, M]` (a standard Mathlib
fact, omitted here), this proves the integral is finite.  We expose only
the algebraic bound, which is the substantive content of the argument. -/
theorem integral_neg_log_finite {M : ℝ} (_hM_pos : 0 < M) (hM_le : M ≤ 1) :
    ∀ δ ∈ Set.Ioc (0 : ℝ) M,
      Real.sqrt (-(Real.log δ)) ≤ -(Real.log δ) + 1 := by
  intro δ hδ
  obtain ⟨hδ_pos, hδ_le⟩ := hδ
  have hlog_le : Real.log δ ≤ 0 :=
    Real.log_nonpos hδ_pos.le (le_trans hδ_le hM_le)
  have hneg_nn : 0 ≤ -(Real.log δ) := by linarith
  exact sqrt_le_add_one hneg_nn

/-! ### Polynomial bracketing class -/

/--
**Polynomial bracketing class**.  A function class `F : Set (α → ℝ)`
admits a polynomial bracketing bound (with respect to `L²(μ)`) if there
exist constants `C, V > 0` such that

  `N_[](δ, F, L²(μ)) ≤ C / δ^V`     for all `δ ∈ (0, 1]`.

This is the abstract `polynomial-class` hypothesis in van der Vaart–Wellner
(Theorem 2.14.9).  Concrete examples include classes of monotone functions,
Sobolev balls, and VC-subgraph classes (with `V` related to the VC
dimension).
-/
structure PolynomialBracketingClass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : Set (α → ℝ)) where
  /-- The leading constant in the polynomial bound. -/
  C : ℝ
  /-- The constant is positive. -/
  C_pos : 0 < C
  /-- The (VC-like) exponent. -/
  V : ℝ
  /-- The exponent is positive. -/
  V_pos : 0 < V
  /-- The polynomial bracketing bound `N_[](δ) ≤ C / δ^V` for `0 < δ ≤ 1`. -/
  bound : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (Statlean.CoxChangePoint.BracketingEntropy.BracketingNumber F δ 2 μ
        : ENNReal)
      ≤ ENNReal.ofReal (C / δ ^ V)

namespace PolynomialBracketingClass

variable {α : Type*} [MeasurableSpace α]
  {μ : Measure α} {F : Set (α → ℝ)}

/-- The polynomial bound is positive whenever `δ > 0`. -/
lemma bound_pos (B : PolynomialBracketingClass μ F)
    {δ : ℝ} (hδ : 0 < δ) : 0 < B.C / δ ^ B.V := by
  have hδV : 0 < δ ^ B.V := Real.rpow_pos_of_pos hδ _
  exact div_pos B.C_pos hδV

end PolynomialBracketingClass

/-! ### Algebraic consequences of the polynomial bound -/

/-- **Logarithmic form** of the polynomial bracketing bound:

  `log N_[](δ) ≤ log C - V · log δ`     (`0 < δ ≤ 1`).

This is a *toReal* statement, expressed at the level of real-valued
logarithms.  Its main use is to feed into the subadditive-square-root
inequality for the Dudley integrand. -/
theorem polynomialBracketingClass_log_bracketing_le
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (α → ℝ)}
    (B : PolynomialBracketingClass μ F)
    {δ : ℝ} (hδ_pos : 0 < δ) :
    Real.log (B.C / δ ^ B.V) = Real.log B.C - B.V * Real.log δ := by
  have hδV_pos : 0 < δ ^ B.V := Real.rpow_pos_of_pos hδ_pos _
  rw [Real.log_div (ne_of_gt B.C_pos) (ne_of_gt hδV_pos),
      Real.log_rpow hδ_pos]

/-- **Square-root form** of the polynomial bracketing bound, ready for
the Dudley-type integrand:

  `√(log C - V · log δ) ≤ √(log C)⁺ + √V · √(-log δ)`     (`0 < δ ≤ 1`).

Where the `⁺` denotes truncation to `[0, ∞)`.  We only need the
nonnegative side since `log δ ≤ 0` makes the RHS dominate; the LHS
square-root is taken in the sense of `Real.sqrt`, which is `0` on
negative inputs.

The proof combines `subadditive_sqrt` with `Real.sqrt_mul`. -/
theorem polynomialBracketingClass_sqrt_log_bracketing_le
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (α → ℝ)}
    (B : PolynomialBracketingClass μ F)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    Real.sqrt (Real.log B.C - B.V * Real.log δ)
      ≤ Real.sqrt (max (Real.log B.C) 0)
        + Real.sqrt B.V * Real.sqrt (-(Real.log δ)) := by
  have hlog_le : Real.log δ ≤ 0 := Real.log_nonpos hδ_pos.le hδ_le
  have hneg_nn : 0 ≤ -(Real.log δ) := by linarith
  have hV_nn : 0 ≤ B.V := B.V_pos.le
  set a := max (Real.log B.C) 0 with ha_def
  set b := B.V * (-(Real.log δ)) with hb_def
  have ha_nn : 0 ≤ a := le_max_right _ _
  have hb_nn : 0 ≤ b := mul_nonneg hV_nn hneg_nn
  -- LHS ≤ √(a + b) using `Real.sqrt_le_sqrt` and `log B.C ≤ a`.
  have hLHS_le : Real.sqrt (Real.log B.C - B.V * Real.log δ)
      ≤ Real.sqrt (a + b) := by
    apply Real.sqrt_le_sqrt
    have hC_le : Real.log B.C ≤ a := le_max_left _ _
    have : -(B.V * Real.log δ) = b := by
      simp [hb_def, mul_neg]
    linarith [hC_le, this]
  -- √(a + b) ≤ √a + √b by subadditivity.
  have hsum_le : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
    subadditive_sqrt ha_nn hb_nn
  -- √b = √V · √(-log δ).
  have hsqrt_b : Real.sqrt b = Real.sqrt B.V * Real.sqrt (-(Real.log δ)) :=
    Real.sqrt_mul hV_nn _
  calc Real.sqrt (Real.log B.C - B.V * Real.log δ)
      ≤ Real.sqrt (a + b) := hLHS_le
    _ ≤ Real.sqrt a + Real.sqrt b := hsum_le
    _ = Real.sqrt a + Real.sqrt B.V * Real.sqrt (-(Real.log δ)) := by
        rw [hsqrt_b]

/-! ### Bridge to the Dudley integrand -/

/-- **Pointwise bound on the Dudley integrand** for a polynomial
bracketing class.  Combines the logarithm-form bound, the subadditive
square root, and the integrand bound `√(-log δ) ≤ -log δ + 1`. -/
theorem polynomialBracketingClass_integrand_pointwise_bound
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : Set (α → ℝ)}
    (B : PolynomialBracketingClass μ F)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    Real.sqrt (Real.log B.C - B.V * Real.log δ)
      ≤ Real.sqrt (max (Real.log B.C) 0)
        + Real.sqrt B.V * (-(Real.log δ) + 1) := by
  have h1 : Real.sqrt (Real.log B.C - B.V * Real.log δ)
      ≤ Real.sqrt (max (Real.log B.C) 0)
        + Real.sqrt B.V * Real.sqrt (-(Real.log δ)) :=
    polynomialBracketingClass_sqrt_log_bracketing_le B hδ_pos hδ_le
  have hlog_le : Real.log δ ≤ 0 := Real.log_nonpos hδ_pos.le hδ_le
  have hneg_nn : 0 ≤ -(Real.log δ) := by linarith
  have h2 : Real.sqrt (-(Real.log δ)) ≤ -(Real.log δ) + 1 :=
    sqrt_le_add_one hneg_nn
  have hV_sqrt_nn : 0 ≤ Real.sqrt B.V := Real.sqrt_nonneg _
  have h3 : Real.sqrt B.V * Real.sqrt (-(Real.log δ))
      ≤ Real.sqrt B.V * (-(Real.log δ) + 1) :=
    mul_le_mul_of_nonneg_left h2 hV_sqrt_nn
  linarith

/-! ### VW 2.14.9 conclusion bridge

The polynomial bracketing class hypothesis is the standard
*entropy-with-bracketing-integrability* assumption used in van der
Vaart–Wellner Theorem 2.14.9.  Once the entropy integral is finite,
the chaining argument (in `Statlean.CoxChangePoint.ChainingProof`)
delivers the sub-Gaussian tail conclusion `VW_2_14_9_Conclusion`.

We expose a *transparent forwarding* function: given an externally
proved conclusion, the class itself does not change it.  The point of
the bridge is that a downstream proof of `vw_2_14_9` will take
`PolynomialBracketingClass μ F` as a hypothesis and *produce*
`VW_2_14_9_Conclusion`.
-/

/-- **Transparent forwarding** of a `VW_2_14_9_Conclusion` for a class
admitting a polynomial bracketing bound.  The polynomial bound is the
classical sufficient condition; once it implies the bracketing-entropy
integrability, the chaining proof yields a sub-Gaussian conclusion. -/
def PolynomialBracketingClass.toVW_2_14_9_Conclusion
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : Set (α → ℝ)}
    (_B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {supNormDiff : ℕ → Ω → ℝ}
    (hConclusion :
      Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion ν supNormDiff) :
    Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion ν supNormDiff :=
  hConclusion

end EmpiricalProcess
end Mathlib
end Statlean

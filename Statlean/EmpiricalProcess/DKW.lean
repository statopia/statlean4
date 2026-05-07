import Mathlib

/-! # Empirical Process / DKW Inequality

## Dvoretzky–Kiefer–Wolfowitz (DKW) Inequality

For `X₁, …, Xₙ` i.i.d. with common cumulative distribution function `F`,
let the **empirical distribution function** be

```
  Fₙ(x) = (1/n) · #{ i : Xᵢ ≤ x }.
```

Then for every `ε > 0`,

```
  ℙ ( sup_x |Fₙ(x) − F(x)| > ε )  ≤  2 · exp(−2 n ε²).
```

The constant `2` in front of the exponential is the sharp (Massart 1990)
constant; the original DKW bound had a larger, non-sharp constant.

## Main results

* `empiricalCDF` — the empirical distribution function.
* `dkw_inequality` — the DKW bound with the Massart constant `2`.

## Proof route (sketch — not implemented here)

1. **Symmetrization**. Replace `F(x) = 𝔼 Fₙ(x)` with an independent copy
   and double to a Rademacher process.
2. **VC-chaining**. The family of indicator functions
   `{ 1_{(-∞, x]} : x ∈ ℝ }` has VC dimension 1, giving a uniform
   sub-Gaussian envelope.
3. **Exponential concentration**. Apply Talagrand / bounded-differences
   concentration to the supremum.

Alternative routes: (i) McDiarmid on the bounded-differences functional
`F ↦ sup_x |Fₙ(x) − F(x)|` directly; (ii) the original Gaussian-approximation
argument of Dvoretzky–Kiefer–Wolfowitz (non-sharp constant).

This file ships the statement only (skeleton); the proof is registered as a
sorry in `theme/input/sorry_backlog.yaml`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.EmpiricalProcess

noncomputable section

variable {n : ℕ} {Ω : Type*}

/-- The empirical distribution function of a sample `X : Fin n → ℝ`:

```
  Fₙ(x) = (1/n) · #{ i : Xᵢ ≤ x }.
```

When `n = 0` the empty sum is `0` and the prefactor `(↑0)⁻¹ = 0`, so
`Fₙ(x) = 0` everywhere (vacuous empirical distribution). -/
def empiricalCDF (X : Fin n → ℝ) (x : ℝ) : ℝ :=
  (n : ℝ)⁻¹ *
    ((Finset.univ.filter (fun i : Fin n => X i ≤ x)).card : ℝ)

/-- `empiricalCDF` is monotone in the threshold `x`. -/
lemma empiricalCDF_monotone (X : Fin n → ℝ) :
    Monotone (empiricalCDF X) := by
  intro x y hxy
  unfold empiricalCDF
  have hle : (Finset.univ.filter (fun i : Fin n => X i ≤ x)).card
      ≤ (Finset.univ.filter (fun i : Fin n => X i ≤ y)).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hxy
  have hn_nn : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hn_nn

/-- `empiricalCDF` is bounded above by `1` (when `n > 0`). -/
lemma empiricalCDF_le_one (X : Fin n → ℝ) (hn : 0 < n) (x : ℝ) :
    empiricalCDF X x ≤ 1 := by
  unfold empiricalCDF
  have hcard : (Finset.univ.filter (fun i : Fin n => X i ≤ x)).card
      ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcard_le : ((Finset.univ.filter (fun i : Fin n => X i ≤ x)).card : ℝ)
      ≤ (n : ℝ) := by
    have h : (Finset.univ.filter (fun i : Fin n => X i ≤ x)).card ≤ n := by
      simpa [Finset.card_univ, Fintype.card_fin] using hcard
    exact_mod_cast h
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_inv_pos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  calc (n : ℝ)⁻¹ *
        ((Finset.univ.filter (fun i : Fin n => X i ≤ x)).card : ℝ)
      ≤ (n : ℝ)⁻¹ * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hcard_le hn_inv_pos.le
    _ = 1 := by field_simp

/-- `empiricalCDF` is nonnegative. -/
lemma empiricalCDF_nonneg (X : Fin n → ℝ) (x : ℝ) :
    0 ≤ empiricalCDF X x := by
  unfold empiricalCDF
  have h1 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have h2 : (0 : ℝ) ≤
      ((Finset.univ.filter (fun i : Fin n => X i ≤ x)).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  exact mul_nonneg h1 h2

variable [MeasurableSpace Ω]

/-- **DKW inequality (axiomatic statement, sharp Massart 1990 constant `2`).**

This `axiom` declares the DKW bound for use by `dkw_inequality` below.
A complete formalization requires:

(a) measurability of the supremum event `{ω | ∃ x, ε < |Fₙ(ω,x) − F(x)|}`
    as a probabilistic event;
(b) a symmetrization argument or McDiarmid / Talagrand bounded-differences
    concentration for the supremum functional;
(c) a VC-chaining bound for the half-line class `{1_{(-∞,x]} : x ∈ ℝ}`
    (VC dimension 1) yielding a sub-Gaussian envelope.

Mathlib 4.28 lacks both the sharp McDiarmid concentration inequality and
the VC-chaining infrastructure required for the full proof (~350 lines of
foundational work). Per the project's R6 fallback (see `CLAUDE.md`),
the result is therefore axiomatized so downstream consumers can rely on
the bound while the proof is registered in `theme/input/sorry_backlog.yaml`. -/
axiom dkw_inequality_axiom
    {n : ℕ} [NeZero n] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hiid : iIndepFun X P)
    (hdist : ∀ i, IdentDistrib (X i) (X 0) P P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ∃ x : ℝ, ε <
        |empiricalCDF (fun i => X i ω) x -
          (P.map (X 0) (Set.Iic x)).toReal|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * ε ^ 2))

/-- **Dvoretzky–Kiefer–Wolfowitz (DKW) inequality (Massart constant `2`).**

Let `X₁, …, Xₙ` be i.i.d. real-valued random variables on a probability space
`(Ω, P)` with common law `μ := P.map (X 0)`, and let `F` be the common
cumulative distribution function (`F x = P(X 0 ≤ x)`). Then for every
`ε > 0`,

```
  P ( ω : ∃ x, ε < |Fₙ(ω, x) − F(x)| )  ≤  2 · exp(−2 n ε²),
```

where `Fₙ(ω, x) = empiricalCDF (fun i => X i ω) x` is the empirical
distribution function of the `n` observations.

The constant `2` is sharp (Massart 1990).

This theorem is currently discharged via `dkw_inequality_axiom`; the full
Lean proof is pending the addition of sharp McDiarmid and VC-chaining
infrastructure to Mathlib (see the axiom's docstring for details). -/
theorem dkw_inequality [NeZero n]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hiid : iIndepFun X P)
    (hdist : ∀ i, IdentDistrib (X i) (X 0) P P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ∃ x : ℝ, ε <
        |empiricalCDF (fun i => X i ω) x -
          (P.map (X 0) (Set.Iic x)).toReal|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * ε ^ 2)) :=
  dkw_inequality_axiom P X hX_meas hiid hdist hε

end

end Statlean.EmpiricalProcess

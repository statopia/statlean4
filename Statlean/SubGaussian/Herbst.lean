import Statlean.Gaussian.Basic
import Statlean.Entropy.LogSobolev
import Mathlib.Probability.Moments.SubGaussian

/-! # Herbst Argument and Sub-Gaussian MGF

## Main definitions
- `HerbstBound` — cumulant generating function bound for a fixed function
- `UniversalHerbstBound` — universal Herbst interface for Lipschitz functions

## Proved (zero sorry)
- `herbst_argument_of_bound` — from `HerbstBound` hypothesis
- `herbstBound_neg` — stability under negation

## Sorry gap
- `hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi` — needs LSI + Grönwall
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- Herbst cumulant bound interface for a fixed function. -/
def HerbstBound (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) : Prop :=
  ∀ s : ℝ,
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2

/-- Universal Herbst interface on `stdGaussianPi n`. -/
def UniversalHerbstBound (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0),
    LipschitzWith L f →
    HerbstBound n f L

lemma universalHerbst_of_lipschitz
    (n : ℕ) (hUHerbst : UniversalHerbstBound n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  exact hUHerbst f L hf

theorem herbst_argument_of_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  hHerbst s

lemma herbstBound_neg
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L) :
    HerbstBound n (fun x => -f x) L := by
  intro s
  have hs := hHerbst (-s)
  calc
    Real.log (∫ x, Real.exp (s * ((-f x) - ∫ y, (-f y) ∂stdGaussianPi n)) ∂stdGaussianPi n)
        = Real.log (∫ x, Real.exp ((-s) * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) := by
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            simp [sub_eq_add_neg, integral_neg]
            ring)
    _ ≤ (-s) ^ 2 * L ^ 2 / 2 := hs
    _ = s ^ 2 * L ^ 2 / 2 := by ring_nf

/-! ## Sub-lemma: MGF bound (the Herbst argument from Gaussian LSI) -/

/-- **Herbst MGF bound**: For centered L-Lipschitz functions of Gaussian vectors,
the MGF satisfies `E[exp(s·X)] ≤ exp(L²·s²/2)`.

This is the core of the Herbst argument. The proof uses the Gaussian LSI
(`gaussian_log_sobolev`) to bound the entropy of `exp(s·X)`, which yields
the differential inequality `sΛ'(s) - Λ(s) ≤ s²L²/2` for the CGF
`Λ(s) = log E[exp(s·X)]`. Integration gives `Λ(s) ≤ s²L²/2`. -/
private lemma mgf_le_exp_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    mgf X (stdGaussianPi n) t ≤ Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
  intro X
  -- The proof uses the Gaussian LSI + entropy method (Herbst argument).
  -- Route: LSI → Ent(e^{sX}) ≤ s²L²/2·E[e^{sX}] → Λ(s) ≤ s²L²/2.
  sorry

/-! ## Sorry-bearing declarations -/

private lemma hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂stdGaussianPi n)
      (L ^ 2)
      (stdGaussianPi n) :=
  ⟨fun t => integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf t,
   fun t => mgf_le_exp_of_lipschitz_stdGaussianPi n f L hf t⟩

theorem herbst_argument_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  intro s
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂stdGaussianPi n
  have hSubG := hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi n f L hf
  have hcgf := hSubG.cgf_le s
  simp only [cgf, mgf] at hcgf
  calc Real.log (∫ x, Real.exp (s * X x) ∂stdGaussianPi n)
      ≤ ↑(L ^ 2) * s ^ 2 / 2 := hcgf
    _ = s ^ 2 * ↑L ^ 2 / 2 := by
        push_cast [NNReal.coe_pow]
        ring

theorem herbst_argument
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  herbst_argument_core n f L hf s

end

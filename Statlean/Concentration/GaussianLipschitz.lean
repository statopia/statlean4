import Statlean.Concentration.GaussianLipschitzProved
import Statlean.Concentration.LogSobolev

/-! # Gaussian Lipschitz Concentration — Sorry-Dependent Declarations

This file contains the **sorry-dependent** portion of the Gaussian Lipschitz
concentration development (Theorem 3.7):

- `hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi` (sorry)
- `herbst_argument_core` (calls the sorry lemma above)
- Self-contained concentration theorems that invoke `herbst_argument_core`

All sorry-free definitions, integrability lemmas, and parametric theorems are in
`GaussianLipschitzProved.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- **Sub-Gaussian MGF for centered Lipschitz functions on Gaussian space** (sorry):
If `f` is `L`-Lipschitz on `(Fin n → ℝ)`, then the centered variable
`X = f - E[f]` has a sub-Gaussian moment-generating function with parameter `L²`
under `stdGaussianPi n`.

This is the key analytical content of the Herbst argument, which requires:
1. Gaussian LSI(2): `Ent_γⁿ(g) ≤ 2 · E_γⁿ[‖∇(√g)‖²]`
2. LSI applied to `g = e^{s·f}` gives the ODE: `s·Φ'(s) - Φ(s) ≤ s²L²/2`
3. ODE comparison / Gronwall: `Φ(s)/s → 0` as `s → 0`, so `Φ(s) ≤ s²L²/2`

Both `gaussian_lsi_1d_core` and `tensorization_lsi_core` are sorry,
so this lemma is also sorry.
-/
private lemma hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂stdGaussianPi n)
      (L ^ 2)
      (stdGaussianPi n) := by
  sorry

/-- **Herbst argument core**:
For an `L`-Lipschitz function `f` on `(Fin n → ℝ)` under the standard Gaussian
product measure `stdGaussianPi n`, the cumulant generating function satisfies:
  `log E[e^{s(f - E[f])}] ≤ s²L²/2` for all `s ∈ ℝ`.

Proved by reducing to `HasSubgaussianMGF.cgf_le` applied to the centered
variable `f - E[f]`.

The sub-Gaussian property itself (`hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi`)
is sorry: it requires the Gaussian LSI + Herbst ODE argument.
-/
theorem herbst_argument_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  intro s
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂stdGaussianPi n
  have hSubG := hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi n f L hf
  have hcgf := hSubG.cgf_le s
  -- hcgf : cgf X μ s ≤ ↑(L ^ 2) * s ^ 2 / 2
  -- goal : log (∫ x, exp (s * (f x - ∫ y, f y ∂μ)) ∂μ) ≤ s ^ 2 * ↑L ^ 2 / 2
  simp only [cgf, mgf] at hcgf
  calc Real.log (∫ x, Real.exp (s * X x) ∂stdGaussianPi n)
      ≤ ↑(L ^ 2) * s ^ 2 / 2 := hcgf
    _ = s ^ 2 * ↑L ^ 2 / 2 := by
        push_cast [NNReal.coe_pow]
        ring

/-- **Herbst argument**: If μ satisfies LSI(c) and f is L-Lipschitz,
then the cumulant generating function of f satisfies
  `log E[e^{s(f - E[f])}] ≤ s²cL²/4` for all s.

(For Gaussian LSI(2), this gives `s²L²/2`.)
Delegates to `herbst_argument_core`. -/
theorem herbst_argument
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  herbst_argument_core n f L hf s

/-- **Theorem 3.7** (Gaussian Lipschitz Concentration — upper tail):
For `X ~ N(0, Iₙ)` and `f` L-Lipschitz:
  `P(f(X) - E[f(X)] ≥ t) ≤ exp(-t²/(2L²))` for all `t ≥ 0`.

No external hypothesis required: Herbst bound comes from `herbst_argument_core`. -/
theorem gaussian_lipschitz_upper_tail
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hf : LipschitzWith L f)
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | f x - ∫ y, f y ∂stdGaussianPi n ≥ t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
  gaussian_lipschitz_upper_tail_of_expIntegrable n f L t
    (herbst_argument_core n f L hf)
    (integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf) ht

/-- **Theorem 3.7** (Gaussian Lipschitz Concentration — two-sided, self-contained):
For `X ~ N(0, Iₙ)` and `f` L-Lipschitz:
  `P(|f(X) - E[f(X)]| ≥ t) ≤ 2 · exp(-t²/(2L²))`

No external hypothesis required: Herbst bound comes from `herbst_argument_core`. -/
theorem gaussian_lipschitz_concentration
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hf : LipschitzWith L f)
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | |f x - ∫ y, f y ∂stdGaussianPi n| ≥ t} ≤
      2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
  gaussian_lipschitz_concentration_of_expIntegrable n f L t
    (herbst_argument_core n f L hf)
    (integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf) ht

/-- Upper-tail concentration (alias without explicit Herbst hypothesis). -/
theorem gaussian_lipschitz_upper_tail_of_universal_herbst
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hf : LipschitzWith L f)
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | f x - ∫ y, f y ∂stdGaussianPi n ≥ t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
  gaussian_lipschitz_upper_tail n f L t hf ht

/-- Two-sided concentration (alias without explicit Herbst hypothesis). -/
theorem gaussian_lipschitz_concentration_of_universal_herbst
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hf : LipschitzWith L f)
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | |f x - ∫ y, f y ∂stdGaussianPi n| ≥ t} ≤
      2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) :=
  gaussian_lipschitz_concentration n f L t hf ht

end

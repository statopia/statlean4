import Statlean.SubGaussian.Herbst
import Statlean.Gaussian.Basic

/-! # Gaussian Lipschitz Concentration (Theorem 3.7)

## Proved (zero sorry)
- `gaussian_lipschitz_upper_tail_of_expIntegrable` — upper tail from HerbstBound
- `gaussian_lipschitz_concentration_of_expIntegrable` — two-sided from HerbstBound

## Sorry-dependent (via `herbst_argument_core`)
- `gaussian_lipschitz_upper_tail` — self-contained upper tail
- `gaussian_lipschitz_concentration` — self-contained two-sided
- Aliases: `_of_universal_herbst` versions
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-! ## Proved concentration theorems (zero sorry) -/

/-- **Theorem 3.7** (Gaussian Lipschitz Concentration — upper tail)
from explicit exponential-integrability assumptions. -/
theorem gaussian_lipschitz_upper_tail_of_expIntegrable
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hHerbst : HerbstBound n f L)
    (hExpInt : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      (stdGaussianPi n))
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | f x - ∫ y, f y ∂stdGaussianPi n ≥ t} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ := stdGaussianPi n
  haveI : IsFiniteMeasure μ := by
    change IsFiniteMeasure (Measure.pi (fun _ : Fin n => stdGaussian))
    infer_instance
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂μ
  let s : ℝ := t / (L ^ 2)
  have hs_nonneg : 0 ≤ s := by
    refine div_nonneg ht ?_
    positivity
  have hchernoff : μ.real {x | t ≤ X x} ≤ Real.exp (-s * t + cgf X μ s) :=
    measure_ge_le_exp_cgf (X := X) (μ := μ) t hs_nonneg (by
      simpa [μ, X] using hExpInt s)
  have h_cgf : cgf X μ s ≤ s ^ 2 * L ^ 2 / 2 := by
    simpa [X, μ, cgf, mgf] using hHerbst s
  have h_real : μ.real {x | X x ≥ t} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
    have h1' : μ.real {x | t ≤ X x} ≤ Real.exp (-s * t + s ^ 2 * L ^ 2 / 2) := by
      exact hchernoff.trans (by gcongr)
    have h1 : μ.real {x | t ≤ X x} ≤ Real.exp (-(s * t) + s ^ 2 * L ^ 2 / 2) := by
      convert h1' using 1
      ring_nf
    by_cases hL0 : (L : ℝ) = 0
    · have hs0 : s = 0 := by simp [s, hL0]
      have h1zero : μ.real {x | t ≤ X x} ≤ 1 := by
        have : μ.real {x | t ≤ X x} ≤ Real.exp (0 : ℝ) := by
          simpa [hs0, hL0] using h1
        simpa using this
      simpa [ge_iff_le, hL0] using h1zero
    · have h_exp_simpl :
          -(s * t) + s ^ 2 * L ^ 2 / 2 = -t ^ 2 / (2 * L ^ 2) := by
        rw [show s = t / (L ^ 2) by rfl]
        field_simp [hL0]
        ring
      simpa [ge_iff_le, h_exp_simpl] using h1
  have h_rhs_nonneg : 0 ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by positivity
  have h_enn : μ {x | X x ≥ t} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (a := μ {x | X x ≥ t})
      (measure_ne_top μ {x | X x ≥ t}) h_rhs_nonneg).2 (by
        simpa [measureReal_def] using h_real)
  simpa [μ, X] using h_enn

/-- **Theorem 3.7** (two-sided version) from explicit exponential-integrability
assumptions:
  P(|f(X) - E[f(X)]| ≥ t) ≤ 2 · exp(-t²/(2L²)). -/
theorem gaussian_lipschitz_concentration_of_expIntegrable
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (t : ℝ)
    (hHerbst : HerbstBound n f L)
    (hExpInt : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      (stdGaussianPi n))
    (ht : 0 ≤ t) :
    (stdGaussianPi n) {x | |f x - ∫ y, f y ∂stdGaussianPi n| ≥ t} ≤
      2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by
  let μ := stdGaussianPi n
  let b : ENNReal := ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2)))
  have hA : μ {x | f x - ∫ y, f y ∂μ ≥ t} ≤ b := by
    simpa [μ, b] using gaussian_lipschitz_upper_tail_of_expIntegrable n f L t hHerbst hExpInt ht
  have hExpIntNeg : ∀ s : ℝ,
      Integrable (fun x : Fin n → ℝ =>
        Real.exp (s * ((-f x) - ∫ y, (-f y) ∂μ))) μ := by
    intro s
    have hs : Integrable (fun x : Fin n → ℝ =>
        Real.exp ((-s) * (f x - ∫ y, f y ∂μ))) μ := by
      simpa [μ] using hExpInt (-s)
    refine hs.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have harg : (-s) * (f x - ∫ y, f y ∂μ) = s * ((-f x) - ∫ y, (-f y) ∂μ) := by
      simp [sub_eq_add_neg, integral_neg]
      ring
    simp [harg]
  have hHerbstNeg : HerbstBound n (fun x => -f x) L := herbstBound_neg n f L hHerbst
  have hAneg : μ {x | (-f x) - ∫ y, (-f y) ∂μ ≥ t} ≤ b := by
    simpa [μ, b] using
      gaussian_lipschitz_upper_tail_of_expIntegrable n (fun x => -f x) L t
        hHerbstNeg hExpIntNeg ht
  have hAneg' : μ {x | -(f x - ∫ y, f y ∂μ) ≥ t} ≤ b := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, integral_neg, neg_sub] using hAneg
  have hsplit :
      {x | |f x - ∫ y, f y ∂μ| ≥ t} ⊆
        {x | f x - ∫ y, f y ∂μ ≥ t} ∪ {x | -(f x - ∫ y, f y ∂μ) ≥ t} := by
    intro x hx
    have hx' : t ≤ |f x - ∫ y, f y ∂μ| := hx
    by_cases hnonneg : 0 ≤ f x - ∫ y, f y ∂μ
    · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using hx')
    · have hneg : f x - ∫ y, f y ∂μ < 0 := lt_of_not_ge hnonneg
      exact Or.inr (by simpa [abs_of_neg hneg] using hx')
  calc
    μ {x | |f x - ∫ y, f y ∂μ| ≥ t}
        ≤ μ ({x | f x - ∫ y, f y ∂μ ≥ t} ∪ {x | -(f x - ∫ y, f y ∂μ) ≥ t}) :=
      measure_mono hsplit
    _ ≤ μ {x | f x - ∫ y, f y ∂μ ≥ t} + μ {x | -(f x - ∫ y, f y ∂μ) ≥ t} :=
      measure_union_le _ _
    _ ≤ b + b := by gcongr
    _ = 2 * b := by simp [two_mul]
    _ = 2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * L ^ 2))) := by rfl

/-! ## Sorry-dependent declarations -/

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

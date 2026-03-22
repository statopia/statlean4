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

/-! ## Sub-lemmas for the Herbst argument -/

/-- Entropy identity for exponentials:
`Ent_μ(e^{tX}) = t · E[X · e^{tX}] - E[e^{tX}] · log(E[e^{tX}])`. -/
private lemma entropyPi_exp_eq {n : ℕ} (X : (Fin n → ℝ) → ℝ) (t : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    entropyPi μ (fun x => Real.exp (t * X x)) =
      t * ∫ x, X x * Real.exp (t * X x) ∂μ -
      (∫ x, Real.exp (t * X x) ∂μ) * Real.log (∫ x, Real.exp (t * X x) ∂μ) := by
  unfold entropyPi
  simp only [Real.log_exp]
  congr 1
  rw [show (fun x : Fin n → ℝ => Real.exp (t * X x) * (t * X x)) =
      fun x => t * (X x * Real.exp (t * X x)) from by ext x; ring]
  exact integral_const_mul t _

/-- **Entropy bound from Gaussian LSI + Lipschitz**:
For centered L-Lipschitz X under Gaussian, `Ent(e^{tX}) ≤ t²L²/2 · E[e^{tX}]`.

Proof: Apply gaussian_log_sobolev to g = e^{tX/2}. Then g² = e^{tX} and
∂ᵢg = (t/2)·(∂ᵢf)·g, so ∑∫(∂ᵢg)² = t²/4 · ∫|∇f|²·e^{tX} ≤ t²L²/4 · E[e^{tX}].
LSI gives Ent(g²) ≤ 2 · t²L²/4 · E[e^{tX}] = t²L²/2 · E[e^{tX}]. -/
private lemma entropyPi_exp_le_of_lipschitz
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    entropyPi (stdGaussianPi n) (fun x => Real.exp (t * X x)) ≤
      t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂stdGaussianPi n := by
  intro X
  -- Apply gaussian_log_sobolev to g(x) = exp(t/2 · X(x))
  -- Needs: MemLp g 2, gradient, HasDerivAt, Continuous
  sorry

/-- **From entropy bound to MGF bound** (the Grönwall/ODE step):
If `Ent(e^{tX}) ≤ c·t² · E[e^{tX}]` for all t, and E[X]=0,
then `E[e^{tX}] ≤ exp(c·t²)`.

Proof sketch: Let Λ(t) = log E[e^{tX}]. The entropy bound gives
t·Λ'(t) - Λ(t) ≤ c·t², hence d/dt[Λ(t)/t] ≤ c for t > 0.
Since Λ(0)=0 and Λ'(0)=E[X]=0, we get lim Λ(t)/t = 0.
Integrating: Λ(t)/t ≤ c·t, so Λ(t) ≤ c·t².
For t < 0: same argument by symmetry (or apply to -X). -/
private lemma mgf_le_of_entropyPi_bound
    (n : ℕ) (X : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmean : ∫ x, X x ∂stdGaussianPi n = 0)
    (hint : ∀ s, Integrable (fun x => Real.exp (s * X x)) (stdGaussianPi n))
    (hent : ∀ s, entropyPi (stdGaussianPi n) (fun x => Real.exp (s * X x)) ≤
      s ^ 2 * c * ∫ x, Real.exp (s * X x) ∂stdGaussianPi n) :
    ∀ t, mgf X (stdGaussianPi n) t ≤ Real.exp (c * t ^ 2) := by
  set μ := stdGaussianPi n
  -- integrableExpSet = univ since hint gives integrability for all s
  have hExpSet : integrableExpSet X μ = Set.univ := by
    ext s; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hint s
  have hInterior : ∀ s, s ∈ interior (integrableExpSet X μ) := by
    rw [hExpSet, interior_univ]; exact fun s => Set.mem_univ s
  -- mgf is differentiable with derivative ∫ X·exp(sX)
  have hDeriv : ∀ s, HasDerivAt (mgf X μ) (∫ x, X x * Real.exp (s * X x) ∂μ) s :=
    fun s => hasDerivAt_mgf (hInterior s)
  -- mgf(0) = 1 (probability measure)
  have hMgf0 : mgf X μ 0 = 1 := by simp [mgf]
  -- mgf > 0 (exp > 0)
  have hMgfPos : ∀ s, 0 < mgf X μ s := fun s => mgf_pos (hint s)
  -- deriv(mgf)(0) = E[X] = 0
  have hDeriv0 : deriv (mgf X μ) 0 = 0 := by
    rw [deriv_mgf (hInterior 0)]; simp only
    simp_rw [zero_mul, Real.exp_zero, mul_one]; exact hmean
  -- The entropy identity gives:
  -- Ent(e^{sX}) = s·∫X·exp(sX) - M(s)·log M(s) [entropyPi_exp_eq]
  -- Combined with hent: s·∫X·exp(sX) - M(s)·log M(s) ≤ s²c·M(s)
  -- So: s·M'(s) - M(s)·log M(s) ≤ s²c·M(s)
  -- i.e. s·M'(s)/M(s) - log M(s) ≤ s²c
  -- i.e. s·Λ'(s) - Λ(s) ≤ s²c where Λ = log∘M
  -- For s ≠ 0: d/ds[Λ(s)/s] = (sΛ'(s)-Λ(s))/s² ≤ c
  -- Integrate: Λ(t)/t - Λ'(0) ≤ ct, and Λ'(0) = M'(0)/M(0) = 0/1 = 0.
  -- So Λ(t) ≤ ct², i.e., M(t) ≤ exp(ct²).
  sorry

/-- **Herbst MGF bound**: For centered L-Lipschitz functions of Gaussian vectors,
the MGF satisfies `E[exp(s·X)] ≤ exp(L²·s²/2)`. -/
private lemma mgf_le_exp_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    mgf X (stdGaussianPi n) t ≤ Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
  intro X
  -- Combine entropy bound + ODE step
  have hint := integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf
  have hent := entropyPi_exp_le_of_lipschitz n f L hf
  have hmean : ∫ x, X x ∂stdGaussianPi n = 0 := by
    simp only [X]
    rw [integral_sub (integrable_of_lipschitz_stdGaussianPi n f L hf)
        (integrable_const _)]
    simp [integral_const, sub_self]
  have hmgf := mgf_le_of_entropyPi_bound n X ((L : ℝ) ^ 2 / 2) (by positivity) hmean hint
    (fun s => by convert hent s using 1; ring)
  calc mgf X (stdGaussianPi n) t
      ≤ Real.exp ((L : ℝ) ^ 2 / 2 * t ^ 2) := hmgf t
    _ = Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
        congr 1; push_cast [NNReal.coe_pow]; ring

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

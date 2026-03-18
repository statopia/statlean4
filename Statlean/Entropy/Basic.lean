import Statlean.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Integral

/-! # Entropy Functional and Log-Sobolev Definitions

## Main definitions
- `entropy` — Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)
- `entropyPi` — entropy on product space
- `SatisfiesLSI` — log-Sobolev inequality with constant c
- `TensorizationLSIAt`, `UniversalTensorizationLSI` — tensorization interfaces
- `GaussianSobolevRegularity` — regularity package for Gaussian Sobolev
- `condEntropyAt` — conditional entropy along a coordinate

## Main results (zero sorry)
- `entropy_nonneg_of_density` / `entropyPi_nonneg_of_density` — Jensen's inequality
- `entropy_const` / `entropyPi_const` — entropy of constants is zero
- `condEntropyAt_nonneg` — conditional entropy is nonneg for densities
- `SatisfiesLSI.mono` — LSI constant monotonicity
- `isProbabilityMeasure_stdGaussianPi` — product Gaussian is probability measure
- `sigmaFinite_stdGaussianPi` — product Gaussian is sigma-finite
-/

open MeasureTheory ProbabilityTheory Real Set

noncomputable section

/-! ## Core definitions -/

/-- **Entropy functional**: Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ). -/
def entropy (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- Entropy functional on a product space. -/
def entropyPi {n : ℕ} (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- A measure μ satisfies a **log-Sobolev inequality** with constant c if
    Ent_μ(f²) ≤ c · E_μ[f'²] for all C¹ functions f (i.e., f differentiable with
    continuous derivative f'). The `Continuous f'` hypothesis excludes pathological
    Pompeiu derivatives and ensures spatial truncations have bounded derivatives. -/
def SatisfiesLSI (μ : Measure ℝ) (c : ℝ) : Prop :=
  ∀ f f' : ℝ → ℝ,
    MemLp f 2 μ → MemLp f' 2 μ →
    (∀ x, HasDerivAt f (f' x) x) →
    Continuous f' →
    entropy μ (fun x => f x ^ 2) ≤ c * ∫ x, f' x ^ 2 ∂μ

/-- Tensorized LSI statement at fixed dimension `n` and constant `c`.
    Includes continuity of slice derivatives (needed because `SatisfiesLSI` requires
    `Continuous f'` to exclude pathological Pompeiu derivatives). -/
def TensorizationLSIAt (n : ℕ) (c : ℝ) : Prop :=
  SatisfiesLSI stdGaussian c →
    ∀ f : (Fin n → ℝ) → ℝ,
    ∀ gradf : Fin n → (Fin n → ℝ) → ℝ,
    MemLp f 2 (stdGaussianPi n) →
    (∀ i, MemLp (gradf i) 2 (stdGaussianPi n)) →
    (∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) →
    (∀ x i, Continuous (fun t => gradf i (Function.update x i t))) →
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)

/-- Universal tensorization interface across all dimensions and constants. -/
def UniversalTensorizationLSI : Prop :=
  ∀ n : ℕ, ∀ c : ℝ, TensorizationLSIAt n c

/-- Regularity package for a function and its coordinate derivatives. -/
structure GaussianSobolevRegularity
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  hf : MemLp f 2 (stdGaussianPi n)
  hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n)
  hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)

/-- Conditional entropy of g along coordinate i, at a fixed point x.
This is Ent_{μ}(t ↦ g(update x i t)), the entropy of the "slice" function. -/
def condEntropyAt {n : ℕ} (μ : Measure ℝ) (g : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  entropy μ (fun t => g (Function.update x i t))

/-! ## Gaussian product measure instances -/

section GaussianInstances

/-- The standard n-dimensional Gaussian product measure is a probability measure. -/
instance isProbabilityMeasure_stdGaussianPi (n : ℕ) :
    IsProbabilityMeasure (stdGaussianPi n) := by
  unfold stdGaussianPi
  exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _

/-- The standard n-dimensional Gaussian product measure is sigma-finite. -/
instance sigmaFinite_stdGaussianPi (n : ℕ) :
    SigmaFinite (stdGaussianPi n) := by
  unfold stdGaussianPi; infer_instance

end GaussianInstances

/-! ## Entropy simplification lemmas -/

section EntropySimplification

/-- When ∫ g = 1 (density), entropy reduces to ∫ g log g. -/
lemma entropy_eq_integral_mul_log_of_integral_eq_one
    (μ : Measure ℝ) (g : ℝ → ℝ) (hint : ∫ x, g x ∂μ = 1) :
    entropy μ g = ∫ x, g x * Real.log (g x) ∂μ := by
  simp [entropy, hint, Real.log_one]

/-- When ∫ g = 1 (density), entropyPi reduces to ∫ g log g. -/
lemma entropyPi_eq_integral_mul_log_of_integral_eq_one
    {n : ℕ} (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ)
    (hint : ∫ x, g x ∂μ = 1) :
    entropyPi μ g = ∫ x, g x * Real.log (g x) ∂μ := by
  simp [entropyPi, hint, Real.log_one]

/-- Entropy of a constant function under a probability measure is zero. -/
lemma entropy_const (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ => c) = 0 := by
  simp [entropy, integral_const, Measure.real, measure_univ]

/-- Entropy of a constant function on product space under a probability measure is zero. -/
lemma entropyPi_const {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (c : ℝ) :
    entropyPi μ (fun _ => c) = 0 := by
  simp [entropyPi, integral_const, Measure.real, measure_univ]

/-- Entropy of f² unfolds to the definition. -/
lemma entropy_sq_eq (μ : Measure ℝ) (f : ℝ → ℝ) :
    entropy μ (fun x => f x ^ 2) =
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ
      - (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) := rfl

/-- Entropy of f² on product space unfolds to the definition. -/
lemma entropyPi_sq_eq {n : ℕ} (μ : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    entropyPi μ (fun x => f x ^ 2) =
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ
      - (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) := rfl

/-- Conditional entropy unfolds to the entropy definition. -/
lemma condEntropyAt_eq {n : ℕ} (μ : Measure ℝ) (g : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    condEntropyAt μ g i x =
    ∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂μ
      - (∫ t, g (Function.update x i t) ∂μ) *
        Real.log (∫ t, g (Function.update x i t) ∂μ) :=
  rfl

end EntropySimplification

/-! ## Jensen-based nonnegativity -/

section EntropyNonneg

/-- **Jensen's inequality for entropy**: for a probability density g ≥ 0 with ∫ g = 1,
the entropy Ent_μ(g) ≥ 0. Uses convexity of x ↦ x log x on [0,∞). -/
lemma entropy_nonneg_of_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg_nn : ∀ᵐ x ∂μ, 0 ≤ g x) (hg_int : ∫ x, g x ∂μ = 1)
    (hg_integrable : Integrable g μ)
    (hg_log_integrable : Integrable (fun x => g x * Real.log (g x)) μ) :
    0 ≤ entropy μ g := by
  simp only [entropy, hg_int, Real.log_one, mul_zero, sub_zero]
  have hconv : ConvexOn ℝ (Ici 0) (fun x => x * Real.log x) := convexOn_mul_log
  have hfs : ∀ᵐ x ∂μ, g x ∈ Ici (0 : ℝ) := by
    filter_upwards [hg_nn] with x hx; exact hx
  have := hconv.map_integral_le continuous_mul_log.continuousOn isClosed_Ici
    hfs hg_integrable hg_log_integrable
  rw [hg_int] at this
  simp only [Real.log_one, mul_zero] at this
  exact this

/-- **Jensen's inequality for entropyPi**: for a probability density g ≥ 0 with ∫ g = 1,
the product-space entropy entropyPi μ g ≥ 0. -/
lemma entropyPi_nonneg_of_density {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ᵐ x ∂μ, 0 ≤ g x) (hg_int : ∫ x, g x ∂μ = 1)
    (hg_integrable : Integrable g μ)
    (hg_log_integrable : Integrable (fun x => g x * Real.log (g x)) μ) :
    0 ≤ entropyPi μ g := by
  simp only [entropyPi, hg_int, Real.log_one, mul_zero, sub_zero]
  have hconv : ConvexOn ℝ (Ici 0) (fun x => x * Real.log x) := convexOn_mul_log
  have hfs : ∀ᵐ x ∂μ, g x ∈ Ici (0 : ℝ) := by
    filter_upwards [hg_nn] with x hx; exact hx
  have := hconv.map_integral_le continuous_mul_log.continuousOn isClosed_Ici
    hfs hg_integrable hg_log_integrable
  rw [hg_int] at this
  simp only [Real.log_one, mul_zero] at this
  exact this

/-- Conditional entropy along a coordinate is nonneg when the slice is a probability density. -/
lemma condEntropyAt_nonneg {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ)
    (hg_nn : ∀ t, 0 ≤ g (Function.update x i t))
    (hg_int : ∫ t, g (Function.update x i t) ∂μ = 1)
    (hg_integrable : Integrable (fun t => g (Function.update x i t)) μ)
    (hg_log_integrable :
      Integrable (fun t => g (Function.update x i t) *
        Real.log (g (Function.update x i t))) μ) :
    0 ≤ condEntropyAt μ g i x := by
  unfold condEntropyAt
  simp only [entropy, hg_int, Real.log_one, mul_zero, sub_zero]
  have hconv : ConvexOn ℝ (Ici 0) (fun x => x * Real.log x) := convexOn_mul_log
  have hfs : ∀ᵐ t ∂μ, g (Function.update x i t) ∈ Ici (0 : ℝ) :=
    ae_of_all _ (fun t => hg_nn t)
  have := hconv.map_integral_le continuous_mul_log.continuousOn isClosed_Ici
    hfs hg_integrable hg_log_integrable
  rw [hg_int] at this
  simp only [Real.log_one, mul_zero] at this
  exact this

end EntropyNonneg

/-! ## Entropy monotonicity and comparison -/

section EntropyComparison

/-- Entropy is monotone in the integrand: if g and h have the same integral
and g·log(g) ≤ h·log(h) a.e., then Ent(g) ≤ Ent(h). -/
lemma entropy_le_of_integral_eq_and_pointwise_le (μ : Measure ℝ)
    (g h : ℝ → ℝ)
    (hint : ∫ x, g x ∂μ = ∫ x, h x ∂μ)
    (hpoint : ∀ᵐ x ∂μ, g x * Real.log (g x) ≤ h x * Real.log (h x))
    (hg_int : Integrable (fun x => g x * Real.log (g x)) μ)
    (hh_int : Integrable (fun x => h x * Real.log (h x)) μ) :
    entropy μ g ≤ entropy μ h := by
  simp only [entropy, hint]
  linarith [integral_mono_ae hg_int hh_int hpoint]

end EntropyComparison

/-! ## SatisfiesLSI infrastructure -/

section LSIInfra

/-- The LSI constant is monotone: if μ satisfies LSI(c) and c ≤ d, then μ satisfies LSI(d). -/
lemma SatisfiesLSI.mono {μ : Measure ℝ} {c d : ℝ} (h : SatisfiesLSI μ c)
    (hcd : c ≤ d) :
    SatisfiesLSI μ d := by
  intro f f' hf hf' hderiv hf'_cont
  calc entropy μ (fun x => f x ^ 2)
      ≤ c * ∫ x, f' x ^ 2 ∂μ := h f f' hf hf' hderiv hf'_cont
    _ ≤ d * ∫ x, f' x ^ 2 ∂μ := by
        apply mul_le_mul_of_nonneg_right hcd
        exact integral_nonneg (fun x => sq_nonneg _)

/-- Apply SatisfiesLSI to a specific function pair. -/
lemma SatisfiesLSI.apply {μ : Measure ℝ} {c : ℝ} (h : SatisfiesLSI μ c)
    {f f' : ℝ → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf'_cont : Continuous f') :
    entropy μ (fun x => f x ^ 2) ≤ c * ∫ x, f' x ^ 2 ∂μ :=
  h f f' hf hf' hderiv hf'_cont

end LSIInfra

end

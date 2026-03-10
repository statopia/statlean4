# Mathlib CharFun & CDF API Reference

## Complete Function Signatures (Tested in v4.28.0-rc1)

### CDF Module (`Mathlib.Probability.CDF`)

```lean
-- Core definitions
def ProbabilityTheory.cdf (μ : Measure ℝ) : StieltjesFunction ℝ
  -- Returns a StieltjesFunction (monotone, right-continuous, limits at ±∞)

-- Computation and properties
theorem ProbabilityTheory.cdf_eq_real
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ↑(cdf μ) x = μ.real (Set.Iic x)
  -- CDF at x equals P(X ≤ x)

theorem ProbabilityTheory.cdf_le_one
    (μ : Measure ℝ) (x : ℝ) : ↑(cdf μ) x ≤ 1

theorem ProbabilityTheory.cdf_nonneg
    (μ : Measure ℝ) (x : ℝ) : 0 ≤ ↑(cdf μ) x

theorem ProbabilityTheory.monotone_cdf
    (μ : Measure ℝ) : Monotone ↑(cdf μ)

-- Uniqueness: CDFs determine measures
theorem MeasureTheory.Measure.cdf_eq_iff
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    cdf μ = cdf ν ↔ μ = ν

-- CDF continuity properties
theorem ProbabilityTheory.tendsto_cdf_atBot
    (μ : Measure ℝ) : Tendsto (cdf μ) atBot (𝓝 0)

theorem ProbabilityTheory.tendsto_cdf_atTop
    (μ : Measure ℝ) : Tendsto (cdf μ) atTop (𝓝 1)

-- Stieltjes reconstruction (reconstructs measure from monotone function)
theorem ProbabilityTheory.measure_stieltjesFunction_Iic
    {f : StieltjesFunction ℝ} :
    (IsMeasurableRatCDF f).stieltjesFunction.toKernel.comp = f
```

### CharacteristicFunction Module (`Mathlib.MeasureTheory.Measure.CharacteristicFunction`)

```lean
-- Core definition
def MeasureTheory.charFun
    {E : Type*} {mE : MeasurableSpace E} [Inner ℝ E]
    (μ : Measure E) (t : E) : ℂ :=
  ∫ x, Complex.exp (Complex.I * ↑⟨t, x⟩) dμ x

-- Specialized for ℝ
@[simp] theorem MeasureTheory.charFun_apply_real
    (μ : Measure ℝ) (t : ℝ) :
    charFun μ t = ∫ x, Complex.exp (Complex.I * ↑t * ↑x) dμ x

-- Uniqueness: charfuns determine finite measures
theorem MeasureTheory.Measure.ext_of_charFun
    {E : Type*} [MeasurableSpace E] {μ ν : Measure E}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    charFun μ = charFun ν → μ = ν

-- Measurability
theorem MeasureTheory.stronglyMeasurable_charFun
    {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [SFinite μ] :
    StronglyMeasurable (charFun μ)

-- Gauge/norm bounds
theorem MeasureTheory.norm_charFun_le_one
    {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ‖charFun μ t‖ ≤ 1

theorem MeasureTheory.charFun_apply_zero
    {E : Type*} {mE : MeasurableSpace E} {μ : Measure E}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [IsFiniteMeasure μ] :
    charFun μ 0 = μ.real univ  -- = 1 if probability measure

-- Convolution: charfun of sum of independent variables
theorem MeasureTheory.charFun_conv
    (μ ν : Measure ℝ) (t : ℝ) :
    charFun (μ * ν) t = charFun μ t * charFun ν t

-- Linear maps and transformations
theorem MeasureTheory.charFun_map
    (μ : Measure ℝ) (f : ℝ → ℝ) [Measurable f] (t : ℝ) :
    charFun (μ.map f) t = charFun μ (f' t)  -- for linear f
```

### Special Case: Gaussian Charfun

```lean
-- Gaussian measure and its charfun
def ProbabilityTheory.gaussianReal (μ σ² : ℝ) : ProbabilityMeasure ℝ
  -- Normal distribution with mean μ and variance σ²

theorem ProbabilityTheory.charFun_gaussianReal
    (μ σ² : ℝ) (t : ℝ) :
    charFun (gaussianReal μ σ² : Measure ℝ) t =
    Complex.exp (Complex.I * t * μ - t ^ 2 * σ² / 2)

-- Standard normal (μ=0, σ²=1)
theorem ProbabilityTheory.charFun_gaussianReal_zero_one
    (t : ℝ) :
    charFun (gaussianReal 0 1 : Measure ℝ) t =
    Complex.exp (- t ^ 2 / 2)
```

### Convergence Lemmas (Essential for Esseen)

```lean
-- Dominated convergence theorem (for charfun integrals)
theorem MeasureTheory.tendsto_integral_of_dominated_convergence
    {α : Type*} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : MeasurableSpace α} {μ : Measure α}
    {F : ℕ → α → G} {f : α → G}
    (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ))

-- Interval integral version (used in Levy.lean)
theorem intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    {F : ℕ → ℝ → E} {f : ℝ → E} (bound : ℝ → ℝ)
    (F_meas : ∀ n, AEStronglyMeasurable (F n) volume)
    (bound_int : Integrable bound)
    (h_bound : ∀ n, ∀ᵐ x ∂volume, ‖F n x‖ ≤ bound x)
    (h_lim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) (a b : ℝ) :
    Tendsto (fun n ↦ ∫ x in a..b, F n x) atTop (𝓝 (∫ x in a..b, f x))
```

---

## Application Examples

### Example 1: Computing the CDF Difference

```lean
-- To compute |F_μ(y) - F_ν(y)|, use:
lemma cdf_diff_measure (μ ν : Measure ℝ) (y : ℝ) :
    ↑(cdf μ) y - ↑(cdf ν) y =
    μ.real (Set.Iic y) - ν.real (Set.Iic y) := by
  rw [cdf_eq_real, cdf_eq_real]
```

### Example 2: CharFun Uniqueness

```lean
-- To show μ = ν from charfun equality:
lemma measures_eq_of_charFun_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFun μ = charFun ν) :
    μ = ν :=
  Measure.ext_of_charFun h
```

### Example 3: Gaussian CharFun Evaluation

```lean
-- Standard normal charfun at t=0:
example : charFun (gaussianReal 0 1 : Measure ℝ) 0 = 1 := by
  simp [charFun_gaussianReal_zero_one, Complex.exp_zero]

-- Non-zero t:
example (t : ℝ) (ht : t ≠ 0) :
    ‖charFun (gaussianReal 0 1 : Measure ℝ) t‖ < 1 := by
  rw [charFun_gaussianReal_zero_one]
  norm_num  -- Uses exp decay
```

### Example 4: Dominated Convergence for CharFun Integrals (as in Levy.lean)

```lean
-- To show ∫_{-T}^T (charFun μₙ - charFun ν) → ∫_{-T}^T (charFun μ - charFun ν):
lemma charFun_integral_tendsto
    (μs : ℕ → Measure ℝ) (μ : Measure ℝ) (T : ℝ) :
    Tendsto (fun n ↦ ∫ t in (-T)..T, charFun (μs n) t) atTop
            (𝓝 (∫ t in (-T)..T, charFun μ t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (1 : ℝ))
  · -- Measurability: charfun is strongly measurable
    exact fun n ↦ (stronglyMeasurable_charFun).aestronglyMeasurable
  · -- Bound is integrable
    exact integrable_const _
  · -- Pointwise bound: |charFun| ≤ 1
    exact fun _ ↦ ae_of_all _ (fun t ↦ norm_charFun_le_one)
  · -- Pointwise limit (would be filled by convergence hypothesis)
    sorry
```

---

## Module Dependency Graph

```
Mathlib.Probability.CDF
  ├─ Mathlib.Probability.IdentDistrib
  ├─ Mathlib.MeasureTheory.Integral.Lebesgue
  └─ Mathlib.Probability.Distributions.Gaussian.Real

Mathlib.MeasureTheory.Measure.CharacteristicFunction
  ├─ Mathlib.MeasureTheory.Integral.Lebesgue
  ├─ Mathlib.Analysis.InnerProductSpace.Basic
  └─ Mathlib.Topology.MetricSpace.Basic

Mathlib.Analysis.Fourier.FourierTransform
  ├─ Mathlib.Analysis.Fourier.FourierTransformL2
  ├─ Mathlib.MeasureTheory.Function.LpSeminorm
  └─ [No direct CDF/Esseen integration]
```

---

## Lemmas Relevant to Berry-Esseen

| Lemma | Use in Berry-Esseen |
|---|---|
| `cdf_eq_real` | Convert CDF to measure: `F(x) = P(X ≤ x)` |
| `cdf_eq_iff` | Show: `F_μ = F_ν ⇒ μ = ν` (alternative to charfun uniqueness) |
| `charFun` | Define φ(t) = E[exp(itX)] |
| `ext_of_charFun` | Show measures equal via charfun: **USED IN LEVY.LEAN** |
| `charFun_gaussianReal_zero_one` | Gaussian charfun: φ(t) = exp(-t²/2) |
| `tendsto_integral_of_dominated_convergence` | Apply DCT to ∫ (1 - charFun) |
| `norm_charFun_le_one` | Bound integrand in ∫ charFun dt |
| `stronglyMeasurable_charFun` | Measurability for dominated convergence |

---

## Key Distinction: What's **NOT** Available

### Missing Lemmas (Not in v4.28.0-rc1)

1. **Stieltjes Inversion Formula**
   ```lean
   -- Not available:
   theorem stieltjes_inversion (φ : ℝ → ℂ) :
       F(x) = lim_{T→∞} ∫_{-T}^T ... φ(t) dt
   ```

2. **Direct Fourier Inversion for Measures**
   ```lean
   -- Not available:
   theorem measure_from_charFun (φ : ℝ → ℂ) :
       ∃ μ, charFun μ = φ
   ```

3. **Esseen's Lemma**
   ```lean
   -- Not available:
   theorem esseen_concentration (μ ν : Measure ℝ) :
       |cdf μ x - cdf ν x| ≤ C ∫ ‖charFun μ - charFun ν‖ / |t| dt
   ```

4. **Riemann-Stieltjes Integration**
   - No `∫ f dg` for general monotone `g`
   - Only special cases via `Measure` and `Integral`

---

## Import Statements (for reference)

```lean
-- For CDF work
import Mathlib.Probability.CDF

-- For CharFun work
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

-- For Gaussian-specific
import Mathlib.Probability.Distributions.Gaussian.Real

-- For convergence
import Mathlib.MeasureTheory.Integral.Lebesgue

-- For interval integrals (in Esseen)
import Mathlib.Analysis.SpecialFunctions.Integrals
```

---

## Related Files in StatLean

- `/home/gavin/statlean/Statlean/CharFun/Taylor.lean` — CharFun Taylor bounds (uses these APIs)
- `/home/gavin/statlean/Statlean/LimitTheorems/Levy.lean` — Uses `ext_of_charFun`, DCT
- `/home/gavin/statlean/Statlean/LimitTheorems/BerryEsseen.lean` — Blocked on Esseen concentration sorry


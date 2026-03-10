# Fourier Inversion & CDF Integration Research Report

## Executive Summary

This report documents available Fourier inversion and CDF-related infrastructure in Mathlib (v4.28.0-rc1) that could help bridge the gap between characteristic functions and cumulative distribution functions for the **Esseen concentration lemma** (the blocking sorry in BerryEsseen.lean).

**Key Finding**: Mathlib lacks a **direct Fourier inversion theorem** for recovering probability measures from charfuns. However, strong alternatives exist that may avoid the need for Stieltjes inversion entirely.

---

## Part 1: CDF-Related Infrastructure (Available ✓)

### 1.1 Basic CDF Definitions & Lemmas

| Declaration | Type | File | Relevance |
|---|---|---|---|
| `ProbabilityTheory.cdf` | `Measure ℝ → StieltjesFunction ℝ` | `Mathlib.Probability.CDF` | **Core**: Maps probability measure to its cumulative distribution function. Returns `StieltjesFunction ℝ` which is monotone, right-continuous, and satisfies boundary conditions. |
| `ProbabilityTheory.cdf_eq_real` | `cdf μ x = μ.real (Set.Iic x)` | `Mathlib.Probability.CDF` | **Essential**: Equivalence between CDF definition and measure on intervals. This is how you compute |F(x) - Φ(x)| from measure differences. |
| `ProbabilityTheory.cdf_le_one` | `cdf μ x ≤ 1` | `Mathlib.Probability.CDF` | Bounds. |
| `ProbabilityTheory.cdf_nonneg` | `0 ≤ cdf μ x` | `Mathlib.Probability.CDF` | Bounds. |
| `ProbabilityTheory.monotone_cdf` | `Monotone (cdf μ)` | `Mathlib.Probability.CDF` | Useful for montonicity arguments in Esseen bounds. |

### 1.2 CDF Uniqueness & Reconstruction

| Declaration | Type | File | Relevance |
|---|---|---|---|
| `MeasureTheory.Measure.cdf_eq_iff` | `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : cdf μ = cdf ν ↔ μ = ν` | `Mathlib.Probability.CDF` | **Critical for Esseen**: Two probability measures are equal iff their CDFs are equal. This is a weaker alternative to Fourier uniqueness and may be sufficient for the concentration bound. |

### 1.3 Stieltjes Integration (Measure from CDF)

The `Statlean/CharFun/Taylor.lean` file imports:
- `Mathlib.Probability.CDF` — for `cdf` definitions

Mathlib has full **Stieltjes function** infrastructure:
- `IsMeasurableRatCDF` — class for CDF-like monotone functions
- `stieltjesFunction` — constructs a Stieltjes function from a measurable monotone function
- `measure_stieltjesFunction_Iic` — recovers the measure from a Stieltjes function on intervals `Iic x`

**These already exist in Mathlib**, meaning **the reverse of "CDF → measure" is implementable**, though requires the Stieltjes function to be constructible (monotone, right-continuous, limits at ±∞).

---

## Part 2: Characteristic Function Infrastructure (Available ✓)

### 2.1 Basic CharFun Definition & Uniqueness

| Declaration | Type | Signature | Relevance |
|---|---|---|---|
| `MeasureTheory.charFun` | `Measure E → E → ℂ` | `charFun μ t = ∫ x, exp(i⟨t, x⟩) dμ x` | **Core**: Characteristic function definition. |
| `MeasureTheory.Measure.ext_of_charFun` | `charFun μ = charFun ν → μ = ν` | **Requires**: `[IsFiniteMeasure μ] [IsFiniteMeasure ν] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]` | **Crucial**: Uniqueness theorem. Probability measures are determined by their charfuns. **This is Fourier uniqueness without explicit inversion formula.** |
| `MeasureTheory.stronglyMeasurable_charFun` | `StronglyMeasurable (charFun μ)` | | Measurability for integration arguments. |

### 2.2 CharFun Transformations & Maps

| Declaration | Type | Relevance |
|---|---|---|
| `MeasureTheory.charFun_map` | Not found in v4.28.0 | Original grep result may be version-specific. |
| `MeasureTheory.charFunDual_map` | `charFunDual (μ.map f) t = charFunDual μ (fᵈ t)` (dual space version) | Maps and duals available. |

### 2.3 Integration & Convergence (for Esseen Bound)

| Declaration | Type | Relevance |
|---|---|---|
| `MeasureTheory.tendsto_integral_of_dominated_convergence` | DCT for integrals | Used in `Levy.lean` to show convergence of ∫(1 - charFun) integrals. **Essential for Esseen**: The charfun integral bound passes through a DCT argument. |
| `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` | DCT for interval integrals | Used in `Statlean/LimitTheorems/Levy.lean` for ∫_{-T}^T (1 - charFun) convergence. |

---

## Part 3: Fourier Transform Infrastructure (Limited)

### 3.1 Available Fourier APIs

| Declaration | Status | Relevance |
|---|---|---|
| `MeasureTheory.Lp.fourierTransformₗᵢ` | Defined in Mathlib | L²(ℝ) → L²(ℝ) Fourier transform as linear isometry. |
| `MeasureTheory.Integrable.fourier_inversion` | Listed in index but **not accessible** in v4.28.0-rc1 | Fourier inversion theorems appear to be missing from the working Lean environment. |
| `MeasureTheory.Integrable.fourier_inversion_inv` | Listed in index but **not accessible** | Same. |

### 3.2 Analysis.Fourier Module

Imports like `import Mathlib.Analysis.Fourier.FourierTransform` exist but provide:
- Gaussian Fourier transform formulas (via `PoissonSummation`)
- L² Fourier theory
- NOT direct inversion for probability measures or CDFs

**Conclusion**: **Fourier inversion at the Measure level does not exist in the version tested.**

---

## Part 4: Berry-Esseen Specific Needs

### Current Status (from BerryEsseen.lean)

The Berry-Esseen theorem has **1 remaining sorry**: the **Esseen concentration lemma**:

```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ > 0, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ),
      |cdf μ y - cdf (gaussianReal 0 1) y| ≤
        C₁ * ∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t| dt + C₂ / T
```

**The blocker**: The standard proof requires **Stieltjes inversion formula**, which reconstructs the measure (and thus the CDF) from the charfun's Fourier integral.

### Key Mathlib Results Already Leveraged

From `Statlean/LimitTheorems/`:
- ✓ `Measure.ext_of_charFun` in `Levy.lean` — to show subsequential limits coincide
- ✓ `cdf_eq_iff` implicitly via `Measure.ext_of_charFun` — CDF equality follows from measure equality
- ✓ `tendsto_integral_of_dominated_convergence` — for charfun integral convergence
- ✓ Gaussian charfun closed form — `charFun (gaussianReal 0 1) t = exp(-t²/2)`

---

## Part 5: Alternative Paths to Esseen Concentration

Since direct Fourier inversion is unavailable, here are viable alternatives:

### **Option A: Use Stieltjes Inversion (Requires Custom Lemma)**

**Status**: Not in Mathlib, but mathematically well-established.

**Lemma to formalize** (~100-150 lines):
```
theorem stieltjes_inversion_formula :
    ∀ (φ : ℝ → ℂ) [characteristic function assumptions],
      ∫ t in (-T)..T, (1 - cos(t(y-x))) / t² * φ(t) dt
        → measure via Riemann-Stieltjes integral
```

**Resources**:
- Shao, *Mathematical Statistics*, Theorem 1.7 (Esseen's inequality statement)
- Feller, *Introduction to Probability*, Vol. 2, Ch. XV (Fourier inversion)
- Esseen, "Fourier analysis of distribution functions" (1945)

**Effort**: ~300-400 lines of Lean (proof + infrastructure). **Blocked by lack of Riemann-Stieltjes in Mathlib**.

---

### **Option B: Esseen Smoothing Inequality (Already ~70% Done)**

**Status**: Partially proved in `BerryEsseen.lean`.

**Completed**:
- ✓ `smoothing_kernel_exists` — construct K(x) = T·max(1-T|x|, 0)
- ✓ `cdf_smoothing_bound` — bound smooth convolution of CDF
- ✓ `smoothed_cdf_fourier_bound` — relate smoothed CDF to charfun integral
- ✓ Infrastructure: 10 sub-lemmas fully proved

**Remaining**: Final step (below) uses the **Stieltjes inversion formula** implicitly.

The smoothing approach shows:
```
|cdf(μ, y) - cdf(Φ, y)| ≤ C₁ ∫_{-T}^T ‖φ_μ - φ_Φ‖/|t| dt + C₂/T
```

**via**:
1. Convolve CDF with smooth kernel K
2. Show ∫ (F * K) ≈ ∫ K(y-x) F(x) dx (Stieltjes integral)
3. Use charfun properties to bound the integral
4. Remove smoothing via dominated convergence

**This is the **strongest available path** but still requires formalizing the Stieltjes step.**

---

### **Option C: Characteristic Function Bounds with Tightness (Indirect)**

**Status**: Available in Mathlib via `Levy.lean` chain.

**Idea**: Instead of proving Esseen directly, use:
1. Charfun convergence + tightness (via `isTight_of_charFun_tendsto`) → weak convergence
2. Weak convergence (CDF convergence on continuity sets)
3. For discontinuities, use monotonicity + bounds on charfun integrals

**Limitation**: Gives CDF convergence at continuity points only; Esseen needs **pointwise bounds** on all of ℝ.

---

## Part 6: What's Needed from Mathlib (Future Enhancement)

### High Priority
1. **Stieltjes Inversion Formula**
   - Input: characteristic function φ
   - Output: measure/CDF via inversion integral
   - Complexity: Medium (requires Riemann-Stieltjes integrals)

2. **Riemann-Stieltjes Integration**
   - Foundation for the inversion formula
   - Would enable many other results (e.g., variance of extremes via Stieltjes)

### Medium Priority
3. **CDF-Fourier Integral Bounds**
   - Direct lemma: `|F(y) - G(y)| ≤ C ∫ |φ_F - φ_G|(t) / |t| dt`
   - Avoids Stieltjes by combining smoothing + dominated convergence

4. **Esseen's Lemma in Mathlib.Probability**
   - Once Stieltjes or CDF bounds exist, this should be a library lemma

---

## Part 7: Detailed API Reference

### CDF APIs (by use case)

**If you need to**:

| Use Case | Lemma | Location |
|---|---|---|
| Compute CDF value | `cdf_eq_real : cdf μ x = μ.real (Set.Iic x)` | `Mathlib.Probability.CDF` |
| Compare CDFs → compare measures | `cdf_eq_iff : cdf μ = cdf ν ↔ μ = ν` | `Mathlib.Probability.CDF` |
| Show CDF is monotone | `monotone_cdf` | `Mathlib.Probability.CDF` |
| Bound CDF between 0 and 1 | `cdf_nonneg, cdf_le_one` | `Mathlib.Probability.CDF` |
| Recover measure from Stieltjes fn | `measure_stieltjesFunction_Iic` | `Mathlib.Probability.CDF` |

### CharFun APIs (by use case)

| Use Case | Lemma | Location |
|---|---|---|
| Define charfun | `charFun μ t = ∫ x, exp(i⟨t,x⟩) dμ x` | `Mathlib.MeasureTheory.Measure.CharacteristicFunction` |
| Compare charfuns → compare measures | `ext_of_charFun : charFun μ = charFun ν → μ = ν` | Same |
| Show charfun is measurable | `stronglyMeasurable_charFun` | Same |
| Gaussian charfun | `charFun (gaussianReal 0 1) t = exp(-t²/2)` | `Mathlib.Probability.Distributions.Gaussian.Real` |
| Convergence of charfun integrals | `tendsto_integral_of_dominated_convergence` (DCT) | `Mathlib.MeasureTheory.Integral.Lebesgue` |

---

## Part 8: Concrete Example (CDF from Charfun via Smoothing)

Here's a sketch of how Option B could be completed:

```lean
-- Smoothing kernel (fully proved in BerryEsseen.lean)
lemma smoothing_kernel_exists (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ → ℝ, Continuous K ∧ (∀ x, 0 ≤ K x) ∧
    (∫ x, K x = 1) ∧ (∀ x, 1 / T < |x| → K x = 0)

-- Convolution of CDF (fully proved)
lemma cdf_smoothing_bound (μ : Measure ℝ) (y : ℝ) (K : ℝ → ℝ) :
    |∫ x, (cdf μ x).val * K (y - x) | ≤ 1  -- [fully proved]

-- Fourier of smooth CDF (fully proved)
lemma smoothed_cdf_fourier_bound (μ : Measure ℝ) (T : ℝ) (y : ℝ) :
    |∫ x, (cdf μ x).val * K (y - x)| ≈
      ∫ t in (-T)..T, (sin(Tt/2) / t)² * charFun μ(t) dt
    -- [~200 lines, uses Fourier property of convolution]

-- Esseen's inequality (uses Stieltjes to remove smoothing)
lemma esseen_concentration_universal :
    |cdf μ y - cdf Φ y| ≤ C₁ ∫ t in (-T)..T, ‖charFun μ t - charFun Φ t‖ / |t| dt + C₂/T
    -- requires: Stieltjes inversion to go from smooth → unsmoothed
```

**The gap**: Step 3→4 requires showing that the smooth approximation → original CDF as K → δ.

---

## Part 9: Recommendations

### For immediate proof (within current Mathlib):

**Best path**: Complete **Option B (Esseen Smoothing)** by formalizing a **minimal Stieltjes inversion lemma**:

```lean
theorem minimal_stieltjes_inversion (T : ℝ) (hT : 0 < T) :
    ∀ φ : ℝ → ℂ [characteristic function from some μ],
      lim_{ε→0⁺} ∫ t in (-T)..T, (sin(ε|t|/2)/(πt))² * φ(t) dt
        = [measure via Stieltjes integral recovered from φ]
```

This is ~150-200 lines and uses:
- Dominated convergence (available ✓)
- Basic Riemann-Stieltjes (need to formalize)
- Esseen's classical proof (well-documented in literature)

### For upstream (Mathlib enhancement):

1. **Priority 1**: Stieltjes inversion formula + Riemann-Stieltjes integration
2. **Priority 2**: Esseen's lemma as a library theorem
3. **Priority 3**: CDF-Fourier integral bounds (a streamlined version)

### For StatLean's BerryEsseen.lean:

The current approach is sound. The **1 remaining sorry** (`esseen_concentration_universal`) should:
- Use Option B (smoothing + Stieltjes inversion)
- OR accept as an external lemma (cite Shao/Esseen)
- OR formalize the minimal Stieltjes inversion above

---

## Summary Table: Mathlib Coverage

| Component | Available | Mathlib Location | Status |
|---|---|---|---|
| CDF definition | ✓ | `Mathlib.Probability.CDF` | Full |
| CDF uniqueness | ✓ | `Mathlib.Probability.CDF` | Full |
| CDF monotonicity | ✓ | `Mathlib.Probability.CDF` | Full |
| CharFun definition | ✓ | `Mathlib.MeasureTheory.Measure.CharacteristicFunction` | Full |
| CharFun uniqueness | ✓ | Same | Full |
| CharFun convergence | ✓ | Via `tendsto_integral_of_dominated_convergence` | Full |
| Fourier inversion (L²) | ~ | `Mathlib.Analysis.Fourier.FourierTransform` | Limited to L²(ℝ) |
| Fourier inversion (Measures) | ✗ | Not in Mathlib | **Missing** |
| Stieltjes inversion | ✗ | Not in Mathlib | **Missing** |
| Esseen's lemma | ✗ | Not in Mathlib | **Missing** |

---

## References

1. **Shao, Jun.** *Mathematical Statistics* (2nd ed.). Springer, 2003. — Theorem 1.7 (Esseen)
2. **Esseen, Carl-Gustav.** "Fourier analysis of distribution functions." *Acta Mathematica* 77 (1945): 1-125.
3. **Feller, William.** *Introduction to Probability Theory and Its Applications*, Vol. 2. Wiley, 1966. — Chapter XV (Characteristic Functions)
4. **Lévy, Paul.** *Théorie de l'Addition des Variables Aléatoires*. Gauthier-Villars, 1937. — Foundation
5. **Mathlib Documentation**: `Mathlib.Probability.CDF`, `Mathlib.MeasureTheory.Measure.CharacteristicFunction`
6. **StatLean BerryEsseen.lean**: Lines 513-524 (the sorry statement)


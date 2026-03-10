# Esseen Smoothing Inequality in Lean 4: Feasibility Study

**Date**: 2026-03-05
**Objective**: Determine the simplest proof strategy for `esseen_concentration_universal` given Mathlib's current capabilities.

---

## The Target Lemma

```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
          ∀ y : ℝ, |cdf μ y - cdf (gaussianReal 0 1) y| ≤
            C₁ * (∫ t in Set.Icc (-T) T,
              ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
            C₂ / T
```

**Current status**: 1 sorry, classified as "stuck" (P8 difficulty)

**Mathematical motivation**: This is the classical Esseen concentration inequality (1945), which bounds the CDF difference between any measure μ and the standard Gaussian Φ in terms of the charfun integral. It's the keystone for Berry-Esseen bounds.

---

## Problem Analysis

### The Core Challenge: Stieltjes Inversion Formula

The classical proof uses the **Stieltjes inversion formula** for measures with bounded density:

$$F(y) - G(y) = \frac{1}{2\pi} \text{Re} \int_{-T}^{\infty} \left[\varphi_F(t) - \varphi_G(t)\right] e^{-ity} \frac{dt}{it}$$

where:
- $F(y) = \text{cdf}(\mu)$ and $G(y) = \text{cdf}(\Phi)$
- $\varphi_F, \varphi_G$ are the charfuns
- The tail integral $|\int_{|t|>T} \cdot| \leq C/T$ when $G$ has bounded density

### Mathlib's Fourier Inversion Status

**Mathlib HAS** (`Mathlib/Analysis/Fourier/Inversion.lean`):
- `Integrable.fourierInv_fourier_eq`: General Fourier inversion for integrable functions on ℝⁿ
- `Continuous.fourierInv_fourier_eq`: Pointwise version for continuous functions
- Supporting lemmas for Gaussian-weighted integral convergence

**Mathlib LACKS**:
- Stieltjes inversion for CDF differences (measure-theoretic version)
- Bounded density → tail integral bound
- Direct CDF ↔ charfun inversion

---

## Five Candidate Approaches

### Approach 1: Direct Stieltjes Inversion (Full Fourier Bridge)

**Method**: Build Stieltjes inversion from Mathlib's `Integrable.fourierInv_fourier_eq` + Gaussian tail bound.

**Procedure**:
1. Define auxiliary function $B_h(x) = (h/\pi) / (x^2 + h^2)$ (Poisson kernel)
2. Use classical identity: $\text{cdf}(\mu)(y) = (1/2) + (1/\pi) \int_0^\infty \text{Im}[\varphi_\mu(-t) e^{-ity}] / t \, dt$
3. Invoke Mathlib's charfun definition: `charFun μ t := ∫ x, exp(⟪x, t⟫ * I) ∂μ`
4. Apply `Integrable.fourierInv_fourier_eq` to $B_h$ (smooth, compactly supported mollifier)
5. Send $h \to 0$ to recover CDF pointwise
6. Bound tail error using Gaussian density bounds

**Mathlib dependencies**:
- `MeasureTheory.Integrable.fourierInv_fourier_eq` (exists ✓)
- `Complex.norm_exp_I_mul_ofReal` (exp bounds, exists ✓)
- CDF bounds: `cdf_nonneg`, `cdf_le_one` (exist ✓)
- Integrable.mono, integral_mul_le (exist ✓)

**Estimated code**:
```
- Poisson kernel definition + properties: 50 lines
- mollifier sequence + decay: 60 lines
- Fubini + charfun/Fourier exchange: 40 lines
- Tail bound via Gaussian density: 50 lines
TOTAL: ~200 lines
```

**Feasibility**: ⭐⭐⭐ **HIGH** — All components exist; main work is metric-space plumbing.

**Blocker risk**: `fourierInv_fourier_eq` is for functions V → E with inner products. Need to carefully map ℝ → ℂ and handle the measure-theoretic → function-theoretic translation.

---

### Approach 2: Exploit Gaussian Density Bound (Direct CDF Lipschitz)

**Method**: Use that Φ (standard Gaussian CDF) has bounded density φ(x) = (2π)^{-1/2} exp(-x²/2). Skip full inversion; instead, bound the "smoothed CDF" directly.

**Procedure**:
1. Mollify μ by convolution with small-bandwidth Gaussian: $\mu_h = \mu * \mathcal{N}(0, h^2)$
2. Then $\text{cdf}(\mu_h)$ has bounded derivative $\leq C/h$
3. Use charfun relationship: $\hat{\mu}_h(t) = \hat{\mu}(t) e^{-t^2 h^2/2}$
4. Compute $\text{cdf}(\mu_h)(y) - \text{cdf}(\Phi)(y)$ via Gaussian integral formula
5. Bound $|\text{cdf}(\mu) - \text{cdf}(\mu_h)| \leq o(h)$ using regularity
6. Optimize over h

**Mathlib dependencies**:
- Gaussian measure + charfun: `charFun_gaussianReal` (exists ✓)
- Convolution measure properties
- Density bounds from Gaussian density
- Integral bounds

**Estimated code**:
```
- Mollification setup: 40 lines
- Density derivative bound: 30 lines
- Charfun mollification formula: 50 lines
- CDF difference via mollified charfun: 60 lines
- Error term h-optimization: 40 lines
TOTAL: ~220 lines
```

**Feasibility**: ⭐⭐⭐ **HIGH** — Avoids full Fourier inversion; relies on more direct Gaussian properties.

**Blocker risk**: Convolution measure theory + Gaussian integrals might have gaps in Mathlib. Would need `integral_gaussian_measure_mul_exp` variants.

---

### Approach 3: Fejér Kernel Decomposition (Truncation Trick)

**Method**: Use Fejér kernel (Cesàro mean of Dirichlet) to regularize the charfun integral.

**Procedure**:
1. Define Fejér kernel: $F_T(t) = T \sin^2(\pi t T) / (\pi^2 t^2 T^2)$ (integrates to 1)
2. Fejér FT inversion: $\text{cdf}(\mu)(y) = (1/2) + \text{Re} \int \hat{\mu}(t) F_T(t) e^{-ity} dt + o(1/T)$
3. Fejér → square-integrable mollifier (vs. Dirichlet's singular Fourier transform)
4. Apply Plancherel for L² charfun bounds
5. Use Gaussian tail bounds for remainder

**Mathlib dependencies**:
- Fejér kernel properties (May NOT be in Mathlib — check)
- Plancherel theorem (exists for L² ✓)
- Charfun L² properties

**Estimated code**:
```
- Fejér kernel definition: 25 lines
- Fejér inversion formula: 80 lines
- Plancherel application: 40 lines
- Tail error bound: 40 lines
TOTAL: ~185 lines
```

**Feasibility**: ⭐⭐ **MEDIUM-HIGH** — Cleaner mathematically, but Fejér kernel infrastructure may be missing from Mathlib.

**Blocker risk**: **HIGH** — Fejér kernel not standard in Mathlib. Would need to define + prove basic properties (kernel positivity, integral = 1, etc.). Adds ~60 lines of setup.

---

### Approach 4: Discretization + Measure Partition (Grid-Based)

**Method**: Approximate CDF at finitely many grid points, use charfun bounds at each point.

**Procedure**:
1. Pick grid $y_1, \ldots, y_N$ covering $[-K, K]$ with spacing $\Delta y = 2K/N$
2. For each $y_i$, bound $|\text{cdf}(\mu)(y_i) - \text{cdf}(\Phi)(y_i)|$ using a local charfun truncation
3. Use "Lipschitz patchwork": $|\text{cdf}(\mu)(y) - \text{cdf}(\mu)(y_i)| \leq \mu([-\infty, y] \setminus [-\infty, y_i])$
4. Extend to all y via measure-theoretic monotonicity
5. Optimize grid density

**Mathlib dependencies**:
- CDF monotonicity: `monotone_cdf` (exists ✓)
- Measure restriction: `measure_preimage` (exists ✓)
- Integral bounds (standard ✓)

**Estimated code**:
```
- Grid setup + partition: 30 lines
- Per-grid-point charfun bound: 50 lines
- Patchwork Lipschitz: 40 lines
- Extension to all y: 30 lines
- Optimization + constants: 30 lines
TOTAL: ~180 lines
```

**Feasibility**: ⭐⭐ **MEDIUM** — More elementary, avoids Fourier inversion entirely, but introduces grid-dependent constants and density optimization.

**Blocker risk**: **MEDIUM** — Passing from finite grid to all ℝ requires smooth measure-theoretic machinery (maybe `IsClosed` for level sets). Constants C₁, C₂ become complicated functions of grid parameters.

---

### Approach 5: Avoid Universal Constants (Pragmatic Restructuring)

**Method**: Change the statement to relax universal constants. Instead of:
$$\forall \mu, |F_\mu(y) - \Phi(y)| \leq C_1 \int \cdots + C_2/T$$

State:
$$\forall \mu, \exists C_1(\mu), C_2(\mu), \quad |F_\mu(y) - \Phi(y)| \leq C_1(\mu) \int \cdots + C_2(\mu)/T$$

**Procedure**:
1. Use existing `berry_esseen_smoothing` lemma (ALREADY PROVED ✓)
2. Extract constants from that lemma's proof
3. Quantify over μ first, then ∃ C₁, C₂

**Mathlib dependencies**: None — uses existing infrastructure.

**Estimated code**:
```
- Wrapper around existing lemma: 10 lines
- Constant extraction: 5 lines
TOTAL: ~15 lines
```

**Feasibility**: ⭐⭐⭐⭐⭐ **TRIVIAL** — Already done (in disguise).

**Blocker risk**: **NONE** — But **mathematically wrong**: doesn't solve the original problem (universal constants are essential for Berry-Esseen).

---

## Mathlib API Audit

### ✅ Available (Key to Success)

| API | Module | Notes |
|-----|--------|-------|
| `charFun μ t` | `MeasureTheory.Measure.CharacteristicFunction` | Definition ✓ |
| `charFun_gaussianReal` | `ProbabilityTheory` | Gaussian charfun ✓ |
| `norm_charFun_le_one` | `MeasureTheory.Measure.CharacteristicFunction` | \|\|charFun\|\| ≤ 1 ✓ |
| `cdf μ y` | `ProbabilityTheory` | CDF definition ✓ |
| `cdf_nonneg`, `cdf_le_one` | `ProbabilityTheory` | CDF bounds ✓ |
| `monotone_cdf` | `ProbabilityTheory` | CDF monotonicity ✓ |
| `Integrable.fourierInv_fourier_eq` | `MeasureTheory.Analysis.Fourier.Inversion` | **Fourier inversion** ✓ |
| `Complex.norm_exp_I_mul_ofReal` | `Analysis.SpecialFunctions.Complex.Log` | exp\|I·t\| bounds ✓ |
| `Integrable.mono` | `MeasureTheory.Integral.Bochner` | Integral comparison ✓ |
| `measure_Icc` | `MeasureTheory` | Interval measure ✓ |

### ❌ Missing (Blockers)

| Item | Module | Why Needed | Workaround |
|------|--------|-----------|-----------|
| Stieltjes inversion (CDF version) | — | Direct formula F(y) - G(y) = (1/2π) Re ∫ φ(t)e^{-ity}/it dt | Build from `fourierInv_fourier_eq` (~150 lines) |
| Fejér kernel | — | Positive mollifier for Fourier inversion | Define + prove basic properties (~60 lines) |
| `integral_gaussian_measure_mul_exp` | — | $\int \mathcal{N}(0,1) \cdot e^{itx} dx = \text{charfun}(t)$ | Use existing charfun definition ✓ |
| Convolution.cdf | — | CDF of convolved measures | Use `Measure.map` + density integral ✓ |

---

## Complexity vs. Mathlib Gap Analysis

### Approach Comparison Table

| Approach | Math Difficulty | Lean Implementation | Mathlib Gap | Lines | Risk | Verdict |
|----------|-----------------|--------------------|-----------|----|------|---------|
| **1. Full Stieltjes** | High | Medium | Medium (need Poisson kernel + tail) | 200 | Medium | 🟡 POSSIBLE |
| **2. Gaussian Density** | High | Medium | Medium (convolution properties) | 220 | High | 🟡 POSSIBLE |
| **3. Fejér Kernel** | High | High | High (Fejér not in Mathlib) | 245 | High | 🔴 RISKY |
| **4. Discretization** | Medium | Low | Low (grid + measure theory) | 180 | Medium | 🟡 POSSIBLE |
| **5. Relax Constants** | Low | Trivial | None | 15 | None | 🟢 WORKS (WRONG) |

---

## Recommendation

### **Primary Path: Approach 1 (Full Stieltjes Inversion)**

**Why**:
- Uses only existing Mathlib APIs (`fourierInv_fourier_eq`, charfun, Gaussian bounds)
- Most mathematically direct
- Clear decomposition into 4 sub-lemmas (mollifier, Fourier exchange, inversion limit, tail bound)
- All components have been tested in other Lean proofs

**Implementation Plan**:

```lean
-- Step 1: Poisson kernel auxiliary function
private lemma poisson_kernel_integral (h : ℝ) (hh : 0 < h) :
    ∫ x, h / (π * (x^2 + h^2)) = 1 := by
  -- Use substitution x = h*tan(θ), integral = (1/π) * arctan(∞) - arctan(-∞)
  sorry  -- ~30 lines

-- Step 2: Mollifier sequence that approximates CDF
private lemma smooth_cdf_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : ℝ) (h : ℝ) (hh : 0 < h) :
    let ϕ := fun x => h / (π * ((x - y)^2 + h^2))
    (∫ x, ϕ x * (cdf μ x : ℝ)) - (cdf μ y) = O(h) := by
  -- Gaussian mollifier + monotone convergence
  sorry  -- ~60 lines

-- Step 3: Fourier exchange via Fubini
private lemma charfun_mollifier_exchange (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y h : ℝ) (hh : 0 < h) :
    (∫ x, (h / (π * ((x - y)^2 + h^2))) * (cdf μ x : ℝ)) =
    (1 / (2π)) * ∫ t in Set.Icc (-1/h) (1/h),
      (charFun μ t - charFun (gaussianReal 0 1) t) * (some_mollifier_charfun t h) / |t| dt := by
  -- Fubini + charfun definition
  sorry  -- ~40 lines

-- Step 4: Tail integral bound
private lemma charfun_tail_integral_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 < T) :
    (∫ t in Set.Ioi T, (charFun μ t - charFun (gaussianReal 0 1) t) / |t|) ≤ C / T := by
  -- Bound using Gaussian density (bounded continuous derivative)
  sorry  -- ~50 lines

-- Main theorem
lemma esseen_concentration_universal : ... := by
  use C₁, C₂, hpos_C₁, hpos_C₂
  intro T hT μ _ y
  -- Assembly from above four lemmas
  sorry  -- ~20 lines
```

**Timeline**: ~200-220 lines, ~8-12 person-hours for careful Lean development.

---

### **Fallback Path: Approach 4 (Discretization)**

If Stieltjes inversion gets stuck on Fourier-theoretic subtleties:

**Why**:
- Avoids Fourier inversion entirely
- Uses only elementary measure theory
- Easier to debug if stuck

**Drawback**: Constants C₁, C₂ are more complicated (depend on grid density optimization).

---

## Key Technical Challenges (Implementation)

### 1. **Fourier Inversion Type Mismatch**
   - `fourierInv_fourier_eq: V → E` for finite-dimensional inner product spaces
   - We need it for ℝ → ℂ
   - **Solution**: Use `Real.fourierChar_apply` and the ℝ-specific instances

### 2. **CDF as Integrable Function**
   - CDF is not smooth; it's monotone and right-continuous
   - Cannot apply standard Fourier inversion directly
   - **Solution**: Mollify first (Poisson kernel), send mollifier width → 0

### 3. **Passing Universal Constants Through Limits**
   - Esseen's proof: constants hide in limit process
   - Need to extract concrete C₁, C₂ valid for all T, y, μ
   - **Solution**: Use Gaussian density bound (bounded continuous derivative) to make constants explicit

### 4. **Integrable.mono Application**
   - Comparing integrals with different integrands
   - Need `|charFun μ t - charFun Φ t| / |t| ≤ ???` for bounds to apply
   - **Solution**: Use `norm_charFun_le_one` to get |charFun| ≤ 2, then |difference| / |t| ≤ 2/|t|

---

## Conclusion

| Approach | Feasibility | Recommended? | Effort |
|----------|-------------|--------------|--------|
| **1. Stieltjes Inversion** | **HIGH** ✓ | **PRIMARY** ✓ | 200 lines |
| 2. Gaussian Density | HIGH ✓ | Secondary | 220 lines |
| 3. Fejér Kernel | MEDIUM | Not now | 245 lines |
| 4. Discretization | HIGH ✓ | Fallback | 180 lines |
| 5. Relax Constants | TRIVIAL | ✗ WRONG | 15 lines |

**Decision**: **Approach 1 (Full Stieltjes Inversion)** is recommended as the primary path. It has the best risk-reward ratio and uses only existing Mathlib infrastructure. Estimated implementation time: **1-2 focused coding sessions** (8-12 hours).

If Fourier-theoretic plumbing becomes intractable, **Approach 4 (Discretization)** is a robust fallback.


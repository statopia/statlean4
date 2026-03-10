# Esseen Smoothing Inequality: Technical Implementation Notes

**Target**: `esseen_concentration_universal` in `Statlean/LimitTheorems/BerryEsseen.lean:524`

---

## Mathematical Kernel

### The Esseen Inequality (1945)

**Statement**: For any probability measure μ on ℝ with cdf F and charfun φ:

$$|F(y) - \Phi(y)| \leq \frac{1}{2\pi} \int_{-T}^{T} \frac{|\varphi(t) - \phi_\Phi(t)|}{|t|} dt + \frac{C_2}{T}$$

where:
- $\Phi$ = standard Gaussian CDF
- $\phi_\Phi(t) = e^{-t^2/2}$ (Gaussian charfun)
- Constants C₁ = 1/(2π), C₂ depends on Gaussian density boundedness

**Key observation**: The tail integral bound C₂/T is the "price paid" for truncating the infinite charfun integral. The Gaussian has bounded density φ(x) = (2π)^{-1/2} e^{-x²/2}, which gives exponential decay in t.

---

## Stieltjes Inversion Formula (The Bridge)

### Classical Version

For a measure μ with bounded density f:

$$F(y) - G(y) = \frac{1}{2\pi} \operatorname{Re} \int_{-\infty}^{\infty} \left[\varphi_\mu(t) - \varphi_G(t)\right] \frac{e^{-ity}}{it} dt$$

where the integral is understood in the principal value sense.

### Why Mathlib's `fourierInv_fourier_eq` Doesn't Directly Apply

**Mathlib version**:
```lean
theorem MeasureTheory.Integrable.fourierInv_fourier_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v
```

**Issues**:
1. **Type**: Works for V → E where V is finite-dimensional inner product space, E is complete normed space
   - Need ℝ → ℂ specialization
2. **Integrand**: Expects `f : V → E`, not a measure/CDF
   - Need to lift CDF (monotone function) to integrable function via mollification
3. **Continuity**: Requires `ContinuousAt f v`
   - CDFs are right-continuous but not continuous; need to mollify first
4. **Fourier inverse definition**: Uses `𝓕⁻` for real inverse Fourier; charfun uses different convention with exp(itx), not exp(-itx)
   - Need to handle sign conventions

### Workaround: Mollification Pipeline

```
CDF (monotone, right-continuous)
  ↓ [Poisson kernel convolution]
Mollified CDF (smooth, bounded density)
  ↓ [Apply fourierInv_fourier_eq]
Fourier inversion (pointwise)
  ↓ [Limit as mollifier width → 0]
Original CDF recovered
  ↓ [Bound tail using Gaussian decay]
Esseen inequality
```

---

## Implementation Strategy: Step-by-Step

### Step 1: Poisson Kernel Setup

**Definition**:
$$K_h(x) = \frac{h}{\pi(x^2 + h^2)}$$

**Properties to prove**:
```lean
lemma poisson_kernel_nonneg (h : ℝ) (hh : 0 < h) (x : ℝ) : 0 ≤ K_h h x
lemma poisson_kernel_integral (h : ℝ) (hh : 0 < h) :
    ∫ x, K_h h x = 1
lemma poisson_kernel_decay (h : ℝ) (hh : 0 < h) (R : ℝ) (hR : 0 < R) :
    ∫ x in {x | |x| > R}, K_h h x < h / R
```

**Mathlib support**:
- Integration by substitution: `intervalIntegral.integral_comp_mul_left` (exists ✓)
- Arctangent: `Real.arctan` (exists ✓)
- Limit as h → 0: `Filter.Tendsto` (exists ✓)

**Estimated effort**: 30-40 lines

---

### Step 2: Mollified CDF Approximation

**Goal**: Show that convolution of CDF with Poisson kernel approximates CDF well.

**Formula**:
$$F_h(y) := \int K_h(y - x) \, dF(x) \approx F(y) + O(h)$$

**Key lemma**:
```lean
private lemma mollified_cdf_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ h, 0 < h → h < δ →
        |∫ x, K_h h (y - x) * (cdf μ x : ℝ) - cdf μ y| < ε
```

**Proof sketch**:
1. Split integral: $\int_{|x-y| ≤ 1} + \int_{|x-y| > 1}$
2. First part: CDF is right-continuous, use uniform continuity on compact sets
3. Second part: CDF ∈ [0,1], bound by Poisson kernel decay
4. Optimize δ based on ε

**Mathlib support**:
- CDF monotonicity: `monotone_cdf` ✓
- CDF bounds: `cdf_nonneg`, `cdf_le_one` ✓
- Integral inequality: `integral_le_integral_of_nonneg` ✓
- Dominated convergence: `Filter.tendsto_integral_of_dominated_convergence` ✓

**Estimated effort**: 50-70 lines

---

### Step 3: Fourier Transform of Mollified CDF

**Goal**: Connect mollified CDF to charfun via Fourier transform.

**Key identity**:
$$\hat{F}_h(t) := \int e^{itx} dF_h(x) = \int e^{itx} K_h(x) \, dx \cdot \hat{F}(t)$$

Wait, this is backwards. Let me reconsider the convolution direction:

**Correct formulation** (Fubini swap):
$$\int e^{-itx} K_h(y-x) \, dF(x) = \int e^{-ity} K_h(t) \hat{F}(t) dt$$

Hmm, this gets complicated with double integrals. Instead:

**Better approach: Direct charfun computation**

For mollified CDF $F_h(y) = \int K_h(y-x) dF(x)$, compute its charfun:

```lean
private lemma mollified_cdf_charfun (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h) (t : ℝ) :
    let F_h := fun y => ∫ x, poisson_kernel h (y - x) * cdf μ x
    (charFun (μ.map F_h) t) = (charFun_poisson_kernel h t) * (charFun μ t)
```

**Challenge**: `μ.map F_h` doesn't directly work since F_h is the CDF function, not a random variable on a probability space.

**Better yet**: Use the Esseen decomposition that's **already partially done** in `BerryEsseen.lean`:
- The file already has `berry_esseen_smoothing` PROVED ✓
- This uses mollified CDFs and smoothing kernels
- The missing part is extracting universal constants

**Key insight**: Look at what `berry_esseen_smoothing` does exactly!

---

### Step 3 (Revised): Analysis of Existing `berry_esseen_smoothing`

From the code (line 262-293 in BerryEsseen.lean):

```lean
lemma berry_esseen_smoothing (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : ℝ) (hT : 0 < T) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : ℝ, |cdf μ y - cdf ν y| ≤
        C₁ * (∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) + C₂ / T
```

**This ALREADY EXISTS and is PROVED!**

The only issue: it requires **two arbitrary measures** μ and ν. The `esseen_concentration_universal` version specializes ν = gaussianReal 0 1.

**Actual blocker**: The proof of `berry_esseen_smoothing` uses sub-lemmas that compute generic CDF bounds, not specific Gaussian bounds. To extract universal constants independent of μ, we need the Stieltjes inversion formula.

---

### Step 4: Stieltjes Inversion Application

**The critical lemma**:

```lean
private lemma esseen_fourier_inversion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : ℝ) (T : ℝ) (hT : 0 < T) :
    |cdf μ y - cdf (gaussianReal 0 1) y| ≤
      (1 / (2 * π)) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
      (2 / T)  -- Constant comes from Gaussian density bound
```

**Proof structure**:
1. Use mollification: $F_h, \Phi_h$ for small h
2. Apply Fourier inversion to get pointwise equality (via `fourierInv_fourier_eq`)
3. Extract charfun integral representation
4. Bound tail integral using Gaussian density: $\sup_x |\phi(x)| = 1/\sqrt{2\pi}$
5. Send h → 0

**Mathlib dependencies**:
- `Integrable.fourierInv_fourier_eq` (core Fourier inversion) ✓
- `Real.fourierChar_apply` (charfun for ℝ) ✓
- `Complex.norm_exp_I_mul_ofReal` (bounds on exp(itx)) ✓
- `integral_mul_le_of_nonneg_left` (Hölder / dominance) ✓

**Estimated effort**: 80-120 lines (mostly integration bounds)

---

## Alternative: Bypass Stieltjes, Use Existing `berry_esseen_smoothing` Directly

**Insight**: The lemma `berry_esseen_smoothing` is ALREADY PROVED for arbitrary μ, ν.

To get `esseen_concentration_universal`, we only need to observe:
1. Set ν = gaussianReal 0 1
2. The constants C₁, C₂ from `berry_esseen_smoothing` are **universal in μ** (they don't depend on specific properties of μ)

**This means**: The Stieltjes inversion formula is HIDDEN inside the proof of `berry_esseen_smoothing`!

**Check the proof of `berry_esseen_smoothing`** to see if it already establishes universal constants.

---

## Critical Observation from Code

Looking at `smoothed_cdf_fourier_bound` (line 208-259):

```lean
lemma smoothed_cdf_fourier_bound (μ ν : Measure ℝ) ...
    (∀ y : ℝ, |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
      C₁ * (∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|) +
      C_f / T)
```

This lemma DIRECTLY connects CDF difference to charfun integral! It contains the Stieltjes inversion implicitly.

**Path forward**:
1. Examine `smoothed_cdf_fourier_bound` proof
2. Check if constants C₁, C_f are universal (don't depend on μ, ν structure)
3. If yes, `esseen_concentration_universal` is just a direct application with ν = gaussianReal 0 1

---

## Recommended Next Step for Coder

**DO THIS FIRST**:

```bash
cd /home/gavin/statlean
grep -A 80 "lemma smoothed_cdf_fourier_bound" Statlean/LimitTheorems/BerryEsseen.lean
```

Examine lines 208-259 to understand:
1. Are constants C₁, C_f obtained from CDF bounds (cdf_nonneg, cdf_le_one)?
2. If yes, they're universal and don't depend on μ, ν structure
3. Then `esseen_concentration_universal` follows immediately from `berry_esseen_smoothing` with ν = gaussianReal 0 1

**If that path works**: ~10 lines (trivial)

**If that path doesn't work** (constants are data-dependent): Need full Stieltjes inversion (~200 lines)

---

## Key Mathlib API Reference

| Need | Mathlib Location | Function |
|------|------------------|----------|
| Fourier inversion | `Mathlib/Analysis/Fourier/Inversion.lean` | `MeasureTheory.Integrable.fourierInv_fourier_eq` |
| CharFun definition | `Mathlib/MeasureTheory/Measure/CharacteristicFunction.lean` | `charFun μ t := ∫ x, exp(⟪x, t⟫ * I) ∂μ` |
| Gaussian charfun | `Mathlib/Probability/` | `charFun_gaussianReal` |
| CDF bounds | `Mathlib/Probability/` | `cdf_nonneg`, `cdf_le_one`, `monotone_cdf` |
| Poisson kernel (need to define) | — | Define h/(π(x²+h²)) |
| Integral by substitution | `Mathlib/Analysis/SpecialFunctions/Integrals/Fourier.lean` | `intervalIntegral.integral_comp_mul_left` |

---

## Estimate Summary

| Path | Effort | Risk | Feasibility |
|------|--------|------|-------------|
| **Examine `smoothed_cdf_fourier_bound` first** | 5 min | None | Essential |
| If universal: Direct application | 10 lines | None | ⭐⭐⭐⭐⭐ |
| If not universal: Full Stieltjes | 200 lines | Medium | ⭐⭐⭐ |

---

## Final Recommendation

**Start by reading the proof of `smoothed_cdf_fourier_bound` carefully.** The answer to whether `esseen_concentration_universal` is trivial or requires 200 lines depends entirely on whether that lemma's constants are universal.

If they are universal → **This is a 1-minute fix** (just specialize with ν = gaussianReal 0 1 in `berry_esseen_smoothing`).

If they are data-dependent → **Build full Stieltjes inversion** using the Poisson kernel + Fourier exchange approach outlined in Steps 1-4 above.


# Esseen Inequality Implementation: Quick Start Guide

**Status**: Research complete. Ready to code.

---

## TL;DR

The Esseen smoothing inequality `esseen_concentration_universal` in `BerryEsseen.lean:524` needs a Stieltjes inversion formula to extract universal constants from the already-proved `berry_esseen_smoothing` lemma.

### Critical First Step (5 minutes)

Read `/home/gavin/statlean/Statlean/LimitTheorems/BerryEsseen.lean:208-259` (`smoothed_cdf_fourier_bound` lemma) and answer:

**Q: Are the constants C₁ and C_f independent of the choice of measures μ and ν?**

- **YES** → `esseen_concentration_universal` is **1-line proof** (specialize existing lemma)
- **NO** → Need 200-line Stieltjes inversion implementation (Approach 1 below)

---

## The Five Approaches (Ranked by Feasibility)

### ✅ **Approach 1: Stieltjes Inversion from Mathlib's Fourier**
**Status**: Recommended
**Effort**: 200 lines
**Risk**: Medium
**Timeline**: 8-12 hours

**Key idea**: Bridge from Mathlib's `Integrable.fourierInv_fourier_eq` (function-theoretic) to CDF/charfun (measure-theoretic) using:
1. Poisson kernel mollification (h/(π(x²+h²)))
2. Fubini/charfun Fourier exchange
3. Gaussian density tail bound (C₂/T)
4. Limit as mollifier width → 0

**Mathlib dependencies**: All ✓ available
- `fourierInv_fourier_eq` (Fourier inversion)
- `charFun_gaussianReal` (Gaussian charfun)
- `cdf_nonneg`, `cdf_le_one` (CDF bounds)
- Integration lemmas (Fubini, dominated convergence)

**Files to create/modify**:
- `Statlean/LimitTheorems/BerryEsseen.lean` (fill `esseen_concentration_universal` sorry)

---

### ✅ **Approach 2: Gaussian Density Convolution**
**Status**: Alternative
**Effort**: 220 lines
**Risk**: High (convolution lemmas may be incomplete)
**Timeline**: 12-16 hours

**Key idea**: Mollify μ by convolution with Gaussian, then bound CDFs using Gaussian integral properties.
- Avoids full Fourier inversion
- Relies on charfun Gaussian formulas

**Mathlib gap**: Convolution + density integral may require custom lemmas.

---

### ✅ **Approach 3: Discretization (Grid-Based)**
**Status**: Fallback
**Effort**: 180 lines
**Risk**: Medium (measure-theoretic subtleties)
**Timeline**: 10-14 hours

**Key idea**: Approximate CDF on finite grid, use charfun bounds per grid point, patchwork via CDF monotonicity.
- More elementary (no Fourier inversion)
- Constants more complicated

**Advantage**: If Stieltjes approach gets stuck on Fourier details, this is a robust backup.

---

### ❌ **Approach 4: Fejér Kernel (Not Recommended Yet)**
**Status**: Risky
**Effort**: 245 lines
**Risk**: High (Fejér kernel not in Mathlib)
**Timeline**: 16-20 hours

Feasible but adds ~60 lines just to define/verify Fejér kernel properties.

---

### ❌ **Approach 5: Change Statement (Wrong Solution)**
**Status**: Anti-recommendation
**Effort**: 10 lines
**Risk**: None

Relaxing universal quantifiers makes it trivial but **mathematically invalid** for Berry-Esseen.

---

## Implementation Checklist (Approach 1)

### Phase 0: Validation
- [ ] Read `BerryEsseen.lean:208-259` (`smoothed_cdf_fourier_bound` proof)
- [ ] Determine: are C₁, C_f universal?
  - [ ] If YES: Jump to "Trivial Case" below
  - [ ] If NO: Proceed to Phase 1

### Trivial Case (If C₁, C_f Are Universal)
```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
          ∀ y : ℝ, |cdf μ y - cdf (gaussianReal 0 1) y| ≤
            C₁ * (∫ t in Set.Icc (-T) T,
              ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
            C₂ / T := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := berry_esseen_smoothing μ (gaussianReal 0 1) T hT
  exact ⟨C₁, C₂, hC₁, hC₂, h⟩
```
**Effort**: 5 minutes. **Done!**

### Phase 1: Poisson Kernel (if needed)
- [ ] Define `poisson_kernel : ℝ → ℝ → ℝ := fun h x => h / (π * (x^2 + h^2))`
- [ ] Prove:
  - `poisson_kernel_nonneg` (obvious)
  - `poisson_kernel_integral`: $\int K_h = 1$ (use arctangent)
  - `poisson_kernel_decay`: $\int_{|x|>R} K_h < h/R$ (tail bound)

**Code**: ~40 lines

**Mathlib lemmas**:
- `intervalIntegral.integral_comp_smul_deriv`
- `Real.arctan_neg`, `Real.arctan_add_arctan_eq`

### Phase 2: Mollified CDF Approximation
- [ ] Prove `mollified_cdf_approximation`: $\int K_h(y-x) dF(x) \to F(y)$ as h → 0
- [ ] Use: CDF right-continuity + Poisson kernel decay

**Code**: ~60 lines

**Key lemma structure**:
```lean
private lemma mollified_cdf_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      |∫ x, poisson_kernel h (y - x) * (cdf μ x : ℝ) - cdf μ y| < ε
```

### Phase 3: Fourier Exchange
- [ ] Connect mollified CDF integral to charfun via Fubini
- [ ] Extract: $\int K_h(y-x) dF(x) = (1/2\pi) \int \hat{\mu}(t) \hat{K}_h(t) e^{-ity} / it \, dt$

**Code**: ~50 lines

**Tricky part**: Sign conventions in charfun vs. Fourier transform. Mathlib uses exp(⟪x,t⟫ * I) = exp(itx), so fourier inverse uses exp(-itx). Need careful tracking.

### Phase 4: Tail Integral Bound
- [ ] Prove: $\int_{|t|>T} ... / |t| dt \leq C/T$ using Gaussian density bound
- [ ] Use: $\sup_x |\phi(x)| = (2\pi)^{-1/2}$ (bounded density)

**Code**: ~60 lines

**Key insight**: Gaussian decay in charfun: $e^{-t^2/2}$ gives exponential control on integrand tail.

### Phase 5: Assembly
- [ ] Combine all pieces into main theorem
- [ ] Extract universal constants: $C_1 = 1/(2\pi), C_2 = $ (from tail bound)

**Code**: ~20 lines

---

## Code Template (For Reference)

```lean
namespace Statlean.BerryEsseen

open MeasureTheory ProbabilityTheory

-- Constants
private noncomputable def esseen_constant_1 : ℝ := 1 / (2 * π)
private noncomputable def esseen_constant_2 : ℝ := 2  -- from Gaussian density bound

-- Step 1: Poisson kernel
private def poisson_kernel (h : ℝ) (x : ℝ) : ℝ := h / (π * (x^2 + h^2))

private lemma poisson_kernel_integral (h : ℝ) (hh : 0 < h) :
    ∫ x, poisson_kernel h x = 1 := by
  sorry  -- 30 lines

-- Step 2: Mollification
private lemma mollified_cdf_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      |∫ x, poisson_kernel h (y - x) * (cdf μ x : ℝ) - cdf μ y| < ε := by
  sorry  -- 60 lines

-- Step 3: Fourier
private lemma charfun_mollifier_exchange (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y h : ℝ) (hh : 0 < h) :
    (∫ x, poisson_kernel h (y - x) * (cdf μ x : ℝ)) =
    (1 / (2 * π)) * ∫ t, (charFun μ t - charFun (gaussianReal 0 1) t) *
      (some_charfun_formula t h) / |t| dt := by
  sorry  -- 50 lines

-- Step 4: Tail bound
private lemma charfun_tail_integral_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 < T) :
    (∫ t in Set.Ioi T, (charFun μ t - charFun (gaussianReal 0 1) t) / |t|) ≤
      esseen_constant_2 / T := by
  sorry  -- 60 lines

-- Main theorem
lemma esseen_concentration_universal :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
          ∀ y : ℝ, |cdf μ y - cdf (gaussianReal 0 1) y| ≤
            C₁ * (∫ t in Set.Icc (-T) T,
              ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
            C₂ / T := by
  refine ⟨esseen_constant_1, esseen_constant_2, by norm_num, by norm_num, fun T hT μ _ y => ?_⟩
  sorry  -- 20 lines: assembly from steps 1-4

end Statlean.BerryEsseen
```

---

## Testing Strategy

1. **Unit test each sub-lemma**:
   ```bash
   lake build Statlean.BerryEsseen
   # Should see 4 sorries (steps 1-4) + 1 main
   ```

2. **Incremental fill**:
   - Complete Step 1 (Poisson kernel) first
   - Verify `lake build` passes
   - Move to Step 2, etc.

3. **Integration test**:
   - Once all 4 steps done, assemble main theorem
   - Check constants are correct
   - Verify `lake build Statlean.Verified` if applicable

---

## Known Pitfalls

### Pitfall 1: Fourier Convention Mismatch
**Problem**: Mathlib's `charFun` uses exp(itx), but `fourierInv_fourier_eq` uses Fourier transform conventions.

**Solution**: Use `Real.fourierChar_apply` and explicitly handle the sign in the exponential.

### Pitfall 2: CDF Not Continuous
**Problem**: CDFs are right-continuous, not continuous everywhere. Can't apply `fourierInv_fourier_eq` directly.

**Solution**: Mollify first (Steps 1-2), then apply inversion to mollified version (which IS smooth).

### Pitfall 3: Integrand Singularity at t=0
**Problem**: Integrand ∝ 1/|t| is singular at t=0.

**Solution**: Use `Set.Icc (-T) T` (closed interval) and handle 0 separately:
```lean
∫ t in Set.Icc (-T) T, ... / |t| =
  ∫ t in {0}, ... (= 0 by singularity) +
  ∫ t in Set.Icc (-T) T \ {0}, ... / |t|
```

### Pitfall 4: Constants Not Extracted Cleanly
**Problem**: Esseen proof hides constants in limit processes.

**Solution**: Use **explicit Gaussian density bound**:
- $\sup_x |\phi(x)| = 1/\sqrt{2\pi}$
- This makes tail bound $\leq 2/T$ concrete

---

## Success Criteria

```
- [ ] esseen_concentration_universal compiles with zero sorry
- [ ] lake build Statlean.LimitTheorems.BerryEsseen succeeds
- [ ] No warnings about sorry or admit
- [ ] Constants C₁, C₂ are explicit (not existential)
```

---

## Related Lemmas (Already Proved)

Use these as reference while filling the sorry:

| Lemma | File | Purpose |
|-------|------|---------|
| `berry_esseen_smoothing` | BerryEsseen.lean:262 | Uses mollification + charfun bounds (TWO measures) |
| `smoothing_kernel_exists` | BerryEsseen.lean:58 | Triangular mollifier (one instance) |
| `cdf_smoothing_bound` | BerryEsseen.lean:158 | |CDF mollified - original| ≤ C/T |
| `smoothed_cdf_fourier_bound` | BerryEsseen.lean:208 | **KEY**: Mollified |CDF_1 - CDF_2| ≤ C₁ ∫ charfun / |t| + C₂/T |

**Key insight**: `smoothed_cdf_fourier_bound` IS THE STIELTJES INVERSION IN DISGUISE. Reading its proof will reveal exactly what universality assumptions are made about the constants.

---

## Estimated Timeline

| Phase | Effort | Risk | Time |
|-------|--------|------|------|
| Validation (Phase 0) | 5 min | None | 5 min |
| Poisson kernel | 40 lines | Low | 1-2 hrs |
| Mollification | 60 lines | Medium | 2-3 hrs |
| Fourier exchange | 50 lines | **HIGH** | 3-4 hrs |
| Tail bound | 60 lines | Low | 2-3 hrs |
| Assembly | 20 lines | Low | 1 hr |
| **TOTAL** | **230 lines** | **Medium** | **9-13 hrs** |

**If Phase 0 reveals constants are universal**: Skip to trivial case (5 min).

---

## References

- **Esseen (1945)**: "Fourier analysis of distribution functions"
- **Berry (1941)**: "The accuracy of asymptotic distribution of the mean"
- **Mathlib docs**:
  - `MeasureTheory.Integrable.fourierInv_fourier_eq` in `Analysis/Fourier/Inversion.lean`
  - `charFun` in `MeasureTheory/Measure/CharacteristicFunction.lean`
  - CDF in `ProbabilityTheory`

---

## Next Action

**Open**: `/home/gavin/statlean/Statlean/LimitTheorems/BerryEsseen.lean`

**Jump to**: Line 208, function `smoothed_cdf_fourier_bound`

**Read**: Its proof (lines 208-259)

**Ask**: Are constants C₁, C_f universal (independent of μ, ν)?

**Outcome**:
- YES → Done (5 min)
- NO → Implement Approach 1 (9-13 hrs)


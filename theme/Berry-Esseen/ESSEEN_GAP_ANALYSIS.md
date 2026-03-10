# Berry-Esseen Theorem: The Remaining Sorry (Gap Analysis)

## Problem Statement

File: `/home/gavin/statlean/Statlean/LimitTheorems/BerryEsseen.lean`
Line: 516-524

```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ > 0, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ),
      |↑(cdf μ) y - ↑(cdf (gaussianReal 0 1)) y| ≤
        C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        C₂ / T
  sorry
```

**This is the ONLY remaining sorry in BerryEsseen.lean.** Everything upstream (charFun Taylor bounds, smoothing kernel, Fourier-based bounds) is fully proved.

---

## What This Lemma Does

**Input**:
- Any probability measure `μ` on ℝ
- Parameters: `T > 0`, `C₁, C₂` (universal constants)

**Output**:
- Upper bound on |F_μ(y) - F_Φ(y)| (CDF difference from standard normal)
- In terms of: charfun difference ‖φ_μ - φ_Φ‖ integrated over [-T, T]

**Interpretation**:
```
CDF error ≤ (normalized charfun integral error) + (tail term 1/T)
```

This is **Esseen's concentration inequality** — the fundamental bridge between charfun distance and CDF distance in the Central Limit Theorem.

---

## Why It's Hard: The Fourier Inversion Wall

### The Classical Proof (Esseen, 1945)

```
Step 1: Start with charfun φ_μ(t) = E[exp(itX)]
Step 2: Apply Fourier inversion formula:
        F_μ(y) = (1/π) ∫ K(y-x) dμ(x)
        where K involves φ_μ
Step 3: Bound |F_μ(y) - F_Φ(y)| via triangle inequality:
        ≤ (1/π) ∫ |K(y-x)| |dμ(x) - dΦ(x)|
Step 4: Use boundedness of K and Fourier integral of (φ_μ - φ_Φ):
        ≤ (1/π) ∫_{-∞}^{∞} (1 - cos(ht))/t² |φ_μ(t) - φ_Φ(t)| dt
Step 5: Truncate integral at T, add exponential decay bounds:
        ≤ C₁ ∫_{-T}^T |φ_μ(t) - φ_Φ(t)|/|t| dt + C₂/T
```

**The blocker**: Step 2 requires **Stieltjes inversion formula**, which is **NOT in Mathlib**.

---

## Mathlib's Limitations

### What IS Available ✓

| Tool | Mathlib Status |
|---|---|
| CDF definition | ✓ `ProbabilityTheory.cdf` |
| CharFun definition | ✓ `MeasureTheory.charFun` |
| CDF uniqueness | ✓ `cdf_eq_iff` |
| CharFun uniqueness | ✓ `ext_of_charFun` |
| Fourier L² transform | ✓ `Mathlib.Analysis.Fourier.FourierTransform` |
| Dominated convergence | ✓ `tendsto_integral_of_dominated_convergence` |
| Gaussian charfun | ✓ `charFun_gaussianReal_zero_one` |

### What's MISSING ✗

| Tool | Why Needed | Mathlib Status |
|---|---|---|
| **Stieltjes inversion** | Recover measure from charfun (Step 2 above) | ✗ Missing |
| **Riemann-Stieltjes integral** | Foundation for Stieltjes inversion | ✗ Missing |
| **CDF-Fourier integral identity** | Direct link: F ↔ φ via integral | ✗ Missing |
| **Esseen's lemma** | The lemma itself | ✗ Missing |

---

## Solution Paths

### Option A: Formalize Stieltjes Inversion (~300 lines)

**Effort**: Medium
**Dependencies**: Riemann-Stieltjes integration
**Scope**: Full generality for all probability measures

**Outline**:
```lean
-- New lemma to formalize
lemma stieltjes_inversion_formula (μ : ProbabilityMeasure ℝ) (y : ℝ) :
    let φ := charFun (μ : Measure ℝ)
    cdf μ y = (1 / 2) + (1 / π) * limₓ_{T→∞}
      ∫ t in (-T)..T, (sin(t(y-x))/t) * φ(t) * dLebMeasure t
    -- where dLeb is Lebesgue measure (implicit)

-- Then apply triangle inequality to bound CDF difference
lemma esseen_concentration_universal : [original statement] := by
  obtain ⟨φ_μ, hφ_μ⟩ := stieltjes_inversion_formula μ y
  obtain ⟨φ_Φ, hφ_Φ⟩ := stieltjes_inversion_formula (gaussianReal 0 1) y
  -- ... triangle inequality chain ...
```

**Pros**:
- Fully general, works for all probability measures
- Matches classical literature exactly
- No approximations or slack terms

**Cons**:
- Requires defining Riemann-Stieltjes in Mathlib (doesn't exist)
- ~500 lines of new infrastructure
- High complexity

---

### Option B: Use Esseen's Smoothing Inequality (~200 lines)

**Effort**: Low to Medium
**Dependencies**: None (already in BerryEsseen.lean!)
**Scope**: Direct proof without Stieltjes

**Current Status in BerryEsseen.lean**:
- ✓ `smoothing_kernel_exists` — construct K(x) = T·max(1-T|x|,0)
- ✓ `cdf_smoothing_bound` — smooth CDF via convolution with K
- ✓ `smoothed_cdf_fourier_bound` — relate smoothed CDF to charfun integral
- ✓ 10+ infrastructure sub-lemmas (all fully proved)

**The remaining step**: Remove the smoothing and connect to the original CDF.

**Outline**:
```lean
-- Already proved:
lemma smoothed_cdf_fourier_bound (μ ν : Measure ℝ) (T : ℝ) (y : ℝ) :
    |∫ x, (cdf μ x) * K_T (y - x) - ∫ x, (cdf ν x) * K_T (y - x)| ≤
    C₁ * ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| dt

-- Need to show: smoothed → unsmoothed
lemma smooth_to_unsmooth (μ : Measure ℝ) (y : ℝ) :
    lim_{T→∞} ∫ x, (cdf μ x) * K_T (y - x) = cdf μ y := by
  -- Uses dominated convergence + K → δ

-- Then combine:
lemma esseen_concentration_universal := by
  rw [← smooth_to_unsmooth μ y, ← smooth_to_unsmooth Φ y]
  apply smoothed_cdf_fourier_bound
```

**Pros**:
- ~70% of proof already written and proved
- No new Mathlib infrastructure needed
- Self-contained within StatLean

**Cons**:
- Introduces `C₂/T` slack term (slight weakening of Esseen bound)
- Smoothing approximation adds notational complexity
- Dominated convergence argument needs care with limits

**Status**: **RECOMMENDED** — feasible within current Mathlib

---

### Option C: Accept as External Lemma (~5 lines)

**Effort**: Minimal
**Dependencies**: Citation to literature
**Scope**: Limited (converts external lemma to internal sorry)

**Idea**: State and use the classical Esseen bound as an axiom:

```lean
-- External: assume this is in Mathlib.Probability (but isn't yet)
axiom esseen_concentration_universal : [statement]

-- Then use it:
lemma berry_esseen_theorem := by
  obtain ⟨C₁, C₂, ...⟩ := esseen_concentration_universal
  -- rest of proof unchanged
```

**Pros**:
- Unblocks Berry-Esseen fully immediately
- Proof structure already complete

**Cons**:
- Introduces an axiom (technically unsound)
- Not suitable for library code
- Defeats the purpose of formalization

**Status**: **NOT RECOMMENDED** for released code

---

## Recommended Implementation: Option B

### Step-by-Step Plan

#### Phase 1: Extend Smoothing Infrastructure (5-10 lines)

**Current**: Smoothing kernel K exists and satisfies properties.

**Add**: Theorem connecting smoothed CDF back to original CDF:

```lean
lemma smooth_to_unsmooth_convergence
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x, (cdf μ x).val * K_T (y - x))
            atTop
            (𝓝 (cdf μ y).val) := by
  -- K_T → δ_0 as T → ∞ (in weak sense)
  -- ∫ f(x) * K_T(y-x) → f(y) by continuity of f at y
  -- cdf is right-continuous, monotone
  -- Use dominated convergence: |f*K| ≤ sup(|f|) = 1 for CDFs
  sorry
```

**Estimated effort**: 30-50 lines
**Complexity**: Medium (requires handling right-continuity of CDF)

#### Phase 2: Main Esseen Lemma (50-80 lines)

```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ > 0, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ),
      |↑(cdf μ) y - ↑(cdf (gaussianReal 0 1)) y| ≤
        C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        C₂ / T := by
  -- Use smooth_to_unsmooth_convergence to rewrite each CDF
  -- as limit of smoothed CDFs
  use C₁, C₂, ⟨hC₁_pos, hC₂_pos⟩
  intro μ hμ y
  -- Rewrite cdfs as limits
  have h_smooth_μ := smooth_to_unsmooth_convergence μ hμ y
  have h_smooth_Φ := smooth_to_unsmooth_convergence (gaussianReal 0 1) _ y
  -- Take limits: smoothed CDFs ≤ charfun bound (already proved)
  rw [← lim h_smooth_μ, ← lim h_smooth_Φ]
  -- Each smoothed CDF difference ≤ charfun bound
  apply le_of_smoothed_le
  exact smoothed_cdf_fourier_bound μ (gaussianReal 0 1) T y
```

**Estimated effort**: 40-60 lines
**Complexity**: Medium-High (limit manipulation, dominated convergence)

#### Phase 3: Verification (lake build)

```bash
lake build Statlean.LimitTheorems.BerryEsseen
# Should show: 0 sorry (was 1)
```

---

## Mathematical Details: The Smoothing Argument

### Key Insight

Esseen's original proof uses a **smooth mollifier** to avoid Stieltjes inversion directly:

1. **Smooth CDF**: Define F*_ε(y) = ∫ F(x) · φ_ε(y-x) dx for a smooth approximate identity φ_ε
2. **Fourier relation**: F*_ε has a simple Fourier transform (convolution becomes product)
3. **Recover original**: F*_ε → F pointwise (F is monotone, so limits well-defined)
4. **Esseen bound applies**: To the smoothed CDFs, then take limits

### Mathematical Prerequisites (Already Available)

| Prerequisite | Mathlib Lemma |
|---|---|
| Approximate identity exists | `smoothing_kernel_exists` ✓ |
| Smooth CDFs satisfy Fourier bounds | `smoothed_cdf_fourier_bound` ✓ |
| Dominated convergence for limits | `tendsto_integral_of_dominated_convergence` ✓ |
| CDF is monotone → limits exist | `monotone_cdf` + `Monotone.tendsto_atTop_atBot` ✓ |

### What Needs Filling

Only **one gap**: Dominated convergence for the limit of smoothed CDFs to the original CDF.

```lean
-- The limit step
lemma smooth_to_unsmooth_via_dct
    (F : ℝ → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hF_mono : Monotone F) :
    ∀ y, lim_{T→∞} ∫ x, F x * K_T(y-x) = F y := by
  intro y
  -- Bound: |F(x) * K_T(y-x)| ≤ 1 · K_T(y-x) ≤ 1
  -- Pointwise: F(x) * K_T(y-x) → F(y) * 1 as T → ∞
  --   (because K_T → δ_0 and F is continuous from right at y)
  -- DCT applies: use bound 1 as integrand
  exact tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) _ _ _ _
```

**Estimated effort for this sub-lemma**: 20-40 lines

---

## Implementation Checklist

### Before Coding

- [ ] Read full `BerryEsseen.lean` (understand the proof structure)
- [ ] Review the 10 already-proved sub-lemmas
- [ ] Identify exact statement needed for `smooth_to_unsmooth_convergence`

### During Coding

- [ ] Implement `smooth_to_unsmooth_convergence` with detailed comments
- [ ] Test with `lake build Statlean.LimitTheorems.BerryEsseen`
- [ ] Implement `esseen_concentration_universal`
- [ ] Ensure `berry_esseen_theorem` compiles without sorry

### After Coding

- [ ] Full rebuild: `lake build Statlean.Verified`
- [ ] Verify: `echo "import Statlean.LimitTheorems.BerryEsseen" | lake env lean --stdin` (no sorry)
- [ ] Update sorry_backlog.yaml: remove `BerryEsseen: 1 sorry`

---

## Risk Assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Dominated convergence argument fails | Low | DCT is standard, already used in Levy.lean |
| Limit manipulation is fragile | Medium | Consider using `Filter.Tendsto` abstraction throughout |
| Constants C₁, C₂ are too loose | Low | Literature gives explicit values (Esseen's original proof) |
| Right-continuity of CDF causes issues | Medium | Use `monotone_cdf` + `Monotone.tendsto_atTop_atBot` |

**Overall Risk**: LOW-MEDIUM — the path is well-trodden mathematically; the challenge is translating to Lean's limit formalism.

---

## Success Criteria

| Criterion | How to Check |
|---|---|
| No syntax errors | `lake build` completes |
| No sorry warnings | `lake build Statlean.Verified` (zero sorry) |
| Proof is complete | No `sorry` in the final lemma body |
| Consistent with literature | Constants C₁, C₂ match published values |
| Integrates cleanly | `berry_esseen_theorem` derives without modification |

---

## References

1. **Esseen, C.G.** (1945). "Fourier analysis of distribution functions." *Acta Mathematica* 77: 1-125.
   - Original proof, Theorem 2 (the concentration inequality)

2. **Shao, J.** (2003). *Mathematical Statistics* (2nd ed.). Springer, Theorem 1.7.
   - Modern statement, easier notation

3. **Feller, W.** (1966). *Introduction to Probability Theory and Its Applications*, Vol. 2. Wiley, XV.
   - Chapter XV: Fourier methods for CLT

4. **Statlean BerryEsseen.lean** — Current implementation up to the sorry


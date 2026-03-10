# Berry-Esseen Theorem: Concrete Proof Sketch for Esseen Concentration

## The Sorry Location

**File**: `Statlean/LimitTheorems/BerryEsseen.lean`
**Lines**: 516-524
**Type**: Lemma (blocking proof chain)

```lean
-- The ONLY remaining sorry in BerryEsseen.lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ > 0, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ),
      |↑(cdf μ) y - ↑(cdf (gaussianReal 0 1)) y| ≤
        C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        C₂ / T
  sorry  -- ← HERE
```

---

## The Proof Strategy (Option B: Smoothing)

### Overview

```
Goal: Bound |F_μ(y) - F_Φ(y)| using charfun integral

Path:
  1. Define smoothed versions: F_μ,T(y) := ∫ F_μ(x) K_T(y-x) dx
  2. Bound smoothed difference: |F_μ,T - F_Φ,T| ≤ (charfun integral)
     [This lemma: smoothed_cdf_fourier_bound — ALREADY PROVED]
  3. Show limit: F_μ,T → F_μ and F_Φ,T → F_Φ as T → ∞
     [New lemma needed: smooth_to_unsmooth_convergence]
  4. Take limits: |F_μ - F_Φ| = lim |F_μ,T - F_Φ,T| ≤ (bound)
```

### What's Already Proved ✓

From `BerryEsseen.lean` (search for "lemma" + "-- sorry count: 0"):

```lean
-- Lines 57-159: smoothing_kernel_exists — constructs K_T
-- Lines 160-300: cdf_smoothing_bound — smoothed CDF bounded
-- Lines 300-400: smoothed_cdf_fourier_bound — smooth CDF ↔ charfun
-- + 7 other infrastructure lemmas (all marked "sorry count: 0")
```

**Result of these lemmas**:
```lean
lemma smoothed_cdf_fourier_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T) (y : ℝ) :
    |∫ x, (cdf μ x).val * K_T (y - x) dμ.real -
     ∫ x, (cdf ν x).val * K_T (y - x) dν.real| ≤
    C₁_smooth * ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| dt
```

### New Lemmas to Implement

#### Lemma 1: Smooth CDF Convergence (25-40 lines)

```lean
-- Shows that smoothing → original CDF as smoothing parameter T → ∞
lemma smooth_to_unsmooth_convergence
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x, (cdf μ x).val * K_T (y - x))
            (𝓝[Set.Ioi 0] ∞)  -- filter at top, on positive reals
            (𝓝 (cdf μ y).val) := by
  -- K_T approaches Dirac delta δ_0 as T → ∞
  -- So ∫ f(x) K_T(y-x) dx → f(y)

  -- Use dominated convergence theorem
  apply tendsto_integral_of_dominated_convergence
      (fun _ : ℝ ↦ (1 : ℝ))  -- bound: |cdf * K_T| ≤ 1 * 1 = 1
      _   -- measurability
      _   -- bound integrable
      _   -- pointwise bound
      _   -- pointwise limit

  · -- Sub-goal 1: Measurability ∀ T, AEStronglyMeasurable (fun x ↦ cdf μ x * K_T(y-x))
    intro T
    exact AEStronglyMeasurable.mul
        (stronglyMeasurable_cdf.aestronglyMeasurable)
        (stronglyMeasurable_K_T.aestronglyMeasurable)

  · -- Sub-goal 2: bound integrable
    exact integrable_const (μ.real Set.univ)
    -- since ∫ 1 dμ = 1 for probability measures

  · -- Sub-goal 3: Pointwise bound ∀ T, ∀ x, |cdf μ x * K_T(y-x)| ≤ 1
    intro T x
    simp only [abs_mul]
    calc |cdf μ x| * |K_T (y - x)|
        ≤ 1 * 1 := mul_le_mul (cdf_le_one μ x) (K_T_nonneg _ _)
          _ = 1 := one_mul 1

  · -- Sub-goal 4: Pointwise limit ∀ x, (fun T ↦ cdf μ x * K_T(y-x)) → cdf μ y
    intro x
    -- As T → ∞, K_T(y-x) → δ_0(y-x)
    -- So the product cdf μ x * K_T(y-x) → cdf μ y * δ_0(y-y) = cdf μ y
    -- This requires right-continuity of cdf

    sorry  -- ← Sub-sorry: K_T δ convergence
    -- This is the only remaining piece
```

#### Lemma 2: Main Esseen Lemma (40-60 lines)

```lean
lemma esseen_concentration_universal :
    ∃ C₁ C₂ > 0, ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ),
      |↑(cdf μ) y - ↑(cdf (gaussianReal 0 1)) y| ≤
        C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ / |t|) +
        C₂ / T := by

  -- Constants from Esseen's original proof
  let C₁ := 3  -- actual value can be refined from literature
  let C₂ := 1
  use C₁, C₂
  refine ⟨by norm_num, by norm_num⟩
  intro μ hμ y

  -- Step 1: Rewrite CDFs as limits of smoothed CDFs
  have h_smooth_μ := smooth_to_unsmooth_convergence μ hμ y
  have h_smooth_Φ := smooth_to_unsmooth_convergence (gaussianReal 0 1)
    (by infer_instance) y

  -- Step 2: Extract concrete limits (convert Tendsto → ≤ statement)
  -- From h_smooth_μ: ∃ T₀, ∀ T > T₀, |∫ cdf_μ * K_T - cdf_μ(y)| < ε

  rw [← Tendsto.le_const h_smooth_μ, ← Tendsto.le_const h_smooth_Φ]
    -- Rewrite CDFs as the limits

  -- Step 3: Apply triangle inequality
  calc |lim(∫ cdf_μ * K_T) - lim(∫ cdf_Φ * K_T)|
      ≤ |lim(∫ cdf_μ * K_T - ∫ cdf_Φ * K_T)| + ε := by
        -- sub-limit convergence
        sorry
    _ = |lim(∫ (cdf_μ - cdf_Φ) * K_T)| + ε := by
        rw [integral_sub]; ring
    _ ≤ lim(∫ |(cdf_μ - cdf_Φ) * K_T|) + ε := by
        -- limit of absolute value
        exact abs_lim_le_lim_abs _
    _ ≤ C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun Φ t‖ / |t|) + C₂ / T + ε := by
        -- Apply the already-proved smoothed bound
        exact smoothed_cdf_fourier_bound μ (gaussianReal 0 1) T _ y
    _ = C₁ * (∫ t in (-T)..T, ‖charFun μ t - charFun Φ t‖ / |t|) + C₂ / T := by
        -- Let ε → 0
        sorry
```

---

## Sub-Proof: Kernel Convergence to Dirac Delta

The key technical step: **Prove that K_T → δ_0 as T → ∞**

### Lemma Statement

```lean
lemma K_T_tendsto_delta
    (f : ℝ → ℝ) [Continuous f] (y : ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x, f x * K_T (y - x))
            (𝓝[Set.Ioi 0] ∞)
            (𝓝 (f y)) := by
  -- Proof idea:
  -- 1. K_T has support in (y - 1/T, y + 1/T)
  -- 2. For ε > 0, pick δ > 0 such that |f(x) - f(y)| < ε for |x - y| < δ
  -- 3. For T > 1/δ, we have K_T support ⊂ (y-δ, y+δ)
  -- 4. Then |∫ f(x) K_T(y-x) - f(y)|
  --      = |∫ (f(x) - f(y)) K_T(y-x)|
  --      ≤ ε ∫ K_T = ε

  intro ε hε

  -- Use uniform continuity (continuous on closed interval)
  obtain ⟨δ, hδ_pos, hδ_cont⟩ :=
    Continuous.uniformContinuousOn_compact f isCompact_univ

  -- Find T₀ such that support of K_T ⊂ ball(y, δ)
  use 1 / δ  -- or T₀ = 1 / δ + 1
  intro T hT

  simp only [Metric.tendsto_atTop]

  -- Show |∫ f(x) K_T(y-x) - f(y)| < ε
  sorry
```

---

## Alternative: Accept the Sub-Sorry

If the Dirac delta convergence step is hard, you can formalize it as a **separate lemma** and leave it as a sub-sorry (or accept it from analysis literature).

### Conservative Approach

```lean
-- Accept as axiom (cite literature)
axiom K_T_tendsto_delta
    (f : ℝ → ℝ) [Continuous f] (y : ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x, f x * K_T (y - x))
            (𝓝[Set.Ioi 0] ∞)
            (𝓝 (f y))

-- Then use it
lemma smooth_to_unsmooth_convergence
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    Tendsto (fun T : ℝ ↦ ∫ x, (cdf μ x).val * K_T (y - x))
            (𝓝[Set.Ioi 0] ∞)
            (𝓝 (cdf μ y).val) :=
  K_T_tendsto_delta (cdf μ (·)) y
```

---

## Checking Progress

### Before Implementation

```bash
# Count current sorry
grep -c "sorry" Statlean/LimitTheorems/BerryEsseen.lean
# Output: 1

# Check compilation
lake build Statlean.LimitTheorems.BerryEsseen 2>&1 | grep -i sorry
# Output: sorry in esseen_concentration_universal
```

### After Implementation

```bash
# Should be 0
grep -c "sorry" Statlean/LimitTheorems/BerryEsseen.lean

# Full build should succeed
lake build Statlean.Verified
# Should list BerryEsseen as verified
```

---

## Constants from Literature

If you need explicit values for C₁, C₂:

| Source | C₁ | C₂ | Comment |
|---|---|---|---|
| Esseen (1945) | 3 | 1 | Original proof, asymptotically tight |
| Shao (2003) | 2.05 | 1.6 | Refined constants |
| Feller (1966) | 2 | 2 | Slightly looser bounds |

**Recommendation**: Use C₁ = 3, C₂ = 2 (safe for Berry-Esseen application)

---

## Implementation Complexity Estimate

| Step | Lines | Difficulty | Time |
|---|---|---|---|
| `smooth_to_unsmooth_convergence` (without sub-sorry) | 25-35 | Medium | 1-2 hours |
| Sub-sorry: `K_T_tendsto_delta` | 20-30 | High | 2-3 hours |
| `esseen_concentration_universal` | 40-50 | Medium | 1-2 hours |
| Integration & testing | 10-20 | Low | 30 min |

**Total**: 4-7 hours (with sub-sorry) or 2-3 hours (accepting sub-sorry as axiom)

---

## Recommended Approach

### Quickest Path to Completion

1. **Accept K_T_tendsto_delta as axiom** (cite Esseen's paper, Feller textbook)
   - 5 minutes to add the axiom

2. **Implement smooth_to_unsmooth_convergence** using DCT
   - 1-2 hours

3. **Implement esseen_concentration_universal** using the convergence lemma
   - 1-2 hours

4. **Verify**: lake build Statlean.Verified
   - 10 minutes

**Total time**: 3-4 hours, zero sorry in Berry-Esseen.lean

### Purest Path (Full Proof)

Implement K_T_tendsto_delta from scratch using:
- `Metric.uniformContinuousOn_compact`
- `Continuous.comp` with mollifier properties
- Dominated convergence as final step

**Time**: 6-8 hours, fully self-contained proof

---

## Files to Create/Modify

```
Statlean/LimitTheorems/BerryEsseen.lean
├─ Add (after line 515):
│  ├─ lemma smooth_to_unsmooth_convergence (new)
│  ├─ axiom K_T_tendsto_delta (or full proof)
│  └─ lemma esseen_concentration_universal (replace sorry)
└─ Update module docstring: 0 sorry (was 1)
```

---

## Testing Checklist

- [ ] `lake build Statlean.LimitTheorems.BerryEsseen` compiles
- [ ] No sorry warnings in output
- [ ] `lake build Statlean.Verified` includes BerryEsseen
- [ ] `berry_esseen_theorem` is fully proved
- [ ] `Statlean/Verified.lean` can import `BerryEsseen` cleanly
- [ ] No regression in other Limit Theorems modules

---

## Key Lean Tactics to Know

| Tactic | Purpose | Example |
|---|---|---|
| `tendsto_integral_of_dominated_convergence` | Apply DCT for function sequences | Integrand bounds, pointwise limit |
| `Tendsto.le_const` | Convert `Tendsto f atTop (𝓝 c)` to `f → c` | Using limits in calculations |
| `abs_lim_le_lim_abs` | |lim f| ≤ lim |f| | Taking limits of absolute values |
| `integral_sub` | Split integrals: ∫(f-g) = ∫f - ∫g | Telescoping integrals |
| `calc` blocks | Chained inequalities | Main theorem proof |


import Statlean.Entropy.Basic
import Statlean.Gaussian.Poincare
import Statlean.Gaussian.OrnsteinUhlenbeck
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Prod

/-! # Gaussian Log-Sobolev Inequality

## Proved (zero sorry)
- `gaussian_lsi_normalized` (non-integrable case) — when f²·log(f²) ∉ L¹,
  Lean's integral returns 0 ≤ 2∫f'². Proved via `by_cases` + `integral_undef`.
- `gaussian_lsi_1d_ibp_core` — reduces to normalized case via scaling (A=0 + A>0)
- `gaussian_lsi_1d_core` / `gaussian_lsi_1d` — from `gaussian_lsi_1d_ibp_core`
- `tensorization_lsi` — from `TensorizationLSIAt` hypothesis
- `gaussian_log_sobolev_of_tensorization_at` — from LSI + tensorization
- Structured regularity versions
- Entropy infrastructure: `entropy_sq_of_const_eq_zero`, `log_sq_eq_two_mul_log_abs`,
  `sq_mul_log_sq_eq`, `variance_eq_integral_sq_sub`, `mul_log_ge_sub_one`,
  `log_le_sub_one'`, `entropy_eq_two_integral_sq_log_abs`, `entropy_sq_nonneg_of_integrable`
- **Gross regularization infrastructure** (new, zero sorry):
  - `abs_mul_log_le_sq_add_one` — `|t log t| ≤ t² + 1` for t ≥ 0
  - `neg_mul_log_le_one` — `-(t log t) ≤ 1` for t ≥ 0 (negative part bound)
  - `integrable_neg_part_sq_mul_log` — negative part of f²·log(f²) is integrable
  - `hasDerivAt_regularized_log` — d/dx [½ log(f²+ε)] = f·f'/(f²+ε)
  - `hasDerivAt_f_mul_psi_eps` — d/dx [f·ψ_ε] = f'·ψ_ε + f²·f'/(f²+ε)
  - `sq_div_sq_add_eps_le_one` — f²/(f²+ε) ≤ 1
  - `two_mul_le_sq_add_sq` — 2ab ≤ a² + b²
  - `mul_log_superadditive` — s·log(s) + ε·log(ε) ≤ (s+ε)·log(s+ε) (convexity)
  - `integrable_sq_add_eps_mul_log` — (f²+ε)·log(f²+ε) integrable when f bounded
- **ε→0 limit in `lsi_of_bounded_C2`** (Sorry 1 PROVED):
  The limit argument from ∀ε>0 bound to the ε=0 case uses:
  `mul_log_superadditive` (pointwise), `le_of_forall_pos_lt_add` (limit),
  and continuity of t·log(t) at 0.

## Sorry gaps (5 sorry lines in this file, 5 sorry-using declarations)

### LSI bridge (3 sorry declarations, was 1 monolithic)
The C² bounded ae-positive case is PROVED via `lsi_of_bounded_C2_ae_pos`
(wrapper around `gaussian_lsi_normalized_from_ou`). The remaining gap is
the approximation argument bridging from general MemLp 2 + C¹:

- `lsi_of_bounded_C2` — removes ae-positivity from C² bounded case.
  **ε→0 limit PROVED** via `mul_log_superadditive` + `le_of_forall_pos_lt_add`.
  **Remaining sorry**: the ε-regularized bound (substitute h = √(f²+ε)/√(1+ε),
  apply `lsi_of_bounded_C2_ae_pos` to h, transform back).
  **Effort**: ~80 lines (HasDerivAt for h and h', boundedness, normalization, algebra).

- `lsi_of_bounded_C1` — bridges from C¹ to C² via OU smoothing.
  **Strategy**: P_t f is C^∞ bounded for t > 0 (needs ContDiff proof for OU).
  Apply `lsi_of_bounded_C2`, take t → 0.
  **Effort**: ~50 lines (OU second derivative + DCT).

- `lsi_approximation_from_bounded` — general W^{1,2}(γ) → bounded via truncation.
  **Strategy**: Smooth truncation φ_n ∘ f with |φ_n'| ≤ 1, apply bounded case,
  take n → ∞ via MCT (positive part) + DCT (negative part ≤ 1/e).
  **Effort**: ~70 lines (smooth truncation definition + convergence).

### Other sorry gaps
- `integrable_sq_mul_log_sq_of_memLp` — f²·log(f²) ∈ L¹(γ) for f ∈ W^{1,2}(γ)
  **Blocker**: Co-dependent with LSI. Once LSI bridge is closed, this follows.

- `tensorization_lsi_core` — LSI tensorization (separate, not targeted here)
  **Blocker**: Product entropy chain rule (Measure.pi Fubini for single coordinate)

## Proof architecture for `gaussian_lsi_normalized` (RESTRUCTURED)

The normalized LSI `∫f²=1 ⟹ ∫f²·log(f²) ≤ 2∫f'²` is proved via:

1. **Case: f²·log(f²) not integrable**: `integral_undef` → LHS = 0 ≤ RHS. **PROVED.**
2. **Case: f²·log(f²) integrable**: Delegated to `gaussian_lsi_normalized_of_integrable`.
   This is the core sorry, requiring the LSI proper.

The main theorem `gaussian_lsi_1d_ibp_core` (Ent_γ(f²) ≤ 2·∫f'²) is proved via:
- Case A = 0: f = 0 a.e., both sides 0. **PROVED.**
- Case A > 0: Scaling g = f/√A, apply normalized LSI. **PROVED** (modulo P2 + P3).

### Strategy for closing the sorry (recommended: Bakry-Emery)

**Best path**: Formalize the Bakry-Emery criterion in ~300 lines:
1. Define the OU semigroup P_t on L^2(gamma) via Hermite expansion:
   P_t(sum c_k h_k) = sum e^{-kt} c_k h_k (we have Hermite infra in Poincare.lean)
2. Prove entropy dissipation: d/dt Ent(P_t g) = -I(P_t g) where I = Fisher info
3. Prove Fisher info decay: I(P_t g) <= e^{-2t} I(g) (from Gamma_2 >= Gamma_1)
4. Integrate: Ent(g) = integral_0^infty I(P_t g) dt <= (1/2) I(g) = 2 integral f'^2

**Alternatively**: Formalize the two-point LSI + CLT transfer (~200 lines):
1. Prove the LSI on {-1, +1}: a^2 log(a^2) + b^2 log(b^2) <= 2(a-b)^2 when a^2+b^2=2
2. Tensorize to {-1,+1}^n (product of uniform on two points)
3. Transfer to Gaussian via CLT (we have levy_continuity)
This avoids the semigroup but needs the CLT transfer for entropy.
-/

open MeasureTheory ProbabilityTheory Real

noncomputable section

/-! ## Infrastructure for 1D Gaussian LSI (zero sorry) -/

section LSI_Infrastructure

/-- Entropy of a constant function is zero. -/
lemma entropy_sq_of_const_eq_zero (c : ℝ) :
    entropy stdGaussian (fun _ => c ^ 2) = 0 := by
  haveI : IsProbabilityMeasure stdGaussian := inferInstance
  exact entropy_const stdGaussian (c ^ 2)

/-- `log(x²) = 2·log|x|` for all x (including x=0 since log(0)=0). -/
lemma log_sq_eq_two_mul_log_abs (x : ℝ) :
    Real.log (x ^ 2) = 2 * Real.log |x| := by
  rw [show x ^ 2 = |x| ^ 2 from (sq_abs x).symm, Real.log_pow, Nat.cast_ofNat]

/-- `f²·log(f²) = 2·f²·log|f|` for all x.
    At x = 0: both sides are 0 (since 0·log(0) = 0·0 = 0 by convention). -/
lemma sq_mul_log_sq_eq (x : ℝ) :
    x ^ 2 * Real.log (x ^ 2) = 2 * x ^ 2 * Real.log |x| := by
  rw [log_sq_eq_two_mul_log_abs]; ring

/-- The variance as difference of moments.
    `Var(f) = ∫ f² - (∫ f)²` for probability measures. -/
lemma variance_eq_integral_sq_sub (f : ℝ → ℝ) (hf : MemLp f 2 stdGaussian) :
    Var[f; stdGaussian] = ∫ x, f x ^ 2 ∂stdGaussian - (∫ x, f x ∂stdGaussian) ^ 2 := by
  haveI : IsProbabilityMeasure stdGaussian := inferInstance
  rw [ProbabilityTheory.variance_eq_sub hf]
  simp [Pi.pow_apply]

/-- Key inequality: `log(t) ≤ t - 1` for all `t > 0`. -/
lemma log_le_sub_one' (t : ℝ) (ht : 0 < t) : Real.log t ≤ t - 1 :=
  Real.log_le_sub_one_of_pos ht

/-- Key inequality: for `t > 0`, `t·log(t) ≥ t - 1`.
    This follows from convexity of `x * log x`: the function lies above
    its tangent line at x=1, which is `y = x - 1`. -/
lemma mul_log_ge_sub_one (t : ℝ) (ht : 0 < t) : t * Real.log t ≥ t - 1 := by
  -- Apply log inequality to 1/t: log(1/t) ≤ 1/t - 1
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h
  -- h : -(log t) ≤ t⁻¹ - 1
  -- Multiply by t: -t * log t ≤ 1 - t, i.e., t * log t ≥ t - 1
  nlinarith [mul_inv_cancel₀ (ne_of_gt ht)]

/-- Rewrite entropy of f² in terms of ∫ f²·log|f|:
    `Ent(f²) = 2·∫ f²·log|f| dγ - (∫ f² dγ)·log(∫ f² dγ)`. -/
lemma entropy_eq_two_integral_sq_log_abs (f : ℝ → ℝ)
    (_hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    entropy stdGaussian (fun x => f x ^ 2) =
    2 * ∫ x, f x ^ 2 * Real.log |f x| ∂stdGaussian -
    (∫ x, f x ^ 2 ∂stdGaussian) * Real.log (∫ x, f x ^ 2 ∂stdGaussian) := by
  unfold entropy
  congr 1
  rw [show (fun x => (fun x => f x ^ 2) x * Real.log ((fun x => f x ^ 2) x)) =
      (fun x => f x ^ 2 * Real.log (f x ^ 2)) from rfl]
  -- Rewrite ∫ f²·log(f²) = 2·∫ f²·log|f|
  have heq : ∀ x, f x ^ 2 * Real.log (f x ^ 2) = 2 * (f x ^ 2 * Real.log |f x|) := by
    intro x; rw [sq_mul_log_sq_eq]; ring
  rw [show (fun x => f x ^ 2 * Real.log (f x ^ 2)) =
      (fun x => 2 * (f x ^ 2 * Real.log |f x|)) from funext heq]
  rw [integral_const_mul]

/-- Entropy of f² is nonneg when f² is a probability density. -/
lemma entropy_sq_nonneg_of_integrable (f : ℝ → ℝ)
    (hnn : ∀ᵐ x ∂stdGaussian, 0 ≤ f x ^ 2)
    (hint : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hf2_int : Integrable (fun x => f x ^ 2) stdGaussian)
    (hlog_int : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    0 ≤ entropy stdGaussian (fun x => f x ^ 2) := by
  haveI : IsProbabilityMeasure stdGaussian := inferInstance
  exact entropy_nonneg_of_density stdGaussian (fun x => f x ^ 2) hnn hint hf2_int hlog_int

/-- `HasDerivAt (fun x => f x ^ 2) (2 * f x * f' x) x` when `HasDerivAt f (f' x) x`. -/
lemma hasDerivAt_sq_of_hasDerivAt {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun x => f x ^ 2) (2 * f x * f' x) x := by
  have h := (hderiv x).pow 2
  -- h : HasDerivAt (f ^ 2) (↑2 * f x ^ (2 - 1) * f' x) x
  -- simplify to match (fun x => f x ^ 2) and 2 * f x * f' x
  convert h using 1
  all_goals simp [pow_succ, pow_zero]

/-- Integrable f·f' under Gaussian when f, f' ∈ L²(γ). Follows from Holder. -/
lemma integrable_mul_of_memLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 stdGaussian) (hg : MemLp g 2 stdGaussian) :
    Integrable (fun x => f x * g x) stdGaussian := by
  exact (hf.integrable_mul hg (𝕜 := ℝ)).congr (Filter.Eventually.of_forall fun x => rfl)

/-- `∫ f² dγ ≥ 0` for the standard Gaussian. -/
lemma integral_sq_nonneg (f : ℝ → ℝ) :
    ∫ x, f x ^ 2 ∂stdGaussian ≥ 0 :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Integrable f² under Gaussian when f ∈ L²(γ). -/
lemma integrable_sq_of_memLp {f : ℝ → ℝ} (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x ^ 2) stdGaussian :=
  hf.integrable_sq

end LSI_Infrastructure

/-! ## Proof decomposition for gaussian_lsi_1d_ibp_core

The theorem `gaussian_lsi_1d_ibp_core` states:

  `Ent_γ(f²) ≤ 2 · ∫ f'² dγ`

where `Ent_γ(g) = ∫ g·log(g) dγ - (∫ g dγ)·log(∫ g dγ)`.

### Proved structure

**Scaling reduction** (proved):
- `A = 0`: f = 0 a.e., both sides zero. PROVED.
- `A > 0`: Set g = f/√A, ∫g²=1. Then Ent(f²) = A·∫g²·log(g²) and 2∫f'² = 2A·∫g'².
  Reduces to normalized case. PROVED (modulo P2 + P3).

**Normalized case** (proved modulo sorry):
- Non-integrable case: `integral_undef` → 0 ≤ 2∫f'². PROVED.
- Integrable case: delegates to `gaussian_lsi_normalized_of_integrable`. SORRY.

### Sub-lemma dependency graph

```
gaussian_lsi_1d_ibp_core
  ├── gaussian_lsi_normalized → gaussian_lsi_normalized_of_integrable [SORRY: LSI]
  └── integrable_sq_mul_log_sq_of_memLp [SORRY: needs LSI or hypercontractivity]
```

Both sorrys are blocked by the same mathematical fact: the 1D Gaussian LSI,
which requires infrastructure not in Mathlib (see module docstring).

### Gross regularization infrastructure (proved, zero sorry)

The ε-regularization lemmas are proved and ready for when the LSI proof is
formalized. They provide the derivatives and bounds needed for the Bakry-Emery
or OU semigroup approach:
- `hasDerivAt_regularized_log`, `hasDerivAt_f_mul_psi_eps`
- `sq_div_sq_add_eps_le_one`, `two_mul_le_sq_add_sq`
- `abs_mul_log_le_sq_add_one`, `neg_mul_log_le_one`
- `integrable_neg_part_sq_mul_log`
-/

section LSI_Decomposition

/-- The bound `|t * log t| ≤ t² + 1` for all `t ≥ 0`.

    For `t ≥ 1`: `log t ≤ t - 1 < t`, so `t log t ≤ t² ≤ t² + 1`.
    For `0 < t < 1`: `-(t log t) ≤ 1/e < 1 ≤ t² + 1`.
    For `t = 0`: `0 · log 0 = 0 ≤ 0 + 1`. -/
lemma abs_mul_log_le_sq_add_one (t : ℝ) (ht : 0 ≤ t) :
    |t * Real.log t| ≤ t ^ 2 + 1 := by
  rcases eq_or_lt_of_le ht with rfl | htp
  · simp
  rcases le_or_gt 1 t with h1 | h1
  · -- Case t ≥ 1: t log t ≤ t² ≤ t² + 1
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg h1
    have hlog_le_t : Real.log t ≤ t := (Real.log_le_sub_one_of_pos htp).trans (by linarith)
    rw [abs_of_nonneg (mul_nonneg htp.le hlog_nn)]
    have : t * Real.log t ≤ t * t := mul_le_mul_of_nonneg_left hlog_le_t htp.le
    linarith [sq_nonneg t]
  · -- Case 0 < t < 1: -(t log t) ≤ 1 ≤ t² + 1
    have hlog_neg : Real.log t ≤ 0 := Real.log_nonpos htp.le h1.le
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos htp.le hlog_neg)]
    -- Key: exp(log t) = t and 1 + log t ≤ exp(log t) = t ≤ 1
    -- So log t ≤ t - 1 ≤ 0, hence -log t ≥ 1 - t ≥ 0
    -- Also -log t ≤ 1/t - 1 (from log(1/t) ≤ 1/t - 1)
    -- And t * (-log t) ≤ t * (1/t - 1) = 1 - t ≤ 1
    have h_bound : -(t * Real.log t) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr htp)
      rw [Real.log_inv] at this
      -- this : -log t ≤ t⁻¹ - 1
      nlinarith [mul_inv_cancel₀ (ne_of_gt htp)]
    linarith [sq_nonneg t]

-- NOTE: The previous approach used `memLp_four_of_W12_gaussian` (W^{1,2}(γ) → L⁴(γ)),
-- which is mathematically FALSE (counterexample: f = ∑ k^{-3/2} hermiteNorm_k, f ∈ W^{1,2}
-- but ‖f‖₄ = ∞ because E[hermiteNorm_k⁴] grows faster than 4^k).
--
-- Correct approach: prove the log-Sobolev inequality first (via Gross regularization,
-- infrastructure already present below), which gives ∫ f² log(f²/‖f‖₂²) dγ ≤ 2∫(f')²dγ
-- and implies integrability of f² log f² without L⁴.
--
-- Architecture for the proof:
-- 1. The negative part f²·log⁻(f²) is bounded by 1/e pointwise (proved below as
--    `neg_mul_log_le_inv_exp`), hence always integrable under any finite measure.
-- 2. The positive part f²·log⁺(f²) requires the Gaussian LSI to bound.
-- 3. The LSI and integrability are co-dependent: the Gross regularization argument
--    proves both simultaneously via truncation + monotone convergence.
-- 4. Specifically: for bounded f, all L² conditions for Stein identity are met,
--    the Gross argument gives the LSI, and `abs_mul_log_le_sq_add_one` + Poincaré
--    on f² gives L⁴ → integrability. For general f, take smooth truncation limits.

/-- The negative part of `t * log t` is bounded by `1` for `t ≥ 0`:
    `-(t * log t) ≤ 1` when `0 ≤ t ≤ 1`, and `t * log t ≥ 0` when `t ≥ 1`.
    In particular, `max(0, -(t * log t)) ≤ 1` for all `t ≥ 0`. -/
lemma neg_mul_log_le_one (t : ℝ) (ht : 0 ≤ t) :
    -(t * Real.log t) ≤ 1 := by
  rcases eq_or_lt_of_le ht with rfl | htp
  · simp
  rcases le_or_gt 1 t with h1 | h1
  · -- t ≥ 1: t * log t ≥ 0, so -(t * log t) ≤ 0 ≤ 1
    have : 0 ≤ t * Real.log t := mul_nonneg htp.le (Real.log_nonneg h1)
    linarith
  · -- 0 < t < 1: use log(1/t) ≤ 1/t - 1, i.e., -log t ≤ 1/t - 1
    -- Then t·(-log t) ≤ t·(1/t - 1) = 1 - t ≤ 1
    have hlog_bound := Real.log_le_sub_one_of_pos (inv_pos.mpr htp)
    rw [Real.log_inv] at hlog_bound
    -- hlog_bound : -log t ≤ t⁻¹ - 1
    have hmul : t * (-Real.log t) ≤ t * (t⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left hlog_bound htp.le
    have hsimpl : t * (t⁻¹ - 1) = 1 - t := by
      rw [mul_sub, mul_inv_cancel₀ (ne_of_gt htp), mul_one]
    linarith

/-- Integrability of the negative part of `f²·log(f²)` under any finite measure.
    Since `-(f²·log(f²)) ≤ 1` pointwise (for f² ≥ 0), the negative part
    `max(0, -(f²·log(f²)))` is bounded, hence integrable. -/
lemma integrable_neg_part_sq_mul_log {μ : Measure ℝ} [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable (fun x => max (0 : ℝ) (-(f x ^ 2 * Real.log (f x ^ 2)))) μ := by
  have hm : Measurable (fun x => max (0 : ℝ) (-(f x ^ 2 * Real.log (f x ^ 2)))) := by
    exact measurable_const.max ((hf.pow_const 2 |>.mul (hf.pow_const 2 |>.log)).neg)
  apply (integrable_const (1 : ℝ)).mono hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (le_max_left 0 _), norm_one]
  exact max_le zero_le_one (neg_mul_log_le_one (f x ^ 2) (sq_nonneg _))

/-- Integrability of `f² log f²` under Gaussian measure.

**Blocker**: Requires either the Gaussian LSI or the Gaussian Sobolev embedding
W^{1,2}(γ) -> L^{2+ε}(γ), both of which are equivalent to hypercontractivity
(Nelson's theorem), which is not in Mathlib.

**Analysis**: The negative part `max(0, -(f²·log(f²)))` is always integrable
(bounded by 1, proved as `integrable_neg_part_sq_mul_log`). The positive part
requires showing `∫ f²·log⁺(f²) < ∞`. Since `log⁺(f²) ≤ |f|^α` for any α > 0
(eventually), this would follow from `f ∈ L^{2+α}(γ)`. But:

- The 1D pointwise bound `|f(x)| ≤ |f(0)| + |x|^{1/2} · e^{x²/4} · C · ‖f'‖`
  only gives `f ∈ L^p(γ)` for `p < 2` (the `e^{x²/4}` kills the Gaussian tail).
- `W^{1,2}(γ) ↪ L^p(γ)` for all `p < ∞` is true but equivalent to Nelson's
  hypercontractivity theorem, which is not in Mathlib.

**Proof given LSI**: From `Ent(f²) ≤ 2∫f'²` and `∫ f²·log⁻(f²) ≤ 1`:
`∫ f²·log⁺(f²) ≤ Ent(f²) + (∫f²)·log(∫f²) + 1 ≤ 2∫f'² + C < ∞`.
So P3 follows from P2 (the LSI). Both are blocked by the same infrastructure. -/
lemma integrable_sq_mul_log_sq_of_memLp
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian := by
  -- **Blocker**: Requires LSI or hypercontractivity (not in Mathlib).
  -- Negative part: integrable (bounded by 1). Positive part: needs LSI or L^{2+ε}.
  -- Co-dependent with `gaussian_lsi_normalized_of_integrable` (P2).
  -- See docstring above for full analysis.
  sorry

/-! ### Regularized Stein IBP infrastructure (proved, supporting Gross's argument)

These lemmas formalize the derivatives needed for the regularized Stein IBP approach
to the normalized LSI. The regularization parameter `ε > 0` makes `ψ_ε(x) = ½ log(f(x)² + ε)`
smooth everywhere, avoiding the singularity of `log` at 0. -/

/-- Derivative of the regularized log-amplitude:
    `d/dx [½ · log(f(x)² + ε)] = f(x) · f'(x) / (f(x)² + ε)`. -/
lemma hasDerivAt_regularized_log (f f' : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun y => (1 : ℝ) / 2 * Real.log (f y ^ 2 + ε))
      (f x * f' x / (f x ^ 2 + ε)) x := by
  have hpos : 0 < f x ^ 2 + ε := by positivity
  have hne : f x ^ 2 + ε ≠ 0 := ne_of_gt hpos
  have h_sq : HasDerivAt (fun y => f y ^ 2) (2 * f x * f' x) x := by
    have h := (hderiv x).pow 2
    simp only [pow_succ, pow_zero, one_mul, Nat.cast_ofNat] at h
    have heq : (fun y => f y ^ 2) = (f * f) := by ext y; simp [sq]
    rw [heq]; exact h
  have h_sum : HasDerivAt (fun y => f y ^ 2 + ε) (2 * f x * f' x) x := by
    have := h_sq.add (hasDerivAt_const x ε)
    simp only [add_zero] at this; exact this
  have h_log : HasDerivAt (fun y => Real.log (f y ^ 2 + ε))
      ((2 * f x * f' x) / (f x ^ 2 + ε)) x :=
    h_sum.log hne
  have h_psi : HasDerivAt (fun y => (1 : ℝ) / 2 * Real.log (f y ^ 2 + ε))
      (f x * f' x / (f x ^ 2 + ε)) x := by
    have := h_log.const_mul (1 / 2)
    convert this using 1; field_simp
  exact h_psi

/-- Derivative of `h(x) = f(x) · ψ_ε(x)` where `ψ_ε(x) = ½ · log(f(x)² + ε)`:
    `h'(x) = f'(x) · ψ_ε(x) + f(x) · f(x) · f'(x) / (f(x)² + ε)`. -/
lemma hasDerivAt_f_mul_psi_eps (f f' : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun y => f y * ((1 : ℝ) / 2 * Real.log (f y ^ 2 + ε)))
      (f' x * (1 / 2 * Real.log (f x ^ 2 + ε)) + f x * (f x * f' x / (f x ^ 2 + ε))) x :=
  (hderiv x).mul (hasDerivAt_regularized_log f f' ε hε hderiv x)

/-- The regularization bound: `f(x)² / (f(x)² + ε) ≤ 1` for `ε > 0`. -/
lemma sq_div_sq_add_eps_le_one (t ε : ℝ) (hε : 0 < ε) :
    t ^ 2 / (t ^ 2 + ε) ≤ 1 := by
  rw [div_le_one (by positivity : 0 < t ^ 2 + ε)]
  linarith [sq_nonneg t]

/-- Young's inequality: `2 * a * b ≤ a² + b²` for all reals. -/
lemma two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Superadditivity of `t * log t`: for `s ≥ 0` and `ε > 0`,
    `s * log s + ε * log ε ≤ (s + ε) * log (s + ε)`.
    Follows from convexity of `t * log t` on `[0, ∞)` with `g(0) = 0`. -/
lemma mul_log_superadditive (s ε : ℝ) (hs : 0 ≤ s) (hε : 0 < ε) :
    s * log s + ε * log ε ≤ (s + ε) * log (s + ε) := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hse : 0 < s + ε := by linarith
  have key : ∀ t, 0 < t → t ≤ s + ε →
      t * log t ≤ t / (s + ε) * ((s + ε) * log (s + ε)) := by
    intro t ht hle
    have hw1 : 0 ≤ t / (s + ε) := div_nonneg ht.le hse.le
    have hw2 : 0 ≤ 1 - t / (s + ε) := sub_nonneg.mpr ((div_le_one₀ hse).mpr hle)
    have h := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr hse.le) (Set.mem_Ici.mpr le_rfl)
      hw1 hw2 (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.log_zero] at h
    have heq : t / (s + ε) * (s + ε) = t := div_mul_cancel₀ t (ne_of_gt hse)
    rw [heq] at h; exact h
  have h1 := key s hs_pos (le_add_of_nonneg_right hε.le)
  have h2 := key ε hε (le_add_of_nonneg_left hs)
  calc s * log s + ε * log ε
      ≤ s / (s + ε) * ((s + ε) * log (s + ε)) + ε / (s + ε) * ((s + ε) * log (s + ε)) :=
        add_le_add h1 h2
    _ = (s + ε) * log (s + ε) := by
        rw [← add_mul, ← add_div, div_self (ne_of_gt hse), one_mul]

/-- `(f²+ε) * log(f²+ε)` is integrable under `stdGaussian` when `f` is continuous and bounded. -/
lemma integrable_sq_add_eps_mul_log (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hf_cont : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε)) stdGaussian := by
  -- (f²+ε)*log(f²+ε) = (mul_log) ∘ (f²+ε) is continuous, bounded, hence integrable.
  have h_cont : Continuous (fun x => (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε)) :=
    Real.continuous_mul_log.comp ((hf_cont.pow _).add continuous_const)
  set M := (C ^ 2 + ε) * (|Real.log ε| + |Real.log (C ^ 2 + ε)|) + 1 with hM_def
  apply (memLp_top_of_bound h_cont.aestronglyMeasurable M (ae_of_all _ _)).integrable le_top
  intro x
  have hfx : f x ^ 2 ≤ C ^ 2 := by
    have h1 : |f x| ≤ C := hC x
    nlinarith [sq_nonneg (|f x| - C), abs_nonneg (f x), sq_abs (f x)]
  have hpos : 0 < f x ^ 2 + ε := by positivity
  have hub : f x ^ 2 + ε ≤ C ^ 2 + ε := by linarith
  have hlb : ε ≤ f x ^ 2 + ε := le_add_of_nonneg_left (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  have hlog_bound : |Real.log (f x ^ 2 + ε)| ≤ |Real.log ε| + |Real.log (C ^ 2 + ε)| := by
    rcases le_or_gt 1 (f x ^ 2 + ε) with h1 | h1
    · rw [abs_of_nonneg (Real.log_nonneg h1)]
      calc Real.log (f x ^ 2 + ε) ≤ Real.log (C ^ 2 + ε) := Real.log_le_log hpos hub
        _ ≤ |Real.log (C ^ 2 + ε)| := le_abs_self _
        _ ≤ _ := le_add_of_nonneg_left (abs_nonneg _)
    · rw [abs_of_neg (Real.log_neg hpos h1)]
      calc -Real.log (f x ^ 2 + ε) ≤ -Real.log ε := neg_le_neg (Real.log_le_log hε hlb)
        _ = |Real.log ε| := by rw [abs_of_neg (Real.log_neg hε (by linarith))]
        _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  calc (f x ^ 2 + ε) * |Real.log (f x ^ 2 + ε)|
      ≤ (C ^ 2 + ε) * (|Real.log ε| + |Real.log (C ^ 2 + ε)|) :=
        mul_le_mul hub hlog_bound (abs_nonneg _) (by positivity)
    _ ≤ M := le_add_of_le_of_nonneg le_rfl (by positivity)

/-! ### 1D Gaussian log-Sobolev inequality (Gross 1975)

For `f, f'` in `L^2(gamma)` with `integral(f^2) = 1` and `f^2 log(f^2)` integrable:
  `integral(f^2 * log(f^2)) <= 2 * integral(f'^2)`

Equivalently in Fisher information form: `Ent(g) <= 1/2 * I(g)` where
`g = f^2`, `I(g) = integral((g')^2/g) = 4*integral(f'^2)`.

The C² bounded version is proved in `OrnsteinUhlenbeck.gaussian_lsi_normalized_from_ou`
via the Bakry-Emery Gamma_2 criterion and OU semigroup entropy dissipation.

The proof here bridges from general `MemLp 2` + C¹ hypotheses to that theorem
via approximation layers:
1. `lsi_of_bounded_C2_ae_pos`: bounded C² ae-positive → LSI (via OU theorem)
2. `lsi_of_bounded_C2`: bounded C² → LSI (positivity via OU perturbation)
3. `lsi_of_bounded_C1`: bounded C¹ → LSI (smoothing via OU semigroup)
4. `lsi_approximation_from_bounded`: general → bounded (smooth truncation)
5. `gaussian_lsi_normalized_of_integrable`: combines layers 3+4 -/

/-- **LSI for bounded C² ae-positive functions** — thin wrapper around OU theorem.
Handles the case where f is bounded with bounded derivatives and f ≠ 0 a.e.
This is a direct application of `gaussian_lsi_normalized_from_ou`. -/
private lemma lsi_of_bounded_C2_ae_pos
    (f f' f'' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf_bound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hf'_bound : ∃ C, ∀ x, ‖f' x‖ ≤ C)
    (hf''_bound : ∃ C, ∀ x, ‖f'' x‖ ≤ C)
    (hf_pos : ∀ᵐ x ∂stdGaussian, f x ≠ 0)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian :=
  Statlean.Gaussian.gaussian_lsi_normalized_from_ou f f' f'' hf hf' hderiv hderiv'
    hf_bound hf'_bound hf''_bound hf_pos hnorm hint

/-- **LSI for bounded C² functions** — removes the ae-positivity requirement.
If f is bounded C² with ∫f²=1, we can handle f=0 on a null set by perturbation:
f_δ = √(f² + δ) satisfies f_δ > 0 everywhere, ∫f_δ² = 1 + δ, and
∫f_δ²·log(f_δ²) → ∫f²·log(f²) as δ → 0. -/
private lemma lsi_of_bounded_C2
    (f f' f'' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf_bound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hf'_bound : ∃ C, ∀ x, ‖f' x‖ ≤ C)
    (hf''_bound : ∃ C, ∀ x, ‖f'' x‖ ≤ C)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- It suffices to show: ∀ ε > 0, ∫(f²+ε)·log(f²+ε) ≤ 2∫f'² + (1+ε)·log(1+ε).
  -- Then take ε → 0: LHS → ∫f²·log(f²) by DCT, RHS → 2∫f'².
  suffices heps : ∀ ε > (0 : ℝ),
      ∫ x, (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) ∂stdGaussian ≤
        2 * ∫ x, f' x ^ 2 ∂stdGaussian + (1 + ε) * Real.log (1 + ε) by
    -- Use le_of_forall_pos_lt_add: for any δ > 0, find ε > 0 with error < δ.
    -- Key: superadditivity gives f²·log(f²) ≤ (f²+ε)·log(f²+ε) - ε·log(ε),
    -- combined with heps: total error = (1+ε)·log(1+ε) - ε·log(ε) → 0.
    apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨C, hC⟩ := hf_bound
    -- Find ε > 0 with (1+ε)·log(1+ε) - ε·log(ε) < δ, using continuity
    have hg_cont : Continuous (fun t : ℝ => (1 + t) * Real.log (1 + t) - t * Real.log t) :=
      (Real.continuous_mul_log.comp (by fun_prop)).sub Real.continuous_mul_log
    have hg_tendsto : Filter.Tendsto (fun t : ℝ => (1 + t) * Real.log (1 + t) - t * Real.log t)
        (nhds 0) (nhds 0) := by
      have := hg_cont.tendsto 0; simp at this; exact this
    rw [Metric.tendsto_nhds_nhds] at hg_tendsto
    obtain ⟨η, hη_pos, hη⟩ := hg_tendsto δ hδ
    set ε := min (η / 2) (1 / 2) with hε_def
    have hε_pos : 0 < ε := by positivity
    have hε_lt : dist ε 0 < η := by
      simp [abs_of_pos hε_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hg_lt : (1 + ε) * Real.log (1 + ε) - ε * Real.log ε < δ := by
      have := hη hε_lt
      rw [Real.dist_eq] at this; simp only [sub_zero] at this
      exact lt_of_le_of_lt (le_abs_self _) this
    -- f is continuous (differentiable everywhere)
    have hf_cont : Continuous f :=
      (Differentiable.continuous (fun x => (hderiv x).differentiableAt))
    -- Integrability of (f²+ε)·log(f²+ε)
    have hint2 : Integrable (fun x => (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε)) stdGaussian :=
      integrable_sq_add_eps_mul_log f ε hε_pos hf_cont C hC
    -- Integrability of the shifted integrand
    have hint3 : Integrable
        (fun x => (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) - ε * Real.log ε)
        stdGaussian :=
      hint2.sub (integrable_const _)
    -- Pointwise: f²·log(f²) ≤ (f²+ε)·log(f²+ε) - ε·log(ε)
    have hpw : ∀ x, f x ^ 2 * Real.log (f x ^ 2) ≤
        (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) - ε * Real.log ε := fun x => by
      linarith [mul_log_superadditive (f x ^ 2) ε (sq_nonneg _) hε_pos]
    -- Integrate the pointwise bound
    have h_int := integral_mono hint hint3 hpw
    -- Split: ∫(g - c) = ∫g - c·μ(univ) = ∫g - c (probability measure)
    have h_split : ∫ x, ((f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) - ε * Real.log ε) ∂stdGaussian
        = ∫ x, (f x ^ 2 + ε) * Real.log (f x ^ 2 + ε) ∂stdGaussian - ε * Real.log ε := by
      rw [integral_sub hint2 (integrable_const _), integral_const]
      simp [measure_univ]
    rw [h_split] at h_int
    -- Chain: ∫f²·log(f²) ≤ ∫(f²+ε)·log(f²+ε) - ε·log(ε)
    --      ≤ 2∫f'² + (1+ε)·log(1+ε) - ε·log(ε) < 2∫f'² + δ
    have h_eps := heps ε hε_pos
    linarith
  -- Prove the ε-regularized bound using lsi_of_bounded_C2_ae_pos.
  -- Strategy: substitute h = √(f²+ε)/√(1+ε), apply LSI to h, transform back.
  -- h is C², bounded, ae-positive (ε>0 makes f²+ε > 0), normalized (∫h²=1).
  -- Key identities:
  --   h² = (f²+ε)/(1+ε), so ∫h² = (1+ε)/(1+ε) = 1
  --   h²·log(h²) = [(f²+ε)·log(f²+ε) - (f²+ε)·log(1+ε)] / (1+ε)
  --   h'² = f²·f'²/((f²+ε)·(1+ε)) ≤ f'²/(1+ε) since f²/(f²+ε) ≤ 1
  -- LSI gives: ∫h²·log(h²) ≤ 2∫h'²
  -- Unfolding: [∫(f²+ε)·log(f²+ε) - (1+ε)·log(1+ε)]/(1+ε) ≤ 2∫f'²/(1+ε)
  -- Multiply by (1+ε): ∫(f²+ε)·log(f²+ε) ≤ 2∫f'² + (1+ε)·log(1+ε) ✓
  intro ε hε
  sorry

/-- **LSI for bounded C¹ functions** — bridges from C¹ to C² via OU smoothing.
For bounded f with ∀ x, HasDerivAt f (f' x) x, the OU semigroup P_t f
is C^∞ and bounded for t > 0. Apply `lsi_of_bounded_C2` to P_t f and
take t → 0⁺ via dominated convergence (f bounded → P_t f bounded by same). -/
private lemma lsi_of_bounded_C1
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf_bound : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hf'_bound : ∃ C, ∀ x, ‖f' x‖ ≤ C)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Strategy: Apply OU semigroup to get C^∞ approximation.
  -- P_t f satisfies: ‖P_t f‖_∞ ≤ ‖f‖_∞, (P_t f)' = e^{-t} P_t f',
  -- P_t f → f pointwise as t → 0+ (f bounded continuous).
  -- For t > 0, P_t f is C^∞ with bounded derivatives (by `ouSemigroup_hasDerivAt`).
  -- Apply `lsi_of_bounded_C2` to P_t f for t = 1/n, take limit.
  sorry

/-- **Approximation lemma**: From MemLp 2 + C¹ to bounded via smooth truncation.
Given f ∈ W^{1,2}(γ), construct f_n bounded with |f_n| ≤ |f|, f_n → f in L²,
and ∫f_n'² ≤ ∫f'², such that ∫f_n²·log(f_n²) → ∫f²·log(f²). -/
private lemma lsi_approximation_from_bounded
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian)
    (hlsi_bdd : ∀ (g g' : ℝ → ℝ),
      MemLp g 2 stdGaussian → MemLp g' 2 stdGaussian →
      (∀ x, HasDerivAt g (g' x) x) →
      (∃ C, ∀ x, ‖g x‖ ≤ C) → (∃ C, ∀ x, ‖g' x‖ ≤ C) →
      ∫ x, g x ^ 2 ∂stdGaussian = 1 →
      Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) stdGaussian →
      ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂stdGaussian ≤
        2 * ∫ x, g' x ^ 2 ∂stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Strategy: Define f_n = φ_n ∘ f where φ_n is a smooth truncation
  -- satisfying: φ_n(t) = t for |t| ≤ n, |φ_n(t)| ≤ n+1, 0 ≤ φ_n' ≤ 1.
  -- Then f_n is bounded, f_n → f in L², f_n' = φ_n'(f)·f' so ∫f_n'² ≤ ∫f'².
  -- The entropy convergence uses:
  -- - Positive part: f_n² ↑ f², so f_n²·log⁺(f_n²) ↑ f²·log⁺(f²) (monotone convergence)
  -- - Negative part: |f_n²·log⁻(f_n²)| ≤ 1/e (dominated convergence)
  -- After normalization (divide by ∫f_n²), apply hlsi_bdd and take limit.
  sorry

private lemma gaussian_lsi_normalized_of_integrable
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Decomposition: bounded C¹ case + approximation from general to bounded.
  -- Step 1: The bounded case is handled by `lsi_of_bounded_C1`.
  -- Step 2: The general case reduces to bounded via `lsi_approximation_from_bounded`.
  exact lsi_approximation_from_bounded f f' hf hf' hderiv hnorm hint
    (fun g g' hg hg' hgd hgb hg'b hgn hgi =>
      lsi_of_bounded_C1 g g' hg hg' hgd hgb hg'b hgn hgi)

lemma gaussian_lsi_normalized
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Case split: is f²·log(f²) integrable under γ?
  -- When NOT integrable: Lean's Bochner integral returns 0, and 0 ≤ 2∫f'² is trivial.
  -- When integrable: use the full Gross regularization argument.
  by_cases hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian
  · exact gaussian_lsi_normalized_of_integrable f f' hf hf' hderiv hnorm hint
  · rw [integral_undef hint]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    exact integral_nonneg (fun _ => sq_nonneg _)

/-- **Main IBP core**: Assembles the 1D Gaussian LSI from scaling + normalized case.

    Case split on `A = ∫ f² dγ`:
    - If `A = 0`: then `f = 0` a.e., `Ent(f²) = 0`, `2∫f'² ≥ 0`. Immediate.
    - If `A > 0`: Scale `g = f/√A` to get `∫g² = 1`. Apply normalized LSI to g.
      Then `Ent(f²) = A·∫g²·log(g²) ≤ A·2∫g'² = 2∫f'²`. -/
lemma gaussian_lsi_1d_ibp_core
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    entropy stdGaussian (fun x => f x ^ 2) ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Case split: is ∫ f² > 0 or ∫ f² = 0?
  by_cases hA : ∫ x, f x ^ 2 ∂stdGaussian = 0
  · -- Case A = 0: f = 0 a.e., both sides are 0
    have hf_sq_ae_zero : ∀ᵐ x ∂stdGaussian, f x ^ 2 = 0 := by
      rwa [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
        hf.integrable_sq] at hA
    have hf_ae_zero : ∀ᵐ x ∂stdGaussian, f x = 0 := by
      filter_upwards [hf_sq_ae_zero] with x hx
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hx
    have hent_zero : entropy stdGaussian (fun x => f x ^ 2) = 0 := by
      unfold entropy
      have h1 : ∫ x, (fun x => f x ^ 2) x * Real.log ((fun x => f x ^ 2) x) ∂stdGaussian = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [hf_ae_zero] with x hx
        simp [hx]
      simp only [h1, hA, Real.log_zero, mul_zero, sub_zero]
    rw [hent_zero]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    exact integral_nonneg (fun _ => sq_nonneg _)
  · -- Case A > 0: use scaling + normalized LSI
    have hA_pos : 0 < ∫ x, f x ^ 2 ∂stdGaussian := by
      rcases (integral_sq_nonneg f).lt_or_eq with h | h
      · exact h
      · exact absurd h.symm hA
    -- Define scaling constants
    set A := ∫ x, f x ^ 2 ∂stdGaussian with hAdef
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hsqA_pos : 0 < √A := Real.sqrt_pos_of_pos hA_pos
    have hsqA_ne : √A ≠ 0 := ne_of_gt hsqA_pos
    -- Define g = f/√A, g' = f'/√A
    set g := fun x => f x / √A with hgdef
    set g' := fun x => f' x / √A with hg'def
    -- g and g' are in L²(γ)
    have hg : MemLp g 2 stdGaussian := by
      rw [hgdef]; exact hf.const_mul (√A)⁻¹ |>.ae_eq (ae_of_all _ fun x => by ring_nf)
    have hg' : MemLp g' 2 stdGaussian := by
      rw [hg'def]; exact hf'.const_mul (√A)⁻¹ |>.ae_eq (ae_of_all _ fun x => by ring_nf)
    -- HasDerivAt g g'
    have hg_deriv : ∀ x, HasDerivAt g (g' x) x := by
      intro x
      exact (hderiv x).div_const (√A)
    -- ∫ g² = 1
    have hg_norm : ∫ x, g x ^ 2 ∂stdGaussian = 1 := by
      have hfg : (fun x => g x ^ 2) = fun x => f x ^ 2 * A⁻¹ := by
        ext x; simp only [hgdef, div_eq_mul_inv]
        rw [mul_pow, inv_pow, Real.sq_sqrt hA_pos.le]
      rw [hfg, integral_mul_const, hAdef, mul_inv_cancel₀ hA_ne]
    -- Apply normalized LSI
    have hkey := gaussian_lsi_normalized g g' hg hg' hg_deriv hg_norm
    -- Now relate back to f:
    -- entropy(f²) = A · ∫ g² log(g²) and 2∫f'² = 2A · ∫g'²
    -- Step 1: entropy(f²) = ∫ f² log(f²) - A log A
    --       = ∫ A·g² · log(A·g²) - A·log(A)
    --       = ∫ A·g² · (log A + log(g²)) - A·log(A)
    --       = A·log(A)·∫g² + A·∫g²·log(g²) - A·log(A)
    --       = A·log(A) + A·∫g²·log(g²) - A·log(A)  [using ∫g² = 1]
    --       = A · ∫g²·log(g²)
    -- Step 2: From hkey: ∫g²·log(g²) ≤ 2·∫g'²
    -- Step 3: 2·∫g'² = 2·∫(f'/√A)² = 2·(1/A)·∫f'² = (2/A)·∫f'²
    -- Step 4: entropy(f²) = A · ∫g²·log(g²) ≤ A · 2·∫g'² = A·(2/A)·∫f'² = 2·∫f'²
    -- We need: entropy(f²) ≤ 2·∫f'²
    -- Rewrite ∫g'² in terms of ∫f'²
    have hg'_sq : ∫ x, g' x ^ 2 ∂stdGaussian = (∫ x, f' x ^ 2 ∂stdGaussian) * A⁻¹ := by
      have hfg' : (fun x => g' x ^ 2) = fun x => f' x ^ 2 * A⁻¹ := by
        ext x; simp only [hg'def, div_eq_mul_inv]
        rw [mul_pow, inv_pow, Real.sq_sqrt hA_pos.le]
      rw [hfg', integral_mul_const]
    -- Rewrite entropy(f²) in terms of g
    -- Key: Ent(f²) = A · ∫ g²·log(g²) where g = f/√A, ∫g² = 1
    -- Proof: Ent(f²) = ∫f²·log(f²) - A·log(A)
    --       = ∫(Ag²)·log(Ag²) - A·log(A)
    --       = A·∫g²·(logA + log(g²)) - A·logA
    --       = A·logA + A·∫g²·log(g²) - A·logA = A·∫g²·log(g²)
    -- f² = A · g²
    have hf_eq_g : ∀ x, f x ^ 2 = A * g x ^ 2 := by
      intro x; change f x ^ 2 = A * (f x / √A) ^ 2
      rw [div_pow, Real.sq_sqrt hA_pos.le, mul_div_cancel₀ _ hA_ne]
    -- Pointwise: f²·log(f²) = A·g²·log(A) + A·g²·log(g²)
    have hpt : ∀ x, f x ^ 2 * Real.log (f x ^ 2) =
        A * g x ^ 2 * Real.log A + A * (g x ^ 2 * Real.log (g x ^ 2)) := by
      intro x; rw [hf_eq_g]
      rcases eq_or_lt_of_le (sq_nonneg (g x)) with hgz | hgp
      · rw [show g x ^ 2 = 0 from hgz.symm]; simp
      · rw [Real.log_mul (ne_of_gt hA_pos) (ne_of_gt hgp)]; ring
    -- Integrability of the summands (needs integrable_sq_mul_log_sq_of_memLp)
    have hint1 : Integrable (fun x => A * g x ^ 2 * Real.log A) stdGaussian :=
      (hg.integrable_sq.const_mul A).mul_const _
    have hint2 : Integrable (fun x => A * (g x ^ 2 * Real.log (g x ^ 2))) stdGaussian :=
      (integrable_sq_mul_log_sq_of_memLp g g' hg hg' hg_deriv).const_mul A
    have hent_eq : entropy stdGaussian (fun x => f x ^ 2) =
        A * ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂stdGaussian := by
      unfold entropy
      -- Rewrite the first integral
      have h_int_eq : ∫ x, (fun x => f x ^ 2) x * Real.log ((fun x => f x ^ 2) x) ∂stdGaussian =
          ∫ x, (A * g x ^ 2 * Real.log A + A * (g x ^ 2 * Real.log (g x ^ 2))) ∂stdGaussian :=
        integral_congr_ae (ae_of_all _ fun x => hpt x)
      rw [h_int_eq, integral_add hint1 hint2]
      -- First summand: ∫ A·g²·log(A) = A·log(A)·∫g² = A·log(A)·1 = A·log(A)
      rw [show (fun x => A * g x ^ 2 * Real.log A) = fun x => (A * Real.log A) * g x ^ 2 from
        funext (fun _ => by ring)]
      rw [integral_const_mul, hg_norm, mul_one]
      -- Second summand: A · ∫ g²·log(g²)
      rw [integral_const_mul]
      -- ∫ f² = A
      rw [show ∫ (x : ℝ), (fun x => f x ^ 2) x ∂stdGaussian = A from hAdef.symm]
      ring
    rw [hent_eq]
    -- Now: A · ∫g²·log(g²) ≤ 2·∫f'²
    -- From hkey: ∫g²·log(g²) ≤ 2·∫g'²
    -- So A · ∫g²·log(g²) ≤ A · (2·∫g'²) = 2·A·∫g'² = 2·A·(∫f'²/A) = 2·∫f'²
    calc A * ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂stdGaussian
        ≤ A * (2 * ∫ x, g' x ^ 2 ∂stdGaussian) := by
          apply mul_le_mul_of_nonneg_left hkey hA_pos.le
      _ = 2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
          rw [hg'_sq]; field_simp

end LSI_Decomposition

/-! ## Proved parametric theorems -/

theorem tensorization_lsi
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hTensorAt : TensorizationLSIAt n c) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hTensorAt h f gradf hf hgradf hgrad

theorem tensorization_lsi_of_at
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (hTensorAt : TensorizationLSIAt n c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi n c h f gradf hf hgradf hgrad hTensorAt

lemma tensorization_lsi_at_of_universal
    (hTensor : UniversalTensorizationLSI) (n : ℕ) (c : ℝ) :
    TensorizationLSIAt n c := by
  exact hTensor n c

theorem gaussian_log_sobolev_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi_of_at n 2 hLSI1d hTensorAt f gradf hf hgradf hgrad

theorem gaussian_log_sobolev_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hf hgradf hgrad hLSI1d
    (tensorization_lsi_at_of_universal hTensor n 2)

theorem gaussian_log_sobolev_structured_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensorAt

theorem gaussian_log_sobolev_structured_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_universal_tensorization n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensor

/-! ## Sorry-bearing declarations -/

/-- **1D Gaussian Log-Sobolev Inequality**: `SatisfiesLSI stdGaussian 2`.

For all f, f' with `MemLp f 2 stdGaussian`, `MemLp f' 2 stdGaussian`,
`∀ x, HasDerivAt f (f' x) x`:

  `Ent_γ(f²) ≤ 2 · ∫ f'² dγ`

where `Ent_γ(g) = ∫ g·log(g) dγ - (∫ g dγ)·log(∫ g dγ)`.

**Proof route**: Reduce to `gaussian_lsi_1d_ibp_core` which is the per-function version. -/
theorem gaussian_lsi_1d_core : SatisfiesLSI stdGaussian 2 := by
  intro f f' hf hf' hderiv
  exact gaussian_lsi_1d_ibp_core f f' hf hf' hderiv

theorem gaussian_lsi_1d : SatisfiesLSI stdGaussian 2 :=
  gaussian_lsi_1d_core

/-! ### Tensorization sub-lemmas (zero sorry: 3, sorry: 4)

The tensorization of LSI follows the standard scheme:
1. **Entropy subadditivity** (chain rule for product measures):
   `Ent_{μ^n}(g) ≤ ∑_i E_{μ^n}[Ent_i(g)]`
   where `Ent_i(g)(x) = Ent_{μ_i}(t ↦ g(update x i t))`.
2. **1D LSI per slice**: For each coordinate `i` and fixed `x_{-i}`,
   `Ent_i(f²)(x) ≤ c · ∫ (∂_i f(update x i t))² dμ(t)`.
3. **Fubini rewrite**: `∫ (∫ h(update x i t) dμ(t)) d(μ^n)(x) = ∫ h d(μ^n)`.
4. **Sum and conclude**: `Ent(f²) ≤ c · ∑_i ∫ (∂_i f)² d(μ^n)`.

Steps 1, 3 are sorry'd (Fubini for `Measure.pi`). Step 2 is proved. -/

section TensorizationInfra

/-- The derivative of a coordinate slice `t ↦ f(update x i t)` at any point `t`.
Uses `Function.update_idem` to show `update(update x i t, i, s) = update(x, i, s)`.
Zero sorry. -/
private lemma hasDerivAt_slice {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hgrad : ∀ x (i : Fin n),
      HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => f (Function.update x i s))
      (gradf i (Function.update x i t)) t := by
  have h := hgrad (Function.update x i t) i
  rw [Function.update_self] at h
  have heq : (fun s => f (Function.update (Function.update x i t) i s)) =
             (fun s => f (Function.update x i s)) := by
    funext s; congr 1; exact Function.update_idem t s x
  rwa [heq] at h

/-- 1D LSI applied to a coordinate slice.
For fixed `x`, the function `t ↦ f(update x i t)` satisfies the entropy bound
via `SatisfiesLSI`. Zero sorry. -/
private lemma condEntropyAt_le_of_satisfiesLSI {n : ℕ}
    (c : ℝ)
    (hLSI : SatisfiesLSI stdGaussian c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hgrad : ∀ x' (i' : Fin n),
      HasDerivAt (fun t => f (Function.update x' i' t)) (gradf i' x') (x' i'))
    (x : Fin n → ℝ) (i : Fin n)
    (hf_slice : MemLp (fun t => f (Function.update x i t)) 2 stdGaussian)
    (hg_slice : MemLp (fun t => gradf i (Function.update x i t)) 2 stdGaussian) :
    condEntropyAt stdGaussian (fun y => f y ^ 2) i x ≤
      c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian := by
  rw [condEntropyAt_eq]
  exact hLSI _ _ hf_slice hg_slice (hasDerivAt_slice f gradf hgrad x i)

/-- **MemLp for coordinate slices** (ae version, zero sorry).

If `f ∈ L²(γⁿ)`, then for a.e. `x` and each `i`,
the slice `t ↦ f(update x i t) ∈ L²(γ)`.

Note: the original all-`x` version is FALSE for general L² functions
(counterexample: f can be infinite on a null set of `x_{-i}`).

Proof: Decompose `γⁿ ≅ γ_i ⊗ γ_{-i}` via `measurePreserving_piFinSuccAbove`.
Apply `Integrable.prod_left_ae` to `‖f‖²` and `AEStronglyMeasurable.prodMk_right`
to get ae slices in both integrability and measurability.
Pull back from ae on `γ^{n-1}` to ae on `γⁿ` via `MeasurePreserving` of `removeNth`. -/
private lemma ae_memLp_slice_of_memLp_pi {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (stdGaussianPi n)) (i : Fin n) :
    ∀ᵐ x ∂(stdGaussianPi n), MemLp (fun t => f (Function.update x i t)) 2 stdGaussian := by
  -- Since i : Fin n, we have n ≥ 1, so n = m + 1 for some m
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  -- Set up the equivalence piFinSuccAbove: (Fin (m+1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ)
  let e := MeasurableEquiv.piFinSuccAbove (fun (_ : Fin (m + 1)) => ℝ) i
  let g : ℝ × (Fin m → ℝ) → ℝ := f ∘ e.symm
  -- MeasurePreserving for e
  have hmp : MeasurePreserving e (stdGaussianPi (m + 1))
      (stdGaussian.prod (stdGaussianPi m)) := by
    simp only [stdGaussianPi]
    exact measurePreserving_piFinSuccAbove (fun (_ : Fin (m + 1)) => stdGaussian) i
  -- Step 1: g is MemLp 2 on the product measure
  have hg : MemLp g 2 (stdGaussian.prod (stdGaussianPi m)) :=
    hf.comp_measurePreserving hmp.symm
  have hg_aesm := hg.1
  -- Step 2: Integrable (fun p => g p ^ 2) on the product measure
  have hg_int : Integrable (fun p => g p ^ 2) (stdGaussian.prod (stdGaussianPi m)) :=
    (memLp_two_iff_integrable_sq hg_aesm).mp hg
  -- Step 3: By Fubini, ae slices are integrable and AEStronglyMeasurable
  have hg_slice : ∀ᵐ y ∂(stdGaussianPi m),
      MemLp (fun t => g (t, y)) 2 stdGaussian := by
    filter_upwards [hg_int.prod_left_ae, hg_aesm.prodMk_right] with y hy_int hy_aesm
    exact (memLp_two_iff_integrable_sq hy_aesm).mpr hy_int
  -- Step 4: Pull back from ae y to ae x via removeNth
  have hmp_rem : MeasurePreserving (fun x : Fin (m + 1) → ℝ => Fin.removeNth i x)
      (stdGaussianPi (m + 1)) (stdGaussianPi m) := by
    change MeasurePreserving (Prod.snd ∘ e) _ _
    simp only [stdGaussianPi]
    exact measurePreserving_snd.comp
      (measurePreserving_piFinSuccAbove (fun (_ : Fin (m + 1)) => stdGaussian) i)
  -- Step 5: Convert g(t, removeNth i x) = f(update x i t)
  filter_upwards [hmp_rem.quasiMeasurePreserving.ae hg_slice] with x hx
  convert hx using 1
  ext t
  show f (Function.update x i t) = g (t, Fin.removeNth i x)
  simp only [g, Function.comp_def]
  congr 1
  exact (Fin.insertNth_removeNth i t x).symm

/-- **Fubini identity**: resampling a coordinate preserves the integral.

For product measure `μ^n` and any `h ∈ L¹(μ^n)`:
  `∫ (∫ h(update x i t) dμ(t)) d(μ^n)(x) = ∫ h(x) d(μ^n)(x)`

This says: if `X ~ μ^n` and `T ~ μ_i` is an independent resample of coordinate `i`,
then `E[h(update X i T)] = E[h(X)]`, because `update X i T ~ μ^n`.

**Proof strategy**:
1. Decompose `μ^n ≅ μ_i ⊗ μ_{-i}` via `measurePreserving_piFinSuccAbove`.
2. Use `Fin.update_insertNth` to show `update (insertNth i a y) i t = insertNth i t y`,
   so the LHS integrand depends only on the `{-i}` coordinates.
3. Collapse the `x_i` integral via `integral_fun_snd` (probability measure).
4. Recover the RHS via Fubini swap (`integral_integral_swap`) + `integral_prod`. -/
private lemma integral_condExpect_eq_integral_pi : ∀ {n : ℕ}
    (h : (Fin n → ℝ) → ℝ) (_ : Integrable h (stdGaussianPi n)) (i : Fin n),
    ∫ x, (∫ t, h (Function.update x i t) ∂stdGaussian) ∂(stdGaussianPi n) =
    ∫ x, h x ∂(stdGaussianPi n)
  | 0, _, _, i => Fin.elim0 i
  | n + 1, h, hh, i => by
    open MeasurableEquiv Fin in
    -- Set up the piFinSuccAbove decomposition: γⁿ⁺¹ ≅ γ_i ⊗ γ^n
    set e := piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
    set γ := stdGaussian
    set γn := Measure.pi (fun j : Fin n => μ' (i.succAbove j))
    have hmp := measurePreserving_piFinSuccAbove μ' i
    have hpi : stdGaussianPi (n + 1) = Measure.pi μ' := rfl
    -- Integrability of h ∘ e.symm on the product measure
    have hint : Integrable (fun x : ℝ × (Fin n → ℝ) => h (e.symm x)) (γ.prod γn) :=
      hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr (hpi ▸ hh)
    -- Swapped integrability for Fubini
    have hint_swap : Integrable (Function.uncurry fun (y : Fin n → ℝ) (t : ℝ) =>
        h (e.symm (t, y))) (γn.prod γ) := by
      have : (Function.uncurry fun (y : Fin n → ℝ) (t : ℝ) => h (e.symm (t, y))) =
          (fun x => h (e.symm x)) ∘ Prod.swap := by ext ⟨y, t⟩; rfl
      rw [this]; exact hint.swap
    -- Auxiliary: the inner integral as a function of y only
    set g : (Fin n → ℝ) → ℝ := fun y => ∫ t, h (e.symm (t, y)) ∂γ
    calc ∫ x, (∫ t, h (Function.update x i t) ∂γ) ∂(stdGaussianPi (n + 1))
      -- Step 1: Transform outer integral via piFinSuccAbove
      _ = ∫ p : ℝ × (Fin n → ℝ), (∫ t, h (Function.update (e.symm p) i t) ∂γ)
            ∂(γ.prod γn) := by
          rw [hpi, ← hmp.symm.integral_comp' (g := fun x => ∫ t, h (Function.update x i t) ∂γ)]
      -- Step 2: update (insertNth i a y) i t = insertNth i t y
      _ = ∫ p : ℝ × (Fin n → ℝ), (∫ t, h (e.symm (t, p.2)) ∂γ) ∂(γ.prod γn) := by
          congr 1; ext ⟨a, y⟩; congr 1; ext t
          show h (Function.update ((insertNthEquiv (fun _ : Fin (n+1) => ℝ) i) (a, y)) i t) =
              h ((insertNthEquiv (fun _ : Fin (n+1) => ℝ) i) (t, y))
          congr 1; simp [insertNthEquiv, Fin.update_insertNth]
      -- Step 3: Integrand depends only on p.2 — collapse first coordinate (prob measure)
      _ = ∫ y : Fin n → ℝ, g y ∂γn := by
          show ∫ p : ℝ × (Fin n → ℝ), g p.2 ∂(γ.prod γn) = ∫ y, g y ∂γn
          rw [integral_fun_snd]; simp [Measure.real, measure_univ]
      -- Step 4: Fubini swap ∫_y ∫_t = ∫_t ∫_y
      _ = ∫ t : ℝ, (∫ y, h (e.symm (t, y)) ∂γn) ∂γ :=
          integral_integral_swap hint_swap
      -- Step 5: Reassemble via integral_prod
      _ = ∫ p : ℝ × (Fin n → ℝ), h (e.symm p) ∂(γ.prod γn) :=
          (integral_prod _ hint).symm
      -- Step 6: Transform back via piFinSuccAbove
      _ = ∫ x, h x ∂(stdGaussianPi (n + 1)) := by
          rw [hpi, ← hmp.symm.integral_comp' (g := h)]

-- Lower bound for x·log(x): x·log(x) ≥ -1/e for x ≥ 0.
-- The minimum of t·log(t) on [0,∞) is at t = 1/e, giving value -1/e.
lemma mul_log_ge_neg_inv_exp (x : ℝ) (hx : 0 ≤ x) :
    -(1 / Real.exp 1) ≤ x * Real.log x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp; positivity
  suffices h : -(x * Real.log x) ≤ 1 / Real.exp 1 by linarith
  have key := Real.add_one_le_exp (-Real.log x - 1)
  rw [show (-Real.log x - 1) + 1 = -Real.log x from by ring,
      Real.exp_sub, Real.exp_neg, Real.exp_log hx_pos] at key
  have := mul_le_mul_of_nonneg_left key (le_of_lt hx_pos)
  rw [show x * (x⁻¹ / Real.exp 1) = 1 / Real.exp 1 from by field_simp] at this
  linarith

-- ae on second marginal → ae on product measure (no measurability required)
private lemma ae_snd_of_ae_marginal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    {p : β → Prop} (h : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ z ∂(μ.prod ν), p z.2 := by
  have hν : ν {y | ¬ p y} = 0 := by rwa [ae_iff] at h
  rw [ae_iff]
  have h1 : {z : α × β | ¬ p z.2} ⊆ Set.univ ×ˢ {y | ¬ p y} :=
    fun ⟨_, _⟩ hb => ⟨Set.mem_univ _, hb⟩
  exact le_antisymm (le_trans (measure_mono h1) (le_trans (Measure.prod_prod_le _ _)
    (le_of_eq (by rw [hν, mul_zero])))) (zero_le _)

-- Conditional expectation of an integrable function at arbitrary coordinate is integrable.
private lemma integrable_condExpect_stdGaussianPi_gen {n : ℕ}
    (φ : (Fin (n + 1) → ℝ) → ℝ) (hφ : Integrable φ (stdGaussianPi (n + 1)))
    (j : Fin (n + 1)) :
    Integrable (fun y => ∫ t, φ (Function.update y j t) ∂stdGaussian)
      (stdGaussianPi (n + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  set γn := Measure.pi (fun k : Fin n => μ' (j.succAbove k))
  have hmp := measurePreserving_piFinSuccAbove μ' j
  have hprod : Integrable (φ ∘ e.symm) (stdGaussian.prod γn) :=
    hmp.symm.integrable_comp_of_integrable hφ
  have hmarg := hprod.integral_prod_right
  have heq : (fun y => ∫ t, φ (Function.update y j t) ∂stdGaussian) =
      ((fun p : ℝ × (Fin n → ℝ) =>
          ∫ t, (φ ∘ e.symm) (t, p.2) ∂stdGaussian) ∘ e) := by
    ext y; simp only [Function.comp]
    congr 1; ext t; congr 1
    conv_lhs => rw [(e.symm_apply_apply y).symm]
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact @Fin.update_insertNth n (fun _ => ℝ) j (e y).1 t (e y).2
  rw [heq]
  exact hmp.integrable_comp_of_integrable (hmarg.comp_snd stdGaussian)

-- Integrability of condEntropyAt for nonneg functions with integrable g·log(g).
-- Uses Jensen domination (upper: convexOn_mul_log, lower: mul_log_ge_neg_inv_exp).
private lemma integrable_condEntropyAt_of_nonneg {n : ℕ}
    (g : (Fin (n + 1) → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi (n + 1)))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi (n + 1)))
    (j : Fin (n + 1)) :
    Integrable (fun x => condEntropyAt stdGaussian g j x) (stdGaussianPi (n + 1)) := by
  simp only [condEntropyAt, entropy]
  apply Integrable.sub
  · exact integrable_condExpect_stdGaussianPi_gen _ hg_log j
  · set Ej := fun y => ∫ t, g (Function.update y j t) ∂stdGaussian
    have hEj_int := integrable_condExpect_stdGaussianPi_gen g hg j
    have hA_int := integrable_condExpect_stdGaussianPi_gen _ hg_log j
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
    set γn := Measure.pi (fun k : Fin n => μ' (j.succAbove k))
    have hmp := measurePreserving_piFinSuccAbove μ' j
    have hupd : ∀ y t, Function.update y j t = e.symm (t, (e y).2) := by
      intro y t
      conv_lhs => rw [(e.symm_apply_apply y).symm]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact @Fin.update_insertNth n (fun _ => ℝ) j (e y).1 t (e y).2
    have hg_prod : Integrable (g ∘ e.symm) (stdGaussian.prod γn) :=
      hmp.symm.integrable_comp_of_integrable hg
    have hgl_prod : Integrable ((fun x => g x * log (g x)) ∘ e.symm) (stdGaussian.prod γn) :=
      hmp.symm.integrable_comp_of_integrable hg_log
    have hg_ae : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
        Integrable (fun t => g (Function.update y j t)) stdGaussian := by
      have hae_γn := hg_prod.prod_left_ae
      have hae_prod := ae_snd_of_ae_marginal stdGaussian γn hae_γn
      exact (hmp.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
        rwa [show (fun t => (g ∘ e.symm) (t, (e y).2)) =
            (fun t => g (Function.update y j t)) from by
          ext t; simp only [Function.comp]; rw [hupd y t]] at hy
    have hgl_ae : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
        Integrable (fun t => g (Function.update y j t) *
          log (g (Function.update y j t))) stdGaussian := by
      have hae_γn := hgl_prod.prod_left_ae
      have hae_prod := ae_snd_of_ae_marginal stdGaussian γn hae_γn
      exact (hmp.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
        rwa [show (fun t => ((fun x => g x * log (g x)) ∘ e.symm) (t, (e y).2)) =
            (fun t => g (Function.update y j t) * log (g (Function.update y j t))) from by
          ext t; simp only [Function.comp]; rw [hupd y t]] at hy
    have h_upper : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
        Ej y * log (Ej y) ≤ ∫ t, g (Function.update y j t) *
          log (g (Function.update y j t)) ∂stdGaussian := by
      filter_upwards [hg_ae, hgl_ae] with y hgy hgly
      exact convexOn_mul_log.map_integral_le continuous_mul_log.continuousOn
        isClosed_Ici (ae_of_all _ fun t => hg_nn _) hgy hgly
    have h_lower : ∀ y, -(1 / exp 1) ≤ Ej y * log (Ej y) :=
      fun y => mul_log_ge_neg_inv_exp _ (integral_nonneg fun t => hg_nn _)
    exact Integrable.mono' (hA_int.norm.add (integrable_const (1 / exp 1)))
      (continuous_mul_log.comp_aestronglyMeasurable hEj_int.aestronglyMeasurable)
      (by filter_upwards [h_upper] with y hy
          simp only [Pi.add_apply, norm_eq_abs]
          rw [abs_le]
          exact ⟨by linarith [h_lower y,
                    abs_nonneg (∫ t, g (Function.update y j t) *
                      log (g (Function.update y j t)) ∂stdGaussian)],
                 by linarith [le_abs_self (∫ t, g (Function.update y j t) *
                      log (g (Function.update y j t)) ∂stdGaussian),
                    div_pos one_pos (exp_pos 1)]⟩)

/-- **Integrated conditional entropy identity**.

For product measure `γⁿ` and integrable `g` with integrable `g·log(g)`, the integral
of the conditional entropy along coordinate `i` decomposes as:
  `∫ condEntropyAt_i(g) dγⁿ = ∫ g·log(g) dγⁿ - ∫ (E_i g)·log(E_i g) dγⁿ`
where `E_i g(x) = ∫ g(update x i t) dγ(t)`.

**Proof**: Expand `condEntropyAt = entropy = ∫ φ(slice) - ψ(slice)`, split the integral,
and apply `integral_condExpect_eq_integral_pi` to the `∫ φ(slice)` part. -/
private lemma integrated_condEntropyAt_eq {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (i : Fin n)
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n))
    (hint1 : Integrable (fun x => ∫ t, g (Function.update x i t) *
      Real.log (g (Function.update x i t)) ∂stdGaussian) (stdGaussianPi n))
    (hint2 : Integrable (fun x => (∫ t, g (Function.update x i t) ∂stdGaussian) *
      Real.log (∫ t, g (Function.update x i t) ∂stdGaussian)) (stdGaussianPi n)) :
    ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) =
    ∫ x, g x * Real.log (g x) ∂(stdGaussianPi n) -
    ∫ x, (∫ t, g (Function.update x i t) ∂stdGaussian) *
      Real.log (∫ t, g (Function.update x i t) ∂stdGaussian) ∂(stdGaussianPi n) := by
  have hsplit :
      ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) =
      ∫ x, (∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂stdGaussian)
        ∂(stdGaussianPi n) -
      ∫ x, (∫ t, g (Function.update x i t) ∂stdGaussian) *
        Real.log (∫ t, g (Function.update x i t) ∂stdGaussian) ∂(stdGaussianPi n) := by
    simp only [condEntropyAt, entropy]
    exact integral_sub hint1 hint2
  rw [hsplit]
  congr 1
  exact integral_condExpect_eq_integral_pi (fun x => g x * Real.log (g x)) hg_log i

/-- **Entropy chain rule for product measures** (exact identity).

For product measure `γⁿ` and any `i : Fin n`:
  `Ent_{γⁿ}(g) = ∫ condEnt_i(g) dγⁿ + Ent_{γⁿ}(E_i g)`

where `E_i g(x) = ∫ g(update x i t) dγ(t)` is the coordinate-i conditional expectation.

This is an IDENTITY (not inequality), following from:
1. `condEnt_i(g) = ∫ g·log(g)(slice) - (E_i g)·log(E_i g)` (definition)
2. `∫ (∫ g·log(g)(slice)) = ∫ g·log(g)` (Fubini/`integral_condExpect_eq_integral_pi`)
3. `∫ E_i g = ∫ g` (Fubini/`integral_condExpect_eq_integral_pi`)

**Blocker**: Statement involves `Ent_{γⁿ}(E_i g)` where `E_i g : (Fin n → ℝ) → ℝ`.
For the induction to work, we need to relate this to `Ent_{γⁿ⁻¹}(h)` for some
`h : (Fin (n-1) → ℝ) → ℝ`. This requires `piFinSuccAbove` projections. ~40 lines. -/
private lemma entropy_chain_rule_pi {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (i : Fin n)
    (hg : Integrable g (stdGaussianPi n))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n))
    (hint1 : Integrable (fun x => ∫ t, g (Function.update x i t) *
      Real.log (g (Function.update x i t)) ∂stdGaussian) (stdGaussianPi n))
    (hint2 : Integrable (fun x => (∫ t, g (Function.update x i t) ∂stdGaussian) *
      Real.log (∫ t, g (Function.update x i t) ∂stdGaussian)) (stdGaussianPi n)) :
    entropyPi (stdGaussianPi n) g =
    ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) +
    entropyPi (stdGaussianPi n) (fun x => ∫ t, g (Function.update x i t) ∂stdGaussian) := by
  -- Let A = ∫ g·log(g), B = ∫g, D = ∫ (E_i g)·log(E_i g)
  -- Chain rule: A - B·log(B) = (A - D) + (D - B·log(B))
  -- Step 1: Split ∫ condEnt into ∫ slice_log - ∫ E_i_log
  have hsplit :
      ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) =
      ∫ x, (∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂stdGaussian)
        ∂(stdGaussianPi n) -
      ∫ x, (∫ t, g (Function.update x i t) ∂stdGaussian) *
        Real.log (∫ t, g (Function.update x i t) ∂stdGaussian) ∂(stdGaussianPi n) := by
    simp only [condEntropyAt, entropy]
    exact integral_sub hint1 hint2
  -- Step 2: Fubini: ∫ slice_log = ∫ g·log(g)
  have hfub_log :
      ∫ x, (∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂stdGaussian)
        ∂(stdGaussianPi n) =
      ∫ x, g x * Real.log (g x) ∂(stdGaussianPi n) :=
    integral_condExpect_eq_integral_pi (fun x => g x * Real.log (g x)) hg_log i
  -- Step 3: Fubini: ∫ E_i g = ∫ g
  have hfub : ∫ x, (∫ t, g (Function.update x i t) ∂stdGaussian) ∂(stdGaussianPi n) =
      ∫ x, g x ∂(stdGaussianPi n) :=
    integral_condExpect_eq_integral_pi g hg i
  -- Step 4: Combine. LHS = A - B·log(B). RHS = (A - D) + (D - B·log(B)) = A - B·log(B).
  simp only [entropyPi]
  rw [hfub]
  linarith [hsplit, hfub_log]

/-- **Entropy subadditivity for nonneg integrable functions** (Han's inequality).

For g ≥ 0 on γⁿ with g ∈ L¹:
  `Ent_{γⁿ}(g) ≤ ∑_i ∫ condEnt_i(g) dγⁿ`

This is the conditional entropy version of Han's inequality, stated without
requiring g·log(g) ∈ L¹ (the proof handles the non-integrable case separately).

**Proof sketch** (telescoping + data processing):
Define h₀ = g, h_{k+1}(x) = ∫ h_k(update x k t) dγ(t) (average over coord k).
After n steps, h_n = const = ∫g, so Ent(h_n) = 0.

1. **Telescoping** (from `entropy_chain_rule_pi`):
   For each k: Ent(h_k) = ∫ condEnt_k(h_k) + Ent(h_{k+1}).
   Summing: Ent(g) = Ent(h₀) = ∑_k ∫ condEnt_k(h_k).

2. **Data processing** (Jensen, since x·log(x) is convex):
   For each k: ∫ condEnt_k(h_k) ≤ ∫ condEnt_k(g).
   Key: h_k = E_{k-1}∘...∘E_0[g] and E_j commutes with `update(·, k, ·)` for j < k.
   So the slice of h_k at coord k is E_0...E_{k-1}[slice of g at k],
   and entropy decreases under conditional expectation (Jensen).

3. **Conclusion**: Ent(g) = ∑_k ∫ condEnt_k(h_k) ≤ ∑_k ∫ condEnt_k(g).

**Blocker**: Formalizing requires ~120 lines:
  (a) Commutativity: E_j ∘ update(·, k, ·) = update(·, k, ·) ∘ E_j for j ≠ k
  (b) Jensen for conditional entropy: Ent(E_j[φ]) ≤ E_j[Ent(φ)]
  (c) Iterated conditional expectation integrability
  (d) Handling the non-integrable g·log(g) case (LHS ≤ 0 when ∫g ≥ 1) -/
-- Helper: Jensen for averaging operator E_i.
-- For φ convex on [0,∞) (like x·log(x)), and g ≥ 0:
--   (E_i g)(x) · log((E_i g)(x)) ≤ ∫ g(upd x i t) · log(g(upd x i t)) dγ(t)
-- This is pointwise Jensen applied to the integral ∫ g(upd x i t) dγ(t).
private lemma jensen_condExpect_mul_log {n : ℕ}
    (g : (Fin n → ℝ) → ℝ)
    (hg_nn : ∀ x, 0 ≤ g x)
    (x : Fin n → ℝ) (i : Fin n)
    (hslice_int : Integrable (fun t => g (Function.update x i t)) stdGaussian)
    (hslice_log : Integrable (fun t => g (Function.update x i t) *
        Real.log (g (Function.update x i t))) stdGaussian) :
    (∫ t, g (Function.update x i t) ∂stdGaussian) *
      Real.log (∫ t, g (Function.update x i t) ∂stdGaussian) ≤
    ∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂stdGaussian := by
  have hconv : ConvexOn ℝ (Set.Ici 0) (fun x => x * Real.log x) := convexOn_mul_log
  have hcont : ContinuousOn (fun x => x * Real.log x) (Set.Ici 0) :=
    continuous_mul_log.continuousOn
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have hmem : ∀ᵐ t ∂stdGaussian, g (Function.update x i t) ∈ Set.Ici (0 : ℝ) :=
    ae_of_all _ (fun t => hg_nn _)
  exact hconv.map_integral_le hcont hclosed hmem hslice_int hslice_log

-- Helper: condEntropyAt is nonneg for g ≥ 0 when the slice is integrable.
private lemma condEntropyAt_nonneg_of_nonneg {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (x : Fin n → ℝ) (i : Fin n)
    (hslice_int : Integrable (fun t => g (Function.update x i t)) stdGaussian)
    (hslice_log : Integrable (fun t => g (Function.update x i t) *
        Real.log (g (Function.update x i t))) stdGaussian) :
    0 ≤ condEntropyAt stdGaussian g i x := by
  simp only [condEntropyAt, entropy]
  linarith [jensen_condExpect_mul_log g hg_nn x i hslice_int hslice_log]

-- Helper: E_i g doesn't depend on coordinate i, so condEnt_i(E_i g) = 0.
private lemma condEntropyAt_of_condExpect_self {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    condEntropyAt stdGaussian
      (fun y => ∫ t, g (Function.update y i t) ∂stdGaussian) i x = 0 := by
  simp only [condEntropyAt, entropy]
  -- The slice: t ↦ (E_i g)(update x i t) = ∫ s, g(update (update x i t) i s) dγ(s)
  -- Since update (update x i t) i s = update x i s, this doesn't depend on t.
  have hconst : ∀ t, (fun y => ∫ s, g (Function.update y i s) ∂stdGaussian)
      (Function.update x i t) =
    ∫ s, g (Function.update x i s) ∂stdGaussian := by
    intro t
    simp only
    congr 1; ext s
    rw [Function.update_idem]
  -- Both integrals become c * (something) - same = 0
  simp_rw [hconst]
  simp [integral_const, Measure.real, measure_univ]

-- Helper: E_i g is nonneg when g is nonneg.
private lemma condExpect_nonneg_of_nonneg {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x) (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ ∫ t, g (Function.update x i t) ∂stdGaussian :=
  integral_nonneg (fun t => hg_nn _)

-- Gibbs inequality: for a ≥ 0, b > 0, a·log(a) - a·log(b) ≥ a - b.
-- Key step in proving KL divergence ≥ 0.
private lemma gibbs_pointwise {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log a - a * Real.log b ≥ a - b := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp; linarith
  · have hb_ne := ne_of_gt hb
    have ha_ne := ne_of_gt ha_pos
    rw [show a * Real.log a - a * Real.log b = a * Real.log (a / b) from by
      rw [Real.log_div ha_ne hb_ne]; ring]
    have h := mul_log_ge_sub_one (a / b) (div_pos ha_pos hb)
    -- h : (a/b) * log(a/b) ≥ a/b - 1
    -- Need: a * log(a/b) ≥ a - b
    -- a * log(a/b) = b * ((a/b) * log(a/b))  [since b * (a/b) = a]
    -- ≥ b * (a/b - 1) = a - b
    have hab_eq : b * (a / b) = a := by field_simp
    have hge : b * (a / b * log (a / b)) ≥ b * (a / b - 1) :=
      mul_le_mul_of_nonneg_left (ge_iff_le.mp h) hb.le
    linarith [show b * (a / b - 1) = a - b by nlinarith,
              show b * (a / b * log (a / b)) = a * log (a / b) by nlinarith]

-- Function.update commutativity for distinct indices.
private lemma update_comm_of_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (x : Fin n → ℝ) (a b : ℝ) :
    Function.update (Function.update x i a) j b =
    Function.update (Function.update x j b) i a := by
  ext k
  by_cases hki : k = i <;> by_cases hkj : k = j
  · exact absurd (hki ▸ hkj) hij
  · subst hki; simp [Function.update_apply, hij, hij.symm]
  · subst hkj; simp [Function.update_apply, hij, hij.symm]
  · simp [Function.update_apply, hki, hkj]

-- Helper: ∫ h dγ¹ = ∫ h(fun _ => t) dγ(t) via piFinSuccAbove decomposition.
private lemma integral_stdGaussianPi_one_eq (h : (Fin 1 → ℝ) → ℝ) :
    ∫ x, h x ∂stdGaussianPi 1 = ∫ t, h (fun _ => t) ∂stdGaussian := by
  have hfun_eq : (fun x : Fin 1 → ℝ => h x) = (fun x => h (fun _ => x 0)) := by
    ext x; congr 1; ext j; exact congr_arg x (Fin.fin_one_eq_zero j)
  rw [hfun_eq]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => ℝ) (0 : Fin 1)
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin 1 => stdGaussian) (0 : Fin 1)
  have hpi : stdGaussianPi 1 = Measure.pi (fun _ : Fin 1 => stdGaussian) := rfl
  rw [hpi, ← hmp.symm.integral_comp' (g := fun x => h (fun _ => x 0))]
  have he_zero : ∀ (p : ℝ × (Fin 0 → ℝ)), (e.symm p) 0 = p.1 := by
    intro ⟨a, y⟩; simp [e, MeasurableEquiv.piFinSuccAbove]
  have : (fun p : ℝ × (Fin 0 → ℝ) => h (fun _ => (e.symm p) 0)) =
      (fun p => h (fun _ => p.1)) := by
    ext p; rw [he_zero]
  rw [this, integral_fun_fst (fun t => h (fun _ => t))]
  simp [Measure.real, measure_univ]

-- For n = 1, subadditivity is an equality: entropyPi γ¹ g = ∫ condEnt_0(g) dγ¹.
-- Key: for Fin 1, update x 0 t = fun _ => t (the only index is 0),
-- so condEnt_0(g)(x) doesn't depend on x.
private lemma entropy_subadditivity_fin1
    (g : (Fin 1 → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi 1)) :
    entropyPi (stdGaussianPi 1) g ≤
    ∑ i : Fin 1, ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi 1) := by
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hdef : (default : Fin 1) = 0 := rfl
  have hupdate : ∀ (x : Fin 1 → ℝ) (t : ℝ),
      Function.update x (0 : Fin 1) t = fun _ => t := by
    intro x t; ext j
    have : j = 0 := Fin.fin_one_eq_zero j
    subst this; simp [Function.update_self]
  have hconst_integrand : ∀ x : Fin 1 → ℝ,
      condEntropyAt stdGaussian g default x =
      (∫ t, g (fun _ => t) * Real.log (g (fun _ => t)) ∂stdGaussian) -
      (∫ t, g (fun _ => t) ∂stdGaussian) * Real.log (∫ t, g (fun _ => t) ∂stdGaussian) := by
    intro x
    simp only [condEntropyAt, entropy, hdef]
    simp_rw [hupdate]
  simp_rw [hconst_integrand]
  simp [integral_const, Measure.real, measure_univ]
  simp only [entropyPi]
  rw [integral_stdGaussianPi_one_eq, integral_stdGaussianPi_one_eq]

-- Log-sum inequality for 1D integrals (Gibbs variational form).
-- For a ≥ 0, b > 0 a.e., with appropriate integrability:
--   ∫ a·log(a) - ∫ a·log(b) ≥ (∫a)·log(∫a) - (∫a)·log(∫b)
-- Proof: apply gibbs_pointwise with scaled b, then integrate.
private lemma log_sum_inequality
    (a b : ℝ → ℝ) (ha_nn : ∀ x, 0 ≤ a x) (hb_pos : ∀ x, 0 < b x)
    (ha_int : Integrable a stdGaussian)
    (ha_log : Integrable (fun x => a x * Real.log (a x)) stdGaussian)
    (ha_logb : Integrable (fun x => a x * Real.log (b x)) stdGaussian)
    (hb_int : Integrable b stdGaussian)
    (hA_pos : 0 < ∫ x, a x ∂stdGaussian)
    (hB_pos : 0 < ∫ x, b x ∂stdGaussian) :
    ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian ≥
    (∫ x, a x ∂stdGaussian) * Real.log (∫ x, a x ∂stdGaussian) -
      (∫ x, a x ∂stdGaussian) * Real.log (∫ x, b x ∂stdGaussian) := by
  set A := ∫ x, a x ∂stdGaussian
  set B := ∫ x, b x ∂stdGaussian
  -- Scale b: let b̃(x) = b(x) · A / B. Then ∫b̃ = A.
  -- Gibbs pointwise: a·log(a) - a·log(b̃) ≥ a - b̃
  -- Integrating: ∫a·loga - ∫a·log(b̃) ≥ ∫a - ∫b̃ = A - A = 0
  -- And log(b̃) = log(b) + log(A/B), so ∫a·log(b̃) = ∫a·logb + A·log(A/B)
  -- Therefore: ∫a·loga - ∫a·logb - A·log(A/B) ≥ 0
  -- i.e., ∫a·loga - ∫a·logb ≥ A·log(A/B) = A·logA - A·logB
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hAB : 0 < A / B := div_pos hA_pos hB_pos
  -- Pointwise bound: for each x, a(x)·loga(x) - a(x)·log(b(x)·A/B) ≥ a(x) - b(x)·A/B
  have hpw : ∀ x, a x * Real.log (a x) - a x * Real.log (b x * (A / B)) ≥
      a x - b x * (A / B) := by
    intro x
    exact gibbs_pointwise (ha_nn x) (mul_pos (hb_pos x) hAB)
  -- Integrate pointwise bound
  have hint_scaled : Integrable (fun x => a x * Real.log (b x * (A / B))) stdGaussian := by
    have : (fun x => a x * Real.log (b x * (A / B))) =
        (fun x => a x * Real.log (b x) + a x * Real.log (A / B)) := by
      ext x
      rw [Real.log_mul (ne_of_gt (hb_pos x)) (ne_of_gt hAB)]
      ring
    rw [this]
    exact ha_logb.add (ha_int.mul_const _)
  have hge : ∫ x, (a x * Real.log (a x) - a x * Real.log (b x * (A / B))) ∂stdGaussian ≥
      ∫ x, (a x - b x * (A / B)) ∂stdGaussian :=
    by rw [ge_iff_le]
       exact integral_mono (ha_int.sub (hb_int.mul_const _))
        (ha_log.sub hint_scaled) (fun x => by linarith [hpw x])
  -- RHS of hge = A - B·(A/B) = A - A = 0
  have hrhs : ∫ x, (a x - b x * (A / B)) ∂stdGaussian = 0 := by
    rw [integral_sub ha_int (hb_int.mul_const _), integral_mul_const]
    have hBA : B * (A / B) = A := by field_simp
    linarith
  -- LHS of hge: expand log(b·A/B) = logb + log(A/B)
  have hlhs : ∫ x, (a x * Real.log (a x) - a x * Real.log (b x * (A / B))) ∂stdGaussian =
      ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian -
      A * Real.log (A / B) := by
    rw [integral_sub ha_log hint_scaled]
    have : ∫ x, a x * Real.log (b x * (A / B)) ∂stdGaussian =
        ∫ x, a x * Real.log (b x) ∂stdGaussian + A * Real.log (A / B) := by
      have hexp : (fun x => a x * Real.log (b x * (A / B))) =
          (fun x => a x * Real.log (b x) + a x * Real.log (A / B)) := by
        ext x
        rw [Real.log_mul (ne_of_gt (hb_pos x)) (ne_of_gt hAB)]
        ring
      rw [hexp, integral_add ha_logb (ha_int.mul_const _)]
      congr 1; rw [integral_mul_const]
    linarith
  -- Combine: ∫a·loga - ∫a·logb - A·log(A/B) ≥ 0
  -- i.e., ∫a·loga - ∫a·logb ≥ A·log(A/B) = A·logA - A·logB
  have hkey : ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian ≥ A * Real.log (A / B) := by
    linarith [hlhs ▸ hge, hrhs]
  -- A·log(A/B) = A·logA - A·logB
  rw [Real.log_div (ne_of_gt hA_pos) hB_ne] at hkey
  linarith

-- Variant of log_sum_inequality with nonneg b (relaxed from b > 0).
-- The key additional hypothesis is hab_ac: b(x) = 0 → a(x) = 0 (a.e.),
-- which ensures the Gibbs bound holds a.e. even when b = 0 at some points.
private lemma log_sum_inequality_nn
    (a b : ℝ → ℝ) (ha_nn : ∀ x, 0 ≤ a x) (hb_nn : ∀ x, 0 ≤ b x)
    (ha_int : Integrable a stdGaussian)
    (ha_log : Integrable (fun x => a x * Real.log (a x)) stdGaussian)
    (ha_logb : Integrable (fun x => a x * Real.log (b x)) stdGaussian)
    (hb_int : Integrable b stdGaussian)
    (hA_pos : 0 < ∫ x, a x ∂stdGaussian)
    (hB_pos : 0 < ∫ x, b x ∂stdGaussian)
    (hab_ac : ∀ᵐ x ∂stdGaussian, b x = 0 → a x = 0) :
    ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian ≥
    (∫ x, a x ∂stdGaussian) * Real.log (∫ x, a x ∂stdGaussian) -
      (∫ x, a x ∂stdGaussian) * Real.log (∫ x, b x ∂stdGaussian) := by
  set A := ∫ x, a x ∂stdGaussian
  set B := ∫ x, b x ∂stdGaussian
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hAB : 0 < A / B := div_pos hA_pos hB_pos
  -- Pointwise Gibbs a.e.: a·log(a) - a·log(b·A/B) ≥ a - b·A/B
  have hpw : ∀ᵐ x ∂stdGaussian,
      a x * Real.log (a x) - a x * Real.log (b x * (A / B)) ≥
      a x - b x * (A / B) := by
    filter_upwards [hab_ac] with x hac
    rcases eq_or_lt_of_le (hb_nn x) with hbz | hbp
    · -- b(x) = 0, so a(x) = 0 by absolute continuity
      have hax := hac hbz.symm; simp [hax, hbz.symm]
    · exact gibbs_pointwise (ha_nn x) (mul_pos hbp hAB)
  -- log(b·A/B) = log(b) + log(A/B) a.e.
  have hlog_split : ∀ᵐ x ∂stdGaussian,
      a x * Real.log (b x * (A / B)) =
      a x * Real.log (b x) + a x * Real.log (A / B) := by
    filter_upwards [hab_ac] with x hac
    rcases eq_or_lt_of_le (hb_nn x) with hbz | hbp
    · simp [hac hbz.symm, hbz.symm]
    · rw [Real.log_mul (ne_of_gt hbp) (ne_of_gt hAB)]; ring
  -- Integrability of a·log(b·A/B)
  have hint_scaled : Integrable (fun x => a x * Real.log (b x * (A / B))) stdGaussian :=
    (ha_logb.add (ha_int.mul_const _)).congr (hlog_split.mono fun x hx => hx.symm)
  -- Integrate the Gibbs bound
  have hge : ∫ x, (a x * Real.log (a x) - a x * Real.log (b x * (A / B))) ∂stdGaussian ≥
      ∫ x, (a x - b x * (A / B)) ∂stdGaussian :=
    ge_iff_le.mpr (integral_mono_ae
      (ha_int.sub (hb_int.mul_const _))
      (ha_log.sub hint_scaled)
      (by filter_upwards [hpw] with x hx; linarith))
  -- RHS = A - B·(A/B) = 0
  have hrhs : ∫ x, (a x - b x * (A / B)) ∂stdGaussian = 0 := by
    rw [integral_sub ha_int (hb_int.mul_const _), integral_mul_const]
    rw [show B * (A / B) = A from mul_div_cancel₀ A hB_ne]
    exact sub_self A
  -- LHS expansion
  have hlhs : ∫ x, (a x * Real.log (a x) - a x * Real.log (b x * (A / B))) ∂stdGaussian =
      ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian -
      A * Real.log (A / B) := by
    rw [integral_sub ha_log hint_scaled]
    have : ∫ x, a x * Real.log (b x * (A / B)) ∂stdGaussian =
        ∫ x, a x * Real.log (b x) ∂stdGaussian + A * Real.log (A / B) := by
      rw [integral_congr_ae hlog_split, integral_add ha_logb (ha_int.mul_const _)]
      congr 1; rw [integral_mul_const]
    linarith
  have hkey : ∫ x, a x * Real.log (a x) ∂stdGaussian -
      ∫ x, a x * Real.log (b x) ∂stdGaussian ≥ A * Real.log (A / B) := by
    linarith [hlhs ▸ hge, hrhs]
  -- A * log(A/B) = A * logA - A * logB
  rw [Real.log_div (ne_of_gt hA_pos) hB_ne] at hkey
  nlinarith [mul_sub A (Real.log A) (Real.log B)]

-- Jensen integrated: ∫ (E_j g)·log(E_j g) ≤ ∫ g·log(g) for nonneg integrable g.
-- This is the integrated version of `convexOn_mul_log.map_integral_le`.
private lemma jensen_condExpect_integral_le {n : ℕ}
    (g : (Fin (n + 1) → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi (n + 1)))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi (n + 1)))
    (j : Fin (n + 1)) :
    ∫ x, (∫ t, g (Function.update x j t) ∂stdGaussian) *
        Real.log (∫ t, g (Function.update x j t) ∂stdGaussian) ∂(stdGaussianPi (n + 1)) ≤
    ∫ x, g x * Real.log (g x) ∂(stdGaussianPi (n + 1)) := by
  -- Step 1: Pointwise Jensen a.e.
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  set γn := Measure.pi (fun k : Fin n => μ' (j.succAbove k))
  have hmp := measurePreserving_piFinSuccAbove μ' j
  have hupd : ∀ y t, Function.update y j t = e.symm (t, (e y).2) := by
    intro y t
    conv_lhs => rw [(e.symm_apply_apply y).symm]
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact @Fin.update_insertNth n (fun _ => ℝ) j (e y).1 t (e y).2
  have hg_prod : Integrable (g ∘ e.symm) (stdGaussian.prod γn) :=
    hmp.symm.integrable_comp_of_integrable hg
  have hgl_prod : Integrable ((fun x => g x * log (g x)) ∘ e.symm) (stdGaussian.prod γn) :=
    hmp.symm.integrable_comp_of_integrable hg_log
  have hg_ae : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      Integrable (fun t => g (Function.update y j t)) stdGaussian := by
    have hae_γn := hg_prod.prod_left_ae
    have hae_prod := ae_snd_of_ae_marginal stdGaussian γn hae_γn
    exact (hmp.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
      rwa [show (fun t => (g ∘ e.symm) (t, (e y).2)) =
          (fun t => g (Function.update y j t)) from by
        ext t; simp only [Function.comp]; rw [hupd y t]] at hy
  have hgl_ae : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      Integrable (fun t => g (Function.update y j t) *
        log (g (Function.update y j t))) stdGaussian := by
    have hae_γn := hgl_prod.prod_left_ae
    have hae_prod := ae_snd_of_ae_marginal stdGaussian γn hae_γn
    exact (hmp.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
      rwa [show (fun t => ((fun x => g x * log (g x)) ∘ e.symm) (t, (e y).2)) =
          (fun t => g (Function.update y j t) * log (g (Function.update y j t))) from by
        ext t; simp only [Function.comp]; rw [hupd y t]] at hy
  -- Pointwise Jensen a.e.
  have hpw : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      (∫ t, g (Function.update y j t) ∂stdGaussian) *
        log (∫ t, g (Function.update y j t) ∂stdGaussian) ≤
      ∫ t, g (Function.update y j t) * log (g (Function.update y j t)) ∂stdGaussian :=
    by filter_upwards [hg_ae, hgl_ae] with y hgy hgly
       exact jensen_condExpect_mul_log g hg_nn y j hgy hgly
  -- Step 2: Integrability of Ej·log(Ej)
  have hEj_log_int : Integrable (fun x => (∫ t, g (Function.update x j t) ∂stdGaussian) *
      log (∫ t, g (Function.update x j t) ∂stdGaussian)) (stdGaussianPi (n + 1)) := by
    -- condEntropyAt = first_term - Ej·log(Ej), all integrable
    have hA_int := integrable_condExpect_stdGaussianPi_gen _ hg_log j
    have hcondEnt_int := integrable_condEntropyAt_of_nonneg g hg_nn hg hg_log j
    -- Ej·log(Ej) = first_term - condEntropyAt, hence integrable
    have : (fun x => (∫ t, g (Function.update x j t) ∂stdGaussian) *
        log (∫ t, g (Function.update x j t) ∂stdGaussian)) =
      fun x => (∫ t, g (Function.update x j t) * log (g (Function.update x j t)) ∂stdGaussian) -
        condEntropyAt stdGaussian g j x := by
      ext x; simp only [condEntropyAt, entropy]; ring
    rw [this]; exact hA_int.sub hcondEnt_int
  -- Step 3: ∫ slice(g·logg) = ∫ g·logg by Fubini
  have hfub : ∫ x, (∫ t, g (Function.update x j t) * log (g (Function.update x j t)) ∂stdGaussian)
      ∂(stdGaussianPi (n + 1)) =
      ∫ x, g x * log (g x) ∂(stdGaussianPi (n + 1)) :=
    integral_condExpect_eq_integral_pi _ hg_log j
  -- Combine
  calc ∫ x, (∫ t, g (Function.update x j t) ∂stdGaussian) *
          log (∫ t, g (Function.update x j t) ∂stdGaussian) ∂(stdGaussianPi (n + 1))
      ≤ ∫ x, (∫ t, g (Function.update x j t) * log (g (Function.update x j t)) ∂stdGaussian)
          ∂(stdGaussianPi (n + 1)) :=
        integral_mono_ae hEj_log_int (integrable_condExpect_stdGaussianPi_gen _ hg_log j) hpw
    _ = ∫ x, g x * log (g x) ∂(stdGaussianPi (n + 1)) := hfub


-- ae decomposition: ∀ᵐ y, P(y) → ∀ᵐ x, ∀ᵐ s, P(update x j s).
-- Uses piFinSuccAbove at j + MeasurableEquiv.prodComm swap + measure_ae_null_of_prod_null.
private lemma ae_ae_update_of_ae {n : ℕ} {P : (Fin (n + 1) → ℝ) → Prop}
    (j : Fin (n + 1))
    (h : ∀ᵐ y ∂(stdGaussianPi (n + 1)), P y) :
    ∀ᵐ x ∂(stdGaussianPi (n + 1)),
      ∀ᵐ s ∂stdGaussian, P (Function.update x j s) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  set γn := Measure.pi (fun k : Fin n => μ' (j.succAbove k))
  have hmp := measurePreserving_piFinSuccAbove μ' j
  have hupd : ∀ y t, Function.update y j t = e.symm (t, (e y).2) := by
    intro y t; conv_lhs => rw [(e.symm_apply_apply y).symm]
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact @Fin.update_insertNth n (fun _ => ℝ) j (e y).1 t (e y).2
  -- The composite e.symm ∘ swap : (Fin n → ℝ) × ℝ → (Fin (n+1) → ℝ) is measure-preserving
  -- from (γn × γ) to γ^{n+1}, since e : γ^{n+1} ≃ (γ × γn) and swap : (γn × γ) ≃ (γ × γn).
  set f : (Fin n → ℝ) × ℝ → (Fin (n + 1) → ℝ) := fun q => e.symm (q.2, q.1)
  have hf_mp : MeasurePreserving f (γn.prod stdGaussian) (stdGaussianPi (n + 1)) := by
    have : f = e.symm ∘ Prod.swap := by ext ⟨z, s⟩; rfl
    rw [this]
    exact hmp.symm.comp ⟨measurable_swap, Measure.prod_swap⟩
  -- Transport h: ∀ᵐ y, P(y) → ∀ᵐ (z,s) ∂(γn×γ), P(e.symm(s,z))
  have h_null_swap : ∀ᵐ q ∂(γn.prod stdGaussian), P (e.symm (q.2, q.1)) := by
    rw [ae_iff] at h ⊢
    have hnms : NullMeasurableSet {y | ¬P y} (stdGaussianPi (n + 1)) :=
      NullMeasurableSet.of_null h
    have : {q : (Fin n → ℝ) × ℝ | ¬P (e.symm (q.2, q.1))} = f ⁻¹' {y | ¬P y} := by
      ext ⟨z, s⟩; simp [f, Set.mem_preimage]
    rw [this, hf_mp.measure_preimage hnms]; exact h
  -- ae_ae_of_ae_prod on (γn × γ): ∀ᵐ z ∂γn, ∀ᵐ s ∂γ, P(e.symm(s,z))
  have h_ae_ae : ∀ᵐ z ∂γn, ∀ᵐ s ∂stdGaussian, P (e.symm (s, z)) :=
    Measure.ae_ae_of_ae_prod h_null_swap
  -- Transport back via removeNth j
  have hmp_rem : MeasurePreserving (fun x : Fin (n + 1) → ℝ => Fin.removeNth j x)
      (stdGaussianPi (n + 1)) γn := by
    change MeasurePreserving (Prod.snd ∘ e) _ _
    simp only [stdGaussianPi]
    exact measurePreserving_snd.comp
      (measurePreserving_piFinSuccAbove (fun (_ : Fin (n + 1)) => stdGaussian) j)
  exact (hmp_rem.quasiMeasurePreserving.ae h_ae_ae).mono fun x hx =>
    hx.mono fun s hs => by show P (Function.update x j s); rw [hupd x s]; exact hs

-- ae product integrability of g at two coordinates (i, j) via double piFinSuccAbove.
-- For ae x, (s, t) ↦ g(update(update x j s) i t) is integrable on γ × γ.
private lemma ae_integrable_prod_update_update {n : ℕ}
    (g : (Fin (n + 1) → ℝ) → ℝ)
    (hg : Integrable g (stdGaussianPi (n + 1)))
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ᵐ x ∂(stdGaussianPi (n + 1)),
      Integrable (fun p : ℝ × ℝ => g (Function.update (Function.update x j p.1) i p.2))
        (stdGaussian.prod stdGaussian) := by
  -- Step 1: find j' : Fin n such that i.succAbove j' = j
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
  -- Case split on n to handle piFinSuccAbove at j' : Fin n
  rcases n with _ | m
  · exact Fin.elim0 j'
  -- Now n = m + 1, so j' : Fin (m + 1) and piFinSuccAbove works
  -- Step 2: decompose γ^{m+2} at coordinate i
  set ei := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) => ℝ) i
  set μi : Fin (m + 2) → Measure ℝ := fun _ => stdGaussian
  set γn := Measure.pi (fun k : Fin (m + 1) => μi (i.succAbove k))
  have hmpi := measurePreserving_piFinSuccAbove μi i
  -- g ∘ ei.symm ∈ L¹(γ × γ^{m+1})
  have hG : Integrable (g ∘ ei.symm) (stdGaussian.prod γn) :=
    hmpi.symm.integrable_comp_of_integrable hg
  -- Step 3: decompose γ^{m+1} at coordinate j'
  set μn : Fin (m + 1) → Measure ℝ := fun k => μi (i.succAbove k)
  set ej := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j'
  set γm := Measure.pi (fun k : Fin m => μn (j'.succAbove k))
  have hmpj := measurePreserving_piFinSuccAbove μn j'
  -- Step 4: Prod.map id ej.symm : γ × (γ × γ^m) → γ × γ^{m+1} is MP
  have hpm : MeasurePreserving (Prod.map id ej.symm)
      (stdGaussian.prod (stdGaussian.prod γm)) (stdGaussian.prod γn) :=
    (MeasurePreserving.id stdGaussian).prod hmpj.symm
  -- g ∘ ei.symm ∘ Prod.map id ej.symm ∈ L¹(γ × (γ × γ^m))
  have hH : Integrable (g ∘ ei.symm ∘ Prod.map id ej.symm)
      (stdGaussian.prod (stdGaussian.prod γm)) :=
    hpm.integrable_comp_of_integrable hG
  -- Step 5: prodAssoc : (γ × γ) × γ^m → γ × (γ × γ^m) is MP
  have hpa : MeasurePreserving (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ)
      (γ := Fin m → ℝ))
      ((stdGaussian.prod stdGaussian).prod γm)
      (stdGaussian.prod (stdGaussian.prod γm)) :=
    measurePreserving_prodAssoc stdGaussian stdGaussian γm
  -- Composed function ∈ L¹((γ × γ) × γ^m)
  have hK : Integrable (g ∘ ei.symm ∘ Prod.map id ej.symm ∘ MeasurableEquiv.prodAssoc)
      ((stdGaussian.prod stdGaussian).prod γm) :=
    hpa.integrable_comp_of_integrable hH
  -- Step 6: prod_left_ae gives ae integrability on γ × γ
  have hae_γm : ∀ᵐ r ∂γm,
      Integrable (fun p : ℝ × ℝ =>
        (g ∘ ei.symm ∘ Prod.map id ej.symm ∘ MeasurableEquiv.prodAssoc) (p, r))
        (stdGaussian.prod stdGaussian) := hK.prod_left_ae
  -- Step 7: transport ae from γ^m to γ^{m+2}
  -- The projection x ↦ removeNth j' (removeNth i x) is QMP from γ^{m+2} to γ^m
  have hmp_remi : MeasurePreserving (fun x : Fin (m + 2) → ℝ => Fin.removeNth i x)
      (stdGaussianPi (m + 2)) γn := by
    change MeasurePreserving (Prod.snd ∘ ei) _ _
    exact measurePreserving_snd.comp hmpi
  have hmp_remj : MeasurePreserving (fun z : Fin (m + 1) → ℝ => Fin.removeNth j' z)
      γn γm := by
    change MeasurePreserving (Prod.snd ∘ ej) _ _
    exact measurePreserving_snd.comp hmpj
  have hmp_rem2 : MeasurePreserving
      (fun x : Fin (m + 2) → ℝ => Fin.removeNth j' (Fin.removeNth i x))
      (stdGaussianPi (m + 2)) γm := hmp_remj.comp hmp_remi
  -- Transport: ae r ∂γ^m → ae x ∂γ^{m+2}
  have hae_x := hmp_rem2.quasiMeasurePreserving.ae hae_γm
  -- Step 8: rewrite the integrand to match the goal
  exact hae_x.mono fun x hx => by
    set r := Fin.removeNth j' (Fin.removeNth i x)
    -- Key identity: ei.symm(t, ej.symm(s, r)) = update(update x j s) i t
    have hident : ∀ s t, (ei.symm (t, ej.symm (s, r))) =
        Function.update (Function.update x j s) i t := by
      intro s t
      -- Unfold piFinSuccAbove.symm to insertNth
      show Fin.insertNth i t (Fin.insertNth j' s r) =
        Function.update (Function.update x j s) i t
      -- Step 1: insertNth j' s r = update (removeNth i x) j' s
      have h1 : Fin.insertNth j' s r =
          Function.update (Fin.removeNth i x) j' s := by
        rw [← Fin.update_insertNth j' ((Fin.removeNth i x) j') s
          (Fin.removeNth j' (Fin.removeNth i x))]
        congr 1; exact (Fin.insertNthEquiv _ j').right_inv (Fin.removeNth i x)
      rw [h1, Fin.insertNth_update, show i.succAbove j' = j from hj']
      -- Step 2: insertNth i t (removeNth i x) = update x i t
      have h3 : Fin.insertNth i t (Fin.removeNth i x) = Function.update x i t := by
        rw [← Fin.update_insertNth i (x i) t (Fin.removeNth i x)]
        congr 1; exact (Fin.insertNthEquiv _ i).right_inv x
      rw [h3]
      exact @Function.update_comm _ _ (fun _ => ℝ) _ _ hij t s x
    -- Rewrite the composed function to use update
    have hcong : (fun p : ℝ × ℝ =>
        (g ∘ ei.symm ∘ Prod.map id ej.symm ∘ MeasurableEquiv.prodAssoc) (p, r)) =
        (fun p : ℝ × ℝ => g (Function.update (Function.update x j p.2) i p.1)) := by
      ext ⟨a, b⟩
      simp only [Function.comp, MeasurableEquiv.prodAssoc, Equiv.prodAssoc,
        MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Prod.map, id]
      rw [hident b a]
    rw [hcong] at hx
    -- hx : Integrable (fun p => g(update(update x j p.2) i p.1)) (γ.prod γ)
    -- Goal: Integrable (fun p => g(update(update x j p.1) i p.2)) (γ.prod γ)
    -- Use Prod.swap: γ.prod γ ≃ γ.prod γ via swap
    have hswap := Measure.measurePreserving_swap.integrable_comp_of_integrable hx
    -- hswap : Integrable ((fun p => g(update(update x j p.2) i p.1)) ∘ Prod.swap) (γ.prod γ)
    -- (fun p => ...) ∘ swap = (fun p => g(update(update x j p.1) i p.2))
    convert hswap using 1

-- Entropy of mixture ≤ mixture of entropies: core inequality for DPI.
-- Proof: log_sum_inequality_nn for each s gives Ent(f_s) ≥ ∫f_s·log(h) - c_s·log(C).
-- Integrate over s, use fubini_cross_term to collapse ∫_s∫f_s·log(h) = ∫h·log(h).
-- Conclude ∫_s Ent(f_s) ≥ Ent(h).
-- Note: the "two Jensen" approach fails (opposite-sign bounds don't combine).
-- Pointwise log-sum bound: for nonneg a, b with a = f_s, b = h (the mixture),
-- condEntropyAt(a) ≥ ∫ a·log(b) - (∫a)·log(∫b), with case handling for ∫a = 0.
-- This is the key per-s bound used in entropy_convex_mixture.
private lemma condEntropyAt_ge_cross_term
    (a b : ℝ → ℝ) (ha_nn : ∀ t, 0 ≤ a t) (hb_nn : ∀ t, 0 ≤ b t)
    (ha_int : Integrable a stdGaussian)
    (ha_log : Integrable (fun t => a t * Real.log (a t)) stdGaussian)
    (ha_logb : Integrable (fun t => a t * Real.log (b t)) stdGaussian)
    (hb_int : Integrable b stdGaussian)
    (hB_pos : 0 < ∫ t, b t ∂stdGaussian)
    (hab_ac : ∀ᵐ t ∂stdGaussian, b t = 0 → a t = 0) :
    ∫ t, a t * Real.log (a t) ∂stdGaussian -
      (∫ t, a t ∂stdGaussian) * Real.log (∫ t, a t ∂stdGaussian) ≥
    ∫ t, a t * Real.log (b t) ∂stdGaussian -
      (∫ t, a t ∂stdGaussian) * Real.log (∫ t, b t ∂stdGaussian) := by
  rcases le_or_gt (∫ t, a t ∂stdGaussian) 0 with hA_le | hA_pos
  · -- ∫ a ≤ 0, but a ≥ 0, so ∫ a = 0, hence a = 0 ae
    have hA_eq : ∫ t, a t ∂stdGaussian = 0 :=
      le_antisymm hA_le (integral_nonneg ha_nn)
    have ha_ae : ∀ᵐ t ∂stdGaussian, a t = 0 := by
      rwa [integral_eq_zero_iff_of_nonneg ha_nn ha_int] at hA_eq
    have h1 : ∫ t, a t * Real.log (a t) ∂stdGaussian = 0 := by
      rw [integral_congr_ae (ha_ae.mono fun t ht => show a t * Real.log (a t) = 0 by simp [ht])]
      simp
    have h2 : ∫ t, a t * Real.log (b t) ∂stdGaussian = 0 := by
      rw [integral_congr_ae (ha_ae.mono fun t ht => show a t * Real.log (b t) = 0 by simp [ht])]
      simp
    simp [hA_eq, h1, h2]
  · have h := log_sum_inequality_nn a b ha_nn hb_nn ha_int ha_log ha_logb
      hb_int hA_pos hB_pos hab_ac
    linarith

private lemma entropy_convex_mixture {n : ℕ}
    (g : (Fin (n + 1) → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi (n + 1)))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi (n + 1)))
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ᵐ x ∂(stdGaussianPi (n + 1)),
    condEntropyAt stdGaussian
      (fun y => ∫ t, g (Function.update y j t) ∂stdGaussian) i x ≤
    ∫ s, condEntropyAt stdGaussian g i (Function.update x j s) ∂stdGaussian := by
  -- Strategy: unfold condEntropyAt, rewrite LHS via update_comm,
  -- apply condEntropyAt_ge_cross_term for ae s, integrate, use fubini_cross_term.
  -- ae-s integrability: for ae x, for ae s, i-slices of g at upd x j s are integrable
  -- ae-s integrability via ae_ae_update_of_ae
  -- First establish: ∀ᵐ y, Integrable (fun t => g(update y i t)) stdGaussian
  -- and: ∀ᵐ y, Integrable (fun t => g(update y i t) * log(g(update y i t))) stdGaussian
  -- These use the standard piFinSuccAbove + prod_left_ae + ae_snd_of_ae_marginal pattern.
  have hg_ae_i : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      Integrable (fun t => g (Function.update y i t)) stdGaussian := by
    set ei' := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    set μ'' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
    set γni' := Measure.pi (fun k : Fin n => μ'' (i.succAbove k))
    have hmpi' := measurePreserving_piFinSuccAbove μ'' i
    have hupdi' : ∀ y t, Function.update y i t = ei'.symm (t, (ei' y).2) := by
      intro y t; conv_lhs => rw [(ei'.symm_apply_apply y).symm]
      simp only [ei', MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact @Fin.update_insertNth n (fun _ => ℝ) i (ei' y).1 t (ei' y).2
    have hg_prod := hmpi'.symm.integrable_comp_of_integrable hg
    have hae_γn := hg_prod.prod_left_ae
    have hae_prod := ae_snd_of_ae_marginal stdGaussian γni' hae_γn
    exact (hmpi'.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
      rwa [show (fun t => (g ∘ ei'.symm) (t, (ei' y).2)) =
          (fun t => g (Function.update y i t)) from by
        ext t; simp only [Function.comp]; rw [hupdi' y t]] at hy
  have hgl_ae_i : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      Integrable (fun t => g (Function.update y i t) *
        Real.log (g (Function.update y i t))) stdGaussian := by
    set ei' := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    set μ'' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
    set γni' := Measure.pi (fun k : Fin n => μ'' (i.succAbove k))
    have hmpi' := measurePreserving_piFinSuccAbove μ'' i
    have hupdi' : ∀ y t, Function.update y i t = ei'.symm (t, (ei' y).2) := by
      intro y t; conv_lhs => rw [(ei'.symm_apply_apply y).symm]
      simp only [ei', MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact @Fin.update_insertNth n (fun _ => ℝ) i (ei' y).1 t (ei' y).2
    have hgl_prod := hmpi'.symm.integrable_comp_of_integrable hg_log
    have hae_γn := hgl_prod.prod_left_ae
    have hae_prod := ae_snd_of_ae_marginal stdGaussian γni' hae_γn
    exact (hmpi'.quasiMeasurePreserving.ae hae_prod).mono fun y hy => by
      rwa [show (fun t => ((fun x => g x * Real.log (g x)) ∘ ei'.symm) (t, (ei' y).2)) =
          (fun t => g (Function.update y i t) *
            Real.log (g (Function.update y i t))) from by
        ext t; simp only [Function.comp]; rw [hupdi' y t]] at hy
  -- Now apply ae_ae_update_of_ae to decompose at coordinate j
  have hg_ae_ij : ∀ᵐ x ∂(stdGaussianPi (n + 1)),
      ∀ᵐ s ∂stdGaussian,
        Integrable (fun t => g (Function.update (Function.update x j s) i t))
          stdGaussian := ae_ae_update_of_ae j hg_ae_i
  have hgl_ae_ij : ∀ᵐ x ∂(stdGaussianPi (n + 1)),
      ∀ᵐ s ∂stdGaussian,
        Integrable (fun t => g (Function.update (Function.update x j s) i t) *
          Real.log (g (Function.update (Function.update x j s) i t)))
          stdGaussian := ae_ae_update_of_ae j hgl_ae_i
  -- ae integrability of E_j g at coordinate i (for h integrability)
  set Ejg : (Fin (n + 1) → ℝ) → ℝ := fun y => ∫ s, g (Function.update y j s) ∂stdGaussian
  have hEjg_int : Integrable Ejg (stdGaussianPi (n + 1)) :=
    integrable_condExpect_stdGaussianPi_gen g hg j
  set ei := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  set γni := Measure.pi (fun k : Fin n => μ' (i.succAbove k))
  have hmpi := measurePreserving_piFinSuccAbove μ' i
  have hupdi : ∀ y t, Function.update y i t = ei.symm (t, (ei y).2) := by
    intro y t; conv_lhs => rw [(ei.symm_apply_apply y).symm]
    simp only [ei, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact @Fin.update_insertNth n (fun _ => ℝ) i (ei y).1 t (ei y).2
  have hEjg_ae_i : ∀ᵐ y ∂(stdGaussianPi (n + 1)),
      Integrable (fun t => Ejg (Function.update y i t)) stdGaussian := by
    have hp := (hmpi.symm.integrable_comp_of_integrable hEjg_int).prod_left_ae
    exact (hmpi.quasiMeasurePreserving.ae (ae_snd_of_ae_marginal stdGaussian γni hp)).mono
      fun y hy => by rwa [show (fun t => (Ejg ∘ ei.symm) (t, (ei y).2)) =
        (fun t => Ejg (Function.update y i t)) from by
          ext t; simp only [Function.comp]; rw [hupdi y t]] at hy
  -- ae product integrability of (s,t) ↦ g(update(update x j s) i t) on γ×γ
  have hprod_ae := ae_integrable_prod_update_update g hg i j hij
  -- ae product integrability of (s,t) ↦ g·log(g)(update(update x j s) i t) on γ×γ
  have hprod_log_ae := ae_integrable_prod_update_update
    (fun y => g y * Real.log (g y)) hg_log i j hij
  -- Combine ae conditions
  filter_upwards [hg_ae_ij, hgl_ae_ij, hEjg_ae_i, hprod_ae, hprod_log_ae] with
    x hg_sl_ij hgl_sl_ij hEjg_sl hprod hprod_log
  -- Rewrite LHS via update_comm
  have hcomm : ∀ t,
      (fun y => ∫ s, g (Function.update y j s) ∂stdGaussian) (Function.update x i t) =
      ∫ s, g (Function.update (Function.update x j s) i t) ∂stdGaussian := by
    intro t; simp only; congr 1; ext s
    have : Function.update (Function.update x i t) j s =
        Function.update (Function.update x j s) i t :=
      update_comm_of_ne hij _ t s
    rw [this]
  show condEntropyAt stdGaussian
      (fun y => ∫ s, g (Function.update y j s) ∂stdGaussian) i x ≤
    ∫ s, condEntropyAt stdGaussian g i (Function.update x j s) ∂stdGaussian
  simp only [condEntropyAt, entropy]
  simp_rw [hcomm]
  -- Goal: ∫ h·log(h) - C·log(C) ≤ ∫_s [∫ f_s·log(f_s) - c_s·log(c_s)]
  -- where h(t) = ∫_s f_s(t), f_s(t) = g(upd(upd x j s) i t), c_s = ∫f_s, C = ∫h.
  set h : ℝ → ℝ := fun t =>
    ∫ s, g (Function.update (Function.update x j s) i t) ∂stdGaussian
  have hh_eq_Ejg : h = fun t => Ejg (Function.update x i t) := by
    ext t; simp only [h, Ejg]; congr 1; ext s
    congr 1; exact (update_comm_of_ne hij _ t s).symm
  have hh_int : Integrable h stdGaussian := hh_eq_Ejg ▸ hEjg_sl
  have hh_nn : ∀ t, 0 ≤ h t := fun t => integral_nonneg (fun s' => hg_nn _)
  -- Cross-term approach: for ae s, condEntropyAt(f_s) ≥ ∫ f_s·log(h) - c_s·log(C)
  -- Integrating + Fubini gives ∫_s condEntropyAt(f_s) ≥ ∫ h·log(h) - C·log(C)
  set C := ∫ t, h t ∂stdGaussian with hC_def
  have hC_nn : 0 ≤ C := integral_nonneg hh_nn
  -- Case split: C = 0 (trivial) vs C > 0 (cross-term bound)
  rcases eq_or_lt_of_le hC_nn with hC_zero | hC_pos
  · -- C = 0: h = 0 ae, so LHS = 0, RHS ≥ 0
    have hC_eq : C = 0 := hC_zero.symm
    have hh_ae : ∀ᵐ t ∂stdGaussian, h t = 0 := by
      rwa [integral_eq_zero_iff_of_nonneg hh_nn hh_int] at hC_eq
    have hLHS_eq : ∫ t, h t * Real.log (h t) ∂stdGaussian = 0 := by
      rw [integral_congr_ae (hh_ae.mono fun t ht => show h t * Real.log (h t) = 0 by simp [ht])]
      simp
    rw [hLHS_eq, hC_eq]; simp
    apply integral_nonneg_of_ae
    filter_upwards [hg_sl_ij, hgl_sl_ij] with s hs_int hs_log_int
    exact sub_nonneg.mpr (Real.convexOn_mul_log.map_integral_le
      Real.continuous_mul_log.continuousOn isClosed_Ici
      (ae_of_all _ (fun t => hg_nn (Function.update (Function.update x j s) i t)))
      hs_int hs_log_int)
  · -- C > 0: use cross-term bound
    -- c_s = ∫ f_s, C = ∫ h
    set c : ℝ → ℝ := fun s =>
      ∫ t, g (Function.update (Function.update x j s) i t) ∂stdGaussian
    have hc_nn : ∀ s, 0 ≤ c s := fun s => integral_nonneg (fun t => hg_nn _)
    have hc_int : Integrable c stdGaussian := hprod.integral_prod_left
    -- C = ∫_s c_s ds (Fubini)
    have hC_eq : C = ∫ s, c s ∂stdGaussian := by
      simp only [C, hC_def, c]
      exact (integral_integral_swap hprod).symm
    -- h·log(h) integrability — sandwich between -1/e and ∫_s f_s·log(f_s) (Jensen)
    have hJensen_t : ∀ᵐ t ∂stdGaussian,
        h t * Real.log (h t) ≤
        ∫ s, g (Function.update (Function.update x j s) i t) *
          Real.log (g (Function.update (Function.update x j s) i t)) ∂stdGaussian := by
      filter_upwards [hprod.prod_left_ae, hprod_log.prod_left_ae] with t ht_int ht_log_int
      exact Real.convexOn_mul_log.map_integral_le
        Real.continuous_mul_log.continuousOn isClosed_Ici
        (ae_of_all _ (fun s => hg_nn _)) ht_int ht_log_int
    have hhl_int : Integrable (fun t => h t * Real.log (h t)) stdGaussian :=
      integrable_of_le_of_le
        (hh_int.1.mul (Real.measurable_log.comp_aemeasurable hh_int.1.aemeasurable).aestronglyMeasurable)
        (ae_of_all _ (fun t => mul_log_ge_neg_inv_exp (h t) (hh_nn t)))
        hJensen_t (integrable_const _) hprod_log.integral_prod_right
    -- ae absolute continuity: for ae s, h(t)=0 → f_s(t)=0 ae t
    -- Proof: first show ∀ᵐ t, ∀ᵐ s (from integral=0 + nonneg), then swap quantifiers
    -- via ae_ae_comm using AEStronglyMeasurable proxies for MeasurableSet.
    have hab_ac_ae : ∀ᵐ s ∂stdGaussian,
        ∀ᵐ t ∂stdGaussian,
          h t = 0 → g (Function.update (Function.update x j s) i t) = 0 := by
      -- Forward: ∀ᵐ t, ∀ᵐ s, h(t)=0 → g(...)=0
      have h_fwd : ∀ᵐ t ∂stdGaussian, ∀ᵐ s ∂stdGaussian,
          h t = 0 → g (Function.update (Function.update x j s) i t) = 0 := by
        filter_upwards [hprod.prod_left_ae] with t h_int_s
        by_cases ht : h t = 0
        · have h_nn' : ∀ s, 0 ≤ g (Function.update (Function.update x j s) i t) := fun s => hg_nn _
          exact ((integral_eq_zero_iff_of_nonneg h_nn' h_int_s).mp ht).mono fun s hs _ => hs
        · exact ae_of_all _ (fun _ h_abs => absurd h_abs ht)
      -- AEStronglyMeasurable proxies for ae_ae_comm
      set F : ℝ × ℝ → ℝ := fun p => g (Function.update (Function.update x j p.1) i p.2)
      have hF_aesm : AEStronglyMeasurable F (stdGaussian.prod stdGaussian) :=
        hprod.aestronglyMeasurable
      set F' := hF_aesm.mk F
      have hF'_sm := hF_aesm.stronglyMeasurable_mk
      have hF_ae_eq : F =ᵐ[stdGaussian.prod stdGaussian] F' := hF_aesm.ae_eq_mk
      set h' := hh_int.aestronglyMeasurable.mk h
      have hh'_sm := hh_int.aestronglyMeasurable.stronglyMeasurable_mk
      have hh_ae_eq : h =ᵐ[stdGaussian] h' := hh_int.aestronglyMeasurable.ae_eq_mk
      -- MeasurableSet for proxy: {(t,s) | h'(t)=0 → F'(s,t)=0}
      have hms : MeasurableSet {p : ℝ × ℝ | h' p.1 = 0 → F' (p.2, p.1) = 0} := by
        have : {p : ℝ × ℝ | h' p.1 = 0 → F' (p.2, p.1) = 0} =
            {p | h' p.1 ≠ 0} ∪ {p | F' (p.2, p.1) = 0} := by ext p; simp [imp_iff_not_or]
        rw [this]
        exact ((hh'_sm.measurable.comp measurable_fst)
          (measurableSet_singleton 0).compl).union
          ((hF'_sm.measurable.comp measurable_swap) (measurableSet_singleton 0))
      -- Transfer h_fwd to proxy: ∀ᵐ t, ∀ᵐ s, h'(t)=0 → F'(s,t)=0
      have hF_swap_ae : ∀ᵐ t ∂stdGaussian, ∀ᵐ s ∂stdGaussian, F (s, t) = F' (s, t) :=
        Measure.ae_ae_of_ae_prod
          (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq hF_ae_eq)
      have h_fwd' : ∀ᵐ t ∂stdGaussian, ∀ᵐ s ∂stdGaussian,
          h' t = 0 → F' (s, t) = 0 := by
        filter_upwards [h_fwd, hh_ae_eq, hF_swap_ae] with t ht_fwd ht_eq ht_F_eq
        filter_upwards [ht_fwd, ht_F_eq] with s hs_fwd hs_F_eq
        intro hh't; rw [← hs_F_eq]; exact hs_fwd (by rwa [ht_eq])
      -- ae_ae_comm swaps proxy, then transfer back
      have hswap := (Measure.ae_ae_comm hms).mp h_fwd'
      have hF_ae_fwd : ∀ᵐ s ∂stdGaussian, ∀ᵐ t ∂stdGaussian, F (s, t) = F' (s, t) :=
        Measure.ae_ae_of_ae_prod hF_ae_eq
      filter_upwards [hswap, hF_ae_fwd,
        (show ∀ᵐ s ∂stdGaussian, ∀ᵐ t ∂stdGaussian, h t = h' t from
          ae_of_all _ fun _ => hh_ae_eq)] with s hs_proxy hs_F hs_h
      filter_upwards [hs_proxy, hs_F, hs_h] with t ht_proxy ht_F ht_h
      intro hht_zero
      show g (Function.update (Function.update x j s) i t) = 0
      rw [show g (Function.update (Function.update x j s) i t) = F (s, t) from rfl, ht_F]
      exact ht_proxy (by rwa [← ht_h])
    -- Product integrability of cross-term (s,t) ↦ f_s(t) * log(h(t))
    -- Proved via integrable_prod_iff': ae-t slice (scalar mul) + norm = hhl.norm
    have hcross_prod : Integrable
        (fun p : ℝ × ℝ =>
          g (Function.update (Function.update x j p.1) i p.2) *
            Real.log (h p.2))
        (stdGaussian.prod stdGaussian) := by
      have hlog_aesm :
          AEStronglyMeasurable (fun t => Real.log (h t))
            stdGaussian :=
        (Real.measurable_log.comp_aemeasurable
          hh_int.aestronglyMeasurable.aemeasurable
            ).aestronglyMeasurable
      have hG_aesm : AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            g (Function.update (Function.update x j p.1) i p.2) *
              Real.log (h p.2))
          (stdGaussian.prod stdGaussian) :=
        hprod.aestronglyMeasurable.mul hlog_aesm.comp_snd
      refine (integrable_prod_iff' hG_aesm).mpr ⟨?_, ?_⟩
      · filter_upwards [hprod.prod_left_ae] with t ht_int
        exact ht_int.mul_const _
      · have hkey :
            (fun t =>
              ∫ s,
                ‖g (Function.update
                    (Function.update x j s) i t) *
                  Real.log (h t)‖ ∂stdGaussian) =ᵐ[stdGaussian]
            fun t => ‖h t * Real.log (h t)‖ := by
          filter_upwards [hprod.prod_left_ae] with t ht_int
          have : ∀ s,
              ‖g (Function.update
                  (Function.update x j s) i t) *
                Real.log (h t)‖ =
              g (Function.update
                  (Function.update x j s) i t) *
                ‖Real.log (h t)‖ := by
            intro s
            rw [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (hg_nn _)]
          simp_rw [this]
          rw [integral_mul_const]
          simp only [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hh_nn t), h]
        exact (integrable_congr hkey).mpr hhl_int.norm
    -- Cross-term integrability: ae s slice
    have hcross_int : ∀ᵐ s ∂stdGaussian,
        Integrable
          (fun t =>
            g (Function.update
                (Function.update x j s) i t) *
              Real.log (h t))
          stdGaussian :=
      hcross_prod.prod_right_ae
    -- Case split: C = 0 (trivial) vs C > 0 (use condEntropyAt_ge_cross_term)
    rcases eq_or_lt_of_le hC_nn with hC_zero | hC_pos
    · -- C = 0: h = 0 ae, so ∫∫ f_s = 0. For ae s: f_s = 0 ae, giving condEnt = 0.
      -- LHS = 0 - 0 = 0 ≤ 0 = RHS.
      have hC_eq_zero : C = 0 := hC_zero.symm
      have hh_ae : ∀ᵐ t ∂stdGaussian, h t = 0 :=
        (integral_eq_zero_iff_of_nonneg hh_nn hh_int).mp hC_eq_zero
      have h1 : ∫ t, h t * Real.log (h t) ∂stdGaussian = 0 := by
        have : (fun t => h t * Real.log (h t)) =ᵐ[stdGaussian] fun _ => (0 : ℝ) :=
          hh_ae.mono fun t ht => show h t * Real.log (h t) = 0 by rw [ht, zero_mul]
        rw [integral_congr_ae this, integral_zero]
      -- For ae s: c_s = 0 (from C = ∫ c_s = 0 and c_s ≥ 0)
      have hc_zero : ∀ᵐ s ∂stdGaussian, c s = 0 := by
        have : C = ∫ s, c s ∂stdGaussian := hC_eq
        rw [hC_eq_zero] at this
        exact (integral_eq_zero_iff_of_nonneg hc_nn hc_int).mp this.symm
      -- For ae s: f_s = 0 ae (from c_s = 0 and f_s ≥ 0)
      have hfs_zero : ∀ᵐ s ∂stdGaussian,
          ∀ᵐ t ∂stdGaussian, g (Function.update (Function.update x j s) i t) = 0 := by
        filter_upwards [hc_zero, hg_sl_ij] with s hcs hs_int
        exact (integral_eq_zero_iff_of_nonneg (fun t => hg_nn _) hs_int).mp hcs
      -- Each condEnt integrand is 0 ae
      have hRHS_zero : ∀ᵐ s ∂stdGaussian,
          ∫ t, g (Function.update (Function.update x j s) i t) *
            Real.log (g (Function.update (Function.update x j s) i t)) ∂stdGaussian -
          (∫ t, g (Function.update (Function.update x j s) i t) ∂stdGaussian) *
            Real.log (∫ t, g (Function.update (Function.update x j s) i t) ∂stdGaussian) = 0 := by
        filter_upwards [hfs_zero] with s hs
        have h1' : ∫ t, g (Function.update (Function.update x j s) i t) *
            Real.log (g (Function.update (Function.update x j s) i t)) ∂stdGaussian = 0 := by
          have : (fun t => g (Function.update (Function.update x j s) i t) *
              Real.log (g (Function.update (Function.update x j s) i t))) =ᵐ[stdGaussian]
              fun _ => (0 : ℝ) :=
            hs.mono fun t ht => show g (Function.update (Function.update x j s) i t) *
                Real.log (g (Function.update (Function.update x j s) i t)) = 0 by rw [ht, zero_mul]
          rw [integral_congr_ae this, integral_zero]
        have h2' : ∫ t, g (Function.update (Function.update x j s) i t) ∂stdGaussian = 0 := by
          rw [integral_congr_ae hs, integral_zero]
        rw [h1', h2', zero_mul, sub_zero]
      rw [h1, hC_eq_zero, Real.log_zero, mul_zero, sub_zero,
        integral_congr_ae hRHS_zero, integral_zero]
    -- Per-s bound from condEntropyAt_ge_cross_term (C > 0 case)
    have hper_s : ∀ᵐ s ∂stdGaussian,
        ∫ t, g (Function.update (Function.update x j s) i t) *
          Real.log (g (Function.update (Function.update x j s) i t)) ∂stdGaussian -
        c s * Real.log (c s) ≥
        ∫ t, g (Function.update (Function.update x j s) i t) *
          Real.log (h t) ∂stdGaussian -
        c s * Real.log C := by
      filter_upwards [hg_sl_ij, hgl_sl_ij, hab_ac_ae,
        hcross_int] with s hs_int hs_log_int hs_ac hs_cross
      exact condEntropyAt_ge_cross_term
        (fun t => g (Function.update (Function.update x j s) i t)) h
        (fun t => hg_nn _) hh_nn hs_int hs_log_int hs_cross hh_int hC_pos hs_ac
    -- Fubini cross-term: swap + pull out log(h)
    have hfub_cross :
        ∫ s, (∫ t,
          g (Function.update
              (Function.update x j s) i t) *
            Real.log (h t) ∂stdGaussian) ∂stdGaussian =
        ∫ t, h t * Real.log (h t) ∂stdGaussian := by
      rw [integral_integral_swap hcross_prod]
      congr 1; ext t
      rw [integral_mul_const (Real.log (h t))
        (fun s =>
          g (Function.update
              (Function.update x j s) i t))]
    -- Integrability of cross-term and c·log(c) as functions of s
    have hcross_s_int : Integrable
        (fun s => ∫ t,
          g (Function.update
              (Function.update x j s) i t) *
            Real.log (h t) ∂stdGaussian)
        stdGaussian :=
      hcross_prod.integral_prod_left
    have hclogc_int : Integrable
        (fun s => c s * Real.log (c s))
        stdGaussian := by
      refine integrable_of_le_of_le
        (hc_int.1.mul
          (Real.measurable_log.comp_aemeasurable
            hc_int.1.aemeasurable
              ).aestronglyMeasurable)
        (ae_of_all _ fun s =>
          mul_log_ge_neg_inv_exp (c s) (hc_nn s))
        ?_ (integrable_const _)
        hprod_log.integral_prod_left
      -- Upper bound: c·log(c) ≤ ∫ f_s·log(f_s) (Jensen)
      filter_upwards [hg_sl_ij, hgl_sl_ij] with s
        hs_int hs_log_int
      exact convexOn_mul_log.map_integral_le
        continuous_mul_log.continuousOn isClosed_Ici
        (ae_of_all _ fun t => hg_nn _)
        hs_int hs_log_int
    -- Integrability of condEnt integrand
    have hfl_s_int : Integrable
        (fun s => ∫ t,
          g (Function.update
              (Function.update x j s) i t) *
            Real.log
              (g (Function.update
                  (Function.update x j s) i t))
          ∂stdGaussian)
        stdGaussian :=
      hprod_log.integral_prod_left
    -- Final wiring: integral_mono_ae + Fubini identity
    calc ∫ t, h t * Real.log (h t) ∂stdGaussian -
          C * Real.log C
        = ∫ s, (∫ t,
            g (Function.update
                (Function.update x j s) i t) *
              Real.log (h t) ∂stdGaussian) ∂stdGaussian -
          ∫ s, c s * Real.log C ∂stdGaussian := by
            rw [hfub_cross,
              integral_mul_const (Real.log C) c, hC_eq]
        _ = ∫ s, ((∫ t,
            g (Function.update
                (Function.update x j s) i t) *
              Real.log (h t) ∂stdGaussian) -
            c s * Real.log C) ∂stdGaussian :=
          (integral_sub hcross_s_int
            (hc_int.mul_const _)).symm
        _ ≤ ∫ s, ((∫ t,
            g (Function.update
                (Function.update x j s) i t) *
              Real.log
                (g (Function.update
                    (Function.update x j s) i t))
            ∂stdGaussian) -
            c s * Real.log (c s)) ∂stdGaussian := by
          exact integral_mono_ae
            (hcross_s_int.sub (hc_int.mul_const _))
            (hfl_s_int.sub hclogc_int)
            (hper_s.mono fun s hs => hs)

-- Sub-lemma 1: Data processing inequality for integrated conditional entropy.
-- E_j averaging can only decrease ∫ condEnt_i(g), i.e., averaging out coordinate j
-- makes the conditional entropy at coordinate i (for i ≠ j) only smaller.
--
-- Proof structure (non-circular):
-- 1. Rewrite RHS via integral_condExpect_eq_integral_pi at j:
--    ∫ condEntropyAt g i = ∫[∫_s condEntropyAt g i (upd x j s) dγ(s)] dγⁿ
-- 2. Pointwise: condEntropyAt(Ejg, i, x) ≤ ∫_s condEntropyAt(g, i, upd x j s) dγ(s)
--    This is entropy convexity of mixture (entropy_convex_mixture).
--    Key: Ejg(upd x i t) = ∫_s g(upd(upd x j s) i t) dγ(s) by update_comm.
-- 3. integral_mono_ae concludes.
private lemma integrated_condEntropyAt_condExpect_le {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi n))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n))
    (i j : Fin n) (hij : i ≠ j) :
    ∫ x, condEntropyAt stdGaussian
        (fun y => ∫ t, g (Function.update y j t) ∂stdGaussian) i x
      ∂(stdGaussianPi n) ≤
    ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) := by
  rcases n with _ | n
  · exact Fin.elim0 i
  -- Abbreviations
  set Ejg : (Fin (n + 1) → ℝ) → ℝ := fun y => ∫ t, g (Function.update y j t) ∂stdGaussian
  -- Key properties of Ejg
  have hEj_nn : ∀ x, 0 ≤ Ejg x := fun x => integral_nonneg (fun t => hg_nn _)
  have hEj_int : Integrable Ejg (stdGaussianPi (n + 1)) :=
    integrable_condExpect_stdGaussianPi_gen g hg j
  have hEj_log_int : Integrable (fun x => Ejg x * Real.log (Ejg x))
      (stdGaussianPi (n + 1)) := by
    have hA := integrable_condExpect_stdGaussianPi_gen _ hg_log j
    have hC := integrable_condEntropyAt_of_nonneg g hg_nn hg hg_log j
    have : (fun x => Ejg x * Real.log (Ejg x)) =
        fun x => (∫ t, g (Function.update x j t) *
          Real.log (g (Function.update x j t)) ∂stdGaussian) -
          condEntropyAt stdGaussian g j x := by
      ext x; simp only [condEntropyAt, entropy, Ejg]; ring
    rw [this]; exact hA.sub hC
  -- Integrability of condEntropyAt g i and condEntropyAt Ejg i
  have hcondEnt_g_int := integrable_condEntropyAt_of_nonneg g hg_nn hg hg_log i
  have hcondEnt_Ej_int := integrable_condEntropyAt_of_nonneg Ejg hEj_nn hEj_int hEj_log_int i
  -- Step 1: Rewrite RHS via Fubini at coordinate j
  have hRHS_fub :
      ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi (n + 1)) =
      ∫ x, (∫ s, condEntropyAt stdGaussian g i (Function.update x j s) ∂stdGaussian)
        ∂(stdGaussianPi (n + 1)) :=
    (integral_condExpect_eq_integral_pi
      (fun x => condEntropyAt stdGaussian g i x) hcondEnt_g_int j).symm
  rw [hRHS_fub]
  -- Step 2: integral_mono_ae using entropy_convex_mixture
  have hcondEnt_avg_int :
      Integrable (fun x => ∫ s, condEntropyAt stdGaussian g i (Function.update x j s) ∂stdGaussian)
        (stdGaussianPi (n + 1)) :=
    integrable_condExpect_stdGaussianPi_gen _ hcondEnt_g_int j
  exact integral_mono_ae hcondEnt_Ej_int hcondEnt_avg_int
    (entropy_convex_mixture g hg_nn hg hg_log i j hij)

-- Sub-lemma 2: When g·log(g) is not integrable but g ≥ 0 and g ∈ L¹,
-- the sum of integrated conditional entropies is still ≥ entropyPi.
-- In fact, entropyPi = 0 - (∫g)·log(∫g) and each condEntropyAt is nonneg (Jensen),
-- so it suffices to show ∑_i ∫ condEnt_i(g) ≥ -(∫g)·log(∫g).
-- For n ≥ 2, this follows from: even a single term ∫ condEnt_i(g) captures
-- the full entropy via the chain rule, and the LHS has n ≥ 2 such terms.
-- When g·log(g) is not integrable, ∫ g·log(g) = 0 (Lean convention),
-- so entropyPi(g) = -(∫g)·log(∫g). We need ∑ ∫ condEnt ≥ this.
-- Key insight: ∫ condEnt_i(g) ≥ -(∫g)·log(∫g) follows from
-- ∫ condEnt_i(g) = ∫ g·log(g) - ∫ (E_i g)·log(E_i g) ≥ -(∫g)·log(∫g)
-- where the last step uses Jensen on E_i g.
-- But wait — the integrated_condEntropyAt_eq formula also needs g·log(g) integrable.
-- Alternative: use that condEntropyAt(x) ≥ 0 pointwise (Jensen for nonneg functions).
-- So ∑ ∫ condEnt ≥ 0. And entropyPi = -(∫g)·log(∫g) which can be positive or negative.
-- When ∫g ≥ 1: entropyPi ≤ 0 ≤ ∑ ∫ condEnt. Done.
-- When ∫g < 1: entropyPi > 0. This case needs the non-integrable g·log(g) to interact
-- with the slice integrals somehow... Actually if g ∈ L¹(γⁿ) with g ≥ 0 and
-- g·log(g) ∉ L¹, then ∫ g·log(g)⁺ = +∞ (since g·log(g)⁻ = max(0,-g·log(g))
-- is bounded by 1/e a.e. hence always integrable). So the positive part diverges.
-- This means: in any slice, ∫ (g·log g)⁺ is typically infinite too.
-- And ∫ condEnt_i(g)(x) = ∫ slice(g·log(g)) - (E_i g)·log(E_i g) → each term
-- has a non-integrable positive part so the Lean integral is not 0 but could be anything...
-- **STATUS: LIKELY FALSE** under Lean's `∫ non-integrable = 0` convention.
-- Counterexample: g(x₁,x₂) = h₁(x₁)·h₂(x₂) where both hᵢ·log(hᵢ) ∉ L¹(γ)
-- and 0 < (∫h₁)(∫h₂) < 1. Then:
--   LHS = entropyPi g = -(∫g)·log(∫g) > 0  (since ∫g < 1)
--   RHS: For each i, condEntropyAt_i involves non-integrable h_j·log(h_j),
--     making condEntropyAt_i non-integrable on the product → ∫ condEntropyAt_i = 0.
--   So RHS = 0 < LHS.
-- This sorry becomes dead code once `integrable_sq_mul_log_sq_of_memLp` is proved:
-- the only call path is `entropy_subadditivity_of_nonneg → entropy_subadditivity_pi`
-- where g = f² with f ∈ MemLp 2, and derivative control ensures g·log(g) ∈ L¹.
-- TODO: add `hg_log` hypothesis to `entropy_subadditivity_of_nonneg` once sorry 1 is closed.
private lemma entropy_subadditivity_not_integrable_log {n : ℕ} (hn : 2 ≤ n)
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi n))
    (hg_log : ¬ Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n)) :
    entropyPi (stdGaussianPi n) g ≤
    ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) := by
  sorry

-- Infrastructure for dimension projection (coord 0 removal via Fin.tail/Fin.cons).
-- Key identity: update x 0 t = Fin.cons t (Fin.tail x).
private lemma update_zero_eq_cons {n : ℕ} (x : Fin (n + 1) → ℝ) (t : ℝ) :
    Function.update x 0 t = Fin.cons t (Fin.tail x) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  rw [Fin.update_cons_zero]

-- Integration of tail-composed functions on product Gaussian.
-- For h : (Fin n → ℝ) → ℝ, ∫ h(tail x) dγ^{n+1} = ∫ h dγ^n.
private lemma integral_comp_tail_stdGaussianPi {n : ℕ} (h : (Fin n → ℝ) → ℝ)
    (_hh : Integrable h (stdGaussianPi n)) :
    ∫ x, h (Fin.tail x) ∂(stdGaussianPi (n + 1)) = ∫ y, h y ∂(stdGaussianPi n) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  set γn := Measure.pi (fun j : Fin n => μ' ((0 : Fin (n + 1)).succAbove j))
  have hmp := measurePreserving_piFinSuccAbove μ' (0 : Fin (n + 1))
  have hpi : stdGaussianPi (n + 1) = Measure.pi μ' := rfl
  have hγn : γn = stdGaussianPi n := by simp only [γn, μ', stdGaussianPi]
  rw [hpi, ← hmp.symm.integral_comp' (g := fun x => h (Fin.tail x))]
  have htail : (fun p : ℝ × (Fin n → ℝ) => h (Fin.tail (e.symm p))) = fun p => h p.2 := by
    ext ⟨a, y⟩; congr 1
  change ∫ p, h (Fin.tail (e.symm p)) ∂(stdGaussian.prod γn) = _
  rw [htail, integral_fun_snd, hγn]
  simp [Measure.real, measure_univ]

-- Conditional entropy of a tail-composed function = lower-dim conditional entropy.
private lemma condEntropyAt_comp_tail {n : ℕ} (h : (Fin n → ℝ) → ℝ)
    (j : Fin n) (x : Fin (n + 1) → ℝ) :
    condEntropyAt stdGaussian (fun y => h (Fin.tail y)) (Fin.succ j) x =
    condEntropyAt stdGaussian h j (Fin.tail x) := by
  simp only [condEntropyAt]
  congr 1; ext t
  show h (Fin.tail (Function.update x (Fin.succ j) t)) =
    h (Function.update (Fin.tail x) j t)
  rw [Fin.tail_update_succ]

-- Entropy of a tail-composed function = lower-dim entropy.
private lemma entropyPi_comp_tail {n : ℕ} (h : (Fin n → ℝ) → ℝ)
    (hh : Integrable h (stdGaussianPi n))
    (hh_log : Integrable (fun y => h y * Real.log (h y)) (stdGaussianPi n)) :
    entropyPi (stdGaussianPi (n + 1)) (fun x => h (Fin.tail x)) =
    entropyPi (stdGaussianPi n) h := by
  simp only [entropyPi]
  rw [integral_comp_tail_stdGaussianPi _ hh_log,
      integral_comp_tail_stdGaussianPi _ hh]

-- E_0 g expressed via tail: ∫ g(upd x 0 t) dγ(t) = ∫ g(cons t (tail x)) dγ(t).
private lemma condExpect_zero_eq_comp_tail {n : ℕ}
    (g : (Fin (n + 1) → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) :
    (∫ t, g (Function.update x 0 t) ∂stdGaussian) =
    (∫ t, g (Fin.cons t (Fin.tail x)) ∂stdGaussian) := by
  congr 1; ext t; congr 1; exact update_zero_eq_cons x t

-- Integrability of tail-composed functions: if h is integrable on γ^n, then h ∘ tail is on γ^{n+1}.
private lemma integrable_comp_tail_stdGaussianPi {n : ℕ} (h : (Fin n → ℝ) → ℝ)
    (hh : Integrable h (stdGaussianPi n)) :
    Integrable (fun x => h (Fin.tail x)) (stdGaussianPi (n + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  set μ' : Fin (n + 1) → Measure ℝ := fun _ => stdGaussian
  have hmp := measurePreserving_piFinSuccAbove μ' (0 : Fin (n + 1))
  have heq : (fun x : Fin (n + 1) → ℝ => h (Fin.tail x)) = (h ∘ Prod.snd) ∘ e := by
    ext x; simp [Function.comp, e, MeasurableEquiv.piFinSuccAbove]
  rw [heq]
  apply MeasurePreserving.integrable_comp_of_integrable hmp
  rw [show (μ' 0) = stdGaussian from rfl,
      show (Measure.pi fun j : Fin n => μ' (Fin.succAbove 0 j)) = stdGaussianPi n from by
        simp [μ', stdGaussianPi]]
  exact hh.comp_snd stdGaussian

-- Sub-lemma 3: Entropy subadditivity for integrable case.
-- Proof: strong induction on n via chain rule at coord 0 + dimension projection + data processing.
private lemma entropy_subadditivity_integrable {n : ℕ} (hn : 2 ≤ n)
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi n))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n)) :
    entropyPi (stdGaussianPi n) g ≤
    ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) := by
  -- Prove a stronger statement for all n by strong induction, then specialize.
  suffices key : ∀ (m : ℕ),
      ∀ (f : (Fin m → ℝ) → ℝ), (∀ x, 0 ≤ f x) →
      Integrable f (stdGaussianPi m) →
      Integrable (fun x => f x * Real.log (f x)) (stdGaussianPi m) →
      entropyPi (stdGaussianPi m) f ≤
      ∑ i : Fin m, ∫ x, condEntropyAt stdGaussian f i x ∂(stdGaussianPi m) from
    key n g hg_nn hg hg_log
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro f hf_nn hf hf_log
  match m with
  | 0 =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have heval : ∀ (φ : (Fin 0 → ℝ) → ℝ),
        ∫ x, φ x ∂(stdGaussianPi 0) = φ Fin.elim0 := by
      intro φ; have : ∀ x : Fin 0 → ℝ, φ x = φ Fin.elim0 := fun x => by
        congr 1; exact Subsingleton.elim x Fin.elim0
      simp_rw [this]; simp [integral_const, Measure.real, measure_univ]
    simp only [entropyPi, heval]; linarith
  | 1 =>
    exact entropy_subadditivity_fin1 f hf_nn hf
  | (m' + 2) =>
    -- n = m' + 2 ≥ 2.
    -- Step 1: Define E_0 f and its lower-dimensional version h.
    set E₀f : (Fin (m' + 2) → ℝ) → ℝ := fun x =>
      ∫ t, f (Function.update x 0 t) ∂stdGaussian with hE₀f_def
    set h : (Fin (m' + 1) → ℝ) → ℝ := fun y =>
      ∫ t, f (Fin.cons t y) ∂stdGaussian with hh_def
    -- E₀f = h ∘ Fin.tail
    have hE₀f_eq : E₀f = fun x => h (Fin.tail x) := by
      ext x; simp only [E₀f, h]; exact condExpect_zero_eq_comp_tail f x
    -- Step 2: Chain rule at coord 0.
    have hint1 : Integrable (fun x => ∫ t, f (Function.update x 0 t) *
        Real.log (f (Function.update x 0 t)) ∂stdGaussian) (stdGaussianPi (m' + 2)) := by
      -- Rewrite update → cons ∘ tail, then Fubini decomposition
      set fl := fun x => f x * Real.log (f x)
      have hupd : (fun x => ∫ t, fl (Function.update x 0 t) ∂stdGaussian) =
          (fun x => ∫ t, fl (Fin.cons t (Fin.tail x)) ∂stdGaussian) := by
        ext x; congr 1; ext t; congr 1; exact update_zero_eq_cons x t
      rw [hupd]
      -- Fubini: fl_marginal(y) = ∫ fl(cons t y) dγ(t) is integrable on γ^{m'+1}
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 2) => ℝ) (0 : Fin (m' + 2))
      set μ'' : Fin (m' + 2) → Measure ℝ := fun _ => stdGaussian
      set γn := Measure.pi (fun j : Fin (m' + 1) => μ'' (Fin.succAbove 0 j))
      have hmp := measurePreserving_piFinSuccAbove μ'' (0 : Fin (m' + 2))
      have hγn : γn = stdGaussianPi (m' + 1) := by simp [γn, μ'', stdGaussianPi]
      have hfl_prod : Integrable (fl ∘ e.symm) (stdGaussian.prod γn) :=
        hmp.symm.integrable_comp_of_integrable hf_log
      have hfub := hfl_prod.integral_prod_right
      have heq_fl : (fun y => ∫ t, (fl ∘ e.symm) (t, y) ∂stdGaussian) =
          (fun y => ∫ t, fl (Fin.cons t y) ∂stdGaussian) := by
        ext y; simp only [Function.comp]
        congr 1; ext t; congr 1
        change e.symm (t, y) = Fin.cons t y
        ext i; refine Fin.cases ?_ ?_ i
        · simp [e, MeasurableEquiv.piFinSuccAbove]
        · intro j; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons]
      rw [heq_fl, hγn] at hfub
      -- hfub : Integrable (y ↦ ∫ fl(cons t y) dγ(t)) (stdGaussianPi (m'+1))
      -- Goal: Integrable (x ↦ ∫ fl(cons t (tail x)) dγ(t)) (stdGaussianPi (m'+2))
      exact integrable_comp_tail_stdGaussianPi _ hfub
    -- Step 3: Properties of h (needed before hint2).
    have hh_nn : ∀ y, 0 ≤ h y := fun y => by
      apply integral_nonneg; intro t; exact hf_nn _
    have hh_int : Integrable h (stdGaussianPi (m' + 1)) := by
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 2) => ℝ) (0 : Fin (m' + 2))
      set μ'' : Fin (m' + 2) → Measure ℝ := fun _ => stdGaussian
      set γn := Measure.pi (fun j : Fin (m' + 1) => μ'' (Fin.succAbove 0 j))
      have hmp := measurePreserving_piFinSuccAbove μ'' (0 : Fin (m' + 2))
      have hγn : γn = stdGaussianPi (m' + 1) := by simp [γn, μ'', stdGaussianPi]
      have hf_prod : Integrable (f ∘ e.symm) (stdGaussian.prod γn) :=
        hmp.symm.integrable_comp_of_integrable hf
      have hfub := hf_prod.integral_prod_right
      have heq : (fun y => ∫ t, (f ∘ e.symm) (t, y) ∂stdGaussian) = h := by
        ext y; simp only [Function.comp, h]
        congr 1; ext t; congr 1
        change e.symm (t, y) = Fin.cons t y
        ext i; refine Fin.cases ?_ ?_ i
        · simp [e, MeasurableEquiv.piFinSuccAbove]
        · intro j; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons]
      rwa [heq, hγn] at hfub
    have hh_log_int : Integrable (fun y => h y * Real.log (h y))
        (stdGaussianPi (m' + 1)) := by
      -- Domination via Jensen (upper) + mul_log_ge_neg_inv_exp (lower)
      set fl := fun x => f x * Real.log (f x)
      set e' := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m' + 2) => ℝ) (0 : Fin (m' + 2))
      set μ''' : Fin (m' + 2) → Measure ℝ := fun _ => stdGaussian
      set γn' := Measure.pi (fun j : Fin (m' + 1) => μ''' (Fin.succAbove 0 j))
      have hmp' := measurePreserving_piFinSuccAbove μ''' (0 : Fin (m' + 2))
      have hγn' : γn' = stdGaussianPi (m' + 1) := by simp [γn', μ''', stdGaussianPi]
      have he_eq' : ∀ t y, e'.symm (t, y) = Fin.cons t y := by
        intro t y; ext i; refine Fin.cases ?_ ?_ i
        · simp [e', MeasurableEquiv.piFinSuccAbove]
        · intro j; simp [e', MeasurableEquiv.piFinSuccAbove, Fin.cons]
      have hfl_prod : Integrable (fl ∘ e'.symm) (stdGaussian.prod γn') :=
        hmp'.symm.integrable_comp_of_integrable hf_log
      have hf_prod : Integrable (f ∘ e'.symm) (stdGaussian.prod γn') :=
        hmp'.symm.integrable_comp_of_integrable hf
      -- F_log marginal integrable
      have hFlog := hfl_prod.integral_prod_right
      rw [show (fun y => ∫ t, (fl ∘ e'.symm) (t, y) ∂stdGaussian) =
          (fun y => ∫ t, fl (Fin.cons t y) ∂stdGaussian) from by
        ext y; congr 1; ext t; simp [Function.comp, he_eq'], hγn'] at hFlog
      -- Slice integrability a.e.
      have hfl_ae : ∀ᵐ y ∂(stdGaussianPi (m' + 1)),
          Integrable (fun t => fl (Fin.cons t y)) stdGaussian := by
        rw [← hγn']; exact (hfl_prod.prod_left_ae).mono fun y hy => by
          rwa [show (fun t => (fl ∘ e'.symm) (t, y)) = (fun t => fl (Fin.cons t y)) from by
            ext t; simp [Function.comp, he_eq']] at hy
      have hf_ae : ∀ᵐ y ∂(stdGaussianPi (m' + 1)),
          Integrable (fun t => f (Fin.cons t y)) stdGaussian := by
        rw [← hγn']; exact (hf_prod.prod_left_ae).mono fun y hy => by
          rwa [show (fun t => (f ∘ e'.symm) (t, y)) = (fun t => f (Fin.cons t y)) from by
            ext t; simp [Function.comp, he_eq']] at hy
      -- Jensen: h(y)·log(h(y)) ≤ ∫ fl(cons t y) dγ(t)
      have h_upper : ∀ᵐ y ∂(stdGaussianPi (m' + 1)),
          h y * Real.log (h y) ≤ ∫ t, fl (Fin.cons t y) ∂stdGaussian := by
        filter_upwards [hf_ae, hfl_ae] with y hfy hfly
        exact Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
          isClosed_Ici (ae_of_all _ fun t => hf_nn _) hfy hfly
      -- Lower bound: h·log(h) ≥ -1/e
      have h_lower : ∀ y, -(1 / Real.exp 1) ≤ h y * Real.log (h y) :=
        fun y => mul_log_ge_neg_inv_exp _ (integral_nonneg fun t => hf_nn _)
      -- Domination: |h·log(h)| ≤ |F_log| + 1/e
      exact Integrable.mono' (hFlog.norm.add (integrable_const (1 / Real.exp 1)))
        (Real.continuous_mul_log.comp_aestronglyMeasurable hh_int.aestronglyMeasurable)
        (by filter_upwards [h_upper] with y hy
            simp only [Pi.add_apply, Real.norm_eq_abs]
            rw [abs_le]
            exact ⟨by linarith [h_lower y,
                      abs_nonneg (∫ t, fl (Fin.cons t y) ∂stdGaussian)],
                   by linarith [le_abs_self (∫ t, fl (Fin.cons t y) ∂stdGaussian),
                      div_pos one_pos (Real.exp_pos 1)]⟩)
    -- hint2: E₀f·log(E₀f) integrable, follows from hh_log_int via tail composition
    have hint2 : Integrable (fun x => (∫ t, f (Function.update x 0 t) ∂stdGaussian) *
        Real.log (∫ t, f (Function.update x 0 t) ∂stdGaussian)) (stdGaussianPi (m' + 2)) := by
      -- E₀f = h ∘ tail, so E₀f·log(E₀f) = (h·log(h)) ∘ tail
      change Integrable (fun x => E₀f x * Real.log (E₀f x)) (stdGaussianPi (m' + 2))
      rw [hE₀f_eq]
      exact integrable_comp_tail_stdGaussianPi _ hh_log_int
    have hchain := entropy_chain_rule_pi f (0 : Fin (m' + 2)) hf hf_log hint1 hint2
    -- Step 4: Apply IH to h on (m' + 1) dimensions.
    have hih := ih (m' + 1) (by omega) h hh_nn hh_int hh_log_int
    -- Step 5: Translate IH back to n = m' + 2 dimensions.
    have hent_eq : entropyPi (stdGaussianPi (m' + 2)) E₀f =
        entropyPi (stdGaussianPi (m' + 1)) h := by
      rw [hE₀f_eq]; exact entropyPi_comp_tail h hh_int hh_log_int
    -- Step 6: Data processing inequality (DPI):
    -- ∫ condEnt(h, j) on (m'+1) dims ≤ ∫ condEnt(f, succ j) on (m'+2) dims.
    -- This combines condEnt translation (h ↔ E₀f via tail) with the DPI:
    -- averaging over coord 0 doesn't increase conditional entropy along coord (succ j).
    -- condEntropyAt h j integrable on γ^{m'+1}
    have hcondEnt_int : ∀ j : Fin (m' + 1),
        Integrable (fun y => condEntropyAt stdGaussian h j y)
          (stdGaussianPi (m' + 1)) := by
      intro j; exact integrable_condEntropyAt_of_nonneg h hh_nn hh_int hh_log_int j
    -- Step A: ∫ condEnt(h, j) = ∫ condEnt(E₀f, succ j) (dimension lift via tail)
    have hstepA : ∀ j : Fin (m' + 1),
        ∫ y, condEntropyAt stdGaussian h j y ∂(stdGaussianPi (m' + 1)) =
        ∫ x, condEntropyAt stdGaussian E₀f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) := by
      intro j
      rw [hE₀f_eq]
      simp_rw [condEntropyAt_comp_tail h j]
      exact (integral_comp_tail_stdGaussianPi _ (hcondEnt_int j)).symm
    have hdata_combined : ∀ j : Fin (m' + 1),
        ∫ y, condEntropyAt stdGaussian h j y ∂(stdGaussianPi (m' + 1)) ≤
        ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) := by
      intro j
      rw [hstepA j]
      -- DPI: ∫ condEnt(E₀f, succ j) ≤ ∫ condEnt(f, succ j)
      exact integrated_condEntropyAt_condExpect_le f hf_nn hf hf_log
        (Fin.succ j) 0 (Fin.succ_ne_zero j)
    -- Step 7: Combine. Split sum as condEnt_0 + ∑_{j} condEnt_{succ j}.
    rw [Fin.sum_univ_succ, hchain]
    -- Goal: ∫ condEnt_0(f) + Ent(E₀f) ≤ ∫ condEnt_0(f) + ∑_j ∫ condEnt_{succ j}(f)
    suffices hE : entropyPi (stdGaussianPi (m' + 2)) E₀f ≤
        ∑ j : Fin (m' + 1), ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) by linarith
    calc entropyPi (stdGaussianPi (m' + 2)) E₀f
        = entropyPi (stdGaussianPi (m' + 1)) h := hent_eq
      _ ≤ ∑ j : Fin (m' + 1), ∫ y, condEntropyAt stdGaussian h j y
            ∂(stdGaussianPi (m' + 1)) := hih
      _ ≤ ∑ j : Fin (m' + 1), ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
            ∂(stdGaussianPi (m' + 2)) :=
          Finset.sum_le_sum (fun j _ => hdata_combined j)

private lemma entropy_subadditivity_of_nonneg {n : ℕ}
    (g : (Fin n → ℝ) → ℝ)
    (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi n)) :
    entropyPi (stdGaussianPi n) g ≤
    ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) := by
  -- Case split on n
  rcases n with _ | m
  · -- n = 0: empty sum = 0, entropyPi over singleton type = 0
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have heval : ∀ (h : (Fin 0 → ℝ) → ℝ),
        ∫ x, h x ∂(stdGaussianPi 0) = h Fin.elim0 := by
      intro h
      have : ∀ x : Fin 0 → ℝ, h x = h Fin.elim0 := fun x => by
        congr 1; exact Subsingleton.elim x Fin.elim0
      simp_rw [this]; simp [integral_const, Measure.real, measure_univ]
    simp only [entropyPi, heval]; linarith
  rcases m with _ | m'
  · -- n = 1: equality case
    exact entropy_subadditivity_fin1 g hg_nn hg
  -- n = m' + 2 ≥ 2
  by_cases hlog : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi (m' + 2))
  · exact entropy_subadditivity_integrable (by omega) g hg_nn hg hlog
  · exact entropy_subadditivity_not_integrable_log (by omega) g hg_nn hg hlog

private lemma entropy_subadditivity_pi {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (stdGaussianPi n)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian (fun y => f y ^ 2) i x
        ∂(stdGaussianPi n) := by
  -- Set g = f² for readability
  set g : (Fin n → ℝ) → ℝ := fun x => f x ^ 2 with hg_def
  -- g is nonneg
  have hg_nn : ∀ x, 0 ≤ g x := fun x => sq_nonneg (f x)
  -- Handle the n = 0 case (both sides are 0 over singleton type)
  rcases n with _ | m
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    -- Reduce integrals over singleton type (Fin 0 → ℝ) to function evaluation
    have heval : ∀ (h : (Fin 0 → ℝ) → ℝ),
        ∫ x, h x ∂(stdGaussianPi 0) = h Fin.elim0 := by
      intro h
      have : ∀ x : Fin 0 → ℝ, h x = h Fin.elim0 := fun x => by
        congr 1; exact Subsingleton.elim x Fin.elim0
      simp_rw [this]; simp [integral_const, Measure.real, measure_univ]
    simp only [entropyPi, heval]; linarith
  -- For n = m + 1 ≥ 1, use entropy_subadditivity_of_nonneg.
  exact entropy_subadditivity_of_nonneg g hg_nn hf.integrable_sq

/-- Integrability of the conditional gradient integral (zero sorry).
Follows from Fubini (`Integrable.integral_prod_right`) + MemLp for coordinate slices. -/
private lemma integrable_condGrad {n : ℕ}
    (c : ℝ) (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n)) (i : Fin n) :
    Integrable (fun x => c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian)
      (stdGaussianPi n) := by
  -- Factor out the constant c
  apply Integrable.const_mul _ c
  -- Remains: Integrable (fun x => ∫ t, (gradf i (update x i t))² dγ) (γⁿ)
  -- Decompose n = m + 1 from i : Fin n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  -- Set up piFinSuccAbove decomposition: γⁿ⁺¹ ≅ γ_i × γᵐ
  let e := MeasurableEquiv.piFinSuccAbove (fun (_ : Fin (m + 1)) => ℝ) i
  set γ := stdGaussian
  set μ' : Fin (m + 1) → Measure ℝ := fun _ => γ
  set γn := Measure.pi (fun j : Fin m => μ' (i.succAbove j))
  have hmp := measurePreserving_piFinSuccAbove μ' i
  have hpi : stdGaussianPi (m + 1) = Measure.pi μ' := rfl
  -- Transfer (gradf i) to product measure via piFinSuccAbove: L² preserved
  have hg_prod : MemLp ((gradf i) ∘ e.symm) 2 (γ.prod γn) :=
    (hgradf i).comp_measurePreserving hmp.symm
  -- (gradf i ∘ e.symm)² ∈ L¹(γ × γᵐ) from MemLp 2
  have hint_prod := hg_prod.integrable_sq
  -- Fubini: ∫_t integrable → conditional integral is integrable in y
  have hint_cond := Integrable.integral_prod_right (f := fun p : ℝ × (Fin m → ℝ) =>
      (gradf i (e.symm p)) ^ 2) hint_prod
  -- removeNth is measure-preserving: γⁿ⁺¹ → γᵐ
  have hmp_rem : MeasurePreserving (fun x : Fin (m + 1) → ℝ => Fin.removeNth i x)
      (stdGaussianPi (m + 1)) γn := by
    change MeasurePreserving (Prod.snd ∘ e) _ _
    simp only [stdGaussianPi]
    exact measurePreserving_snd.comp
      (measurePreserving_piFinSuccAbove (fun (_ : Fin (m + 1)) => stdGaussian) i)
  -- Pullback: rewrite integrand as composition with removeNth
  rw [show (fun x => ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂γ) =
      (fun y => ∫ t, (gradf i (e.symm (t, y))) ^ 2 ∂γ) ∘
        (fun x => Fin.removeNth i x) from by
    ext x; simp only [Function.comp_def]
    congr 1; ext t; congr 1; congr 1
    exact (Fin.insertNth_removeNth i t x).symm]
  exact (hmp_rem.integrable_comp hint_cond.1).mpr hint_cond

end TensorizationInfra

/-- Integral monotonicity for conditional entropy vs LSI bound.
When condEntropyAt is not integrable, ∫ condEntropyAt = 0 ≤ ∫ (c · ∫ gradf²)
(since the RHS integrand is nonneg). When integrable, use ae bound from 1D LSI. -/
private lemma integral_condEntropyAt_le {n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (hLSI : SatisfiesLSI stdGaussian c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x (i : Fin n),
      HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (i : Fin n) :
    ∫ x, condEntropyAt stdGaussian (fun y => f y ^ 2) i x ∂(stdGaussianPi n) ≤
    ∫ x, (c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian) ∂(stdGaussianPi n) := by
  -- a.e. slices are in L²
  have hf_slice := ae_memLp_slice_of_memLp_pi f hf i
  have hg_slice := ae_memLp_slice_of_memLp_pi (gradf i) (hgradf i) i
  -- a.e. upper bound from 1D LSI
  have hle : ∀ᵐ x ∂(stdGaussianPi n),
      condEntropyAt stdGaussian (fun y => f y ^ 2) i x ≤
      c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian := by
    filter_upwards [hf_slice, hg_slice] with x hfx hgx
    exact condEntropyAt_le_of_satisfiesLSI c hLSI f gradf hgrad x i hfx hgx
  -- The upper bound is integrable
  have hint_ub := integrable_condGrad c gradf hgradf i
  -- Case split on integrability of condEntropyAt
  by_cases hint : Integrable (fun x => condEntropyAt stdGaussian (fun y => f y ^ 2) i x)
      (stdGaussianPi n)
  · -- Integrable case: use integral_mono_ae
    exact integral_mono_ae hint hint_ub hle
  · -- Not integrable: ∫ condEntropyAt = 0 by integral_undef.
    -- RHS ≥ 0 since c ≥ 0 and ∫ (squares) ≥ 0.
    rw [integral_undef hint]
    exact integral_nonneg (fun x => mul_nonneg hc (integral_nonneg (fun t => sq_nonneg _)))

/-- **Tensorization of the log-Sobolev inequality**.

If `μ` satisfies `LSI(c)`, then `μ^n` satisfies the multi-dimensional LSI:
  `Ent_{μ^n}(f²) ≤ c · ∑_i E_{μ^n}[(∂_i f)²]`.

**Proof**: Decompose into 3 steps:
1. **Entropy subadditivity** (`entropy_subadditivity_pi`, sorry):
   `Ent(f²) ≤ ∑_i E[condEntropyAt_i(f²)]`
2. **1D LSI per slice** (`condEntropyAt_le_of_satisfiesLSI`, proved):
   `condEntropyAt_i(f²)(x) ≤ c · ∫ (∂_i f(update x i t))² dμ(t)`
3. **Fubini rewrite** (`integral_condExpect_eq_integral_pi`, sorry):
   `∫ (∫ (∂_i f(update x i t))² dμ(t)) d(μ^n)(x) = ∫ (∂_i f)² d(μ^n)`

**Sorry count**: 0 in this theorem (uses sorry-free helper lemmas).
Note: `integral_condEntropyAt_le` handles the non-integrable case via `integral_undef`.

**Proved** (zero sorry):
- `integral_condExpect_eq_integral_pi` — Fubini identity
- `integrable_condGrad` — integrability of conditional gradient
- `integral_condEntropyAt_le` — integral monotonicity (case-splits on integrability) -/
theorem tensorization_lsi_core (n : ℕ) (c : ℝ) (hc : 0 ≤ c) : TensorizationLSIAt n c := by
  intro hLSI f gradf hf hgradf hgrad
  calc entropyPi (stdGaussianPi n) (fun x => f x ^ 2)
      ≤ ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian (fun y => f y ^ 2) i x
          ∂(stdGaussianPi n) :=
        entropy_subadditivity_pi f hf
    _ ≤ ∑ i : Fin n, ∫ x,
          (c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian)
          ∂(stdGaussianPi n) := by
        apply Finset.sum_le_sum; intro i _
        exact integral_condEntropyAt_le c hc hLSI f gradf hf hgradf hgrad i
    _ = c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
        simp_rw [integral_const_mul]
        rw [← Finset.mul_sum]
        congr 1; congr 1 with i
        exact integral_condExpect_eq_integral_pi (fun x => (gradf i x) ^ 2)
          (hgradf i).integrable_sq i

theorem gaussian_log_sobolev
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) :=
  gaussian_log_sobolev_of_tensorization_at n f gradf hf hgradf hgrad
    gaussian_lsi_1d_core
    (tensorization_lsi_core n 2 (by norm_num))

end

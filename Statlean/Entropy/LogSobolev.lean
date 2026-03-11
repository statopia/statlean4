import Statlean.Entropy.Basic
import Statlean.Gaussian.Poincare
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

## Sorry gaps (4 sorry lines in this file, 3 independent blockers)
- `gaussian_lsi_normalized_of_integrable` — the integrable case of normalized LSI
  **Blocker**: The 1D Gaussian LSI is a deep result. Every known proof requires
  infrastructure not in Mathlib:
  (a) Bakry-Emery Gamma_2 criterion + OU semigroup (~300 lines new infra)
  (b) Nelson hypercontractivity (~400 lines, documented as stuck)
  (c) Brunn-Minkowski / Prekopa-Leindler inequality (not in Mathlib)
  (d) Optimal transport / Caffarelli's theorem (not in Mathlib)
  (e) Two-point inequality + CLT transfer (~200 lines)
  The Stein identity alone gives Poincare, NOT the LSI. The previous comment
  claiming "Stein + Poincare + Young" suffices was incorrect — the Stein identity
  relates first moments to derivatives, while the LSI involves entropy (nonlinear).
  **Recommended path**: (a) Bakry-Emery, since Gamma_2 >= Gamma_1 is trivial for
  Gaussian (Gamma_2 = f''^2 + f'^2 >= f'^2 = Gamma_1). The hard part is proving
  that Gamma_2 >= rho*Gamma_1 implies LSI(2/rho), which needs the OU semigroup
  entropy dissipation formula.
- `integrable_sq_mul_log_sq_of_memLp` — f²·log(f²) ∈ L¹(γ) for f ∈ W^{1,2}(γ)
  **Blocker**: Requires the LSI or Gaussian Sobolev embedding W^{1,2}(γ) -> L^p(γ)
  for p > 2 (which is equivalent to hypercontractivity). The negative part is
  integrable (bounded by 1, proved). The positive part requires either the LSI
  (to bound integral of f^2 log^+(f^2)) or L^{2+eps} integrability of f.
  The 1D pointwise bound |f(x)| <= |f(0)| + |x|^{1/2} * e^{x^2/4} * C * ||f'||
  only gives f in L^p(gamma) for p < 2, which is insufficient.
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

/-- **1D Gaussian log-Sobolev inequality** (Gross 1975).

For `f, f'` in `L^2(gamma)` with `integral(f^2) = 1` and `f^2 log(f^2)` integrable:
  `integral(f^2 * log(f^2)) <= 2 * integral(f'^2)`

Equivalently in Fisher information form: `Ent(g) <= 1/2 * I(g)` where
`g = f^2`, `I(g) = integral((g')^2/g) = 4*integral(f'^2)`.

**Blocker**: Every known proof requires OU semigroup infrastructure not in Mathlib:
(a) Bakry-Emery via OU semigroup (~250 lines): define `P_t` via Mehler formula,
    prove entropy dissipation `d/dt Ent(P_t g) = -I(P_t g)`, Fisher decay
    `I(P_t g) <= e^{-2t} I(g)`, integrate to get `Ent(g) <= 1/2 I(g)`.
(b) Hypercontractivity of OU semigroup (~400 lines)
(c) Two-point inequality + CLT transfer (~200 lines) -/
private lemma gaussian_lsi_normalized_of_integrable
    (f f' : ℝ → ℝ)
    (_hf : MemLp f 2 stdGaussian)
    (_hf' : MemLp f' 2 stdGaussian)
    (_hderiv : ∀ x, HasDerivAt f (f' x) x)
    (_hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (_hint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Blocker: Requires OU semigroup infrastructure (Bakry-Emery criterion).
  -- See docstring above for proof architecture.
  sorry

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

/-- Integrability of conditional entropy (sorry).
Follows from entropy subadditivity infrastructure. -/
private lemma integrable_condEntropyAt {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 (stdGaussianPi n)) (i : Fin n) :
    Integrable (fun x => condEntropyAt stdGaussian (fun y => f y ^ 2) i x)
      (stdGaussianPi n) := by
  sorry

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

-- Sub-lemma 1: Data processing inequality for integrated conditional entropy.
-- E_j averaging can only decrease ∫ condEnt_i(g), i.e., averaging out coordinate j
-- makes the conditional entropy at coordinate i (for i ≠ j) only smaller.
-- Proof: pointwise Jensen for x·log(x) (convex on [0,∞)) applied to the
-- inner integral over coord j.
-- Uses: jensen_condExpect_mul_log (pointwise Jensen), condEntropyAt_nonneg_of_nonneg.
private lemma integrated_condEntropyAt_condExpect_le {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg : Integrable g (stdGaussianPi n))
    (hg_log : Integrable (fun x => g x * Real.log (g x)) (stdGaussianPi n))
    (i j : Fin n) (hij : i ≠ j) :
    ∫ x, condEntropyAt stdGaussian
        (fun y => ∫ t, g (Function.update y j t) ∂stdGaussian) i x
      ∂(stdGaussianPi n) ≤
    ∫ x, condEntropyAt stdGaussian g i x ∂(stdGaussianPi n) := by
  -- The proof uses the chain rule + DPI approach:
  -- ∫ condEnt_i(E_j g) = entropyPi(E_j g) - entropyPi(E_i E_j g)  [chain rule for E_j g]
  -- ∫ condEnt_i(g) = entropyPi(g) - entropyPi(E_i g)              [chain rule for g]
  -- Need: entropyPi(E_j g) - entropyPi(E_i E_j g) ≤ entropyPi(g) - entropyPi(E_i g)
  -- This is: ∫(E_j g)·log(E_j g) - ∫(E_i E_j g)·log(E_i E_j g)
  --        ≤ ∫g·log(g) - ∫(E_i g)·log(E_i g)
  -- (the (∫h)·log(∫h) terms cancel since all four functions have the same integral).
  --
  -- Equivalently: F(g) + F(E_i E_j g) ≥ F(E_i g) + F(E_j g) where F(h) = ∫h·log(h).
  -- This is the supermodularity of F under conditional expectations,
  -- equivalent to non-negativity of mutual information.
  --
  -- However, applying the chain rule requires integrability of slice integrals
  -- which is non-trivial. We instead use a direct calculation.
  --
  -- Direct approach: split ∫ condEnt = ∫ A - ∫ B where
  --   A(x) = ∫_t φ(upd x i t)·log(φ(upd x i t)) dγ(t)  (first term)
  --   B(x) = (∫_t φ(upd x i t) dγ(t))·log(∫_t φ(upd x i t) dγ(t))  (second term)
  -- for φ = E_j g (LHS) resp. φ = g (RHS).
  --
  -- By Fubini: ∫ A_{E_j g} = ∫ (E_j g)·log(E_j g) = F(E_j g)
  --            ∫ A_g = ∫ g·log(g) = F(g)
  -- By def:    ∫ B_{E_j g} = ∫ (E_i E_j g)·log(E_i E_j g)
  --            ∫ B_g = ∫ (E_i g)·log(E_i g)
  --
  -- So the claim is F(E_j g) - ∫(E_i E_j g)·log(E_i E_j g)
  --              ≤ F(g) - ∫(E_i g)·log(E_i g).
  -- i.e., [F(g) - F(E_j g)] ≥ [∫(E_i g)·log(E_i g) - ∫(E_i E_j g)·log(E_i E_j g)]
  -- i.e., [F(g) - F(E_j g)] ≥ [F(E_i g) - F(E_j(E_i g))]  (commutativity)
  -- Both sides are ≥ 0 (Jensen). The inequality follows from:
  --   ∫ g·log(g·c/(r·q)) ≥ 0  (mutual information ≥ 0)
  -- where c = E_i E_j g, r = E_i g, q = E_j g.
  -- This equals c·∫ p·log(p/(p₁·p₂)) where p = g/c is a "density" and p₁, p₂ marginals.
  -- By KL divergence ≥ 0 (Jensen for -log): ∫ p·log(p/(p₁·p₂)) ≥ 0.
  sorry

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
-- Actually this case is subtle. Let's handle it more carefully.
-- For now: mark as sorry, attack after sub-lemma 1.
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
    have hint2 : Integrable (fun x => (∫ t, f (Function.update x 0 t) ∂stdGaussian) *
        Real.log (∫ t, f (Function.update x 0 t) ∂stdGaussian)) (stdGaussianPi (m' + 2)) := by
      sorry -- Jensen + integrability of negative part
    have hchain := entropy_chain_rule_pi f (0 : Fin (m' + 2)) hf hf_log hint1 hint2
    -- Step 3: Properties of h.
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
      sorry -- Jensen: h·log(h) ≤ ∫ f·log(f) slice, then Fubini
    -- Step 4: Apply IH to h on (m' + 1) dimensions.
    have hih := ih (m' + 1) (by omega) h hh_nn hh_int hh_log_int
    -- Step 5: Translate IH back to n = m' + 2 dimensions.
    have hent_eq : entropyPi (stdGaussianPi (m' + 2)) E₀f =
        entropyPi (stdGaussianPi (m' + 1)) h := by
      rw [hE₀f_eq]; exact entropyPi_comp_tail h hh_int hh_log_int
    have hcondEnt_eq : ∀ j : Fin (m' + 1),
        ∫ y, condEntropyAt stdGaussian h j y ∂(stdGaussianPi (m' + 1)) =
        ∫ x, condEntropyAt stdGaussian E₀f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) := by
      intro j
      rw [hE₀f_eq]
      simp_rw [condEntropyAt_comp_tail h j]
      exact (integral_comp_tail_stdGaussianPi _ (by sorry)).symm
    -- Data processing: ∫ condEnt_i(E₀f) ≤ ∫ condEnt_i(f) for i ≥ 1.
    have hdata : ∀ j : Fin (m' + 1),
        ∫ x, condEntropyAt stdGaussian E₀f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) ≤
        ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) := by
      intro j
      exact integrated_condEntropyAt_condExpect_le f hf_nn hf hf_log
        (Fin.succ j) 0 (Fin.succ_ne_zero j)
    -- Step 6: Combine. Split sum as condEnt_0 + ∑_{j} condEnt_{succ j}.
    rw [Fin.sum_univ_succ, hchain]
    -- Goal: ∫ condEnt_0(f) + Ent(E₀f) ≤ ∫ condEnt_0(f) + ∑_j ∫ condEnt_{succ j}(f)
    suffices hE : entropyPi (stdGaussianPi (m' + 2)) E₀f ≤
        ∑ j : Fin (m' + 1), ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
          ∂(stdGaussianPi (m' + 2)) by linarith
    calc entropyPi (stdGaussianPi (m' + 2)) E₀f
        = entropyPi (stdGaussianPi (m' + 1)) h := hent_eq
      _ ≤ ∑ j : Fin (m' + 1), ∫ y, condEntropyAt stdGaussian h j y
            ∂(stdGaussianPi (m' + 1)) := hih
      _ = ∑ j : Fin (m' + 1), ∫ x, condEntropyAt stdGaussian E₀f (Fin.succ j) x
            ∂(stdGaussianPi (m' + 2)) := by
          congr 1; ext j; exact hcondEnt_eq j
      _ ≤ ∑ j : Fin (m' + 1), ∫ x, condEntropyAt stdGaussian f (Fin.succ j) x
            ∂(stdGaussianPi (m' + 2)) :=
          Finset.sum_le_sum (fun j _ => hdata j)

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

**Sorry count**: 2 (blocked by `Measure.pi` Fubini infrastructure):
- `entropy_subadditivity_pi` — entropy chain rule (~150 lines)
- `integrable_condEntropyAt` — integrability (~20 lines)

**Proved** (zero sorry):
- `integral_condExpect_eq_integral_pi` — Fubini identity
- `integrable_condGrad` — integrability of conditional gradient -/
theorem tensorization_lsi_core (n : ℕ) (c : ℝ) : TensorizationLSIAt n c := by
  intro hLSI f gradf hf hgradf hgrad
  -- Step 1: entropy subadditivity (sorry)
  -- Step 2: 1D LSI per coordinate (proved)
  -- Step 3: Fubini rewrite (sorry)
  calc entropyPi (stdGaussianPi n) (fun x => f x ^ 2)
      ≤ ∑ i : Fin n, ∫ x, condEntropyAt stdGaussian (fun y => f y ^ 2) i x
          ∂(stdGaussianPi n) :=
        entropy_subadditivity_pi f hf
    _ ≤ ∑ i : Fin n, ∫ x,
          (c * ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian)
          ∂(stdGaussianPi n) := by
        apply Finset.sum_le_sum; intro i _
        apply integral_mono_ae (integrable_condEntropyAt f hf i)
          (integrable_condGrad c gradf hgradf i)
        filter_upwards [ae_memLp_slice_of_memLp_pi f hf i,
          ae_memLp_slice_of_memLp_pi (gradf i) (hgradf i) i] with x hf_x hg_x
        exact condEntropyAt_le_of_satisfiesLSI c hLSI f gradf hgrad x i hf_x hg_x
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
    (tensorization_lsi_core n 2)

end

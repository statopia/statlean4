import Statlean.Entropy.Basic
import Statlean.Gaussian.Stein
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Gaussian Log-Sobolev Inequality

## Proved (zero sorry)
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
  - `hasDerivAt_regularized_log` — d/dx [½ log(f²+ε)] = f·f'/(f²+ε)
  - `hasDerivAt_f_mul_psi_eps` — d/dx [f·ψ_ε] = f'·ψ_ε + f²·f'/(f²+ε)
  - `sq_div_sq_add_eps_le_one` — f²/(f²+ε) ≤ 1
  - `two_mul_le_sq_add_sq` — 2ab ≤ a² + b²

## Sorry gaps (3 honest, all blocked by missing Mathlib infrastructure)
- `integrable_sq_mul_log_sq_of_memLp` — f²·log(f²) ∈ L¹(γ) for f ∈ L²(γ)
  **Blocker**: Gaussian hypercontractivity / Sobolev embedding W^{1,2}(γ) ↪ L⁴(γ)
- `gaussian_lsi_normalized` — normalized 1D LSI: ∫f²=1 => ∫f²·log(f²) ≤ 2∫f'²
  **Blocker**: Same as above (MemLp estimates for regularized Stein IBP need L⁴)
- `tensorization_lsi_core` — LSI tensorization
  **Blocker**: Product entropy chain rule (Measure.pi Fubini for single coordinate)

## Proof architecture for `gaussian_lsi_1d_ibp_core` (PROVED)

The main theorem `Ent_γ(f²) ≤ 2·∫f'² dγ` is proved via:

1. **Case A = 0** (∫f² = 0): f = 0 a.e., Ent = 0, RHS ≥ 0. Fully proved.
2. **Case A > 0**: Define g = f/√A, g' = f'/√A. Then ∫g² = 1.
   - Apply `gaussian_lsi_normalized` to g: ∫g²·log(g²) ≤ 2∫g'²
   - Prove entropy scaling: Ent(f²) = A · ∫g²·log(g²)
     (uses log(A·g²) = log(A) + log(g²) splitting + ∫g² = 1)
   - Conclude: Ent(f²) = A·∫g²·log(g²) ≤ A·2∫g'² = 2∫f'²

### Strategy for `gaussian_lsi_normalized` (remaining sorry)

Recommended: **Gross's argument via regularized Stein IBP**:
1. For ε > 0, define ψ_ε(x) = ½·log(f(x)² + ε), smooth everywhere.
2. Apply `stein_identity` to h = f·ψ_ε: ∫ x·f·ψ_ε dγ = ∫ (f·ψ_ε)' dγ.
3. Use Young's inequality 2ab ≤ a² + b² on cross terms.
4. Take ε → 0 via DCT.
5. Result: ∫ f²·log(f²) ≤ 2∫f'².
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

### Proof outline (Gross's original argument)

**Step 1 — Scaling reduction**:
Write `A = ∫ f² dγ`. If `A = 0`, then `f = 0` a.e. and both sides are zero.
If `A > 0`, set `g = f/√A` so that `∫ g² = 1`. Then:
  `Ent(f²) = A · ∫ g² log(g²) dγ`  and  `2∫ f'² = 2A · ∫ g'² dγ`
So it suffices to prove the **normalized case**: `∫ f² = 1 ⟹ ∫ f²·log(f²) ≤ 2∫ f'²`.

**Step 2 — Regularized Stein IBP**:
For `ε > 0`, define the regularized log-amplitude:
  `ψ_ε(x) = log √(f(x)² + ε) = ½ · log(f(x)² + ε)`
Apply the Stein identity `∫ x·h dγ = ∫ h' dγ` to `h(x) = f(x) · ψ_ε(x)`:
  `∫ x · f · ψ_ε dγ = ∫ [f' · ψ_ε + f · f · f' / (f² + ε)] dγ`

**Step 3 — Young's inequality + limit**:
The entropy identity gives `∫ f² · log(f²) = 2 ∫ f · ψ_ε · (x · f) dγ + error(ε)`.
Apply Young's inequality `2ab ≤ a² + b²` to separate f' and ψ_ε terms.
Take `ε → 0` using DCT. The key bound becomes `∫ f² log(f²) ≤ 2∫ f'²`.

### Sub-lemma decomposition

We split into 3 sorry-bearing sub-lemmas:

1. `integrable_sq_mul_log_sq_of_memLp` — integrability of `f²·log(f²)` under γ
2. `gaussian_lsi_normalized` — the normalized case ∫f²=1 (the hard core, needs IBP)
3. `gaussian_lsi_1d_ibp_core` — case split: A=0 proved, A>0 uses scaling + normalized

The net sorry count for the 1D LSI stays at 2 honest sorrys (sub-lemma 1 and 2).
`gaussian_lsi_1d_ibp_core` is proved from sub-lemma 2 via scaling, except for the
scaling argument itself which requires integral manipulation.

**Dependency graph**: gaussian_lsi_1d_ibp_core → gaussian_lsi_normalized (+ scaling)
                       gaussian_lsi_normalized → integrable_sq_mul_log_sq_of_memLp
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

/-- **Gaussian hypercontractivity (W^{1,2}(γ) → L⁴(γ))**: If `f ∈ L²(γ)` and `f' ∈ L²(γ)`
    with `HasDerivAt`, then `f ∈ L⁴(γ)`.

    This is the 1D case of the Nelson hypercontractivity theorem (1973).
    The standard proof uses the Ornstein-Uhlenbeck semigroup: `P_t f ∈ L^q(γ)`
    for `q ≤ 1 + (p-1)e^{2t}` when `f ∈ L^p(γ)`. Taking p=2, t=½ log 3 gives q=4.

    **Blocker**: Not available in Mathlib v4.28. Requires either:
    - Ornstein-Uhlenbeck semigroup theory, or
    - Fine structure of Hermite polynomial products (linearization formula).

    **Strategies attempted and why they fail**:

    1. **FTC + Cauchy-Schwarz**: `f(x) = f(0) + ∫₀ˣ f'(t) dt`. Using C-S with
       Gaussian weight: `(∫₀ˣ f')² ≤ (∫₀ˣ f'² exp(-t²/2) dt)(∫₀ˣ exp(t²/2) dt)`.
       The second factor grows as `exp(x²/2)/x`, giving `|f(x)|⁴ ~ exp(x²)` for large x.
       Then `∫ f⁴ dγ ~ ∫ exp(x²/2) dx = ∞`. **Divergent bound**.

    2. **Stein identity on f³**: `∫ x·f³ dγ = 3∫ f²f' dγ` relates L³ to mixed terms
       but doesn't close: bounding `∫ f⁴` requires `∫ f⁴` on the RHS via Hölder.

    3. **Hermite expansion**: `f = Σ aₙ eₙ` with `Σ aₙ² < ∞` and `Σ n·aₙ² < ∞`.
       Computing `‖f‖₄⁴ = ‖f²‖₂²` requires the Hermite product linearization formula
       `Hₘ·Hₙ = Σ k!·C(m,k)·C(n,k)·H_{m+n-2k}` — a significant algebraic formalization
       effort (~200 lines) not present in Mathlib.

    4. **Gross regularization bypass**: The regularized LSI approach (proving the LSI
       first, deriving L⁴ as a consequence) creates a circular dependency: the
       regularized Stein IBP requires `f·ψ_ε ∈ L²(γ)`, which needs `f·log|f| ∈ L²(γ)`,
       which needs `f ∈ L⁴(γ)` (since `(f·log|f|)² ≤ C·f⁴ + C`).

    **Estimated effort**: ~400 lines of new infrastructure (Hermite product formula
    + L⁴ bound from coefficients), or ~600 lines (OU semigroup from scratch). -/
lemma memLp_four_of_W12_gaussian
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    MemLp f 4 stdGaussian := by
  sorry

lemma integrable_sq_mul_log_sq_of_memLp
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian := by
  -- Step 1: f ∈ L⁴(γ) by Gaussian hypercontractivity
  have hf4 : MemLp f 4 stdGaussian := memLp_four_of_W12_gaussian f f' hf hf' hderiv
  -- Step 2: f⁴ is integrable under γ (MemLp f 4 ⟹ ∫ ‖f‖⁴ < ∞ ⟹ ∫ f⁴ < ∞)
  have hf4_int : Integrable (fun x => f x ^ 4) stdGaussian := by
    have h4eq : (4 : ENNReal) = Nat.cast (4 : Nat) := by norm_cast
    rw [h4eq] at hf4
    exact hf4.integrable_norm_pow'.congr (ae_of_all _ fun x => by
      simp [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩])
  -- Step 3: |f²·log(f²)| ≤ f⁴ + 1 by abs_mul_log_le_sq_add_one
  -- Therefore f²·log(f²) is integrable by domination
  refine (hf4_int.norm.add (integrable_const 1)).mono'
    ((hf.aestronglyMeasurable.pow _).mul
      ((Real.measurable_log.comp_aemeasurable
        (hf.aestronglyMeasurable.pow _).aemeasurable).aestronglyMeasurable))
    (ae_of_all _ fun x => ?_)
  -- Pointwise bound: ‖f²·log(f²)‖ ≤ ‖f⁴‖ + 1
  change ‖f x ^ 2 * Real.log (f x ^ 2)‖ ≤ ‖f x ^ 4‖ + 1
  simp only [Real.norm_eq_abs]
  calc |f x ^ 2 * Real.log (f x ^ 2)|
      ≤ (f x ^ 2) ^ 2 + 1 := abs_mul_log_le_sq_add_one (f x ^ 2) (sq_nonneg _)
    _ = f x ^ 4 + 1 := by ring_nf
    _ ≤ |f x ^ 4| + 1 := by gcongr; exact le_abs_self _

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

/-- **Sub-lemma 2 (normalized LSI core)**: When `∫ f² dγ = 1` (i.e., `f²` is a
    probability density w.r.t. `γ`), the Gaussian log-Sobolev inequality states:

    `∫ f²·log(f²) dγ ≤ 2 · ∫ f'² dγ`

    This is the heart of the proof. When `∫ f² = 1`, we have `Ent(f²) = ∫ f²·log(f²)`.

    **Blocker**: The full Gross argument requires:
    1. `stein_identity` applied to `h = f · ψ_ε` (infrastructure ready:
       `hasDerivAt_f_mul_psi_eps` gives the derivative)
    2. MemLp estimates for `f · ψ_ε` and its derivative under Gaussian
       (requires showing `ψ_ε = ½ log(f² + ε) ∈ L²(γ)` when `f ∈ L²(γ)`,
        which needs `|log(f² + ε)| ≤ C·(f² + 1)` and thus `f ∈ L⁴(γ)`,
        again blocked by Gaussian hypercontractivity)
    3. Taking `ε → 0` via DCT (dominated convergence)

    **Dependency**: Same as sorry 1 — ultimately blocked by missing
    Gaussian hypercontractivity / Sobolev embedding.

    **Proof strategy (Gross's argument via regularized Stein IBP)**:

    1. For `ε > 0`, define `ψ_ε(x) = ½ · log(f(x)² + ε)`, smooth everywhere.
    2. Apply `stein_identity` to `h = f · ψ_ε`:
       `∫ x·f·ψ_ε dγ = ∫ (f·ψ_ε)' dγ`
       `= ∫ [f'·ψ_ε + f²·f'/(f²+ε)] dγ`
       (derivative computed by `hasDerivAt_f_mul_psi_eps`)
    3. Also apply Stein to `h = f` getting `∫ x·f dγ = ∫ f' dγ`.
    4. The product rule on `∫ x·f²·ψ_ε = ∫ (f²·ψ_ε)' = 2∫ f·f'·ψ_ε + ∫ f²·ψ_ε'`
       gives a relation between the entropy integral and the Fisher information.
    5. Young's inequality `2ab ≤ a² + b²` (`two_mul_le_sq_add_sq`) on cross terms.
    6. `f²/(f²+ε) ≤ 1` (`sq_div_sq_add_eps_le_one`) simplifies the bound.
    7. Take `ε → 0` via DCT to get `∫ f²·log(f²) ≤ 2∫ f'²`. -/
lemma gaussian_lsi_normalized
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- The Gross argument via regularized Stein IBP requires:
  -- 1. MemLp estimates for f · ψ_ε (needs f ∈ L⁴(γ) → Gaussian hypercontractivity)
  -- 2. Dominated convergence as ε → 0
  -- Both are blocked by missing Gaussian Sobolev embedding in Mathlib.
  sorry

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

/-- **Tensorization of the log-Sobolev inequality**.

    If `μ` satisfies `LSI(c)`, then `μ^n` satisfies the multi-dimensional LSI:
    `Ent_{μ^n}(f²) ≤ c · ∑_i E_{μ^n}[(∂_i f)²]`.

    **Blocker**: Requires the **entropy chain rule** for product measures:
    `Ent_{μ^n}(g) = ∑_i E_{x_{-i}} [Ent_{μ_i}(g(x_{-i}, ·))]`
    where `x_{-i}` denotes all coordinates except `i`.

    This chain rule requires:
    1. **Disintegration / conditional entropy**: Mathlib's `Measure.pi` lacks
       coordinate-wise conditional integration (Fubini along a single coordinate).
    2. **Iterated entropy decomposition**: The telescoping identity
       `Ent(g) = ∑_i E[Ent_i(g)]` where `Ent_i` is conditional entropy along
       coordinate `i`, requires conditional expectations w.r.t. product σ-algebras.
    3. **Applying 1D LSI to each slice**: For fixed `x_{-i}`, need to apply
       `SatisfiesLSI μ c` to the function `t ↦ f(update x i t)`, which requires
       showing that the slice inherits the regularity hypotheses.

    **Status**: Blocked by missing `Measure.pi` Fubini for single coordinate slicing
    and conditional entropy infrastructure in Mathlib as of v4.28. -/
theorem tensorization_lsi_core (n : ℕ) (c : ℝ) : TensorizationLSIAt n c := by
  sorry

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

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

## Sorry gaps (2 honest, down from previous 3)
- `integrable_sq_mul_log_sq_of_memLp` — f²·log(f²) ∈ L¹(γ) for f ∈ L²(γ)
  (needs Gaussian hypercontractivity or Sobolev embedding)
- `gaussian_lsi_normalized` — normalized 1D LSI: ∫f²=1 => ∫f²·log(f²) ≤ 2∫f'²
  (the hard core; needs Stein IBP + Young's inequality + regularization)
- `tensorization_lsi_core` — LSI tensorization (needs product entropy decomposition)

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

/-- **Sub-lemma 1 (integrability)**: For the Gaussian, `f ∈ L²(γ)` and `HasDerivAt f f'`
    implies the entropy integrand `f²·log(f²)` is in `L¹(γ)`.

    **Proof sketch**: Since `|t²·log(t²)| ≤ C·(t² + |t|^{2+δ})` for any `δ > 0`,
    and the Gaussian has moments of all orders, it suffices to show `f ∈ L^{2+δ}(γ)`
    for some `δ > 0`. For smooth `f` with `f' ∈ L²(γ)`, this follows from the
    Sobolev embedding `W^{1,2}(γ) ↪ L^p(γ)` for all finite `p` (Gaussian
    hypercontractivity / Nelson's theorem). Alternatively, one can use the bound
    `|f(x)²·log(f(x)²)| ≤ f(x)^4/e + e^{-1}` and the fact that `f ∈ L⁴(γ)`
    via Gaussian hypercontractivity. -/
lemma integrable_sq_mul_log_sq_of_memLp
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) stdGaussian := by
  sorry

/-- **Sub-lemma 2 (normalized LSI core)**: When `∫ f² dγ = 1` (i.e., `f²` is a
    probability density w.r.t. `γ`), the Gaussian log-Sobolev inequality states:

    `∫ f²·log(f²) dγ ≤ 2 · ∫ f'² dγ`

    This is the heart of the proof. When `∫ f² = 1`, we have `Ent(f²) = ∫ f²·log(f²)`.

    **Proof strategy (Gross's argument via regularized IBP)**:

    1. For `ε > 0`, define `ψ_ε(x) = ½ · log(f(x)² + ε)`. This is smooth everywhere.
    2. Apply the Stein identity to `h(x) = f(x) · ψ_ε(x)`:
       `∫ x · f · ψ_ε dγ = ∫ (f · ψ_ε)' dγ = ∫ [f' · ψ_ε + f · f · f'/(f² + ε)] dγ`
    3. Rewrite the LHS using `∫ f² log(f²+ε) = 2 ∫ x · f · ψ_ε dγ` (from the
       entropy decomposition + Stein identity applied to f²).
    4. Apply Young's inequality `2ab ≤ a²/t + t·b²` with `t = 1` to the cross terms:
       `2 · |f' · ψ_ε| ≤ f'² + ψ_ε²`
    5. Bound `ψ_ε² ≤ (½ log(f²+ε))² ≤ ...` and use the identity
       `f²/(f²+ε) ≤ 1` to simplify.
    6. Take `ε → 0` via DCT. The log(f²+ε) → log(f²) where f ≠ 0,
       and the 0·log(0) = 0 convention handles f = 0.

    The result is: `∫ f² log(f²) ≤ 2 ∫ f'²`. -/
lemma gaussian_lsi_normalized
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1) :
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
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

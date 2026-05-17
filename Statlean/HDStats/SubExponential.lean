import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Exponential Random Variables (MGF form)

This file defines sub-exponential random variables in MGF form
(Vershynin §2.7 / Wainwright §2.1.3): a real random variable
`X : Ω → ℝ` is **`(σ, b)`-sub-exponential** under a measure `μ` if for
every `t : ℝ` with `|t| · b ≤ 1`, the MGF of `X` satisfies
```
  ∫ exp(t · X) ∂μ ≤ exp(t² σ² / 2).
```

This class is the standard tool for Bernstein-type concentration:
unlike sub-Gaussian RVs it admits heavier exponential tails, and
it is closed under scaling, deterministic shifts (of the MGF), and
(under independence) sums.

The implementation here is *intentionally* parallel to Mathlib's
`ProbabilityTheory.HasSubgaussianMGF`, but uses two non-negative
real parameters `(σ, b) : ℝ × ℝ` rather than a single `NNReal`,
which is the conventional Bernstein-Cramer form.  The `NNReal`-typed
variants are easily derived from these.

## Main definitions

* `Statlean.HDStats.HasSubExpMGF X σ b μ` — sub-exponential MGF
  bound for `X` under `μ`.

## Main results

* `HasSubExpMGF.nonneg_left` / `nonneg_right` — projecting out the
  parameter non-negativity hypotheses.
* `HasSubExpMGF.zero` — the constant `0` random variable is
  sub-exponential with any non-negative parameters.
* `HasSubExpMGF.const_smul` — scaling: if `X` is `(σ, b)`-sub-exp
  then `c · X` is `(|c|·σ, |c|·b)`-sub-exp.
* `HasSubExpMGF.mgf_add_const` — MGF of `X + c` is bounded by
  `exp(t·c) · exp(t² σ² / 2)` for deterministic `c : ℝ`.

* `HasSubExpMGF.bernstein_tail` — the standard Bernstein-type tail
  bound `μ {ω | t ≤ X ω} ≤ exp(-min(t²/(2σ²), t/(2b)))`, obtained via
  the Chernoff method optimizing the dual variable `s ∈ [0, 1/b]`.

## Future work

The centered form
```
  μ {ω | t ≤ X ω - E[X]} ≤ exp(-min(t² / (2σ²), t / (2b)))
```
follows directly from `bernstein_tail` applied to the recentered
random variable, once a `mgf_centered` API surface is in place.

The implication "sub-Gaussian ⟹ X² sub-exponential" with parameters
depending only on the sub-Gaussian proxy is the key bridge used in
Hanson–Wright; it is left for a follow-up file together with the
diagonal/off-diagonal decomposition.

## References

* R. Vershynin, *High-Dimensional Probability*, §2.7–2.8.
* M. Wainwright, *High-Dimensional Statistics*, §2.1.3.
-/

namespace Statlean.HDStats

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- `X` is **`(σ, b)`-sub-exponential** under `μ` if `σ, b ≥ 0`, the
moment generating function of `X` is finite (integrable) for every
admissible `t` with `|t| · b ≤ 1`, and the MGF bound
`E[exp(t · X)] ≤ exp(t² σ² / 2)` holds for every such `t`.

This is the Bernstein–Cramer form used in Vershynin §2.7. The
integrability field matches Mathlib's `ProbabilityTheory.HasSubgaussianMGF`
and is required to apply the standard Chernoff inequality
`measure_ge_le_exp_mul_mgf`. -/
def HasSubExpMGF (X : Ω → ℝ) (σ b : ℝ) (μ : Measure Ω) : Prop :=
  0 ≤ σ ∧ 0 ≤ b ∧
    (∀ t : ℝ, |t| * b ≤ 1 → Integrable (fun ω => Real.exp (t * X ω)) μ) ∧
    (∀ t : ℝ, |t| * b ≤ 1 → ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * σ ^ 2 / 2))

namespace HasSubExpMGF

/-- The Gaussian-parameter `σ` is non-negative. -/
lemma nonneg_left {X : Ω → ℝ} {σ b : ℝ} (h : HasSubExpMGF X σ b μ) : 0 ≤ σ := h.1

/-- The Bernstein-parameter `b` is non-negative. -/
lemma nonneg_right {X : Ω → ℝ} {σ b : ℝ} (h : HasSubExpMGF X σ b μ) : 0 ≤ b := h.2.1

/-- The function `ω ↦ exp(t · X ω)` is integrable for every admissible `t`. -/
lemma integrable_exp_mul {X : Ω → ℝ} {σ b : ℝ} (h : HasSubExpMGF X σ b μ)
    {t : ℝ} (ht : |t| * b ≤ 1) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := h.2.2.1 t ht

/-- The MGF bound holds for every admissible `t`. -/
lemma mgf_le {X : Ω → ℝ} {σ b : ℝ} (h : HasSubExpMGF X σ b μ)
    {t : ℝ} (ht : |t| * b ≤ 1) :
    ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * σ ^ 2 / 2) :=
  h.2.2.2 t ht

/-- The zero random variable is sub-exponential with any non-negative
parameters under any probability measure. -/
lemma zero {σ b : ℝ} (hσ : 0 ≤ σ) (hb : 0 ≤ b) [IsProbabilityMeasure μ] :
    HasSubExpMGF (fun _ : Ω => (0 : ℝ)) σ b μ := by
  refine ⟨hσ, hb, ?_, ?_⟩
  · intro t _
    simp only [mul_zero, Real.exp_zero]
    exact integrable_const 1
  · intro t _
    have h1 : ∫ _ : Ω, Real.exp (t * 0) ∂μ = 1 := by
      simp [mul_zero, Real.exp_zero, integral_const]
    have h2 : (1 : ℝ) ≤ Real.exp (t ^ 2 * σ ^ 2 / 2) := Real.one_le_exp (by positivity)
    linarith [h1, h2]

/-- Scaling: if `X` is `(σ, b)`-sub-exponential, then `c · X` is
`(|c|·σ, |c|·b)`-sub-exponential. -/
lemma const_smul {X : Ω → ℝ} {σ b : ℝ}
    (h : HasSubExpMGF X σ b μ) (c : ℝ) :
    HasSubExpMGF (fun ω => c * X ω) (|c| * σ) (|c| * b) μ := by
  obtain ⟨hσ, hb, hint, hbd⟩ := h
  refine ⟨mul_nonneg (abs_nonneg _) hσ, mul_nonneg (abs_nonneg _) hb, ?_, ?_⟩
  · intro t ht
    -- pass scalar through to apply hint at (t * c)
    have ht' : |t * c| * b ≤ 1 := by
      rw [abs_mul]
      calc |t| * |c| * b = |t| * (|c| * b) := by ring
        _ ≤ 1 := ht
    have hint_tc := hint (t * c) ht'
    -- exp(t * (c * X ω)) = exp((t * c) * X ω)
    refine hint_tc.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    change Real.exp ((t * c) * X ω) = Real.exp (t * (c * X ω))
    rw [mul_assoc]
  · intro t ht
    -- pass scalar through MGF
    have ht' : |t * c| * b ≤ 1 := by
      rw [abs_mul]
      calc |t| * |c| * b = |t| * (|c| * b) := by ring
        _ ≤ 1 := ht
    have key := hbd (t * c) ht'
    have rw_int : ∫ ω, Real.exp (t * (c * X ω)) ∂μ
        = ∫ ω, Real.exp ((t * c) * X ω) ∂μ := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro ω
      ring_nf
    rw [rw_int]
    refine key.trans ?_
    apply Real.exp_le_exp.mpr
    -- (t·c)² · σ² / 2 ≤ t² · (|c|·σ)² / 2
    have habs : (|c| * σ) ^ 2 = c ^ 2 * σ ^ 2 := by rw [mul_pow, sq_abs]
    rw [habs]
    nlinarith [sq_nonneg t, sq_nonneg c, sq_nonneg σ]

/-- MGF identity for deterministic shift: `E[exp(t (X + c))] = exp(t·c) · E[exp(t X)]`,
so the sub-exponential bound transfers up to the multiplicative factor `exp(t·c)`.

This is the standard ingredient used to chain centered Bernstein bounds
without committing to a specific centering constant in the predicate. -/
lemma mgf_add_const {X : Ω → ℝ} {σ b : ℝ}
    (h : HasSubExpMGF X σ b μ) (c : ℝ) {t : ℝ} (ht : |t| * b ≤ 1) :
    ∫ ω, Real.exp (t * (X ω + c)) ∂μ
      ≤ Real.exp (t * c) * Real.exp (t ^ 2 * σ ^ 2 / 2) := by
  have hbd := h.mgf_le ht
  have step : ∀ ω, Real.exp (t * (X ω + c))
      = Real.exp (t * c) * Real.exp (t * X ω) := by
    intro ω
    rw [show t * (X ω + c) = t * X ω + t * c from by ring,
        Real.exp_add, mul_comm]
  have heq : ∫ ω, Real.exp (t * (X ω + c)) ∂μ
      = ∫ ω, Real.exp (t * c) * Real.exp (t * X ω) ∂μ := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact step ω
  rw [heq, integral_const_mul]
  have hpos : (0 : ℝ) ≤ Real.exp (t * c) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left hbd hpos

/-- **Bernstein-type tail bound (Chernoff form)**.
For non-negative `t`, the upper tail probability of a sub-exponential
random variable is bounded by `exp(-min(t² / (2σ²), t / (2b)))`.

Proof: by the standard Chernoff method, choosing the dual variable
`s = min(t/σ², 1/b)` ∈ [0, 1/b] in the MGF bound and optimizing the
exponent `s·t - s²σ²/2`.  The two regimes correspond to `t·b ≤ σ²`
(sub-Gaussian tail) and `t·b > σ²` (sub-exponential tail).
The degenerate cases `σ = 0` and `b = 0` are absorbed by the
convention `x/0 = 0` and `μ.real ≤ 1` for probability measures. -/
lemma bernstein_tail {X : Ω → ℝ} {σ b : ℝ}
    (h : HasSubExpMGF X σ b μ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t ≤ X ω}).toReal ≤
      Real.exp (-(min (t ^ 2 / (2 * σ ^ 2)) (t / (2 * b)))) := by
  have hσ_nn : 0 ≤ σ := h.nonneg_left
  have hb_nn : 0 ≤ b := h.nonneg_right
  -- Degenerate case σ = 0: the term `t²/(2σ²) = t²/0 = 0`, so `min ≤ 0`
  by_cases hσ_zero : σ = 0
  · subst hσ_zero
    have hmin_le : min (t ^ 2 / (2 * (0:ℝ) ^ 2)) (t / (2 * b)) ≤ 0 := by
      have h1 : (t ^ 2 / (2 * (0:ℝ) ^ 2)) = 0 := by simp
      rw [h1]
      exact min_le_left _ _
    have hrhs : (1 : ℝ) ≤ Real.exp (-(min (t ^ 2 / (2 * (0:ℝ) ^ 2)) (t / (2 * b)))) := by
      refine Real.one_le_exp ?_
      linarith
    have hlhs : (μ {ω | t ≤ X ω}).toReal ≤ 1 := by
      have hp : μ {ω | t ≤ X ω} ≤ 1 := prob_le_one
      have h1 : (μ {ω | t ≤ X ω}).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top hp
      simpa using h1
    linarith
  -- Degenerate case b = 0: the term `t/(2b) = t/0 = 0`, so `min ≤ 0`
  by_cases hb_zero : b = 0
  · subst hb_zero
    have hmin_le : min (t ^ 2 / (2 * σ ^ 2)) (t / (2 * (0:ℝ))) ≤ 0 := by
      have h1 : (t / (2 * (0:ℝ))) = 0 := by simp
      rw [h1]
      exact min_le_right _ _
    have hrhs : (1 : ℝ) ≤ Real.exp (-(min (t ^ 2 / (2 * σ ^ 2)) (t / (2 * (0:ℝ))))) := by
      refine Real.one_le_exp ?_
      linarith
    have hlhs : (μ {ω | t ≤ X ω}).toReal ≤ 1 := by
      have hp : μ {ω | t ≤ X ω} ≤ 1 := prob_le_one
      have h1 : (μ {ω | t ≤ X ω}).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top hp
      simpa using h1
    linarith
  -- Main case: σ > 0 and b > 0
  have hσ : (0 : ℝ) < σ := lt_of_le_of_ne hσ_nn (Ne.symm hσ_zero)
  have hb : (0 : ℝ) < b := lt_of_le_of_ne hb_nn (Ne.symm hb_zero)
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  -- Choose s = min(t/σ², 1/b) ∈ [0, 1/b], so |s| · b ≤ 1
  set s : ℝ := min (t / σ ^ 2) (1 / b) with hs_def
  have hs_nn : 0 ≤ s := by
    refine le_min ?_ ?_
    · exact div_nonneg ht (sq_nonneg _)
    · exact div_nonneg zero_le_one hb.le
  have hsb_le : |s| * b ≤ 1 := by
    rw [abs_of_nonneg hs_nn]
    have h1 : s ≤ 1 / b := min_le_right _ _
    calc s * b ≤ (1 / b) * b := mul_le_mul_of_nonneg_right h1 hb.le
      _ = 1 := by field_simp
  -- Mathlib Chernoff: μ.real {t ≤ X} ≤ exp(-s·t) · mgf(X, μ, s)
  have hint := h.integrable_exp_mul hsb_le
  have hchern :=
    measure_ge_le_exp_mul_mgf (X := X) (μ := μ) (t := s) t hs_nn hint
  have hmgf_s : mgf X μ s ≤ Real.exp (s ^ 2 * σ ^ 2 / 2) := h.mgf_le hsb_le
  have hexp_neg : (0 : ℝ) ≤ Real.exp (-s * t) := (Real.exp_pos _).le
  have hcomb : (μ {ω | t ≤ X ω}).toReal
      ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * σ ^ 2 / 2) := by
    refine hchern.trans ?_
    exact mul_le_mul_of_nonneg_left hmgf_s hexp_neg
  rw [← Real.exp_add] at hcomb
  refine hcomb.trans ?_
  refine Real.exp_le_exp.mpr ?_
  -- Algebraic core: min(t²/(2σ²), t/(2b)) ≤ s·t - s²σ²/2,
  -- equivalently -s·t + s²σ²/2 ≤ -min(t²/(2σ²), t/(2b))
  have hmin_ineq :
      min (t ^ 2 / (2 * σ ^ 2)) (t / (2 * b)) ≤ s * t - s ^ 2 * σ ^ 2 / 2 := by
    by_cases hcase : t / σ ^ 2 ≤ 1 / b
    · -- Case A (sub-Gaussian regime, t·b ≤ σ²): s = t/σ², exponent = t²/(2σ²)
      have hs_eq : s = t / σ ^ 2 := min_eq_left hcase
      rw [hs_eq]
      have hcompute :
          (t / σ ^ 2) * t - (t / σ ^ 2) ^ 2 * σ ^ 2 / 2 = t ^ 2 / (2 * σ ^ 2) := by
        field_simp
        ring
      rw [hcompute]
      exact min_le_left _ _
    · -- Case B (sub-exponential regime, t·b > σ²): s = 1/b, exponent ≥ t/(2b)
      push_neg at hcase
      have hs_eq : s = 1 / b := min_eq_right hcase.le
      rw [hs_eq]
      have hσb : σ ^ 2 < t * b := by
        have h1 := hcase
        rw [div_lt_div_iff₀ hb hσ2] at h1
        linarith
      have hcompute :
          (1 / b) * t - (1 / b) ^ 2 * σ ^ 2 / 2 = t / b - σ ^ 2 / (2 * b ^ 2) := by
        field_simp
      rw [hcompute]
      have hmin_le :
          min (t ^ 2 / (2 * σ ^ 2)) (t / (2 * b)) ≤ t / (2 * b) := min_le_right _ _
      have hbound : t / (2 * b) ≤ t / b - σ ^ 2 / (2 * b ^ 2) := by
        rw [le_sub_iff_add_le,
            div_add_div _ _ (by positivity : (2 * b : ℝ) ≠ 0)
              (by positivity : (2 * b ^ 2 : ℝ) ≠ 0),
            div_le_div_iff₀ (by positivity) hb]
        nlinarith [sq_nonneg σ, sq_nonneg b, hσb, hb.le]
      linarith
  linarith

end HasSubExpMGF

end Statlean.HDStats

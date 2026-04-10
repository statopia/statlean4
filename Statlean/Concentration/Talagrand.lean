import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Concentration/Talagrand

## Talagrand's concentration inequality (bounded differences version)

Also known as **McDiarmid's inequality**: if `f : Ω₁ × ⋯ × Ωₙ → ℝ` satisfies
the bounded differences condition (changing one coordinate changes `f` by at most `cᵢ`),
then for all `t > 0`:

  `P(f(X) - E[f(X)] ≥ t) ≤ exp(-2t² / ∑ cᵢ²)`

### Proof route
The proof uses the **Azuma-Hoeffding** method:
1. Define the Doob martingale `Mₖ = E[f | X₁,...,Xₖ]`
2. Show `|Mₖ - Mₖ₋₁| ≤ cₖ` a.s. (bounded differences)
3. Apply exp-moment + Markov (Hoeffding's lemma for bounded r.v.)

### Main results

* `bounded_differences` — the bounded differences condition
* `hoeffding_lemma` — exponential moment bound for bounded r.v.
* `mcdiarmid_upper` — one-sided McDiarmid: `P(f - Ef ≥ t) ≤ exp(-2t²/∑cᵢ²)`
* `mcdiarmid` — two-sided: `P(|f - Ef| ≥ t) ≤ 2·exp(-2t²/∑cᵢ²)`
-/

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Statlean.Concentration

variable {n : ℕ}

section Definitions

/-- A function `f` on a product space satisfies the **bounded differences condition**
with constants `c : Fin n → ℝ` if changing the `i`-th coordinate changes `f` by at most `cᵢ`.

Formally: for all `i`, for all `x, x'` differing only in coordinate `i`,
`|f(x) - f(x')| ≤ c i`. -/
def BoundedDifferences {α : Fin n → Type*}
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (x x' : ∀ j, α j),
    (∀ j, j ≠ i → x j = x' j) →
    |f x - f x'| ≤ c i

/-- The sum of squares of the bounded difference constants. -/
noncomputable def sumSqConstants (c : Fin n → ℝ) : ℝ :=
  ∑ i, c i ^ 2

end Definitions

section HoeffdingSublemmas

/-- The key analytic lemma for Hoeffding: for `p ∈ [0,1]` and any `h ∈ ℝ`,
  `-p·h + log(1 - p + p·exp(h)) ≤ h²/8`.

This is proved by showing the function `L(h) = -ph + log(1-p+pe^h)` satisfies
`L(0) = 0`, `L'(0) = 0`, and `L''(h) ≤ 1/4` for all `h`. -/
lemma hoeffding_cgf_bound (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    -p * h + Real.log (1 - p + p * Real.exp h) ≤ h ^ 2 / 8 := by
  -- Define L(x) = -p*x + log(1-p+p*exp x) and show L(h) ≤ h²/8.
  -- Strategy: L(0) = 0, L'(0) = 0, L''(x) = q(1-q) ≤ 1/4 where q = p*e^x/(1-p+p*e^x).
  -- Using MVT twice (once for each sign of h), we get L(h) ≤ h²/8.
  set L : ℝ → ℝ := fun x => -p * x + Real.log (1 - p + p * Real.exp x) with hL_def
  set L' : ℝ → ℝ := fun x => -p + p * Real.exp x / (1 - p + p * Real.exp x) with hL'_def
  -- Positivity of denominator u(x) = 1 - p + p * exp x > 0
  have u_pos : ∀ x : ℝ, 0 < 1 - p + p * Real.exp x := by
    intro x
    rcases eq_or_lt_of_le hp1 with hpeq | hplt
    · subst hpeq; simp; exact Real.exp_pos x
    · have := Real.exp_pos x; nlinarith
  -- Helper: derivative of u
  have hu_deriv : ∀ x : ℝ,
      HasDerivAt (fun y => 1 - p + p * Real.exp y) (p * Real.exp x) x := by
    intro x
    have h := (hasDerivAt_const x (1 - p)).add ((Real.hasDerivAt_exp x).const_mul p)
    convert h using 1; ring
  -- L(0) = 0
  have hL0 : L 0 = 0 := by
    simp [hL_def, Real.exp_zero]
  -- L'(0) = 0
  have hL'0 : L' 0 = 0 := by
    simp only [hL'_def, Real.exp_zero, mul_one]
    ring_nf
  -- HasDerivAt L (L' x) x
  have hL_deriv : ∀ x : ℝ, HasDerivAt L (L' x) x := by
    intro x
    have h1 : HasDerivAt (fun y => -p * y) (-p) x := by
      simpa using (hasDerivAt_id x).const_mul (-p)
    have hu := hu_deriv x
    have h3 : HasDerivAt (fun y => Real.log (1 - p + p * Real.exp y))
        (p * Real.exp x / (1 - p + p * Real.exp x)) x :=
      hu.log (u_pos x).ne'
    exact h1.add h3
  -- HasDerivAt L' (q*(1-q)) x
  have hL'_deriv : ∀ x : ℝ,
      HasDerivAt L'
        ((p * Real.exp x / (1 - p + p * Real.exp x)) *
          (1 - p * Real.exp x / (1 - p + p * Real.exp x))) x := by
    intro x
    have hnum : HasDerivAt (fun y => p * Real.exp y) (p * Real.exp x) x :=
      (Real.hasDerivAt_exp x).const_mul p
    have hu := hu_deriv x
    have hdiv : HasDerivAt (fun y => p * Real.exp y / (1 - p + p * Real.exp y))
        ((p * Real.exp x * (1 - p + p * Real.exp x) - p * Real.exp x * (p * Real.exp x))
          / (1 - p + p * Real.exp x) ^ 2) x :=
      hnum.div hu (u_pos x).ne'
    have hconst : HasDerivAt (fun _ : ℝ => (-p : ℝ)) 0 x := hasDerivAt_const x (-p)
    have hsum := hconst.add hdiv
    convert hsum using 1
    set u := 1 - p + p * Real.exp x with hu_def
    have hune : u ≠ 0 := (u_pos x).ne'
    field_simp
    ring
  -- q(1-q) ≤ 1/4 for any real q
  have hL''_bound : ∀ x : ℝ,
      (p * Real.exp x / (1 - p + p * Real.exp x)) *
        (1 - p * Real.exp x / (1 - p + p * Real.exp x)) ≤ 1/4 := by
    intro x
    set q := p * Real.exp x / (1 - p + p * Real.exp x)
    nlinarith [sq_nonneg (q - 1/2)]
  -- Continuity of L and L'
  have hL_cont : Continuous L :=
    continuous_iff_continuousAt.mpr fun x => (hL_deriv x).continuousAt
  have hL'_cont : Continuous L' :=
    continuous_iff_continuousAt.mpr fun x => (hL'_deriv x).continuousAt
  -- Case split on h
  rcases le_or_gt 0 h with hh_nn | hh_neg
  · -- Case h ≥ 0
    -- Step 1: L'(x) ≤ x/4 on [0, h]
    have hstep1 : ∀ x ∈ Set.Icc (0:ℝ) h, L' x ≤ x / 4 := by
      apply image_le_of_deriv_right_le_deriv_boundary (f := L')
        (f' := fun x =>
          (p * Real.exp x / (1 - p + p * Real.exp x)) *
            (1 - p * Real.exp x / (1 - p + p * Real.exp x)))
        hL'_cont.continuousOn
        (fun x _ => (hL'_deriv x).hasDerivWithinAt)
        (by rw [hL'0]; norm_num)
        ((continuous_id.div_const 4).continuousOn)
      · intro x _
        have hd : HasDerivAt (fun y : ℝ => y / 4) (1/4) x := by
          simpa using (hasDerivAt_id x).div_const 4
        exact hd.hasDerivWithinAt
      · intro x _; exact hL''_bound x
    -- Step 2: L(x) ≤ x²/8 on [0, h]
    have hstep2 : ∀ x ∈ Set.Icc (0:ℝ) h, L x ≤ x^2 / 8 := by
      apply image_le_of_deriv_right_le_deriv_boundary (f := L) (f' := L')
        hL_cont.continuousOn
        (fun x _ => (hL_deriv x).hasDerivWithinAt)
        (by rw [hL0]; positivity)
        (((continuous_pow 2).div_const 8).continuousOn)
      · intro x _
        have h1 : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h2 := h1.div_const 8
        have hd : HasDerivAt (fun y : ℝ => y^2 / 8) (x / 4) x := by
          convert h2 using 1; ring
        exact hd.hasDerivWithinAt
      · intro x hx; exact hstep1 x (Set.Ico_subset_Icc_self hx)
    have := hstep2 h (Set.right_mem_Icc.mpr hh_nn)
    simpa [hL_def] using this
  · -- Case h < 0: use reflection L̃(x) = L(-x)
    set k := -h with hk_def
    have hk_pos : 0 < k := by rw [hk_def]; linarith
    set M : ℝ → ℝ := fun x => L (-x) with hM_def
    set M' : ℝ → ℝ := fun x => -(L' (-x)) with hM'_def
    have hM0 : M 0 = 0 := by simp [hM_def, hL0]
    have hM'0 : M' 0 = 0 := by simp [hM'_def, hL'0]
    -- M'(x) via chain rule: d/dx L(-x) = L'(-x) * (-1) = -L'(-x)
    have hM_deriv : ∀ x : ℝ, HasDerivAt M (M' x) x := by
      intro x
      have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        simpa using (hasDerivAt_id x).neg
      have hcomp := (hL_deriv (-x)).comp x hneg
      -- hcomp : HasDerivAt (L ∘ Neg.neg) (L' (-x) * -1) x
      have hfun_eq : (L ∘ fun y => -y) = M := by
        ext y; simp [hM_def, Function.comp]
      have hval_eq : L' (-x) * (-1) = M' x := by simp [hM'_def]
      rw [hfun_eq, hval_eq] at hcomp
      exact hcomp
    -- (M')'(x) = L''(-x) (chain rule: d/dx (-L'(-x)) = -L''(-x)*(-1) = L''(-x))
    have hM'_deriv : ∀ x : ℝ,
        HasDerivAt M'
          ((p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) *
            (1 - p * Real.exp (-x) / (1 - p + p * Real.exp (-x)))) x := by
      intro x
      have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        simpa using (hasDerivAt_id x).neg
      have hcomp := (hL'_deriv (-x)).comp x hneg
      -- hcomp : HasDerivAt (L' ∘ Neg.neg) (q(1-q)|_{-x} * -1) x
      have hcomp_neg := hcomp.neg
      -- hcomp_neg : HasDerivAt (-(L' ∘ Neg.neg)) (-(q(1-q)|_{-x} * -1)) x
      have hfun_eq : (-(L' ∘ fun y => -y)) = M' := by
        ext y; simp [hM'_def, Function.comp]
      have hval_eq : -(
          (p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) *
            (1 - p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) * (-1)) =
          (p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) *
            (1 - p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) := by ring
      rw [hfun_eq, hval_eq] at hcomp_neg
      exact hcomp_neg
    have hM_cont : Continuous M :=
      continuous_iff_continuousAt.mpr fun x => (hM_deriv x).continuousAt
    have hM'_cont : Continuous M' :=
      continuous_iff_continuousAt.mpr fun x => (hM'_deriv x).continuousAt
    -- Step 1: M'(x) ≤ x/4 on [0, k]
    have hstep1M : ∀ x ∈ Set.Icc (0:ℝ) k, M' x ≤ x / 4 := by
      apply image_le_of_deriv_right_le_deriv_boundary (f := M')
        (f' := fun x =>
          (p * Real.exp (-x) / (1 - p + p * Real.exp (-x))) *
            (1 - p * Real.exp (-x) / (1 - p + p * Real.exp (-x))))
        hM'_cont.continuousOn
        (fun x _ => (hM'_deriv x).hasDerivWithinAt)
        (by rw [hM'0]; norm_num)
        ((continuous_id.div_const 4).continuousOn)
      · intro x _
        have hd : HasDerivAt (fun y : ℝ => y / 4) (1/4) x := by
          simpa using (hasDerivAt_id x).div_const 4
        exact hd.hasDerivWithinAt
      · intro x _; exact hL''_bound (-x)
    -- Step 2: M(x) ≤ x²/8 on [0, k]
    have hstep2M : ∀ x ∈ Set.Icc (0:ℝ) k, M x ≤ x^2 / 8 := by
      apply image_le_of_deriv_right_le_deriv_boundary (f := M) (f' := M')
        hM_cont.continuousOn
        (fun x _ => (hM_deriv x).hasDerivWithinAt)
        (by rw [hM0]; positivity)
        (((continuous_pow 2).div_const 8).continuousOn)
      · intro x _
        have h1 : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h2 := h1.div_const 8
        have hd : HasDerivAt (fun y : ℝ => y^2 / 8) (x / 4) x := by
          convert h2 using 1; ring
        exact hd.hasDerivWithinAt
      · intro x hx; exact hstep1M x (Set.Ico_subset_Icc_self hx)
    have hMk := hstep2M k (Set.right_mem_Icc.mpr hk_pos.le)
    -- M k = L (-k) = L h and k^2 = h^2
    have hMk_eq : M k = L h := by simp [hM_def, hk_def]
    have hk_sq : k^2 = h^2 := by rw [hk_def]; ring
    rw [hMk_eq, hk_sq] at hMk
    simpa [hL_def] using hMk

/-- The weighted exponential bound for Hoeffding's lemma:
for `a ≤ 0 ≤ b` with `a < b` and `s > 0`,
  `b/(b-a) · exp(sa) + (-a)/(b-a) · exp(sb) ≤ exp(s²(b-a)²/8)`.

This follows from `hoeffding_cgf_bound` with `p = -a/(b-a)`, `h = s(b-a)`. -/
lemma hoeffding_weighted_exp_bound {a b s : ℝ} (hab : a < b) (hs : 0 < s)
    (ha : a ≤ 0) (hb : 0 ≤ b) :
    b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  set p := -a / (b - a) with hp_def
  set h := s * (b - a) with h_def
  have hba : 0 < b - a := sub_pos.mpr hab
  have hba_ne : b - a ≠ 0 := ne_of_gt hba
  have hp0 : 0 ≤ p := by
    rw [hp_def]; exact div_nonneg (neg_nonneg.mpr ha) hba.le
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one hba]; linarith
  have hh_pos : 0 < h := mul_pos hs hba
  have u_pos : 0 < 1 - p + p * Real.exp h := by
    have h1mp_nn : 0 ≤ 1 - p := by linarith
    have hepos : 0 < Real.exp h := Real.exp_pos _
    by_cases hp_zero : p = 0
    · simp [hp_zero]
    · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp_zero)
      have : 0 < p * Real.exp h := mul_pos hp_pos hepos
      linarith
  have hcgf := hoeffding_cgf_bound p hp0 hp1 h
  have hlog_le : Real.log (1 - p + p * Real.exp h) ≤ p * h + h ^ 2 / 8 := by linarith
  have hexp_le : 1 - p + p * Real.exp h ≤ Real.exp (p * h + h ^ 2 / 8) :=
    (Real.log_le_iff_le_exp u_pos).mp hlog_le
  have hesa_pos : 0 < Real.exp (s * a) := Real.exp_pos _
  -- Key identity: exp(s*a) * exp(s*(b-a)) = exp(s*b)
  have hexp_eq : Real.exp (s * a) * Real.exp (s * (b - a)) = Real.exp (s * b) := by
    rw [← Real.exp_add]; congr 1; ring
  -- Expand LHS = exp(s*a) * (1 - p + p * exp h)
  have lhs_eq :
      b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) =
      Real.exp (s * a) * (1 - p + p * Real.exp h) := by
    have h1mp : 1 - p = b / (b - a) := by
      rw [hp_def]; field_simp; ring
    rw [← h1mp, hp_def, h_def, ← hexp_eq]
    field_simp
  -- RHS simplification: exp(s*a) * exp(p*h + h²/8) = exp(s²(b-a)²/8)
  have rhs_eq : Real.exp (s * a) * Real.exp (p * h + h ^ 2 / 8) =
                Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
    rw [← Real.exp_add]
    congr 1
    rw [hp_def, h_def]
    field_simp
    ring
  calc b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b)
      = Real.exp (s * a) * (1 - p + p * Real.exp h) := lhs_eq
    _ ≤ Real.exp (s * a) * Real.exp (p * h + h ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hexp_le hesa_pos.le
    _ = Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := rhs_eq

end HoeffdingSublemmas

section HoeffdingLemma

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma integrable_of_ae_bound [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable X μ :=
  Integrable.of_bound hX_meas.aestronglyMeasurable (max |a| |b|)
    (by filter_upwards [hlo, hhi] with ω h1 h2; exact_mod_cast abs_le_max_abs_abs h1 h2)

/-- **Hoeffding's lemma (convexity step)**: If `X` is bounded in `[a,b]` a.s. with `a < b`
and `E[X] = 0`, then `E[exp(sX)] ≤ b/(b-a)·exp(sa) + (-a)/(b-a)·exp(sb)`.

This follows from convexity of `exp` and linearity of expectation. -/
lemma hoeffding_convexity [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b)
    (hab : a < b)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤
      b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hba_ne : b - a ≠ 0 := ne_of_gt hba
  have hX_int : Integrable X μ := integrable_of_ae_bound hX_meas hlo hhi
  have h_pointwise : ∀ᵐ ω ∂μ,
      Real.exp (s * X ω) ≤
        (b - X ω) / (b - a) * Real.exp (s * a) +
          (X ω - a) / (b - a) * Real.exp (s * b) := by
    filter_upwards [hlo, hhi] with ω hω_lo hω_hi
    set p : ℝ := (b - X ω) / (b - a) with hp_def
    set q : ℝ := (X ω - a) / (b - a) with hq_def
    have hp_nn : 0 ≤ p := div_nonneg (by linarith) hba.le
    have hq_nn : 0 ≤ q := div_nonneg (by linarith) hba.le
    have hpq : p + q = 1 := by
      have h1 : (b - X ω) / (b - a) + (X ω - a) / (b - a) = (b - a) / (b - a) := by
        rw [← add_div]; congr 1; ring
      have h2 : (b - a) / (b - a) = 1 := div_self hba_ne
      change (b - X ω) / (b - a) + (X ω - a) / (b - a) = 1
      rw [h1, h2]
    have hx_eq : s * X ω = p • (s * a) + q • (s * b) := by
      change s * X ω = (b - X ω) / (b - a) * (s * a) + (X ω - a) / (b - a) * (s * b)
      field_simp
      ring
    have h_conv := convexOn_exp.2 (Set.mem_univ (s * a)) (Set.mem_univ (s * b))
      hp_nn hq_nn hpq
    rw [hx_eq]
    simpa [smul_eq_mul] using h_conv
  have h_exp_meas : Measurable (fun ω => Real.exp (s * X ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hX_meas)
  have h_exp_bound : ∀ᵐ ω ∂μ, ‖Real.exp (s * X ω)‖ ≤ Real.exp (s * b) := by
    filter_upwards [hhi] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_exp_int : Integrable (fun ω => Real.exp (s * X ω)) μ :=
    Integrable.of_bound h_exp_meas.aestronglyMeasurable (Real.exp (s * b)) h_exp_bound
  have h_term1_int : Integrable (fun ω => (b - X ω) / (b - a)) μ := by
    have h1 : Integrable (fun ω => b - X ω) μ := (integrable_const b).sub hX_int
    exact h1.div_const (b - a)
  have h_term2_int : Integrable (fun ω => (X ω - a) / (b - a)) μ := by
    have h1 : Integrable (fun ω => X ω - a) μ := hX_int.sub (integrable_const a)
    exact h1.div_const (b - a)
  calc ∫ ω, Real.exp (s * X ω) ∂μ
      ≤ ∫ ω, (b - X ω) / (b - a) * Real.exp (s * a) +
          (X ω - a) / (b - a) * Real.exp (s * b) ∂μ :=
        integral_mono_ae h_exp_int
          ((h_term1_int.mul_const _).add (h_term2_int.mul_const _)) h_pointwise
    _ = b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) := by
        rw [integral_add (h_term1_int.mul_const _) (h_term2_int.mul_const _),
            integral_mul_const, integral_mul_const,
            integral_div, integral_div,
            integral_sub (integrable_const b) hX_int,
            integral_sub hX_int (integrable_const a),
            integral_const, integral_const, hmean]
        simp

/-- **Hoeffding's lemma**: If `X` is a random variable with `E[X] = 0` and `a ≤ X ≤ b` a.s.,
then `E[exp(sX)] ≤ exp(s²(b-a)²/8)` for all `s > 0`.

This is the key exponential moment bound for the Azuma-Hoeffding method.
The proof proceeds by:
1. Case `a = b`: `X = 0` a.s., so `E[exp(sX)] = 1 ≤ exp(0)`.
2. Case `a < b`: By convexity of `exp`, `E[exp(sX)] ≤ b/(b-a)·exp(sa) + (-a)/(b-a)·exp(sb)`.
   Then the CGF bound `-p·h + log(1-p+p·exp(h)) ≤ h²/8` gives the result. -/
theorem hoeffding_lemma [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {a b : ℝ}
    (hX_meas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hlo : ∀ᵐ ω ∂μ, a ≤ X ω)
    (hhi : ∀ᵐ ω ∂μ, X ω ≤ b)
    (s : ℝ) (hs : 0 < s) :
    ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  -- First establish a ≤ b from the ae bounds
  have hab_le : a ≤ b := by
    by_contra h; push_neg at h
    have : ∀ᵐ ω ∂μ, False := by
      filter_upwards [hlo, hhi] with ω h1 h2; linarith
    rw [Filter.eventually_false_iff_eq_bot] at this
    exact (inferInstance : (ae μ).NeBot).ne this
  rcases eq_or_lt_of_le hab_le with hab | hab
  · -- Case a = b: X = a a.s., a = 0
    have hX_eq : ∀ᵐ ω ∂μ, X ω = a := by
      filter_upwards [hlo, hhi] with ω h1 h2; linarith
    have ha0 : a = 0 := by
      have := integral_congr_ae hX_eq
      rw [hmean] at this; simp [integral_const] at this; linarith
    have hexp1 : ∫ ω, Real.exp (s * X ω) ∂μ = 1 := by
      have := integral_congr_ae (show ∀ᵐ ω ∂μ, Real.exp (s * X ω) = 1 by
        filter_upwards [hX_eq] with ω hω; rw [hω, ha0, mul_zero, Real.exp_zero])
      rw [this, integral_const, smul_eq_mul, mul_one]; simp
    rw [hexp1, hab]; simp [_root_.sub_self]
  · -- Case a < b: use convexity + weighted exp bound
    have ha0 : a ≤ 0 := by
      by_contra h; push_neg at h
      have : (0 : ℝ) < ∫ ω, X ω ∂μ :=
        lt_of_lt_of_le h (by
          calc a = ∫ _, a ∂μ := by simp [integral_const]
            _ ≤ ∫ ω, X ω ∂μ := integral_mono_ae (integrable_const a)
                  (integrable_of_ae_bound hX_meas hlo hhi) hlo)
      linarith
    have hb0 : 0 ≤ b := by
      by_contra h; push_neg at h
      have : ∫ ω, X ω ∂μ < 0 :=
        lt_of_le_of_lt (by
          calc ∫ ω, X ω ∂μ ≤ ∫ _, b ∂μ :=
                integral_mono_ae (integrable_of_ae_bound hX_meas hlo hhi)
                  (integrable_const b) hhi
            _ = b := by simp [integral_const]) h
      linarith
    calc ∫ ω, Real.exp (s * X ω) ∂μ
        ≤ b / (b - a) * Real.exp (s * a) + (-a) / (b - a) * Real.exp (s * b) :=
          hoeffding_convexity hX_meas hmean hlo hhi hab s hs
      _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) :=
          hoeffding_weighted_exp_bound hab hs ha0 hb0

end HoeffdingLemma

section McDiarmid

variable {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
variable {μ : ∀ i, Measure (α i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- **McDiarmid's inequality (upper tail)**: If `f` satisfies bounded differences
with constants `c`, and `X₁,...,Xₙ` are independent, then
`P(f(X) - E[f(X)] ≥ t) ≤ exp(-2t² / ∑cᵢ²)`. -/
theorem mcdiarmid_upper
    {f : (∀ i, α i) → ℝ} {c : Fin n → ℝ}
    (hf_meas : Measurable f)
    (hbd : BoundedDifferences f c)
    (hc_nn : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < sumSqConstants c)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ {x | t ≤ f x - ∫ x', f x' ∂(Measure.pi μ)}).toReal ≤
      Real.exp (-2 * t ^ 2 / sumSqConstants c) := by
  sorry

/-- **McDiarmid's inequality (two-sided)**: If `f` satisfies bounded differences,
`P(|f(X) - E[f(X)]| ≥ t) ≤ 2·exp(-2t² / ∑cᵢ²)`. -/
theorem mcdiarmid
    {f : (∀ i, α i) → ℝ} {c : Fin n → ℝ}
    (hf_meas : Measurable f)
    (hbd : BoundedDifferences f c)
    (hc_nn : ∀ i, 0 ≤ c i)
    (hc_pos : 0 < sumSqConstants c)
    (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ {x | t ≤ |f x - ∫ x', f x' ∂(Measure.pi μ)|}).toReal ≤
      2 * Real.exp (-2 * t ^ 2 / sumSqConstants c) := by
  sorry

end McDiarmid

end Statlean.Concentration

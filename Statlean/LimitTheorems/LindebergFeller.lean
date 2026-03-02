/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor
import Statlean.LimitTheorems.Levy

/-!
# Lindeberg-Feller Central Limit Theorem

The **Lindeberg-Feller CLT** (Shao, Thm 1.6) for triangular arrays of row-independent,
mean-zero, L² random variables satisfying the Lindeberg condition.

## Main results

- `LindebergSum`: the Lindeberg truncated variance sum
- `charfun_indep_sum_eq_prod`: charfun factorization for independent (non-iid) sums
- `lindeberg_feller_clt`: the main theorem

## References

* Shao, Jun. *Mathematical Statistics*, Theorem 1.6.
-/

open MeasureTheory ProbabilityTheory Filter Topology MeasureTheory.ProbabilityMeasure
open Statlean.LimitTheorems Statlean.BerryEsseen

noncomputable section

namespace Statlean.LimitTheorems.LindebergFeller

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## Definitions -/

/-- Lindeberg truncated variance sum:
    `L(ε) = (1/s²) ∑_j ∫_{|X_j| > εs} X_j² dμ`.
    The Lindeberg condition requires `L_n(ε) → 0` for every `ε > 0`. -/
def LindebergSum (μ : Measure Ω)
    {k : ℕ} (X : Fin k → Ω → ℝ) (s ε : ℝ) : ℝ :=
  (1 / s ^ 2) * ∑ j, ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ

/-! ## Charfun product factorization for independent sums -/

/-- Charfun of standardized sum equals product of individual charfuns.
    Generalization of `charfun_iid_sum_eq_prod`: arbitrary denominator `c > 0`,
    no IdentDistrib assumption. -/
lemma charfun_indep_sum_eq_prod {k : ℕ} (_hk : 0 < k)
    {X : Fin k → Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hm : ∀ j, Measurable (X j))
    (hindep : iIndepFun (m := fun _ => inferInstance) X μ) (t : ℝ) :
    charFun (μ.map (fun ω => (∑ j, X j ω) / c)) t =
      ∏ j : Fin k, charFun (μ.map (X j)) (t / c) := by
  have hS_eq : (fun ω => (∑ j : Fin k, X j ω) / c) =
      (fun x => c⁻¹ * x) ∘ (fun ω => ∑ j : Fin k, X j ω) := by
    ext ω; simp [div_eq_inv_mul]
  have hm_sum : Measurable (fun ω => ∑ j : Fin k, X j ω) :=
    Finset.measurable_sum Finset.univ (fun i _ => hm i)
  have hm_scale : Measurable (fun x : ℝ => c⁻¹ * x) := measurable_const_mul _
  rw [hS_eq, ← Measure.map_map hm_scale hm_sum, charFun_map_mul, inv_mul_eq_div]
  set s := t / c
  suffices h : ∀ (S : Finset (Fin k)),
      charFun (μ.map (fun ω => ∑ i ∈ S, X i ω)) s =
        ∏ i ∈ S, charFun (μ.map (X i)) s by
    convert h Finset.univ using 2
  intro S
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    rw [Measure.map_const, measure_univ, one_smul, charFun_dirac]; simp
  | @insert a fs ha ih =>
    rw [show insert a fs = Finset.cons a fs ha from (Finset.cons_eq_insert a fs ha).symm,
        Finset.prod_cons]
    have sum_eq : (fun ω => ∑ i ∈ Finset.cons a fs ha, X i ω) =
        (fun ω => X a ω + ∑ i ∈ fs, X i ω) := by ext ω; rw [Finset.sum_cons]
    rw [sum_eq]
    have hindep_pair : IndepFun (X a) (∑ i ∈ fs, X i) μ :=
      (hindep.indepFun_finset_sum_of_notMem (fun i => hm i) ha).symm
    have pi_sum_eq : (fun ω => ∑ i ∈ fs, X i ω) = ∑ i ∈ fs, X i := by
      ext ω; simp [Finset.sum_apply]
    have pi_add_eq : (fun ω => X a ω + ∑ i ∈ fs, X i ω) = X a + ∑ i ∈ fs, X i := by
      ext ω; simp [Pi.add_apply, Finset.sum_apply]
    rw [pi_add_eq,
        congr_fun (IndepFun.charFun_map_add_eq_mul (hm a).aemeasurable
          (Finset.aemeasurable_sum fs (fun i _ => (hm i).aemeasurable)) hindep_pair) s,
        Pi.mul_apply, ← pi_sum_eq, ih]

/-! ## Analytic bounds -/

/-- `|e^{iθ} - (1+iθ-θ²/2)| ≤ 4θ²` for all θ. Uses the cubic bound for |θ| ≤ 1
    and triangle inequality for |θ| > 1. -/
private lemma norm_cexp_sub_quadratic_le_sq (θ : ℝ) :
    ‖Complex.exp (↑θ * Complex.I) -
      ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖ ≤ 4 * θ ^ 2 := by
  by_cases hθ : |θ| ≤ 1
  · -- |θ| ≤ 1: from cubic bound, 4|θ|³ ≤ 4θ² since |θ|³ ≤ θ²
    have h1 : |θ| ^ 3 ≤ θ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_of_le_one (abs_nonneg _) hθ (by norm_num)
    calc ‖_‖ ≤ 4 * |θ| ^ 3 := norm_cexp_sub_quadratic_le θ
      _ ≤ 4 * θ ^ 2 := by linarith
  · -- |θ| > 1: triangle inequality
    push_neg at hθ
    have hθ_norm_I : ‖↑θ * Complex.I‖ = |θ| := by
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have hθ_sq_norm : ‖(↑θ : ℂ) ^ 2 / 2‖ = θ ^ 2 / 2 := by
      simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc ‖Complex.exp (↑θ * Complex.I) -
          ((1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2)‖
        ≤ ‖Complex.exp (↑θ * Complex.I)‖ +
          ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |θ| + θ ^ 2 / 2) := by
          gcongr
          · simp [Complex.norm_exp_ofReal_mul_I]
          · calc ‖(1 : ℂ) + ↑θ * Complex.I - (↑θ : ℂ) ^ 2 / 2‖
                ≤ ‖(1 : ℂ) + ↑θ * Complex.I‖ + ‖(↑θ : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
              _ ≤ (‖(1 : ℂ)‖ + ‖↑θ * Complex.I‖) + ‖(↑θ : ℂ) ^ 2 / 2‖ := by
                  gcongr; exact norm_add_le _ _
              _ = 1 + |θ| + θ ^ 2 / 2 := by
                  rw [norm_one, hθ_norm_I, hθ_sq_norm]
      _ ≤ 4 * θ ^ 2 := by nlinarith [sq_abs θ, sq_nonneg (|θ| - 1)]

/-- Per-term charfun error bound used in `sum_charfun_errors_le`. -/
private lemma charfun_error_le_j
    {X : Ω → ℝ} {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε)
    (hm : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hL2 : MemLp X 2 μ)
    (t : ℝ) :
    ‖charFun (μ.map X) (t / s) -
      ((1 : ℂ) - (((∫ ω, (X ω) ^ 2 ∂μ) * t ^ 2 / (2 * s ^ 2) : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * ε / s ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ +
      4 * t ^ 2 / s ^ 2 * ∫ ω in {ω | ε * s < |X ω|}, (X ω) ^ 2 ∂μ := by
  have hs_small : MeasurableSet {ω : Ω | |X ω| ≤ ε * s} :=
    measurableSet_le hm.abs measurable_const
  have hX2_int : Integrable (fun ω => (X ω) ^ 2) μ := hL2.integrable_sq
  have hX_int : Integrable X μ :=
    (hL2.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).integrable (by norm_num)
  -- charFun expressed as integral over Ω
  have char_eq : charFun (μ.map X) (t / s) =
      ∫ ω, Complex.exp (↑(t / s * X ω) * Complex.I) ∂μ := by
    rw [charFun_apply_real]
    have key : ∫ x : ℝ, Complex.exp (↑(t / s) * ↑x * Complex.I) ∂(μ.map X) =
        ∫ ω, Complex.exp (↑(t / s) * ↑(X ω) * Complex.I) ∂μ :=
      integral_map_of_stronglyMeasurable hm
        ((Complex.continuous_exp.comp (by fun_prop :
          Continuous (fun x : ℝ => (↑(t/s) : ℂ) * ↑x * Complex.I))).stronglyMeasurable)
    rw [key]; congr 1; ext ω; push_cast; ring
  -- Integrability of complex terms
  have hI_tXI : Integrable (fun ω => (↑(t / s * X ω) * Complex.I : ℂ)) μ := by
    rw [show (fun ω => (↑(t / s * X ω) * Complex.I : ℂ)) =
        fun ω => ((↑(t / s) * Complex.I : ℂ) * ↑(X ω)) from by ext ω; push_cast; ring]
    exact hX_int.ofReal.const_mul _
  have hI_sq : Integrable (fun ω => ((↑(t / s * X ω) : ℂ) ^ 2 / 2 : ℂ)) μ := by
    rw [show (fun ω => ((↑(t / s * X ω) : ℂ) ^ 2 / 2 : ℂ)) =
        fun ω => ((↑(t / s) : ℂ) ^ 2 / 2 * ↑((X ω) ^ 2)) from by ext ω; push_cast; ring]
    exact hX2_int.ofReal.const_mul _
  have hI_quad : Integrable (fun ω =>
      (1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2) μ :=
    ((integrable_const _).add hI_tXI).sub hI_sq
  -- Quadratic approximation as integral
  have int_tXI : ∫ ω, (↑(t / s * X ω) * Complex.I : ℂ) ∂μ = 0 := by
    rw [show (fun ω => (↑(t / s * X ω) * Complex.I : ℂ)) =
        fun ω => ((↑(t / s) * Complex.I : ℂ) * ↑(X ω)) from by ext ω; push_cast; ring,
      integral_const_mul, integral_complex_ofReal, hmean]; simp
  have int_sq : ∫ ω, ((↑(t / s * X ω) : ℂ) ^ 2 / 2 : ℂ) ∂μ =
      ((↑(t / s) : ℂ) ^ 2 / 2 * ↑(∫ ω, (X ω) ^ 2 ∂μ) : ℂ) := by
    rw [show (fun ω => ((↑(t / s * X ω) : ℂ) ^ 2 / 2 : ℂ)) =
        fun ω => ((↑(t / s) : ℂ) ^ 2 / 2 * ↑((X ω) ^ 2)) from by ext ω; push_cast; ring,
      integral_const_mul, integral_complex_ofReal]
  have quad_eq : ((1 : ℂ) - (((∫ ω, (X ω) ^ 2 ∂μ) * t ^ 2 / (2 * s ^ 2) : ℝ) : ℂ)) =
      ∫ ω, ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2) ∂μ := by
    have h_split : ∫ ω, ((1 : ℂ) + ↑(t / s * X ω) * Complex.I -
        (↑(t / s * X ω) : ℂ) ^ 2 / 2) ∂μ =
        (∫ _ω : Ω, (1 : ℂ) ∂μ + ∫ ω, (↑(t / s * X ω) * Complex.I : ℂ) ∂μ) -
        ∫ ω, ((↑(t / s * X ω) : ℂ) ^ 2 / 2) ∂μ := by
      rw [← integral_add (integrable_const _) hI_tXI]
      exact integral_sub ((integrable_const _).add hI_tXI) hI_sq
    rw [h_split, int_tXI, int_sq, integral_const, probReal_univ, one_smul]
    push_cast; ring
  -- Integrable norm of error (bounded by quadratic)
  have hI_exp : Integrable (fun ω => Complex.exp (↑(t / s * X ω) * Complex.I)) μ :=
    Integrable.mono' (integrable_const (1 : ℝ))
      (((Complex.measurable_ofReal.comp (hm.const_mul (t/s))).mul_const
        Complex.I).cexp.aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  have hI_err_norm : Integrable
      (fun ω => ‖Complex.exp (↑(t / s * X ω) * Complex.I) -
        ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)‖) μ :=
    Integrable.mono' (hX2_int.const_mul (4 * (t / s) ^ 2))
      (hI_exp.sub hI_quad).norm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc ‖Complex.exp (↑(t / s * X ω) * Complex.I) -
              ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)‖
            ≤ 4 * (t / s * X ω) ^ 2 := by
                have h := norm_cexp_sub_quadratic_le_sq (t / s * X ω)
                convert h using 2 <;> push_cast <;> ring
          _ = 4 * (t / s) ^ 2 * (X ω) ^ 2 := by ring)
  -- Rewrite and split integral
  rw [char_eq, quad_eq]
  calc ‖∫ ω, Complex.exp (↑(t / s * X ω) * Complex.I) ∂μ -
        ∫ ω, ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2) ∂μ‖
      = ‖∫ ω, (Complex.exp (↑(t / s * X ω) * Complex.I) -
          ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)) ∂μ‖ := by
        rw [integral_sub hI_exp hI_quad]
    _ ≤ ∫ ω, ‖Complex.exp (↑(t / s * X ω) * Complex.I) -
          ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ ω in {ω | |X ω| ≤ ε * s}, ‖_‖ ∂μ +
          ∫ ω in {ω | ε * s < |X ω|}, ‖_‖ ∂μ := by
        rw [show {ω : Ω | ε * s < |X ω|} = {ω | |X ω| ≤ ε * s}ᶜ from by
          ext ω; simp [not_le], ← integral_add_compl hs_small hI_err_norm]
    _ ≤ (4 * |t| ^ 3 * ε / s ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ) +
          (4 * t ^ 2 / s ^ 2 * ∫ ω in {ω | ε * s < |X ω|}, (X ω) ^ 2 ∂μ) := by
        gcongr
        · -- Small set: cubic bound, |X|³ ≤ εs·X² on {|X| ≤ εs}
          calc ∫ ω in {ω | |X ω| ≤ ε * s}, ‖_‖ ∂μ
              ≤ ∫ ω in {ω | |X ω| ≤ ε * s}, 4 * |t| ^ 3 * ε / s ^ 2 * (X ω) ^ 2 ∂μ := by
                apply setIntegral_mono_on hI_err_norm.integrableOn
                  ((hX2_int.const_mul _).integrableOn) hs_small
                intro ω hω
                simp only [Set.mem_setOf_eq] at hω
                change ‖Complex.exp (↑(t / s * X ω) * Complex.I) -
                    ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)‖
                    ≤ 4 * |t| ^ 3 * ε / s ^ 2 * (X ω) ^ 2
                calc ‖_‖ ≤ 4 * |t / s * X ω| ^ 3 := by
                        have h := norm_cexp_sub_quadratic_le (t / s * X ω)
                        convert h using 2 <;> push_cast <;> ring
                  _ = 4 * |t| ^ 3 / s ^ 3 * |X ω| ^ 3 := by
                      rw [abs_mul, abs_div]; simp only [abs_of_pos hs]; ring
                  _ ≤ 4 * |t| ^ 3 / s ^ 3 * (ε * s * (X ω) ^ 2) := by
                      gcongr
                      calc |X ω| ^ 3 = |X ω| ^ 2 * |X ω| := by ring
                        _ = (X ω) ^ 2 * |X ω| := by rw [sq_abs]
                        _ ≤ (X ω) ^ 2 * (ε * s) := by gcongr
                        _ = ε * s * (X ω) ^ 2 := by ring
                  _ = 4 * |t| ^ 3 * ε / s ^ 2 * (X ω) ^ 2 := by field_simp
            _ ≤ 4 * |t| ^ 3 * ε / s ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
                rw [integral_const_mul]
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact setIntegral_le_integral hX2_int (ae_of_all _ fun ω => sq_nonneg _)
        · -- Large set: quadratic bound
          rw [← integral_const_mul]
          apply setIntegral_mono hI_err_norm.integrableOn
              ((hX2_int.const_mul (4 * t ^ 2 / s ^ 2)).integrableOn)
          intro ω
          change ‖Complex.exp (↑(t / s * X ω) * Complex.I) -
              ((1 : ℂ) + ↑(t / s * X ω) * Complex.I - (↑(t / s * X ω) : ℂ) ^ 2 / 2)‖
              ≤ 4 * t ^ 2 / s ^ 2 * (X ω) ^ 2
          have h := norm_cexp_sub_quadratic_le_sq (t / s * X ω)
          calc ‖_‖ ≤ 4 * (t / s * X ω) ^ 2 := by convert h using 2 <;> push_cast <;> ring
            _ = 4 * t ^ 2 / s ^ 2 * (X ω) ^ 2 := by field_simp

/-- Sum of individual charfun-vs-quadratic errors is bounded by
    `4|t|³ε + 4t²·LindebergSum(ε)`. This is the core Lindeberg truncation bound. -/
private lemma sum_charfun_errors_le
    {k : ℕ} {X : Fin k → Ω → ℝ} {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε)
    (hm : ∀ j, Measurable (X j))
    (hmean : ∀ j, ∫ ω, X j ω ∂μ = 0)
    (hL2 : ∀ j, MemLp (X j) 2 μ)
    (hvar_sum : ∑ j, ∫ ω, (X j ω) ^ 2 ∂μ = s ^ 2)
    (t : ℝ) :
    ∑ j : Fin k, ‖charFun (μ.map (X j)) (t / s) -
      ((1 : ℂ) - (((∫ ω, (X j ω) ^ 2 ∂μ) * t ^ 2 / (2 * s ^ 2) : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * ε + 4 * t ^ 2 * LindebergSum μ X s ε := by
  -- Apply per-term bound and collect
  have per_j : ∀ j : Fin k, ‖charFun (μ.map (X j)) (t / s) -
      ((1 : ℂ) - (((∫ ω, (X j ω) ^ 2 ∂μ) * t ^ 2 / (2 * s ^ 2) : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * ε / s ^ 2 * ∫ ω, (X j ω) ^ 2 ∂μ +
      4 * t ^ 2 / s ^ 2 * ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ :=
    fun j => charfun_error_le_j hs hε (hm j) (hmean j) (hL2 j) t
  calc ∑ j : Fin k, ‖_‖
      ≤ ∑ j : Fin k, (4 * |t| ^ 3 * ε / s ^ 2 * ∫ ω, (X j ω) ^ 2 ∂μ +
          4 * t ^ 2 / s ^ 2 * ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ) :=
        Finset.sum_le_sum (fun j _ => per_j j)
    _ = 4 * |t| ^ 3 * ε / s ^ 2 * ∑ j, ∫ ω, (X j ω) ^ 2 ∂μ +
          4 * t ^ 2 / s ^ 2 * ∑ j, ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 4 * |t| ^ 3 * ε + 4 * t ^ 2 * LindebergSum μ X s ε := by
        rw [hvar_sum, LindebergSum]
        field_simp

/-- Each per-index variance ratio is bounded by ε² + LindebergSum(ε).
    Key step: split σ_j² = ∫_small X_j² + ∫_large X_j²,
    bound small by ε²s² (since |X_j| ≤ εs on the small set),
    bound large by the full LindebergSum (positivity + Finset.single_le_sum). -/
private lemma var_ratio_le_lindeberg
    {k : ℕ} {X : Fin k → Ω → ℝ} {s : ℝ} (hs : 0 < s)
    (hL2 : ∀ j, MemLp (X j) 2 μ) (j : Fin k) (ε : ℝ) :
    (∫ ω, (X j ω) ^ 2 ∂μ) / s ^ 2 ≤ ε ^ 2 + LindebergSum μ X s ε := by
  unfold LindebergSum
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
  have hs2pos : 0 < s ^ 2 := pow_pos hs 2
  -- Split σ_j² = ∫_small X_j² + ∫_large X_j²
  have hsplit : ∫ ω, (X j ω) ^ 2 ∂μ =
      ∫ ω in {ω | |X j ω| ≤ ε * s}, (X j ω) ^ 2 ∂μ +
      ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ := by
    have hcompl : {ω : Ω | |X j ω| ≤ ε * s}ᶜ = {ω | ε * s < |X j ω|} := by
      ext ω; simp [not_le]
    rw [← hcompl]
    exact (integral_add_compl₀
      ((hL2 j).aestronglyMeasurable.norm.nullMeasurableSet_le aestronglyMeasurable_const)
      (hL2 j).integrable_sq).symm
  -- Small set: ∫_{|X_j|≤εs} X_j² ≤ ε²s²  (since X_j² ≤ ε²s² on the set)
  have hsmall : ∫ ω in {ω | |X j ω| ≤ ε * s}, (X j ω) ^ 2 ∂μ ≤ ε ^ 2 * s ^ 2 := by
    have hbound : (fun ω => (X j ω) ^ 2) ≤ᶠ[ae (μ.restrict {ω | |X j ω| ≤ ε * s})]
        fun _ => ε ^ 2 * s ^ 2 := by
      filter_upwards [ae_restrict_mem₀ ((hL2 j).aestronglyMeasurable.norm.nullMeasurableSet_le
        aestronglyMeasurable_const)]
      intro ω hω
      calc (X j ω) ^ 2 = |X j ω| ^ 2 := (sq_abs _).symm
        _ ≤ (ε * s) ^ 2 := by
            apply sq_le_sq'; linarith [abs_nonneg (X j ω)]; exact hω
        _ = ε ^ 2 * s ^ 2 := by ring
    calc ∫ ω in {ω | |X j ω| ≤ ε * s}, (X j ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | |X j ω| ≤ ε * s}, ε ^ 2 * s ^ 2 ∂μ :=
          setIntegral_mono_ae_restrict (hL2 j).integrable_sq.integrableOn
            (integrable_const _).integrableOn hbound
      _ = μ.real {ω | |X j ω| ≤ ε * s} • (ε ^ 2 * s ^ 2) := setIntegral_const _
      _ ≤ ε ^ 2 * s ^ 2 := by
          rw [smul_eq_mul]
          nlinarith [measureReal_le_one (μ := μ) (s := {ω | |X j ω| ≤ ε * s}),
                     measureReal_nonneg (μ := μ) (s := {ω | |X j ω| ≤ ε * s}),
                     mul_nonneg (sq_nonneg ε) (sq_nonneg s)]
  -- Large set: ∫_{|X_j|>εs} X_j² ≤ ∑_i ∫_{|X_i|>εs} X_i²  (nonnegativity + single_le_sum)
  have hlarge : ∫ ω in {ω | ε * s < |X j ω|}, (X j ω) ^ 2 ∂μ ≤
      ∑ i, ∫ ω in {ω | ε * s < |X i ω|}, (X i ω) ^ 2 ∂μ :=
    Finset.single_le_sum
      (f := fun i => ∫ ω in {ω | ε * s < |X i ω|}, (X i ω) ^ 2 ∂μ)
      (fun i _ => integral_nonneg (fun ω => sq_nonneg _))
      (Finset.mem_univ j)
  -- Combine: σ_j²/s² ≤ ε² + (1/s²)·∑_i large_i = ε² + LindebergSum(ε)
  rw [div_le_iff₀ hs2pos]
  have hrhs : (ε ^ 2 + 1 / s ^ 2 * ∑ i, ∫ ω in {ω | ε * s < |X i ω|}, (X i ω) ^ 2 ∂μ) * s ^ 2 =
      ε ^ 2 * s ^ 2 + ∑ i, ∫ ω in {ω | ε * s < |X i ω|}, (X i ω) ^ 2 ∂μ := by
    rw [add_mul, one_div, inv_mul_eq_div, div_mul_cancel₀ _ hs2]
  linarith [hrhs, hsplit]

/-- Lindeberg condition implies max variance ratio → 0 (Feller condition). -/
private lemma lindeberg_implies_max_var_tendsto
    {k : ℕ → ℕ} (hk : ∀ n, 0 < k n)
    {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hL2 : ∀ n j, MemLp (X n j) 2 μ)
    (hvar_sum : ∀ n, ∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ = (s n) ^ 2)
    (hLindeberg : ∀ ε > 0,
      Tendsto (fun n => LindebergSum μ (X n) (s n) ε) atTop (𝓝 0)) :
    Tendsto (fun n =>
      have : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      Finset.sup' (Finset.univ (α := Fin (k n)))
        Finset.univ_nonempty
        (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2)) atTop (𝓝 0) := by
  -- Strategy: Metric.tendsto_atTop + ε-δ argument.
  -- For any δ > 0: choose ε₀ = √(δ/4) so ε₀² = δ/4.
  -- By Lindeberg: ∃ N, ∀ n ≥ N, LindebergSum(n, ε₀) < δ/2.
  -- For n ≥ N: max_j σ_j²/s² ≤ ε₀² + LindebergSum(n, ε₀) < δ/4 + δ/2 < δ.
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Pick ε₀ = √(δ/4) so ε₀² = δ/4 < δ/2
  set ε₀ := Real.sqrt (δ / 4) with hε₀_def
  have hε₀_pos : 0 < ε₀ := Real.sqrt_pos.mpr (by linarith)
  have hε₀_sq : ε₀ ^ 2 = δ / 4 := Real.sq_sqrt (by linarith)
  -- Get N from the Lindeberg condition at ε₀ with tolerance δ/2
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hLindeberg ε₀ hε₀_pos)) (δ / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hN' := hN n hn
  simp only [Real.dist_eq, sub_zero] at hN'
  -- LindebergSum(n, ε₀) is nonneg, so |LindebergSum| = LindebergSum
  have hLpos : 0 ≤ LindebergSum μ (X n) (s n) ε₀ := by
    unfold LindebergSum; positivity
  have hLsm : LindebergSum μ (X n) (s n) ε₀ < δ / 2 := by
    rwa [abs_of_nonneg hLpos] at hN'
  -- The sup' is nonneg (compare with the j=0 term)
  have hne : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
  have hnn : 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2) :=
    le_trans (div_nonneg (integral_nonneg (fun ω => sq_nonneg _)) (sq_nonneg _))
      (Finset.le_sup' (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2)
        (Finset.mem_univ ⟨0, hk n⟩))
  -- The sup' ≤ ε₀² + LindebergSum (by var_ratio_le_lindeberg applied to all j)
  have hkey : Finset.sup' Finset.univ Finset.univ_nonempty
      (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2) ≤
      ε₀ ^ 2 + LindebergSum μ (X n) (s n) ε₀ := by
    apply Finset.sup'_le
    intro j _
    exact var_ratio_le_lindeberg (hs n) (hL2 n) j ε₀
  -- Combine: sup' < δ/4 + δ/2 < δ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith [hε₀_sq]

/-- Product-exponential approximation: when `∑ aⱼ = S` (constant) and `max aⱼ → 0`,
    `∏(1-aⱼ) → e^{-S}` as complex numbers. -/
private lemma prod_one_sub_tendsto_exp_neg
    {k : ℕ → ℕ} (hk : ∀ n, 0 < k n)
    {a : (n : ℕ) → Fin (k n) → ℝ}
    {S : ℝ}
    (ha_nn : ∀ n j, 0 ≤ a n j)
    (ha_sum : ∀ n, ∑ j, a n j = S)
    (ha_max : Tendsto (fun n =>
      have : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      Finset.sup' (Finset.univ (α := Fin (k n)))
        Finset.univ_nonempty (fun j => a n j)) atTop (𝓝 0)) :
    Tendsto (fun n => ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))) atTop
      (𝓝 (Complex.exp (-↑S))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- S ≥ 0 since all a_j ≥ 0
  have hS_nn : 0 ≤ S := by
    rw [← ha_sum 0]; exact Finset.sum_nonneg (fun j _ => ha_nn 0 j)
  -- max * S → 0 (since max → 0 and S is fixed)
  have hmaxS : Tendsto (fun n =>
      (haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j)) * S) atTop (𝓝 0) := by
    have := ha_max.mul_const S; simp at this; exact this
  -- ∏ exp(-a_j) = exp(-∑ a_j) = exp(-S) by Complex.exp_sum
  have hprod_exp : ∀ n, ∏ j : Fin (k n), Complex.exp (-(↑(a n j) : ℂ)) = Complex.exp (-↑S) := by
    intro n; rw [← Complex.exp_sum]; congr 1
    rw [← ha_sum n]; simp [Finset.sum_neg_distrib]
  -- max_j(a n j) ≤ 1 for all large n (since max → 0)
  have hmax_le1 : ∀ᶠ n in atTop,
      (haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j)) ≤ 1 :=
    (((tendsto_order).mp ha_max).2 1 (by norm_num)).mono fun n hn => le_of_lt hn
  -- Squeeze: 0 ≤ ‖∏(1-a_j) - exp(-S)‖ ≤ max_j(a n j) * S → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaxS
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · -- When max ≤ 1, bound the norm by max * S via:
    --   telescope: ‖∏(1-a_j) - ∏exp(-a_j)‖ ≤ ∑ ‖(1-a_j) - exp(-a_j)‖
    --   pointwise: ‖(1-a) - exp(-a)‖ ≤ a² (Taylor for exp, a ∈ [0,1])
    --   aggregate: ∑ a_j² ≤ max(a_j) * ∑ a_j = max * S
    apply hmax_le1.mono
    intro n hn_le1
    haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
    set M := Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j)
    rw [← hprod_exp n]
    -- Norm bounds ≤ 1 for the telescoping lemma
    have hzn : ∀ j : Fin (k n), ‖(1 : ℂ) - ↑(a n j)‖ ≤ 1 := by
      intro j
      have h1 : 0 ≤ a n j := ha_nn n j
      have h2 : a n j ≤ 1 := (Finset.le_sup' _ (Finset.mem_univ j)).trans hn_le1
      rw [show (1 : ℂ) - ↑(a n j) = ↑(1 - a n j) from by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hwn : ∀ j : Fin (k n), ‖Complex.exp (-(↑(a n j) : ℂ))‖ ≤ 1 := by
      intro j
      rw [show (-(↑(a n j) : ℂ)) = ↑(-(a n j)) from by push_cast; ring, Complex.norm_exp_ofReal]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (ha_nn n j))
    -- Pointwise: ‖(1-a) - exp(-a)‖ ≤ a² via Taylor remainder
    have hterm : ∀ j : Fin (k n),
        ‖(1 : ℂ) - ↑(a n j) - Complex.exp (-(↑(a n j) : ℂ))‖ ≤ (a n j) ^ 2 := by
      intro j
      have haj_nn : 0 ≤ a n j := ha_nn n j
      have haj_le : a n j ≤ 1 := (Finset.le_sup' _ (Finset.mem_univ j)).trans hn_le1
      -- |exp(-a) - (1-a)| ≤ a² via Real.abs_exp_sub_one_sub_id_le
      have hkey : |Real.exp (-(a n j)) - (1 - a n j)| ≤ (a n j) ^ 2 := by
        have h := Real.abs_exp_sub_one_sub_id_le (x := -(a n j))
          (by rw [abs_neg, abs_of_nonneg haj_nn]; exact haj_le)
        simp only [show Real.exp (-(a n j)) - 1 - -(a n j) =
            Real.exp (-(a n j)) - (1 - a n j) from by ring,
          show (-(a n j)) ^ 2 = (a n j) ^ 2 from by ring] at h
        exact h
      have hlb : 1 - a n j ≤ Real.exp (-(a n j)) := by linarith [Real.add_one_le_exp (-(a n j))]
      -- Cast to ℂ and compute norm (the difference is real and nonpositive)
      have hcast : (1 : ℂ) - ↑(a n j) - Complex.exp (-(↑(a n j) : ℂ)) =
          ↑((1 - a n j) - Real.exp (-(a n j))) := by
        simp [Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_neg]
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith [le_abs_self (Real.exp (-(a n j)) - (1 - a n j))]
    -- ∑ a_j² ≤ max(a_j) * ∑ a_j = M * S
    have hsum_sq : ∑ j : Fin (k n), (a n j) ^ 2 ≤ M * S := by
      rw [← ha_sum n]
      calc ∑ j : Fin (k n), (a n j) ^ 2
          = ∑ j, (a n j * a n j) := by congr 1; ext j; ring
        _ ≤ ∑ j, (M * a n j) := Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ j)) (ha_nn n j)
        _ = M * ∑ j, a n j := by rw [Finset.mul_sum]
    -- Assemble: telescope + pointwise + aggregate
    calc ‖∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) - ∏ j : Fin (k n), Complex.exp (-(↑(a n j) : ℂ))‖
        ≤ 1 ^ (k n - 1) * ∑ j : Fin (k n),
            ‖(1 : ℂ) - ↑(a n j) - Complex.exp (-(↑(a n j) : ℂ))‖ :=
          norm_prod_sub_prod_le_sum_mul_pow _ _ 1 (by norm_num) hzn hwn
      _ = ∑ j : Fin (k n), ‖(1 : ℂ) - ↑(a n j) - Complex.exp (-(↑(a n j) : ℂ))‖ := by ring_nf
      _ ≤ ∑ j : Fin (k n), (a n j) ^ 2 := Finset.sum_le_sum fun j _ => hterm j
      _ ≤ M * S := hsum_sq

/-! ## Pointwise charfun convergence (core engine) -/

/-- Pointwise convergence of charfun of standardized row sums to the standard Gaussian
    charfun, under the Lindeberg condition. This is the core analytic engine. -/
private theorem charfun_lindeberg_pointwise
    {k : ℕ → ℕ} (hk : ∀ n, 0 < k n)
    {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hm : ∀ n j, Measurable (X n j))
    (hindep : ∀ n, iIndepFun (m := fun _ => inferInstance) (X n) μ)
    (hmean : ∀ n j, ∫ ω, X n j ω ∂μ = 0)
    (hL2 : ∀ n j, MemLp (X n j) 2 μ)
    (hvar_sum : ∀ n, ∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ = (s n) ^ 2)
    (hLindeberg : ∀ ε > 0,
      Tendsto (fun n => LindebergSum μ (X n) (s n) ε) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n => charFun (μ.map (fun ω => (∑ j : Fin (k n), X n j ω) / s n)) t)
      atTop (𝓝 (Complex.exp (-(↑(t ^ 2) / 2)))) := by
  -- Abbreviation: a_{n,j} = σ²_{n,j} * t² / (2 * s²_n)
  --               w_{n,j} = 1 - a_{n,j}  (quadratic approximation value in ℂ)
  let a : (n : ℕ) → Fin (k n) → ℝ := fun n j =>
    (∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2)
  -- Step 1: Charfun factorization  φ_{Sn}(t) = ∏_j φ_j(t/s_n)
  have h_charfun_prod : ∀ n,
      charFun (μ.map (fun ω => (∑ j : Fin (k n), X n j ω) / s n)) t =
      ∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) :=
    fun n => charfun_indep_sum_eq_prod (hk n) (hs n) (hm n) (hindep n) t
  -- a_{n,j} ≥ 0
  have ha_nn : ∀ n j, 0 ≤ a n j := fun n j =>
    div_nonneg (mul_nonneg (integral_nonneg (fun ω => sq_nonneg _)) (sq_nonneg _))
      (by positivity)
  -- ∑_j a_{n,j} = t²/2 (follows from hvar_sum)
  have ha_sum : ∀ n, ∑ j, a n j = t ^ 2 / 2 := fun n => by
    show ∑ j, (∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) = t ^ 2 / 2
    simp_rw [mul_div_assoc]
    rw [← Finset.sum_mul, hvar_sum n]
    field_simp [(hs n).ne']
  -- Step 2: max_j a_{n,j} → 0  (Feller condition, derived from Lindeberg)
  have hmax_a : Tendsto (fun n =>
      haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j)) atTop (𝓝 0) := by
    have hmax_var := lindeberg_implies_max_var_tendsto hk hs hL2 hvar_sum hLindeberg
    -- a_{n,j} = (σ²_{n,j}/s²_n) * (t²/2), so max_j a_{n,j} = max_j(σ²/s²) * (t²/2) → 0
    have h_eq : ∀ n,
        (haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
        Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j)) =
        (haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
        Finset.sup' Finset.univ Finset.univ_nonempty
          (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2)) * (t ^ 2 / 2) := fun n => by
      haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
      rcases (sq_nonneg t |> le_iff_lt_or_eq.mp) with ht_pos | ht_zero
      · have hc : (0 : ℝ) < t ^ 2 / 2 := by linarith
        have heq : Finset.sup' Finset.univ Finset.univ_nonempty (fun j => a n j) =
            Finset.sup' Finset.univ Finset.univ_nonempty
              (fun j => (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2 * (t ^ 2 / 2)) := by
          congr 1; ext j; show (∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) =
              (∫ ω, (X n j ω) ^ 2 ∂μ) / (s n) ^ 2 * (t ^ 2 / 2); ring
        rw [heq, ← Finset.sup'_mul₀ hc]
      · have ht0 : t = 0 := by nlinarith [sq_nonneg t]
        have ha0 : ∀ j : Fin (k n), a n j = 0 := fun j => by
          show (∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) = 0
          simp [ht0]
        simp [show (fun j : Fin (k n) => a n j) = fun _ => 0 from funext ha0, ht0]
    have h := hmax_var.mul_const (t ^ 2 / 2)
    simp only [zero_mul] at h
    exact h.congr (fun n => (h_eq n).symm)
  -- Step 3: ∏_j w_{n,j} → exp(-t²/2)
  have h_prod_conv : Tendsto (fun n => ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))) atTop
      (𝓝 (Complex.exp (-(↑(t ^ 2) / 2)))) := by
    have h := prod_one_sub_tendsto_exp_neg hk ha_nn ha_sum hmax_a
    -- prod_one_sub gives exp(-↑(t²/2 : ℝ)), we need exp(-(↑(t²)/2))
    convert h using 2
    congr 1; push_cast; ring
  -- Step 4: Combine using triangle inequality and ε-argument
  -- Use: for each ε > 0, eventually ‖∏φ - exp‖ ≤ (4|t|³+4t²)ε + ‖∏w - exp‖
  --                                               → 4|t|³ε (since Lindeberg + prod_conv)
  --      Since this holds for all ε > 0, the limit is exp(-t²/2)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Obtain N₁ from the prod_conv convergence
  rw [Metric.tendsto_atTop] at h_prod_conv
  obtain ⟨N₁, hN₁⟩ := h_prod_conv (δ / 2) (by linarith)
  -- Obtain N₂ from Lindeberg condition
  -- Pick ε₀ = δ / (4C) where C = 4|t|³ + 4t² + 1 > 0
  -- Then 4|t|³·ε₀ ≤ δ/4 and 4t²·ε₀ ≤ δ/4 (since |t|³/C ≤ 1/4 and t²/C ≤ 1/4)
  set C := 4 * |t| ^ 3 + 4 * t ^ 2 + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  set ε₀ := δ / (4 * C) with hε₀_def
  have hε₀_pos : 0 < ε₀ := by positivity
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hLindeberg ε₀ hε₀_pos)) ε₀ hε₀_pos
  -- Obtain N₃ from max_a eventually ≤ 1
  obtain ⟨N₃, hN₃⟩ := (((tendsto_order).mp hmax_a).2 1 (by norm_num)).exists_forall_of_atTop
  -- Work from N = max(N₁, N₂, N₃)
  refine ⟨max N₁ (max N₂ N₃), fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₃ : N₃ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  -- ‖∏w - exp‖ < δ/2
  have h_second : ‖∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) -
      Complex.exp (-(↑(t ^ 2) / 2))‖ < δ / 2 := by
    have := hN₁ n hn₁
    rwa [Complex.dist_eq] at this
  -- LindebergSum(n, ε₀) < ε₀ (so 4t² * LindebergSum ≤ 4t² * ε₀ ≤ (4t²+4) * ε₀)
  have hLn : LindebergSum μ (X n) (s n) ε₀ < ε₀ := by
    have := hN₂ n hn₂
    have hLpos : 0 ≤ LindebergSum μ (X n) (s n) ε₀ := by
      unfold LindebergSum
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro j _
      exact integral_nonneg (fun ω => sq_nonneg _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hLpos] at this
  -- max_j a_{n,j} ≤ 1 (for the telescope norm bound)
  have hmax_le1 : ∀ j : Fin (k n), a n j ≤ 1 := by
    intro j
    haveI : Nonempty (Fin (k n)) := Fin.pos_iff_nonempty.mp (hk n)
    exact le_of_lt (lt_of_le_of_lt (Finset.le_sup' _ (Finset.mem_univ j)) (hN₃ n hn₃))
  -- Telescope bound: ‖∏φ - ∏w‖ ≤ ∑‖φ_j - w_j‖  (uses M=1, ‖φ_j‖≤1, ‖w_j‖≤1)
  have h_telescope : ‖∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) -
      ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))‖ ≤
      ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) -
        ((1 : ℂ) - ↑(a n j))‖ := by
    have hφ_le : ∀ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n)‖ ≤ 1 := fun j => by
      haveI : IsProbabilityMeasure (μ.map (X n j)) :=
        Measure.isProbabilityMeasure_map (hm n j).aemeasurable
      exact norm_charFun_le_one _
    have hw_le : ∀ j : Fin (k n), ‖((1 : ℂ) - ↑(a n j))‖ ≤ 1 := fun j => by
      rw [show (1 : ℂ) - ↑(a n j) = ↑((1 : ℝ) - a n j) from by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ 1 - a n j := by linarith [ha_nn n j, hmax_le1 j]
      rw [abs_of_nonneg h0]
      linarith [ha_nn n j]
    have h := norm_prod_sub_prod_le_sum_mul_pow
      (fun j => charFun (μ.map (X n j)) (t / s n))
      (fun j => (1 : ℂ) - ↑(a n j)) 1 (by norm_num) hφ_le hw_le
    simpa using h
  -- Sum bound: ∑‖φ_j - w_j‖ ≤ 4|t|³ε₀ + 4t²·L_n(ε₀)
  have h_sum_bound : ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) -
      ((1 : ℂ) - (((∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) : ℝ) : ℂ))‖ ≤
      4 * |t| ^ 3 * ε₀ + 4 * t ^ 2 * LindebergSum μ (X n) (s n) ε₀ :=
    sum_charfun_errors_le (hs n) hε₀_pos (hm n) (hmean n) (hL2 n) (hvar_sum n) t
  -- Connect w_j to the sum bound expression
  have hw_eq : ∀ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) =
      (1 : ℂ) - (((∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) : ℝ) : ℂ) := by
    intro j; rfl
  -- Assemble the final bound
  rw [Complex.dist_eq, h_charfun_prod n]
  have h_triangle : ‖∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) -
      Complex.exp (-(↑(t ^ 2) / 2))‖ ≤
      ‖∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) -
        ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))‖ +
      ‖∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) -
        Complex.exp (-(↑(t ^ 2) / 2))‖ := by
    calc ‖_ - _‖ = ‖(_ - ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))) +
          (∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) - _)‖ := by ring_nf
      _ ≤ _ + _ := norm_add_le _ _
  have h_sum_rw : ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) -
      ((1 : ℂ) - ↑(a n j))‖ = ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) -
      ((1 : ℂ) - (((∫ ω, (X n j ω) ^ 2 ∂μ) * t ^ 2 / (2 * (s n) ^ 2) : ℝ) : ℂ))‖ := by
    congr 1
  calc ‖∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) -
        Complex.exp (-(↑(t ^ 2) / 2))‖
      ≤ ‖∏ j : Fin (k n), charFun (μ.map (X n j)) (t / s n) -
          ∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j))‖ +
        ‖∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) -
          Complex.exp (-(↑(t ^ 2) / 2))‖ := h_triangle
    _ ≤ ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) - ((1 : ℂ) - ↑(a n j))‖ +
        ‖∏ j : Fin (k n), ((1 : ℂ) - ↑(a n j)) -
          Complex.exp (-(↑(t ^ 2) / 2))‖ := by linarith [h_telescope]
    _ < δ := by
        -- 4t² · L_n ≤ 4t² · ε₀ = (4t²/C) · (δ/4) ≤ δ/4  (since 4t² ≤ C)
        have hLn_nn : 0 ≤ LindebergSum μ (X n) (s n) ε₀ := by unfold LindebergSum; positivity
        have hLn_bound : 4 * t ^ 2 * LindebergSum μ (X n) (s n) ε₀ ≤ δ / 4 :=
          calc 4 * t ^ 2 * LindebergSum μ (X n) (s n) ε₀
              ≤ 4 * t ^ 2 * ε₀ := by nlinarith [hLn]
            _ = (4 * t ^ 2 / C) * (δ / 4) := by rw [hε₀_def]; ring
            _ ≤ 1 * (δ / 4) := by
                gcongr; rw [div_le_one hC_pos]; simp only [hC_def]
                linarith [abs_nonneg t, pow_nonneg (abs_nonneg t) 3]
            _ = δ / 4 := one_mul _
        -- 4|t|³ · ε₀ = (4|t|³/C) · (δ/4) ≤ δ/4  (since 4|t|³ ≤ C)
        have h3t_bound : 4 * |t| ^ 3 * ε₀ ≤ δ / 4 :=
          calc 4 * |t| ^ 3 * ε₀
              = (4 * |t| ^ 3 / C) * (δ / 4) := by rw [hε₀_def]; ring
            _ ≤ 1 * (δ / 4) := by
                gcongr; rw [div_le_one hC_pos]; simp only [hC_def]
                linarith [sq_nonneg t]
            _ = δ / 4 := one_mul _
        -- Assemble: ∑‖φ-w‖ ≤ δ/4+δ/4 = δ/2, ‖∏w-exp‖ < δ/2, sum < δ
        have h_first_half : 4 * |t| ^ 3 * ε₀ +
            4 * t ^ 2 * LindebergSum μ (X n) (s n) ε₀ ≤ δ / 2 := by linarith
        have h_sum_le : ∑ j : Fin (k n), ‖charFun (μ.map (X n j)) (t / s n) -
            ((1 : ℂ) - ↑(a n j))‖ ≤ δ / 2 := by
          have h1 := h_sum_rw ▸ h_sum_bound; linarith
        linarith [add_lt_add_of_le_of_lt h_sum_le h_second]

/-! ## Main theorem -/

/-- **Lindeberg-Feller CLT** (Shao, Thm 1.6).

For a triangular array `X_{n,1}, ..., X_{n,k_n}` of row-independent, mean-zero, L²
random variables with `∑_j Var(X_{n,j}) = s_n²`, if the Lindeberg condition
`(1/s_n²) ∑_j E[X_{n,j}² · 1_{|X_{n,j}| > ε·s_n}] → 0` holds for every `ε > 0`,
then `S_n = (∑_j X_{n,j}) / s_n →ᵈ N(0,1)`. -/
theorem lindeberg_feller_clt
    {k : ℕ → ℕ} (hk : ∀ n, 0 < k n)
    {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hm : ∀ n j, Measurable (X n j))
    (hindep : ∀ n, iIndepFun (m := fun _ => inferInstance) (X n) μ)
    (hmean : ∀ n j, ∫ ω, X n j ω ∂μ = 0)
    (hL2 : ∀ n j, MemLp (X n j) 2 μ)
    (hvar_sum : ∀ n, ∑ j, ∫ ω, (X n j ω) ^ 2 ∂μ = (s n) ^ 2)
    (hLindeberg : ∀ ε > 0,
      Tendsto (fun n => LindebergSum μ (X n) (s n) ε) atTop (𝓝 0)) :
    let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨μ.map (fun ω => (∑ j : Fin (k n), X n j ω) / s n),
        Measure.isProbabilityMeasure_map
          ((Finset.measurable_sum Finset.univ
            (fun i _ => hm n i)).div_const _).aemeasurable⟩
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (↑μ₀ : Measure ℝ) t =
        charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t) ∧
      Tendsto μs atTop (𝓝 μ₀) := by
  intro μs
  -- Step 1: Pointwise charfun convergence
  have hconv : ∀ t, Tendsto (fun n => charFun (↑(μs n) : Measure ℝ) t) atTop
      (𝓝 (charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t)) := by
    intro t
    simp_rw [charFun_gaussianReal_standard]
    exact charfun_lindeberg_pointwise hk hs hm hindep hmean hL2 hvar_sum hLindeberg t
  -- Step 2: f(0) = 1
  have hf0 : charFun (gaussianReal (0 : ℝ) (1 : NNReal)) (0 : ℝ) = 1 := by
    rw [charFun_zero]; simp [Measure.real]
  -- Step 3: Continuity at 0
  have hf_cont : ContinuousAt
      (fun t : ℝ => charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t) 0 := by
    exact (show Continuous _ by simp_rw [charFun_gaussianReal]; fun_prop).continuousAt
  -- Step 4: Lévy continuity theorem
  exact levy_continuity hconv hf0 hf_cont

end Statlean.LimitTheorems.LindebergFeller

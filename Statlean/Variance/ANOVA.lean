import Statlean.Gaussian.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.CondVar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # ANOVA Variance Decomposition

Independent, reusable infrastructure for variance decomposition on product spaces.

## Main results
- `sq_integral_le_integral_sq` — Jensen's inequality (squared form)
- `variance_pi_of_isEmpty` — trivial variance on empty product
- `efron_stein_isEmpty` — Efron-Stein on empty index type
- `memLp_marginal_fst` — L² stability of marginal integration (first coordinate)
- `memLp_marginal_snd` — L² stability of marginal integration (second coordinate)
- `variance_marginals_le_variance_prod` — ANOVA two-factor inequality

All declarations are zero sorry.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Finset

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i))

/-! ## Jensen's inequality (squared form) -/

/-- For a probability measure, `(∫ g dμ)² ≤ ∫ g² dμ`. -/
lemma sq_integral_le_integral_sq {α : Type*} {m : MeasurableSpace α}
    (ν : Measure α) [IsProbabilityMeasure ν]
    (g : α → ℝ) (hg : MemLp g 2 ν) :
    (∫ x, g x ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 ∂ν := by
  have hVar := variance_nonneg g ν
  have hEq := variance_eq_sub (μ := ν) hg
  simp only [Pi.pow_apply] at hEq
  linarith

/-- If the index type is empty, all functions on the product space have variance 0. -/
lemma variance_pi_of_isEmpty [IsEmpty ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ) :
    Var[f; Measure.pi μ] = 0 := by
  haveI huniq : Unique (∀ j : ι, X j) := Pi.uniqueOfIsEmpty _
  have hconst : f = fun _ => f (default : ∀ j : ι, X j) :=
    funext fun x => congr_arg f (Subsingleton.elim x default)
  rw [hconst, variance_eq_sub (memLp_const _)]
  simp

/-! ## ANOVA two-factor inequality -/

section ANOVA

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma memLp_marginal_fst
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ₀.prod ν)) :
    MemLp (fun y => ∫ x, f (x, y) ∂μ₀) 2 ν := by
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  have hg_aesm : AEStronglyMeasurable (fun y => ∫ x, f (x, y) ∂μ₀) ν :=
    hfint.integral_prod_right.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hg_aesm]
  have h_sq_int : Integrable (fun y => ∫ x, f (x, y) ^ 2 ∂μ₀) ν :=
    hf.integrable_sq.swap.integral_prod_left
  have hfswap_aesm : AEStronglyMeasurable (f ∘ Prod.swap) (ν.prod μ₀) :=
    hf.aestronglyMeasurable.comp_measurePreserving
      (Measure.measurePreserving_swap (μ := ν) (ν := μ₀))
  have hslice_aesm : ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x => f (x, y)) μ₀ :=
    hfswap_aesm.prodMk_left
  have hslice_sq : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y) ^ 2) μ₀ :=
    hf.integrable_sq.prod_left_ae
  have hslice_lp : ∀ᵐ y ∂ν, MemLp (fun x => f (x, y)) 2 μ₀ := by
    filter_upwards [hslice_aesm, hslice_sq] with y ha hq
    exact (memLp_two_iff_integrable_sq ha).mpr hq
  apply h_sq_int.mono (hg_aesm.mul hg_aesm |>.congr (ae_of_all _ fun y => (pow_two _).symm))
  filter_upwards [hslice_lp] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  exact sq_integral_le_integral_sq μ₀ (fun x => f (x, y)) hy

lemma memLp_marginal_snd
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite μ₀]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ₀.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ₀ := by
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  have hh_aesm : AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ₀ :=
    hfint.integral_prod_left.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hh_aesm]
  have h_sq_int : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂ν) μ₀ :=
    hf.integrable_sq.integral_prod_left
  have hslice_aesm : ∀ᵐ x ∂μ₀, AEStronglyMeasurable (fun y => f (x, y)) ν :=
    hf.aestronglyMeasurable.prodMk_left
  have hslice_sq : ∀ᵐ x ∂μ₀, Integrable (fun y => f (x, y) ^ 2) ν :=
    hf.integrable_sq.prod_right_ae
  have hslice_lp : ∀ᵐ x ∂μ₀, MemLp (fun y => f (x, y)) 2 ν := by
    filter_upwards [hslice_aesm, hslice_sq] with x ha hq
    exact (memLp_two_iff_integrable_sq ha).mpr hq
  apply h_sq_int.mono (hh_aesm.mul hh_aesm |>.congr (ae_of_all _ fun x => (pow_two _).symm))
  filter_upwards [hslice_lp] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
  exact sq_integral_le_integral_sq ν (fun y => f (x, y)) hx

theorem variance_marginals_le_variance_prod
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite μ₀] [SFinite ν]
    (f : α × β → ℝ) (hf : MemLp f 2 (μ₀.prod ν)) :
    Var[fun y => ∫ x, f (x, y) ∂μ₀; ν] +
      Var[fun x => ∫ y, f (x, y) ∂ν; μ₀] ≤
      Var[f; μ₀.prod ν] := by
  set g : β → ℝ := fun y => ∫ x, f (x, y) ∂μ₀ with hg_def
  set h : α → ℝ := fun x => ∫ y, f (x, y) ∂ν with hh_def
  have hg_lp : MemLp g 2 ν := memLp_marginal_fst hf
  have hh_lp : MemLp h 2 μ₀ := memLp_marginal_snd hf
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  set c := ∫ z, f z ∂(μ₀.prod ν) with hc_def
  have hcg : ∫ y, g y ∂ν = c := by
    simp only [g, hc_def]; rw [← integral_prod_symm f hfint]
  have hch : ∫ x, h x ∂μ₀ = c := by
    simp only [h, hc_def]; rw [← integral_prod f hfint]
  rw [variance_eq_sub hg_lp, variance_eq_sub hh_lp, variance_eq_sub hf]
  simp only [Pi.pow_apply, hcg, hch]
  suffices h_key : ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 ≤
      ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν by linarith
  set φ : α × β → ℝ := fun z => f z - g z.2 with hφ_def
  have hgcomp : MemLp (fun z : α × β => g z.2) 2 (μ₀.prod ν) :=
    hg_lp.comp_measurePreserving measurePreserving_snd
  have hφ_lp : MemLp φ 2 (μ₀.prod ν) := hf.sub hgcomp
  have hφ2_int : Integrable (fun z => φ z ^ 2) (μ₀.prod ν) := hφ_lp.integrable_sq
  have hg2comp_int : Integrable (fun z : α × β => g z.2 ^ 2) (μ₀.prod ν) := hgcomp.integrable_sq
  have integral_g2_eq : ∫ z : α × β, g z.2 ^ 2 ∂(μ₀.prod ν) = ∫ y, g y ^ 2 ∂ν := by
    rw [integral_prod _ hg2comp_int]
    simp [integral_const]
  have hint_fg : Integrable (fun z => f z * g z.2) (μ₀.prod ν) :=
    hf.integrable_mul hgcomp
  have stepA : ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν =
      ∫ y, (∫ x, φ (x, y) ^ 2 ∂μ₀) ∂ν := by
    have expand_φ2 : ∫ z, φ z ^ 2 ∂(μ₀.prod ν) =
        ∫ z, f z ^ 2 ∂(μ₀.prod ν)
        - 2 * ∫ z, f z * g z.2 ∂(μ₀.prod ν)
        + ∫ z : α × β, g z.2 ^ 2 ∂(μ₀.prod ν) :=
      calc ∫ z, φ z ^ 2 ∂(μ₀.prod ν)
          = ∫ z, ((f z ^ 2 - 2 * (f z * g z.2)) + g z.2 ^ 2) ∂(μ₀.prod ν) :=
            integral_congr_ae (ae_of_all _ fun z => by simp [φ]; ring)
        _ = ∫ z, (f z ^ 2 - 2 * (f z * g z.2)) ∂(μ₀.prod ν)
            + ∫ z, g z.2 ^ 2 ∂(μ₀.prod ν) :=
            integral_add (hf.integrable_sq.sub (hint_fg.const_mul 2)) hg2comp_int
        _ = (∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ z, 2 * (f z * g z.2) ∂(μ₀.prod ν))
            + ∫ z, g z.2 ^ 2 ∂(μ₀.prod ν) := by
              congr 1
              exact integral_sub hf.integrable_sq (hint_fg.const_mul 2)
        _ = ∫ z, f z ^ 2 ∂(μ₀.prod ν)
            - 2 * ∫ z, f z * g z.2 ∂(μ₀.prod ν)
            + ∫ z, g z.2 ^ 2 ∂(μ₀.prod ν) := by
              rw [integral_const_mul 2 (fun z => f z * g z.2)]
    have cross_eq : ∫ z, f z * g z.2 ∂(μ₀.prod ν) = ∫ y, g y ^ 2 ∂ν := by
      rw [integral_prod_symm _ hint_fg]
      congr 1; ext y
      rw [show (fun x => f (x, y) * g y) = fun x => g y * f (x, y) from
          funext fun x => mul_comm _ _,
        integral_const_mul (g y) (fun x => f (x, y))]
      ring
    have φ2_eq : ∫ z, φ z ^ 2 ∂(μ₀.prod ν) =
        ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν := by
      linarith [expand_φ2, integral_g2_eq, cross_eq]
    linarith [φ2_eq, (integral_prod_symm (fun z : α × β => φ z ^ 2) hφ2_int).symm]
  have hcenter : ∀ᵐ x ∂μ₀, h x - c = ∫ y, φ (x, y) ∂ν := by
    filter_upwards [hfint.prod_right_ae] with x hfx
    simp only [hφ_def, h]
    rw [← hcg]
    exact (integral_sub hfx (hg_lp.integrable (by norm_num))).symm
  have hslice_φ_lp : ∀ᵐ x ∂μ₀, MemLp (fun y => φ (x, y)) 2 ν := by
    have hslice_aesm : ∀ᵐ x ∂μ₀, AEStronglyMeasurable (fun y => φ (x, y)) ν :=
      hφ_lp.aestronglyMeasurable.prodMk_left
    have hslice_sq : ∀ᵐ x ∂μ₀, Integrable (fun y => φ (x, y) ^ 2) ν :=
      hφ2_int.prod_right_ae
    filter_upwards [hslice_aesm, hslice_sq] with x ha hq
    exact (memLp_two_iff_integrable_sq ha).mpr hq
  have lhs_eq : ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 = ∫ x, (h x - c) ^ 2 ∂μ₀ := by
    have hVar1 : variance h μ₀ = ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 := by
      rw [variance_eq_sub hh_lp, hch]; simp [Pi.pow_apply]
    have hVar2 : variance h μ₀ = ∫ x, (h x - c) ^ 2 ∂μ₀ := by
      rw [variance_eq_integral hh_lp.aemeasurable, hch]
    linarith [hVar1, hVar2]
  rw [stepA, lhs_eq]
  rw [show ∫ y, (∫ x, φ (x, y) ^ 2 ∂μ₀) ∂ν =
      ∫ x, (∫ y, φ (x, y) ^ 2 ∂ν) ∂μ₀ from
    (integral_integral_swap (f := fun x y => φ (x, y) ^ 2) hφ2_int).symm]
  have h_int_lhs : Integrable (fun x => (h x - c) ^ 2) μ₀ :=
    (hh_lp.integrable_sq.sub ((hh_lp.integrable (by norm_num)).const_mul (2 * c))).add
      (integrable_const (c ^ 2)) |>.congr
        (ae_of_all _ fun x => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have h_int_rhs : Integrable (fun x => ∫ y, φ (x, y) ^ 2 ∂ν) μ₀ :=
    hφ2_int.integral_norm_prod_left.congr
      (ae_of_all _ fun x => integral_congr_ae
        (ae_of_all _ fun y => Real.norm_of_nonneg (sq_nonneg _)))
  apply integral_mono_ae h_int_lhs h_int_rhs
  filter_upwards [hcenter, hslice_φ_lp] with x hcx hφx
  rw [hcx]
  exact sq_integral_le_integral_sq ν (fun y => φ (x, y)) hφx

end ANOVA

end


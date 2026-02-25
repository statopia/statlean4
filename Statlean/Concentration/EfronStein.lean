import Statlean.Concentration.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! # Efron-Stein Inequality (Theorem 3.1)

## Statement
Let X₁,...,Xₙ be independent random variables, and let f be a square-integrable
function. Then:

  Var[f(X)] ≤ Σᵢ E[(f(X) - E^{(i)}[f(X)])²]

where E^{(i)}[f(X)] = E[f(X) | Xⱼ, j ≠ i] is the conditional expectation
of f given all variables except Xᵢ.

## Proof strategy
The proof uses the telescoping decomposition:
  f - E[f] = Σᵢ (Dᵢf)
where Dᵢf = E[f | X₁,...,Xᵢ] - E[f | X₁,...,Xᵢ₋₁]
(martingale difference sequence).

Then Var[f] = E[(Σᵢ Dᵢf)²] = Σᵢ E[(Dᵢf)²] (by orthogonality).
Finally, E[(Dᵢf)²] ≤ E[(f - E^{(i)}[f])²] by conditional Jensen.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Finset

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i))

/-- Jensen's inequality (squared form): for a probability measure,
`(∫ g dμ)² ≤ ∫ g² dμ`.
Follows immediately from `variance_nonneg` and `variance_eq_sub`. -/
lemma sq_integral_le_integral_sq {α : Type*} {m : MeasurableSpace α}
    (ν : Measure α) [IsProbabilityMeasure ν]
    (g : α → ℝ) (hg : MemLp g 2 ν) :
    (∫ x, g x ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 ∂ν := by
  have hVar := variance_nonneg g ν
  have hEq := variance_eq_sub (μ := ν) hg
  simp only [Pi.pow_apply] at hEq
  -- hEq : variance g ν = ∫ x, g x ^ 2 ∂ν - (∫ x, g x ∂ν) ^ 2
  linarith

/-- If the index type is empty, all functions on the product space have variance 0
(the domain `∀ j : ι, X j` is a singleton, so f is constant). -/
private lemma variance_pi_of_isEmpty [IsEmpty ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ) :
    Var[f; Measure.pi μ] = 0 := by
  haveI huniq : Unique (∀ j : ι, X j) := Pi.uniqueOfIsEmpty _
  have hconst : f = fun _ => f (default : ∀ j : ι, X j) :=
    funext fun x => congr_arg f (Subsingleton.elim x default)
  rw [hconst, variance_eq_sub (memLp_const _)]
  simp

/-- Efron-Stein is trivially true for an empty index type:
the sum is empty (= 0) and the variance is 0. -/
lemma efron_stein_isEmpty [IsEmpty ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (_hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  simp [variance_pi_of_isEmpty μ f]

/-! ## ANOVA two-factor inequality (key ingredient for Efron-Stein) -/

section ANOVA

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The marginal expectation `fun y => ∫ x, f (x, y) ∂μ₀` is in L²(ν) when `f ∈ L²(μ₀.prod ν)`.
Proof: measurability follows from Fubini; the L² bound follows from Jensen:
  g(y)² ≤ ∫ f(x,y)² dμ₀  ⟹  ∫ g² dν ≤ ∫∫ f² dμ₀ dν = ‖f‖²_{L²} < ∞. -/
private lemma memLp_marginal_fst
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ₀.prod ν)) :
    MemLp (fun y => ∫ x, f (x, y) ∂μ₀) 2 ν := by
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  -- AEStronglyMeasurable of the marginal g(y) = ∫ x, f(x,y) dμ₀
  have hg_aesm : AEStronglyMeasurable (fun y => ∫ x, f (x, y) ∂μ₀) ν :=
    hfint.integral_prod_right.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hg_aesm]
  -- Bounding function: ∫ x, f(x,y)^2 dμ₀ is integrable over y (Fubini)
  have h_sq_int : Integrable (fun y => ∫ x, f (x, y) ^ 2 ∂μ₀) ν :=
    hf.integrable_sq.swap.integral_prod_left
  -- For a.e. y, the y-slice of f is in L²(μ₀)
  -- (via: AEStronglyMeasurable of slice from prod_swap + prodMk_left)
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
  -- Apply Integrable.mono: |(∫ f dμ₀)^2| ≤ |∫ f^2 dμ₀| a.e. by Jensen
  apply h_sq_int.mono (hg_aesm.mul hg_aesm |>.congr (ae_of_all _ fun y => (pow_two _).symm))
  filter_upwards [hslice_lp] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  exact sq_integral_le_integral_sq μ₀ (fun x => f (x, y)) hy

/-- Symmetric version: `fun x => ∫ y, f (x, y) ∂ν` is in L²(μ₀) when `f ∈ L²(μ₀.prod ν)`. -/
private lemma memLp_marginal_snd
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite μ₀]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ₀.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ₀ := by
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  -- AEStronglyMeasurable of the marginal h(x) = ∫ y, f(x,y) dν
  have hh_aesm : AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ₀ :=
    hfint.integral_prod_left.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hh_aesm]
  -- Bounding function: ∫ y, f(x,y)^2 dν is integrable over x (Fubini)
  have h_sq_int : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂ν) μ₀ :=
    hf.integrable_sq.integral_prod_left
  -- For a.e. x, the x-slice of f is in L²(ν)
  have hslice_aesm : ∀ᵐ x ∂μ₀, AEStronglyMeasurable (fun y => f (x, y)) ν :=
    hf.aestronglyMeasurable.prodMk_left
  have hslice_sq : ∀ᵐ x ∂μ₀, Integrable (fun y => f (x, y) ^ 2) ν :=
    hf.integrable_sq.prod_right_ae
  have hslice_lp : ∀ᵐ x ∂μ₀, MemLp (fun y => f (x, y)) 2 ν := by
    filter_upwards [hslice_aesm, hslice_sq] with x ha hq
    exact (memLp_two_iff_integrable_sq ha).mpr hq
  -- Apply Integrable.mono: |(∫ f dν)^2| ≤ |∫ f^2 dν| a.e. by Jensen
  apply h_sq_int.mono (hh_aesm.mul hh_aesm |>.congr (ae_of_all _ fun x => (pow_two _).symm))
  filter_upwards [hslice_lp] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
  exact sq_integral_le_integral_sq ν (fun y => f (x, y)) hx

/-- **ANOVA two-factor inequality** (key lemma for Efron-Stein):

For `f ∈ L²(μ₀ × ν)`, with marginal expectations
  `g(y) = ∫ f(x,y) dμ₀`  and  `h(x) = ∫ f(x,y) dν`,
the sum of their variances is at most the total variance:
  `Var[g; ν] + Var[h; μ₀] ≤ Var[f; μ₀ × ν]`.

**Proof** (ANOVA decomposition):
The key algebraic identity is: `Var[f] - Var[g] = ∫(f - g∘snd)² d(μ₀×ν)`.
From this we deduce `Var[f] - Var[g] ≥ Var[h]` by Fubini swap + Jensen:
  `∫(f-g∘snd)² d(μ₀×ν) = ∫x ∫y (f-g)² dν dμ₀ ≥ ∫x (∫y (f-g) dν)² dμ₀ = ∫x (h-c)² dμ₀ = Var[h]`. -/
theorem variance_marginals_le_variance_prod
    {μ₀ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν] [SFinite μ₀] [SFinite ν]
    (f : α × β → ℝ) (hf : MemLp f 2 (μ₀.prod ν)) :
    Var[fun y => ∫ x, f (x, y) ∂μ₀; ν] +
      Var[fun x => ∫ y, f (x, y) ∂ν; μ₀] ≤
      Var[f; μ₀.prod ν] := by
  -- Marginal expectations
  set g : β → ℝ := fun y => ∫ x, f (x, y) ∂μ₀ with hg_def
  set h : α → ℝ := fun x => ∫ y, f (x, y) ∂ν with hh_def
  -- L² memberships (from sorry lemmas)
  have hg_lp : MemLp g 2 ν := memLp_marginal_fst hf
  have hh_lp : MemLp h 2 μ₀ := memLp_marginal_snd hf
  -- Integrability
  have hfint : Integrable f (μ₀.prod ν) := hf.integrable (by norm_num)
  -- Common mean
  set c := ∫ z, f z ∂(μ₀.prod ν) with hc_def
  have hcg : ∫ y, g y ∂ν = c := by
    simp only [g, hc_def]; rw [← integral_prod_symm f hfint]
  have hch : ∫ x, h x ∂μ₀ = c := by
    simp only [h, hc_def]; rw [← integral_prod f hfint]
  -- Expand Var[X] = ∫X² - (∫X)²
  rw [variance_eq_sub hg_lp, variance_eq_sub hh_lp, variance_eq_sub hf]
  simp only [Pi.pow_apply, hcg, hch]
  -- Suffices: Var[h] = ∫h² - c² ≤ ∫f² - ∫g²
  suffices h_key : ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 ≤
      ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν by linarith
  -- Set φ := f - g∘snd (the "within-column" residual)
  set φ : α × β → ℝ := fun z => f z - g z.2 with hφ_def
  -- φ ∈ L²(μ₀.prod ν), since g∘snd ∈ L²
  have hgcomp : MemLp (fun z : α × β => g z.2) 2 (μ₀.prod ν) :=
    hg_lp.comp_measurePreserving measurePreserving_snd
  have hφ_lp : MemLp φ 2 (μ₀.prod ν) := hf.sub hgcomp
  -- Integrability facts
  have hφ2_int : Integrable (fun z => φ z ^ 2) (μ₀.prod ν) := hφ_lp.integrable_sq
  have hg2comp_int : Integrable (fun z : α × β => g z.2 ^ 2) (μ₀.prod ν) := hgcomp.integrable_sq
  -- ∫(g∘snd)² d(μ₀.prod ν) = ∫g² dν  (via Fubini + prob measure)
  have integral_g2_eq : ∫ z : α × β, g z.2 ^ 2 ∂(μ₀.prod ν) = ∫ y, g y ^ 2 ∂ν := by
    rw [integral_prod _ hg2comp_int]
    simp [integral_const]
  -- Integrability of f * (g∘snd)  using HolderConjugate 2 2 instance
  have hint_fg : Integrable (fun z => f z * g z.2) (μ₀.prod ν) :=
    hf.integrable_mul hgcomp
  -- Step A: ∫f² - ∫g² = ∫φ² d(μ₀.prod ν) = ∫y ∫x φ(x,y)² dμ₀ dν
  have stepA : ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν =
      ∫ y, (∫ x, φ (x, y) ^ 2 ∂μ₀) ∂ν := by
    -- ∫φ² = ∫f² - 2·∫f(g∘snd) + ∫(g∘snd)²
    -- First, rewrite φ² = (f - g∘snd)² = (f² - 2f(g∘snd)) + (g∘snd)²
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
    -- Cross term: ∫f·(g∘snd) = ∫g²  (by Fubini, then ∫f(·,y)dμ₀ = g(y))
    have cross_eq : ∫ z, f z * g z.2 ∂(μ₀.prod ν) = ∫ y, g y ^ 2 ∂ν := by
      rw [integral_prod_symm _ hint_fg]
      congr 1; ext y
      rw [show (fun x => f (x, y) * g y) = fun x => g y * f (x, y) from
          funext fun x => mul_comm _ _,
        integral_const_mul (g y) (fun x => f (x, y))]
      ring
    -- Combine: ∫φ² = ∫f² - ∫g²
    have φ2_eq : ∫ z, φ z ^ 2 ∂(μ₀.prod ν) =
        ∫ z, f z ^ 2 ∂(μ₀.prod ν) - ∫ y, g y ^ 2 ∂ν := by
      linarith [expand_φ2, integral_g2_eq, cross_eq]
    -- Fubini: ∫φ² d(μ₀.prod ν) = ∫y ∫x φ² dμ₀ dν
    linarith [φ2_eq, (integral_prod_symm (fun z : α × β => φ z ^ 2) hφ2_int).symm]
  -- Step B: ∫h² - c² ≤ ∫y ∫x φ(x,y)² dμ₀ dν
  -- Key identity (a.e.): h(x) - c = ∫y φ(x,y) dν  (since ∫g dν = c)
  -- Holds for a.e. x where fun y => f(x,y) is integrable (Fubini)
  have hcenter : ∀ᵐ x ∂μ₀, h x - c = ∫ y, φ (x, y) ∂ν := by
    filter_upwards [hfint.prod_right_ae] with x hfx
    simp only [hφ_def, h]
    rw [← hcg]
    exact (integral_sub hfx (hg_lp.integrable (by norm_num))).symm
  -- Slice MemLp 2: for a.e. x, φ(x,·) ∈ L²(ν)
  have hslice_φ_lp : ∀ᵐ x ∂μ₀, MemLp (fun y => φ (x, y)) 2 ν := by
    have hslice_aesm : ∀ᵐ x ∂μ₀, AEStronglyMeasurable (fun y => φ (x, y)) ν :=
      hφ_lp.aestronglyMeasurable.prodMk_left
    have hslice_sq : ∀ᵐ x ∂μ₀, Integrable (fun y => φ (x, y) ^ 2) ν :=
      hφ2_int.prod_right_ae
    filter_upwards [hslice_aesm, hslice_sq] with x ha hq
    exact (memLp_two_iff_integrable_sq ha).mpr hq
  -- Rewrite LHS: ∫h² - c² = ∫(h-c)²  (using Var[h] = ∫h² - c² = ∫(h-c)²)
  have lhs_eq : ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 = ∫ x, (h x - c) ^ 2 ∂μ₀ := by
    have hVar1 : variance h μ₀ = ∫ x, h x ^ 2 ∂μ₀ - c ^ 2 := by
      rw [variance_eq_sub hh_lp, hch]; simp [Pi.pow_apply]
    have hVar2 : variance h μ₀ = ∫ x, (h x - c) ^ 2 ∂μ₀ := by
      rw [variance_eq_integral hh_lp.aemeasurable, hch]
    linarith [hVar1, hVar2]
  rw [stepA, lhs_eq]
  -- Fubini swap: ∫y ∫x φ² dμ₀ dν = ∫x ∫y φ² dν dμ₀
  rw [show ∫ y, (∫ x, φ (x, y) ^ 2 ∂μ₀) ∂ν =
      ∫ x, (∫ y, φ (x, y) ^ 2 ∂ν) ∂μ₀ from
    (integral_integral_swap (f := fun x y => φ (x, y) ^ 2) hφ2_int).symm]
  -- Integrability of (h-c)² and ∫y φ² dν (function of x)
  have h_int_lhs : Integrable (fun x => (h x - c) ^ 2) μ₀ :=
    (hh_lp.integrable_sq.sub ((hh_lp.integrable (by norm_num)).const_mul (2 * c))).add
      (integrable_const (c ^ 2)) |>.congr
        (ae_of_all _ fun x => by simp only [Pi.add_apply, Pi.sub_apply]; ring)
  have h_int_rhs : Integrable (fun x => ∫ y, φ (x, y) ^ 2 ∂ν) μ₀ :=
    hφ2_int.integral_norm_prod_left.congr
      (ae_of_all _ fun x => integral_congr_ae
        (ae_of_all _ fun y => Real.norm_of_nonneg (sq_nonneg _)))
  -- Apply integral_mono_ae: a.e. (h(x)-c)² = (∫y φ dν)² ≤ ∫y φ² dν  by Jensen
  apply integral_mono_ae h_int_lhs h_int_rhs
  filter_upwards [hcenter, hslice_φ_lp] with x hcx hφx
  rw [hcx]
  exact sq_integral_le_integral_sq ν (fun y => φ (x, y)) hφx

end ANOVA

/-- **Jensen comparison for Efron-Stein** (sorry):
For `g = condExpExceptCoord μ i₀ f` (`sigmaAlgExcept i₀`-measurable) and `j ≠ i₀`:
  `(Measure.pi μ)[Var[g | G_j^except]] ≤ (Measure.pi μ)[Var[f | G_j^except]]`

**Proof sketch** (product Fubini for condExp, not yet in Mathlib):
For product measures, the key identity holds a.e.:
  `g(x) - E[g | G_j^e](x) = E[f(·) - E[f | G_j^e](·) | G_{i₀}^e](x)`
By conditional Jensen `(E[φ|G])² ≤ E[φ²|G]` and Fubini, integrating gives the bound. -/
private lemma efron_stein_condVar_le_of_condExp
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ) (hf : MemLp f 2 (Measure.pi μ))
    (i₀ j : ι) (hij : j ≠ i₀) :
    (Measure.pi μ)[Var[condExpExceptCoord μ i₀ f; Measure.pi μ | sigmaAlgExcept j]] ≤
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] := by
  sorry

/-- Internal induction for `efron_stein_core` on `n = Fintype.card ι`. -/
private theorem efron_stein_core_gen (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι]
      {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (∀ j, X j) → ℝ),
      Fintype.card ι = n →
      MemLp f 2 (Measure.pi μ) →
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  induction n with
  | zero =>
    intro ι _ X _ μ _ f hn hf
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp [variance_pi_of_isEmpty μ f]
  | succ n ih =>
    intro ι _ X _ μ _ f hn hf
    classical
    have hpos : 0 < Fintype.card ι := hn ▸ Nat.succ_pos n
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp hpos
    -- g = E[f | G_{i₀}^except], the marginal of f averaging out coordinate i₀
    set g := condExpExceptCoord μ i₀ f with hg_def
    have hg : MemLp g 2 (Measure.pi μ) := hf.condExp
    -- Law of Total Variance for coordinate i₀:
    --   E[Var[f | G_{i₀}^e]] + Var[g] = Var[f]
    have hltv : (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i₀]] +
        Var[g; Measure.pi μ] = Var[f; Measure.pi μ] :=
      integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i₀)
        (μ := Measure.pi μ) hf
    -- g is G_{i₀}^e-measurable, so E[g | G_{i₀}^e] = g pointwise
    have hcondExp_g : (Measure.pi μ)[g | sigmaAlgExcept i₀] = g :=
      condExp_of_stronglyMeasurable (sigmaAlgExcept_le (X := X) i₀)
        stronglyMeasurable_condExp (hg.integrable (by norm_num))
    -- Hence E[Var[g | G_{i₀}^e]] = 0 by LTV for g
    have hltv_g : (Measure.pi μ)[Var[g; Measure.pi μ | sigmaAlgExcept i₀]] = 0 := by
      have hltv2 := integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i₀)
        (μ := Measure.pi μ) hg
      simp only [hcondExp_g] at hltv2
      linarith [variance_nonneg g (Measure.pi μ)]
    -- Sum decomposition: Σᵢ = E[Var[f|G_{i₀}^e]] + Σ_{j≠i₀}
    have hsum_f :
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] =
        (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i₀]] +
        ∑ j ∈ Finset.univ.erase i₀,
          (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀)).symm.trans (add_comm _ _)
    -- Key bound: Var[g] ≤ Σ_{j≠i₀} E[Var[f | G_j^e]]
    -- (sorry: requires IH on ι' = {j // j ≠ i₀} via product measure transport
    --  + Jensen comparison from efron_stein_condVar_le_of_condExp)
    have hg_bound : Var[g; Measure.pi μ] ≤
        ∑ j ∈ Finset.univ.erase i₀,
          (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] := by
      sorry
    -- Conclude: Var[f] = E[Var[f|G_{i₀}^e]] + Var[g]
    --                  ≤ E[Var[f|G_{i₀}^e]] + Σ_{j≠i₀} E[Var[f|G_j^e]]
    --                  = Σᵢ E[Var[f|G_i^e]]
    linarith [hltv, hg_bound, hsum_f.ge]

/-- **Efron-Stein core** (Theorem 3.1):
For independent random variables X₁,...,Xₙ on a product probability space
and a square-integrable function f, variance is bounded by the sum of conditional variances:
  `Var[f] ≤ Σᵢ (Measure.pi μ)[Var[f | G_i^except]]`

**Proof**: By induction on `n = Fintype.card ι` (see `efron_stein_core_gen`).
- Base n = 0: Trivial (ι empty, f constant, variance = 0).
- Step n → n+1: Fix i₀. LTV gives Var[f] = E[Var[f|G_{i₀}^e]] + Var[g].
  Apply key bound Var[g] ≤ Σ_{j≠i₀} E[Var[f|G_j^e]] (sorry: IH + Jensen comparison).
  Sum decomposition gives the result.

Remaining sorry: `hg_bound` in `efron_stein_core_gen`, which needs:
1. IH transport: applying the (n-1)-dim IH to g via the product measure decomposition.
2. Jensen comparison: `efron_stein_condVar_le_of_condExp` (also sorry).
Both require product-measure Fubini for conditional expectations (not in Mathlib). -/
theorem efron_stein_core
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] :=
  efron_stein_core_gen (Fintype.card ι) μ f rfl hf

/-- **ANOVA key inequality** (consequence of Efron-Stein):
For the product probability measure `Measure.pi μ` with n = `Fintype.card ι` coordinates,
the sum of variances of marginal conditional expectations satisfies:
  `∑ᵢ Var[E[f|G_i^except]] ≤ (n-1) · Var[f]`

**Proof**: Follows from Efron-Stein (`efron_stein_core`) plus the law of total variance.
By LTV: `E[Var[f|Gᵢ]] + Var[E[f|Gᵢ]] = Var[f]`, so summing over all i:
  `∑ᵢ E[Var[f|Gᵢ]] + ∑ᵢ Var[E[f|Gᵢ]] = n · Var[f]`
By Efron-Stein: `Var[f] ≤ ∑ᵢ E[Var[f|Gᵢ]]`
Therefore: `∑ᵢ Var[E[f|Gᵢ]] = n · Var[f] - ∑ᵢ E[Var[f|Gᵢ]] ≤ n · Var[f] - Var[f] = (n-1) · Var[f]`
-/
lemma efron_stein_anova_key
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∑ i : ι,
      Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ] ≤
    ((Fintype.card ι : ℝ) - 1) * Var[f; Measure.pi μ] := by
  -- Law of total variance for each coordinate i:
  --   E[Var[f|Gᵢ]] + Var[E[f|Gᵢ]] = Var[f]
  have hltv : ∀ i : ι,
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] +
        Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ] = Var[f; Measure.pi μ] :=
    fun i => integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i)
              (μ := Measure.pi μ) hf
  -- Sum over all i: ∑ E[Var[f|Gᵢ]] + ∑ Var[E[f|Gᵢ]] = n · Var[f]
  have hsum :
      (∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) +
        (∑ i : ι, Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ]) =
        (Fintype.card ι : ℝ) * Var[f; Measure.pi μ] := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hltv]
    simp [Finset.sum_const, nsmul_eq_mul]
  -- By Efron-Stein: Var[f] ≤ ∑ E[Var[f|Gᵢ]]
  have hES := efron_stein_core (μ := μ) f hf
  -- Arithmetic: (A + B = n·V) and (V ≤ A) implies B ≤ (n-1)·V
  linarith

/-- Efron-Stein in integral form from an already-established integral bound.
Kept as a compatibility wrapper. -/
theorem efron_stein_of_integral_bound
    (f : (∀ j, X j) → ℝ)
    (hES :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  exact hES

/-- One Efron-Stein summand equals the integral of the conditional variance
with respect to the sigma-algebra that forgets coordinate `i`. -/
lemma efron_stein_term_eq_integral_condVar_exceptCoord
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) =
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  classical
  have hm : sigmaAlgExcept i ≤ (inferInstance : MeasurableSpace (∀ j, X j)) :=
    sigmaAlgExcept_le (X := X) i
  have hfi : Integrable (fun ω => (f ω - condExpExceptCoord μ i f ω) ^ 2) (Measure.pi μ) := by
    exact (hf.sub hf.condExp).integrable_sq
  calc
    ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)
        = ∫ ω in Set.univ, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by simp
    _ = ∫ ω in Set.univ, (Var[f; Measure.pi μ | sigmaAlgExcept i]) ω ∂(Measure.pi μ) := by
      symm
      exact setIntegral_condVar (m := sigmaAlgExcept i) (hm := hm)
        (μ := Measure.pi μ) (X := f) (s := Set.univ) hfi (by simp)
    _ = (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by simp

/-- The full Efron-Stein right-hand side is the sum of conditional variances. -/
lemma efron_stein_rhs_eq_sum_integral_condVar
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    (∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ))
      =
    (∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using efron_stein_term_eq_integral_condVar_exceptCoord (μ := μ) i f hf

/-- Efron-Stein in conditional-variance-sum form:
if `Var[f]` is bounded by the sum of conditional variances, then it is bounded
by the standard Efron-Stein integral right-hand side. -/
theorem efron_stein_of_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ))
    (hCondVar :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  have hEq :=
    efron_stein_rhs_eq_sum_integral_condVar (μ := μ) f hf
  calc
    Var[f; Measure.pi μ]
      ≤ ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := hCondVar
    _ = ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
      simpa [eq_comm] using hEq

/-- **Efron-Stein Inequality** (Theorem 3.1):
For independent random variables X₁,...,Xₙ and a square-integrable function f:
  `Var[f(X)] ≤ Σᵢ E[(f(X) - E^{(i)}[f(X)])²]`
where `E^{(i)}` is the conditional expectation averaging out coordinate i.

This version requires no external hypothesis: the core inequality is
established via `efron_stein_core` (sorry, martingale telescoping argument). -/
theorem efron_stein
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) :=
  efron_stein_of_condVar_sum_bound (μ := μ) f hf (efron_stein_core (μ := μ) f hf)

/-- Convert an Efron-Stein integral-form bound to the equivalent
conditional-variance-sum form. -/
theorem efron_stein_to_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ))
    (hES :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  simpa [efron_stein_rhs_eq_sum_integral_condVar (μ := μ) f hf] using hES

/-- Efron-Stein integral form and conditional-variance-sum form are equivalent. -/
theorem efron_stein_iff_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    (Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ))
      ↔
    (Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) := by
  constructor
  · intro hES
    exact efron_stein_to_condVar_sum_bound (μ := μ) f hf hES
  · intro hCondVar
    exact efron_stein_of_condVar_sum_bound (μ := μ) f hf hCondVar

/-- The Efron-Stein right-hand side is always nonnegative. -/
lemma efron_stein_rhs_nonneg
    (f : (∀ j, X j) → ℝ) :
    0 ≤ ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  classical
  refine Finset.sum_nonneg ?_
  intro i hi
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Single-coordinate case (`|ι| = 1`): Efron-Stein is exact. -/
theorem efron_stein_unique_eq
    [Unique ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] =
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  classical
  have hsig : sigmaAlgExcept (default : ι) = (⊥ : MeasurableSpace (∀ j, X j)) :=
    sigmaAlgExcept_eq_bot (X := X) (default : ι)
  have hterm :
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ) =
        Var[f; Measure.pi μ] := by
    calc
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ)
          = (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept (default : ι)]] :=
        efron_stein_term_eq_integral_condVar_exceptCoord (μ := μ) (default : ι) f hf
      _ = (Measure.pi μ)[Var[f; Measure.pi μ | (⊥ : MeasurableSpace (∀ j, X j))]] := by
        simp [hsig]
      _ = ∫ ω, (Var[f; Measure.pi μ | (⊥ : MeasurableSpace (∀ j, X j))]) ω ∂(Measure.pi μ) := by
        rfl
      _ = ∫ ω, Var[f; Measure.pi μ] ∂(Measure.pi μ) := by
        simp [condVar_bot (μ := Measure.pi μ) (hX := hf.aemeasurable)]
      _ = Var[f; Measure.pi μ] := by simp
  have hsum :
      (∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) =
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ) := by
    exact (Fintype.sum_unique (f := fun i : ι =>
      ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)))
  rw [hsum, hterm]

/-- Single-coordinate case (`|ι| = 1`): inequality form. -/
theorem efron_stein_unique
    [Unique ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  exact (efron_stein_unique_eq (μ := μ) f hf).le

/-- Efron-Stein core for a single-coordinate index type (`|ι| = 1`):
follows from `efron_stein_unique` (exact equality) converted to the
conditional-variance-sum form via `efron_stein_iff_condVar_sum_bound`. -/
lemma efron_stein_core_unique [Unique ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] :=
  (efron_stein_iff_condVar_sum_bound (μ := μ) f hf).mp (efron_stein_unique (μ := μ) f hf)

end

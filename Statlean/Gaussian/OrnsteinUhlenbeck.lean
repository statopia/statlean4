import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
import Statlean.Entropy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Ornstein-Uhlenbeck Semigroup for 1D Gaussian LSI

The OU semigroup on L²(γ) via the Mehler formula:
  `P_t f(x) = E_Y[f(e^{-t}·x + √(1 - e^{-2t})·Y)]`
where `Y ~ N(0,1)`.

## Main results

The goal is to decompose the 1D Gaussian log-Sobolev inequality
  `Ent_γ(f²) ≤ 2 · ∫ (f')² dγ`
into independently attackable sub-lemmas via the Bakry-Emery criterion:

1. **OU invariance**: `∫ P_t f dγ = ∫ f dγ`
2. **OU commutation**: `(P_t f)'(x) = e^{-t} · P_t(f')(x)`
3. **OU convergence**: `P_t f(x) → E_γ[f]` as `t → ∞`
4. **Entropy dissipation**: `d/dt Ent_γ(P_t g) = -I_γ(P_t g)`
5. **Fisher contraction**: `I_γ(P_t g) ≤ e^{-2t} · I_γ(g)`

Combining: `Ent(g) = ∫₀^∞ I(P_t g) dt ≤ I(g)/2 = 2∫(f')²`.

## Sorry count: 5 (sub-lemmas 1-5 above)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace Statlean.Gaussian

/-! ## Definition -/

/-- The Ornstein-Uhlenbeck semigroup via the Mehler formula.
    For `t ≥ 0`, this is a well-defined contraction on L²(γ). -/
def ouSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ∂stdGaussian

/-- At time 0, the OU semigroup is the identity. -/
lemma ouSemigroup_zero (f : ℝ → ℝ) (x : ℝ) :
    ouSemigroup 0 f x = f x := by
  simp only [ouSemigroup, neg_zero, exp_zero, one_mul, mul_zero,
    sub_self, sqrt_zero, zero_mul, add_zero]
  simp [integral_const]

/-! ## Sub-lemma 1: OU invariance

The Gaussian measure is invariant under P_t:
  `∫ P_t f dγ = ∫ f dγ`

Proof: By Fubini, `∫∫ f(e^{-t}x + √(1-e^{-2t})y) dγ(y) dγ(x) = ∫ f(z) dγ(z)`
since `z = e^{-t}X + √(1-e^{-2t})Y ~ N(0,1)` when `X, Y` iid `N(0,1)`
(because `e^{-2t} + (1-e^{-2t}) = 1`).

Uses: `gaussianReal_add_gaussianReal_of_indepFun`, `gaussianReal_map_const_mul`. -/
lemma integral_ouSemigroup (t : ℝ) (ht : 0 ≤ t)
    (f : ℝ → ℝ) (hf : Integrable f stdGaussian) :
    ∫ x, ouSemigroup t f x ∂stdGaussian = ∫ x, f x ∂stdGaussian := by
  simp only [ouSemigroup, stdGaussian]
  set a := exp (-t) with ha_def
  set b := sqrt (1 - exp (-2 * t)) with hb_def
  have hb_nn : 0 ≤ 1 - exp (-2 * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [ha_def, hb_def, sq_sqrt hb_nn]
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, pow_one, ← exp_add]; ring_nf
  have hφ_meas : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  -- Key: the affine map (a, b) on N(0,1)² preserves N(0,1) since a²+b²=1
  have hmap : Measure.map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) (Prod.snd : ℝ × ℝ → ℝ)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map
        measurable_fst.aemeasurable measurable_snd.aemeasurable]
      simp [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ]
    have hind2 : IndepFun (fun p : ℝ × ℝ => a * p.1) (fun p : ℝ × ℝ => b * p.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      hind.comp (measurable_const.mul measurable_id : Measurable (fun x : ℝ => a * x))
                (measurable_const.mul measurable_id : Measurable (fun y : ℝ => b * y))
    have hmap_a : Measure.map (fun p : ℝ × ℝ => a * p.1)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 ⟨a ^ 2, sq_nonneg a⟩ := by
      rw [show Measure.map (fun p : ℝ × ℝ => a * p.1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
              Measure.map (fun x => a * x) (Measure.map (Prod.fst : ℝ × ℝ → ℝ)
                ((gaussianReal 0 1).prod (gaussianReal 0 1))) from
            (Measure.map_map (measurable_const.mul measurable_id) measurable_fst).symm,
           Measure.map_fst_prod, measure_univ, one_smul, gaussianReal_map_const_mul]
      simp [mul_comm]
    have hmap_b : Measure.map (fun p : ℝ × ℝ => b * p.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 ⟨b ^ 2, sq_nonneg b⟩ := by
      rw [show Measure.map (fun p : ℝ × ℝ => b * p.2) ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
              Measure.map (fun y => b * y) (Measure.map (Prod.snd : ℝ × ℝ → ℝ)
                ((gaussianReal 0 1).prod (gaussianReal 0 1))) from
            (Measure.map_map (measurable_const.mul measurable_id) measurable_snd).symm,
           Measure.map_snd_prod, measure_univ, one_smul, gaussianReal_map_const_mul]
      simp [mul_comm]
    have hmap_sum : Measure.map ((fun p : ℝ × ℝ => a * p.1) + (fun p : ℝ × ℝ => b * p.2))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) =
        gaussianReal (0 + 0) (⟨a ^ 2, sq_nonneg a⟩ + ⟨b ^ 2, sq_nonneg b⟩) :=
      gaussianReal_add_gaussianReal_of_indepFun hind2 hmap_a hmap_b
    rw [show (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
            (fun p : ℝ × ℝ => a * p.1) + (fun p : ℝ × ℝ => b * p.2) by funext p; rfl,
        hmap_sum]
    simp only [add_zero]; congr 1; ext; simp [NNReal.coe_add, hab]
  -- Convert hf to use gaussianReal 0 1 explicitly
  have hfγ : Integrable f (gaussianReal 0 1) := hf
  -- Integrability of the composed function under product measure (via change of variables)
  have hfφ_int : Integrable (fun p : ℝ × ℝ => f (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [show (fun p : ℝ × ℝ => f (a * p.1 + b * p.2)) =
        f ∘ (fun p : ℝ × ℝ => a * p.1 + b * p.2) from rfl]
    rw [← hmap] at hfγ; exact hfγ.comp_measurable hφ_meas
  -- LHS = ∫_p f(a·p.1+b·p.2) d(γ⊗γ)  [Fubini]
  -- = ∫_z f(z) d(map φ (γ⊗γ))         [change of variables]
  -- = ∫_z f(z) dγ                      [map equality]
  rw [← integral_prod _ hfφ_int,
      ← integral_map hφ_meas.aemeasurable (by rw [hmap]; exact hfγ.aestronglyMeasurable),
      hmap]

/-! ## Sub-lemma 2: OU spatial commutation

The OU semigroup commutes with spatial differentiation up to a factor:
  `d/dx P_t f(x) = e^{-t} · P_t(f')(x)`

Proof: From the Mehler formula, `d/dx f(e^{-t}x + √(...)y) = e^{-t} · f'(e^{-t}x + √(...)y)`.
Exchange `d/dx` with `∫` by dominated convergence (using `f' ∈ L²(γ)`). -/
lemma ouSemigroup_hasDerivAt (t : ℝ) (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'_bound : ∃ C, ∀ x, ‖f' x‖ ≤ C)
    (hf_int : ∀ x, Integrable (fun y => f (exp (-t) * x +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian)
    (x : ℝ) :
    HasDerivAt (ouSemigroup t f) (exp (-t) * ouSemigroup t f' x) x := by
  set a := exp (-t)
  set c := sqrt (1 - exp (-2 * t))
  simp only [ouSemigroup]
  -- Rewrite target: a * ∫ f'(...) = ∫ a * f'(...)
  have hgoal : a * ∫ y, f' (a * x + c * y) ∂stdGaussian =
      ∫ y, a * f' (a * x + c * y) ∂stdGaussian := by
    simp_rw [← smul_eq_mul (a := a)]
    exact (integral_smul a _).symm
  rw [hgoal]
  -- Apply Leibniz rule (differentiation under the integral)
  obtain ⟨C, hC⟩ := hf'_bound
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y => f (a * x + c * y))
    (F' := fun x y => a * f' (a * x + c * y))
    (bound := fun _ => ‖a‖ * C)
    (s := Set.univ)
    (Filter.univ_mem' (fun _ => Set.mem_univ _))
    -- ae measurability of F x
    (Eventually.of_forall fun x' =>
      (hf_int x').aestronglyMeasurable)
    -- integrability of F x₀
    (hf_int x)
    -- ae measurability of F' x₀
    (by have hf'_eq : f' = deriv f := funext fun z => (hderiv z).deriv.symm
        rw [hf'_eq]
        have hmeas : Measurable (fun y : ℝ => deriv f (a * x + c * y)) := by
          exact (measurable_deriv f).comp
            ((measurable_const.add (measurable_const.mul measurable_id)) :
              Measurable (fun y : ℝ => a * x + c * y))
        exact hmeas.aestronglyMeasurable.const_mul _)
    -- uniform bound
    (by filter_upwards with y; intro x' _
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))
    -- bound integrable
    (integrable_const _)
    -- pointwise HasDerivAt
    (by filter_upwards with y; intro x' _
        have hinner : HasDerivAt (fun u => a * u + c * y) a x' := by
          have := (hasDerivAt_id x').const_mul a
          simp only [mul_one] at this
          exact this.add_const _
        have houter := hderiv (a * x' + c * y)
        have hcomp := houter.comp x' hinner
        simp only [mul_comm (f' _) a] at hcomp
        exact hcomp)).2

/-! ## Sub-lemma 3: OU convergence

As `t → ∞`, `P_t f(x) → E_γ[f]` for each `x`.

Proof: `e^{-t} → 0` and `√(1-e^{-2t}) → 1`, so the integrand
`f(e^{-t}x + √(1-e^{-2t})y) → f(y)` pointwise. Apply DCT with
constant dominating function from boundedness of `f`. -/
lemma ouSemigroup_tendsto (f : ℝ → ℝ) (_hf : Integrable f stdGaussian)
    (hf_cont : Continuous f) (hf_bdd : Bornology.IsBounded (Set.range f))
    (x : ℝ) :
    Tendsto (fun t => ouSemigroup t f x) atTop
      (nhds (∫ y, f y ∂stdGaussian)) := by
  simp only [ouSemigroup]
  -- Extract uniform bound from boundedness of range
  obtain ⟨r, hr⟩ := Metric.isBounded_range_iff.mp hf_bdd
  have hbound : ∀ y : ℝ, ‖f y‖ ≤ ‖f 0‖ + r := fun y => by
    have h := hr 0 y
    rw [dist_comm, Real.dist_eq] at h
    calc ‖f y‖ = ‖f 0 + (f y - f 0)‖ := by ring_nf
      _ ≤ ‖f 0‖ + ‖f y - f 0‖ := norm_add_le _ _
      _ ≤ ‖f 0‖ + r := by gcongr; rw [Real.norm_eq_abs]; exact h
  -- Pointwise convergence: exp(-t)*x + sqrt(1-exp(-2t))*y → 0 + 1*y = y
  have harg : ∀ y : ℝ,
      Tendsto (fun t : ℝ => exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)
        atTop (nhds y) := fun y => by
    have h1 : Tendsto (fun t : ℝ => exp (-t) * x) atTop (nhds 0) := by
      simp_rw [mul_comm (exp _) x]
      simpa [mul_zero] using tendsto_exp_neg_atTop_nhds_zero.const_mul x
    have h2a : Tendsto (fun t : ℝ => exp (-2 * t)) atTop (nhds 0) := by
      have hcomp : Tendsto (2 * · : ℝ → ℝ) atTop atTop :=
        Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b / 2, fun x hx => by linarith⟩)
      convert tendsto_exp_neg_atTop_nhds_zero.comp hcomp using 1
      ext t; simp [Function.comp, mul_comm 2 t]
    have h2b : Tendsto (fun t : ℝ => sqrt (1 - exp (-2 * t))) atTop (nhds 1) := by
      have hconv : Tendsto (fun t : ℝ => (1 : ℝ) - exp (-2 * t)) atTop (nhds 1) := by
        simpa [sub_zero] using h2a.const_sub (1 : ℝ)
      simpa [sqrt_one] using continuous_sqrt.continuousAt.tendsto.comp hconv
    simpa [zero_add, one_mul] using h1.add (h2b.mul_const y)
  -- Apply filter dominated convergence theorem
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f 0‖ + r)
  · -- AE strong measurability: f ∘ (affine map) is continuous
    filter_upwards with t
    exact (hf_cont.comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · -- Pointwise bound by constant ‖f 0‖ + r
    filter_upwards with t; filter_upwards with y; exact hbound _
  · -- Constant dominating function is integrable w.r.t. probability measure
    exact integrable_const _
  · -- Pointwise ae convergence by continuity of f and convergence of argument
    filter_upwards with y
    exact hf_cont.continuousAt.tendsto.comp (harg y)

/-! ## Infrastructure: Gaussian Dirichlet form (proved)

The OU generator `L = ∂² - x·∂` satisfies `∫ (Lφ)·ψ dγ = -∫ φ'·ψ' dγ`.
This follows from one application of the Stein identity to `h = φ'·ψ`. -/
lemma gaussian_dirichlet_form
    (φ' φ'' ψ ψ' : ℝ → ℝ)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x)
    (hprod : MemLp (fun x => φ' x * ψ x) 2 stdGaussian)
    (hprod' : MemLp (fun x => φ'' x * ψ x + φ' x * ψ' x) 2 stdGaussian)
    (hint_xφψ : Integrable (fun x => x * (φ' x * ψ x)) stdGaussian)
    (hint_φψ' : Integrable (fun x => φ' x * ψ' x) stdGaussian)
    (hint_φ''ψ : Integrable (fun x => φ'' x * ψ x) stdGaussian) :
    ∫ x, (φ'' x - x * φ' x) * ψ x ∂stdGaussian =
      -(∫ x, φ' x * ψ' x ∂stdGaussian) := by
  have hstein := stein_identity (fun x => φ' x * ψ x)
    (fun x => φ'' x * ψ x + φ' x * ψ' x) hprod hprod'
    (fun x => (hφ' x).mul (hψ x))
  simp only [] at hstein
  have h_add : ∫ x, (φ'' x * ψ x + φ' x * ψ' x) ∂stdGaussian =
      ∫ x, φ'' x * ψ x ∂stdGaussian +
        ∫ x, φ' x * ψ' x ∂stdGaussian :=
    integral_add hint_φ''ψ hint_φψ'
  rw [h_add] at hstein
  have h_sub : ∫ x, (φ'' x - x * φ' x) * ψ x ∂stdGaussian =
      ∫ x, φ'' x * ψ x ∂stdGaussian -
        ∫ x, x * (φ' x * ψ x) ∂stdGaussian := by
    rw [← integral_sub hint_φ''ψ hint_xφψ]
    congr 1; ext x; ring
  rw [h_sub]; linarith

/-! ## Sub-lemma 4: Entropy dissipation

For `g ≥ 0` with `∫ g dγ = 1` and `g·log(g) ∈ L¹(γ)`, and `P_t g > 0` a.e. for `t > 0`:
  `d/dt Ent_γ(P_t g) = -I_γ(P_t g)`

where `I_γ(h) = ∫ (h')²/h dγ` is the Fisher information.

Proof:
  `d/dt ∫ (P_t g) log(P_t g) dγ = ∫ (∂_t P_t g)(1 + log(P_t g)) dγ`  (Leibniz rule)
  `= ∫ (L P_t g)(1 + log(P_t g)) dγ`  (OU equation: ∂_t P_t g = L P_t g)
  `= -∫ (P_t g)' · (P_t g)'/(P_t g) dγ`  (Gaussian IBP: ∫ Lφ·ψ dγ = -∫ φ'ψ' dγ)
  `= -I_γ(P_t g)`.

This is the deepest sub-lemma: requires OU equation +
differentiation under integral + Gaussian IBP. -/
lemma entropy_dissipation (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg'_int : MemLp g' 2 stdGaussian)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x) :
    HasDerivAt (fun s => ∫ x, ouSemigroup s g x * log (ouSemigroup s g x) ∂stdGaussian)
      (-(∫ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x ∂stdGaussian))
      t := by
  sorry

/-! ## Pointwise Cauchy-Schwarz for OU semigroup

For `g > 0` a.e., `(P_t g')(x)² / P_t g(x) ≤ P_t(g'²/g)(x)`.

This is Jensen's inequality for the convex function `u ↦ u²/a`:
  `(∫ h dν)² / (∫ k dν) ≤ ∫ (h²/k) dν`
when `k > 0` a.e. Equivalently, writing `h = √k · (h/√k)`,
Cauchy-Schwarz gives `(∫ h)² ≤ (∫ k)(∫ h²/k)`.

Blocker: needs integral Cauchy-Schwarz for conditional expectations.
Estimated effort: B-grade (~60 lines). -/
private lemma ouSemigroup_sq_div_le (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x) (x : ℝ) :
    ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
      ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
  sorry

/-! ## Sub-lemma 5: Fisher information contraction

For `g ≥ 0`, `g > 0` a.e., `g' ∈ L²(γ)`:
  `I_γ(P_t g) ≤ e^{-2t} · I_γ(g)`

Proof:
  `I(P_t g) = ∫ ((P_t g)')² / (P_t g) dγ`
  `= e^{-2t} · ∫ (P_t g')² / (P_t g) dγ`  (by commutation: (P_t g)' = e^{-t} P_t g')
  `≤ e^{-2t} · ∫ P_t(g'²/g) dγ`  (Cauchy-Schwarz: (E[h])² ≤ E[g]·E[h²/g])
  `= e^{-2t} · ∫ g'²/g dγ`  (by invariance: ∫ P_t φ dγ = ∫ φ dγ)
  `= e^{-2t} · I(g)`. -/
lemma fisherInfo_ouSemigroup_le (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x)
    (hg_int : Integrable g stdGaussian)
    (hg'_int : MemLp g' 2 stdGaussian)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hFisher : Integrable (fun x => g' x ^ 2 / g x) stdGaussian) :
    ∫ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x ∂stdGaussian ≤
      exp (-2 * t) * ∫ x, g' x ^ 2 / g x ∂stdGaussian := by
  -- Step 1: Factor out e^{-2t} from LHS
  have h_lhs : ∀ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x =
      exp (-2 * t) * (ouSemigroup t g' x ^ 2 / ouSemigroup t g x) := by
    intro x
    have : exp (-t) ^ 2 = exp (-2 * t) := by
      rw [← exp_nat_mul]; ring_nf
    rw [mul_pow, this, mul_div_assoc]
  simp_rw [h_lhs]
  rw [integral_const_mul]
  -- Step 2: Suffices to show ∫ (P_t g')²/(P_t g) ≤ ∫ g'²/g
  apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
  -- Step 2a: Pointwise bound via Cauchy-Schwarz
  calc ∫ x, ouSemigroup t g' x ^ 2 / ouSemigroup t g x ∂stdGaussian
      ≤ ∫ x, ouSemigroup t (fun y => g' y ^ 2 / g y) x ∂stdGaussian := by
        apply integral_mono_ae
        · sorry -- integrability of (P_t g')²/(P_t g)
        · sorry -- integrability of P_t(g'²/g)
        · exact ae_of_all _ (fun x => ouSemigroup_sq_div_le g g' t ht hg_pos x)
    -- Step 3: ∫ P_t(g'²/g) dγ = ∫ g'²/g dγ by OU invariance
    _ = ∫ x, g' x ^ 2 / g x ∂stdGaussian := by
        exact integral_ouSemigroup t ht _ hFisher

/-! ## Main theorem: 1D Gaussian LSI from OU semigroup

Combines all sub-lemmas:
  `Ent_γ(f²) ≤ 2 · ∫ (f')² dγ`

for `f, f'` in `L²(γ)` with `∫ f² = 1` and `f²·log(f²)` integrable.

Proof architecture:
  1. Set `g = f²`, `g' = 2f·f'`. Then `I(g) = ∫ (g')²/g dγ = 4∫(f')²`.
  2. For `t > 0`: `P_t g > 0` a.e. (Gaussian smoothing of nonneg function).
  3. `Ent(g) = F(0) - F(∞)` where `F(t) = ∫ (P_t g)·log(P_t g) dγ`:
     - `F(∞) = (∫g)·log(∫g) = 1·log(1) = 0` (by OU convergence + ∫g=1).
     - By entropy dissipation: `F(0) - F(∞) = ∫₀^∞ I(P_t g) dt`.
  4. By Fisher contraction: `I(P_t g) ≤ e^{-2t} · I(g)`.
  5. `Ent(g) ≤ ∫₀^∞ e^{-2t} dt · I(g) = I(g)/2 = 2∫(f')²`. -/
theorem gaussian_lsi_normalized_from_ou
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hnorm : ∫ x, f x ^ 2 ∂stdGaussian = 1)
    (hint : Integrable (fun x => f x ^ 2 * log (f x ^ 2)) stdGaussian) :
    ∫ x, f x ^ 2 * log (f x ^ 2) ∂stdGaussian ≤
      2 * ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- This proof combines sub-lemmas 1-5 above.
  -- Currently sorry'd; the wiring itself is ~30 lines once sub-lemmas are proved.
  sorry

end Statlean.Gaussian

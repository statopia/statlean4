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
/-- The OU generator L applied to P_t g, defined pointwise as
    L(P_t g)(x) = (P_t g)''(x) - x · (P_t g)'(x). -/
private noncomputable def ouGeneratorAt (t : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (ouSemigroup t g)) x - x * deriv (ouSemigroup t g) x

/-- OU equation: the time derivative of P_t g equals L(P_t g) pointwise.
    ∂_t P_t g(x) = (P_t g)''(x) - x · (P_t g)'(x)

Proof sketch: Differentiate the Mehler integral ∫ g(e^{-s}x + √(1-e^{-2s})y) dγ(y)
w.r.t. s. The chain rule gives -e^{-s}·x·g'(arg) + (e^{-2s}/√(1-e^{-2s}))·y·g'(arg).
Then show this equals L(P_s g)(x) using the spatial derivatives of P_s g.

Blocker: requires second-order Leibniz rule (differentiating ∫ under two derivatives).
Estimated effort: A-grade (~150-200 lines). -/
private lemma ouSemigroup_time_deriv (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_int : Integrable g stdGaussian)
    (x : ℝ) :
    HasDerivAt (fun s => ouSemigroup s g x) (ouGeneratorAt t g x) t := by
  sorry

/-- Leibniz rule for entropy functional: if F(s) = ∫ P_s g · log(P_s g) dγ, then
    F'(t) = ∫ (∂_t P_t g)(x) · (1 + log(P_t g(x))) dγ(x).

Uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
pointwise derivative d/ds [u·log u] = (1 + log u)·u'.

Blocker: needs dominated convergence with a uniform bound on
|(∂_s P_s g)(1 + log(P_s g))| near s = t.
Estimated effort: B-grade (~80 lines). -/
private lemma entropy_hasDerivAt_of_time_deriv (g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hPt_pos : ∀ᵐ x ∂stdGaussian, 0 < ouSemigroup t g x)
    (htime_deriv : ∀ x, HasDerivAt (fun s => ouSemigroup s g x)
      (ouGeneratorAt t g x) t)
    (hint : Integrable (fun x => ouGeneratorAt t g x *
      (1 + log (ouSemigroup t g x))) stdGaussian)
    (hent_int : ∀ᶠ s in nhds t, Integrable (fun x =>
      ouSemigroup s g x * log (ouSemigroup s g x)) stdGaussian) :
    HasDerivAt (fun s => ∫ x, ouSemigroup s g x * log (ouSemigroup s g x) ∂stdGaussian)
      (∫ x, ouGeneratorAt t g x * (1 + log (ouSemigroup t g x)) ∂stdGaussian)
      t := by
  sorry

/-- The OU generator integrated against (1 + log(P_t g)) gives the negative Fisher info.

    ∫ L(P_t g) · (1 + log(P_t g)) dγ
    = -∫ (P_t g)' · (1 + log(P_t g))' dγ     [gaussian_dirichlet_form]
    = -∫ (P_t g)' · (P_t g)'/(P_t g) dγ       [chain rule: (log h)' = h'/h]
    = -∫ (e^{-t} P_t g')² / (P_t g) dγ        [OU commutation: (P_t g)' = e^{-t} P_t g']

Blocker: integrability hypotheses for gaussian_dirichlet_form application.
Estimated effort: B-grade (~60-80 lines). -/
private lemma dirichlet_form_entropy (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg'_int : MemLp g' 2 stdGaussian)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hPt_pos : ∀ᵐ x ∂stdGaussian, 0 < ouSemigroup t g x)
    -- Additional regularity hypotheses needed for gaussian_dirichlet_form application
    -- Blocker: these follow from smoothness of P_t g under the Gaussian kernel,
    -- but proving them requires substantial regularity theory.
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_int_all : ∀ x, Integrable (fun y => g (exp (-t) * x +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian)
    (hg'_int_all : ∀ x, Integrable (fun y => g' (exp (-t) * x +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian)
    (hPt_pos_all : ∀ x, 0 < ouSemigroup t g x)
    (hPt_g'_bound : ∃ C, ∀ x, ‖ouSemigroup t g' x‖ ≤ C)
    (hPt_hasDerivAt2 : ∀ x, HasDerivAt (fun z => exp (-t) * ouSemigroup t g' z)
      (deriv (fun z => exp (-t) * ouSemigroup t g' z) x) x)
    (hprod_memLp : MemLp (fun x => deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x))) 2 stdGaussian)
    (hprod'_memLp : MemLp (fun x =>
      deriv (deriv (ouSemigroup t g)) x * (1 + log (ouSemigroup t g x)) +
      deriv (ouSemigroup t g) x * (deriv (ouSemigroup t g) x / ouSemigroup t g x))
      2 stdGaussian)
    (hint_xφψ : Integrable (fun x => x * (deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x)))) stdGaussian)
    (hint_φψ' : Integrable (fun x => deriv (ouSemigroup t g) x *
      (deriv (ouSemigroup t g) x / ouSemigroup t g x)) stdGaussian)
    (hint_φ''ψ : Integrable (fun x => deriv (deriv (ouSemigroup t g)) x *
      (1 + log (ouSemigroup t g x))) stdGaussian) :
    ∫ x, ouGeneratorAt t g x * (1 + log (ouSemigroup t g x)) ∂stdGaussian =
    -(∫ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x ∂stdGaussian) := by
  -- Step 1: Establish that deriv(P_t g) = e^{-t} * P_t g' via commutation
  have hcomm : ∀ x, HasDerivAt (ouSemigroup t g) (exp (-t) * ouSemigroup t g' x) x :=
    fun x => ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound hg_int_all x
  have hderiv_eq : deriv (ouSemigroup t g) = fun x => exp (-t) * ouSemigroup t g' x :=
    funext fun x => (hcomm x).deriv
  -- Step 2: ψ = 1 + log(P_t g), ψ' = (P_t g)'/(P_t g) = deriv(P_t g)/P_t g
  -- HasDerivAt for ψ x = 1 + log(P_t g x)
  have hψ_deriv : ∀ x, HasDerivAt (fun z => 1 + log (ouSemigroup t g z))
      (deriv (ouSemigroup t g) x / ouSemigroup t g x) x := by
    intro x
    have hlog := HasDerivAt.log (hcomm x) (ne_of_gt (hPt_pos_all x))
    -- hlog : HasDerivAt (fun z => log(P_t g z)) ((e^{-t} * P_t g' x) / P_t g x) x
    have h1 := hasDerivAt_const x (1 : ℝ)
    have := h1.add hlog
    simp only [zero_add] at this
    -- this has derivative (e^{-t} * P_t g' x) / P_t g x
    -- We need to show this = deriv(P_t g) x / P_t g x
    rw [hderiv_eq]
    exact this
  -- Step 3: Apply gaussian_dirichlet_form with
  --   φ' = deriv(P_t g), φ'' = deriv(deriv(P_t g))
  --   ψ = 1 + log(P_t g), ψ' = deriv(P_t g) / P_t g
  have hφ_deriv : ∀ x, HasDerivAt (deriv (ouSemigroup t g))
      (deriv (deriv (ouSemigroup t g)) x) x := by
    intro x
    rw [hderiv_eq]
    exact hPt_hasDerivAt2 x
  have hgdf := gaussian_dirichlet_form
    (deriv (ouSemigroup t g))
    (deriv (deriv (ouSemigroup t g)))
    (fun x => 1 + log (ouSemigroup t g x))
    (fun x => deriv (ouSemigroup t g) x / ouSemigroup t g x)
    hφ_deriv hψ_deriv
    hprod_memLp hprod'_memLp hint_xφψ hint_φψ' hint_φ''ψ
  -- Step 4: Unfold ouGeneratorAt and apply hgdf
  simp only [ouGeneratorAt] at *
  rw [hgdf]
  -- Step 5: RHS matching — show φ'·ψ' = (e^{-t} P_t g')² / P_t g
  congr 1; congr 1; ext x
  rw [hderiv_eq]; ring

/-- Positivity of the OU semigroup: P_t g > 0 a.e. when g ≥ 0 a.e. and ∫ g > 0.
    This follows from P_t g(x) = ∫ g(e^{-t}x + √(1-e^{-2t})y) dγ(y) > 0
    since g ≥ 0 with positive integral implies g > 0 on a set of positive measure,
    and the Gaussian kernel spreads this positivity everywhere.

Estimated effort: B-grade (~40-60 lines). -/
private lemma ouSemigroup_pos_ae (g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian) :
    ∀ᵐ x ∂stdGaussian, 0 < ouSemigroup t g x := by
  sorry

lemma entropy_dissipation (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian)
    (hg'_int : MemLp g' 2 stdGaussian)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    -- integrability of generator term times log (follows from regularity of P_t g)
    (hint_gen : Integrable (fun x => ouGeneratorAt t g x *
      (1 + log (ouSemigroup t g x))) stdGaussian)
    -- entropy integrable in a neighborhood of t
    (hent_int : ∀ᶠ s in nhds t, Integrable (fun x =>
      ouSemigroup s g x * log (ouSemigroup s g x)) stdGaussian) :
    HasDerivAt (fun s => ∫ x, ouSemigroup s g x * log (ouSemigroup s g x) ∂stdGaussian)
      (-(∫ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x ∂stdGaussian))
      t := by
  -- Step 0: P_t g > 0 a.e. for t > 0
  have hPt_pos := ouSemigroup_pos_ae g t ht hg_nn hg_int hg_pos_int
  -- Step 1: The OU equation holds pointwise
  have htime := fun x => ouSemigroup_time_deriv g g' t ht hg_deriv hg'_bound hg_int x
  -- Step 2: Leibniz rule gives F'(t) = ∫ L(P_t g) · (1 + log(P_t g)) dγ
  have hleib := entropy_hasDerivAt_of_time_deriv g t ht hg_nn hg_int hPt_pos htime
    hint_gen hent_int
  -- Step 3: Dirichlet form gives ∫ L(P_t g)(1+log(P_t g)) dγ = -Fisher
  -- Additional regularity hypotheses for dirichlet_form_entropy (sorry'd for now)
  have hdirich := dirichlet_form_entropy g g' t ht hg_nn hg_int hg'_int hg_deriv hPt_pos
    hg'_bound
    (sorry : ∀ x, Integrable (fun y => g (exp (-t) * x +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian)
    (sorry : ∀ x, Integrable (fun y => g' (exp (-t) * x +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian)
    (sorry : ∀ x, 0 < ouSemigroup t g x)
    (sorry : ∃ C, ∀ x, ‖ouSemigroup t g' x‖ ≤ C)
    (sorry : ∀ x, HasDerivAt (fun z => exp (-t) * ouSemigroup t g' z)
      (deriv (fun z => exp (-t) * ouSemigroup t g' z) x) x)
    (sorry : MemLp (fun x => deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x))) 2 stdGaussian)
    (sorry : MemLp (fun x =>
      deriv (deriv (ouSemigroup t g)) x * (1 + log (ouSemigroup t g x)) +
      deriv (ouSemigroup t g) x * (deriv (ouSemigroup t g) x / ouSemigroup t g x))
      2 stdGaussian)
    (sorry : Integrable (fun x => x * (deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x)))) stdGaussian)
    (sorry : Integrable (fun x => deriv (ouSemigroup t g) x *
      (deriv (ouSemigroup t g) x / ouSemigroup t g x)) stdGaussian)
    (sorry : Integrable (fun x => deriv (deriv (ouSemigroup t g)) x *
      (1 + log (ouSemigroup t g x))) stdGaussian)
  -- Step 4: Combine
  rwa [hdirich] at hleib

/-! ## Pointwise Cauchy-Schwarz for OU semigroup

For `g > 0` a.e., `(P_t g')(x)² / P_t g(x) ≤ P_t(g'²/g)(x)`.

This is Jensen's inequality for the convex function `u ↦ u²/a`:
  `(∫ h dν)² / (∫ k dν) ≤ ∫ (h²/k) dν`
when `k > 0` a.e. Equivalently, writing `h = √k · (h/√k)`,
Cauchy-Schwarz gives `(∫ h)² ≤ (∫ k)(∫ h²/k)`.

Blocker: needs integral Cauchy-Schwarz for conditional expectations.
Estimated effort: B-grade (~60 lines). -/

/-- Integral Cauchy-Schwarz in the form `(∫ h)² / (∫ k) ≤ ∫ (h²/k)`
when `k > 0` a.e. under a probability measure.

Proof: set `c = (∫ h)/(∫ k)` and expand `0 ≤ ∫ (h - c·k)²/k`. -/
private lemma integral_sq_div_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h k : ℝ → ℝ) (hk_pos : ∀ᵐ x ∂μ, 0 < k x)
    (hh_int : Integrable h μ) (hk_int : Integrable k μ)
    (hhk_int : Integrable (fun x => h x ^ 2 / k x) μ) :
    (∫ x, h x ∂μ) ^ 2 / (∫ x, k x ∂μ) ≤ ∫ x, h x ^ 2 / k x ∂μ := by
  by_cases hk_int_pos : 0 < ∫ x, k x ∂μ
  · rw [div_le_iff₀ hk_int_pos]
    set c := (∫ x, h x ∂μ) / (∫ x, k x ∂μ) with hc_def
    set A := ∫ x, h x ∂μ with hA_def
    set B := ∫ x, h x ^ 2 / k x ∂μ with hB_def
    set K := ∫ x, k x ∂μ with hK_def
    have hnn : 0 ≤ ∫ x, (h x - c * k x) ^ 2 / k x ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hk_pos] with y hky
      exact div_nonneg (sq_nonneg _) (le_of_lt hky)
    have hint1 : Integrable (fun x => h x ^ 2 / k x - 2 * c * h x) μ :=
      hhk_int.sub (hh_int.const_mul _)
    have hint2 : Integrable (fun x => c ^ 2 * k x) μ := hk_int.const_mul _
    have hexpand : ∫ x, (h x - c * k x) ^ 2 / k x ∂μ = B - 2 * c * A + c ^ 2 * K := by
      have hae : ∀ᵐ x ∂μ, (h x - c * k x) ^ 2 / k x =
          (h x ^ 2 / k x - 2 * c * h x) + c ^ 2 * k x := by
        filter_upwards [hk_pos] with y hky
        have hky_ne : k y ≠ 0 := ne_of_gt hky
        field_simp
        ring
      rw [integral_congr_ae hae, integral_add hint1 hint2,
        integral_sub hhk_int (hh_int.const_mul _),
        integral_const_mul, integral_const_mul]
    rw [hexpand] at hnn
    have hcK : c * K = A := div_mul_cancel₀ A (ne_of_gt hk_int_pos)
    nlinarith [sq_nonneg (c * K - A)]
  · have hk_nn : 0 ≤ ∫ x, k x ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hk_pos] with y hky; exact le_of_lt hky
    have hk_zero : ∫ x, k x ∂μ = 0 := le_antisymm (not_lt.mp hk_int_pos) hk_nn
    rw [hk_zero, div_zero]
    apply integral_nonneg_of_ae
    filter_upwards [hk_pos] with y hky
    exact div_nonneg (sq_nonneg _) (le_of_lt hky)

private lemma ouSemigroup_sq_div_le (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x) (x : ℝ) :
    ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
      ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
  simp only [ouSemigroup]
  -- Transfer g > 0 a.e. to the composed version g(φ(y)) > 0 a.e.
  -- This uses that φ(y) = e^{-t}x + √(1-e^{-2t})y pushes stdGaussian
  -- to a measure absolutely continuous w.r.t. stdGaussian
  have hg_comp_pos : ∀ᵐ y ∂stdGaussian,
      0 < g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) := by
    sorry -- ae transfer: g > 0 a.e.(γ) implies g∘φ > 0 a.e.(γ)
  exact integral_sq_div_le _ _ hg_comp_pos (sorry) (sorry) (sorry)

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

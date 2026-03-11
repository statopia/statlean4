import Statlean.Gaussian.Basic
import Statlean.Gaussian.Stein
import Statlean.Entropy.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Probability.Distributions.Gaussian.Fernique

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

/-! ### OU equation: time derivative = generator

The time derivative of P_t g equals L(P_t g) pointwise:
  ∂_t P_t g(x) = (P_t g)''(x) - x · (P_t g)'(x)

Proof sketch: Differentiate the Mehler integral ∫ g(e^{-s}x + √(1-e^{-2s})y) dγ(y)
w.r.t. s. The chain rule gives -e^{-s}·x·g'(arg) + (e^{-2s}/√(1-e^{-2s}))·y·g'(arg).
Then show this equals L(P_s g)(x) using the spatial derivatives of P_s g.

Estimated effort: A-grade (~150-200 lines). -/

/-- The Leibniz rule part of the OU time derivative:
    d/dt P_t g(x) = exp(-2t)*P_t(g'')(x) - x*exp(-t)*P_t(g')(x).

    Proof: Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to
    F(s,y) = g(exp(-s)*x + sqrt(1-exp(-2s))*y) with respect to s.
    The chain rule gives F'(s,y) = g'(arg) * (-exp(-s)*x + exp(-2s)/sqrt(...)*y).
    Then split the integral and apply Stein identity to the y-weighted part.

    Blocker: Leibniz dominated convergence + Stein identity composition.
    Estimated effort: B-grade (~100 lines). -/
private lemma ouSemigroup_time_deriv_leibniz (g g' g'' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg''_bound : ∃ C, ∀ x, ‖g'' x‖ ≤ C)
    (hg_int : Integrable g stdGaussian)
    (x : ℝ) :
    HasDerivAt (fun s => ouSemigroup s g x)
      (exp (-2 * t) * ouSemigroup t g'' x - x * (exp (-t) * ouSemigroup t g' x)) t := by
  simp only [ouSemigroup]
  obtain ⟨C, hC⟩ := hg'_bound
  obtain ⟨C'', hC''⟩ := hg''_bound
  have hC_nn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hg_cont : Continuous g := Differentiable.continuous
    (fun z => (hg_deriv z).differentiableAt)
  have hg'_cont : Continuous g' := Differentiable.continuous
    (fun z => (hg'_deriv z).differentiableAt)
  -- Key positivity facts
  have h1me2t_pos : 0 < 1 - exp (-2 * t) := by
    linarith [exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)]
  have hbt_pos : 0 < sqrt (1 - exp (-2 * t)) := sqrt_pos.mpr h1me2t_pos
  have hbt_ne : sqrt (1 - exp (-2 * t)) ≠ 0 := ne_of_gt hbt_pos
  -- Abbreviations for the Mehler argument at time t
  set at_ := exp (-t) * x
  set bt := sqrt (1 - exp (-2 * t))
  -- Step 1: Apply Leibniz differentiation under the integral
  -- The derivative of F(s,y) = g(exp(-s)*x + sqrt(1-exp(-2s))*y) w.r.t. s is
  -- F'(s,y) = g'(arg) * d/ds(arg) where d/ds(arg) = -exp(-s)*x + exp(-2s)/sqrt(1-exp(-2s))*y
  -- We get HasDerivAt (fun s => ∫ F(s,y) dγ(y)) (∫ F'(t,y) dγ(y)) t
  have hLeibniz : HasDerivAt (fun s => ∫ y, g (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y)
      ∂stdGaussian)
    (∫ y, g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) *
      (-exp (-t) * x + exp (-2 * t) / sqrt (1 - exp (-2 * t)) * y) ∂stdGaussian) t := by
    -- Neighborhood
    set s_set := Set.Ioo (t / 2) (3 * t / 2)
    have hs_nhds : s_set ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
    have h1me2s_pos : ∀ s ∈ s_set, 0 < 1 - exp (-2 * s) := by
      intro s hs; linarith [exp_lt_one_iff.mpr (show -2 * s < 0 by linarith [hs.1])]
    have hb_lower_pos : 0 < sqrt (1 - exp (-t)) :=
      sqrt_pos.mpr (by linarith [exp_lt_one_iff.mpr (show -t < 0 by linarith)])
    set M := 1 / sqrt (1 - exp (-t))
    -- Integrability of F(t, ·): g composed with affine
    -- g has linear growth since g' is bounded: |g(z)| ≤ |g(0)| + C*|z|
    have hg_growth : ∀ z, ‖g z‖ ≤ ‖g 0‖ + C * ‖z‖ := by
      intro z
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := g) (f' := g') (s := Set.univ) (x := 0) (y := z) (C := C)
        (fun w _ => (hg_deriv w).hasDerivWithinAt) (fun w _ => hC w)
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
      simp only [sub_zero] at hmvt
      calc ‖g z‖ = ‖(g z - g 0) + g 0‖ := by ring_nf
        _ ≤ ‖g z - g 0‖ + ‖g 0‖ := norm_add_le _ _
        _ ≤ C * ‖z‖ + ‖g 0‖ := by linarith
        _ = ‖g 0‖ + C * ‖z‖ := by ring
    have hF_int : Integrable (fun y => g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y))
        stdGaussian := by
      set a := exp (-t) * x
      set b := sqrt (1 - exp (-2 * t))
      have hmeas : AEStronglyMeasurable (fun y => g (a + b * y)) stdGaussian :=
        (hg_cont.measurable.comp (measurable_const.add
          (measurable_const.mul measurable_id))).aestronglyMeasurable
      have hid_int : Integrable (fun y : ℝ => ‖y‖) stdGaussian :=
        ((memLp_congr_ae (ae_of_all _ (fun y => by simp [pow_one]))).mp
          (memLp_pow_id_gaussianReal 1 2 (by simp))).integrable one_le_two |>.norm
      -- Dominator: |g(0)| + C*(|a| + |b|*|y|) is integrable
      have hdom_int : Integrable (fun y => ‖g 0‖ + C * (‖a‖ + ‖b‖ * ‖y‖)) stdGaussian :=
        (integrable_const _).add (((integrable_const (‖a‖)).add
          (hid_int.const_mul ‖b‖)).const_mul C)
      exact hdom_int.mono hmeas (ae_of_all _ fun y => by
        have hnn : 0 ≤ ‖g 0‖ + C * (‖a‖ + ‖b‖ * ‖y‖) := by positivity
        simp only [Real.norm_eq_abs] at *
        rw [abs_of_nonneg hnn]
        calc |g (a + b * y)| ≤ ‖g 0‖ + C * ‖a + b * y‖ := hg_growth _
          _ ≤ ‖g 0‖ + C * (‖a‖ + ‖b * y‖) := by
              gcongr; exact norm_add_le _ _
          _ = ‖g 0‖ + C * (‖a‖ + ‖b‖ * ‖y‖) := by rw [norm_mul b y])
    -- F' measurability helpers
    have hF'_meas : AEStronglyMeasurable
        (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) *
          (-exp (-t) * x + exp (-2 * t) / sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
      apply AEStronglyMeasurable.mul
      · exact (hg'_cont.measurable.comp (measurable_const.add
          (measurable_const.mul measurable_id))).aestronglyMeasurable
      · exact (measurable_const.add (measurable_const.mul measurable_id)).aestronglyMeasurable
    -- Uniform bound
    have hbound : ∀ᵐ y ∂stdGaussian, ∀ s ∈ s_set,
        ‖g' (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y) *
          (-exp (-s) * x + exp (-2 * s) / sqrt (1 - exp (-2 * s)) * y)‖
        ≤ C * (‖x‖ + M * ‖y‖) := by
      filter_upwards with y; intro s hs
      have hs_pos : 0 < s := by linarith [hs.1]
      set arg' := exp (-s) * x + sqrt (1 - exp (-2 * s)) * y
      set darg' := -exp (-s) * x + exp (-2 * s) / sqrt (1 - exp (-2 * s)) * y
      show ‖g' arg' * darg'‖ ≤ C * (‖x‖ + M * ‖y‖)
      rw [norm_mul]
      have h1 : ‖g' arg'‖ ≤ C := hC _
      have hexp_s_le : exp (-s) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      have hcoeff_le : exp (-2 * s) / sqrt (1 - exp (-2 * s)) ≤ M := by
        rw [div_le_div_iff₀ (sqrt_pos.mpr (h1me2s_pos s hs)) hb_lower_pos]
        calc exp (-2 * s) * sqrt (1 - exp (-t))
            ≤ 1 * sqrt (1 - exp (-t)) :=
              mul_le_mul_of_nonneg_right (exp_le_one_iff.mpr (by linarith)) (sqrt_nonneg _)
          _ ≤ 1 * sqrt (1 - exp (-2 * s)) :=
              mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by
                linarith [exp_le_exp.mpr (show -2 * s ≤ -t by linarith [hs.1])]))
                zero_le_one
      have h2 : ‖darg'‖ ≤ ‖x‖ + M * ‖y‖ := by
        calc ‖darg'‖
            ≤ ‖-exp (-s) * x‖ + ‖exp (-2 * s) / sqrt (1 - exp (-2 * s)) * y‖ :=
              norm_add_le _ _
          _ = exp (-s) * ‖x‖ + (exp (-2 * s) / sqrt (1 - exp (-2 * s))) * ‖y‖ := by
              simp only [show -exp (-s) * x = -(exp (-s) * x) from by ring,
                norm_neg, norm_mul, Real.norm_eq_abs,
                abs_of_pos (exp_pos (-s)),
                abs_of_pos (div_pos (exp_pos _) (sqrt_pos.mpr (h1me2s_pos s hs)))]
          _ ≤ 1 * ‖x‖ + M * ‖y‖ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hexp_s_le (norm_nonneg _)
              · exact mul_le_mul_of_nonneg_right hcoeff_le (norm_nonneg _)
          _ = ‖x‖ + M * ‖y‖ := by ring
      exact mul_le_mul h1 h2 (by positivity) hC_nn
    -- Bound integrable
    have hbound_int : Integrable (fun y => C * (‖x‖ + M * ‖y‖)) stdGaussian := by
      have hid_int : Integrable (fun y : ℝ => ‖y‖) stdGaussian :=
        ((memLp_congr_ae (ae_of_all _ (fun y => by simp [pow_one]))).mp
          (memLp_pow_id_gaussianReal 1 2 (by simp))).integrable one_le_two |>.norm
      exact ((integrable_const (‖x‖)).add (hid_int.const_mul M)).const_mul C
    -- Pointwise HasDerivAt
    have hpointwise : ∀ᵐ y ∂stdGaussian, ∀ s ∈ s_set,
        HasDerivAt (fun s => g (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y))
          (g' (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y) *
            (-exp (-s) * x + exp (-2 * s) / sqrt (1 - exp (-2 * s)) * y)) s := by
      filter_upwards with y; intro s hs
      have h1me := h1me2s_pos s hs
      have hd_exp : HasDerivAt (fun s => exp (-s)) (-exp (-s)) s := by
        have := (hasDerivAt_neg s).exp
        simp only [mul_neg, mul_one] at this; exact this
      have hd_u : HasDerivAt (fun s => 1 - exp (-2 * s)) (2 * exp (-2 * s)) s := by
        have hd2 := (hasDerivAt_id s).const_mul (-2 : ℝ)
        simp only [mul_one, id] at hd2
        have hde := hd2.exp
        simp only [mul_neg, mul_one, id] at hde
        convert (hasDerivAt_const s (1 : ℝ)).sub hde using 1; ring
      have hd_sqrt : HasDerivAt (fun s => sqrt (1 - exp (-2 * s)))
          (exp (-2 * s) / sqrt (1 - exp (-2 * s))) s := by
        have hsq := (Real.hasDerivAt_sqrt (ne_of_gt h1me)).comp s hd_u
        simp only [Function.comp] at hsq
        convert hsq using 1; field_simp
      exact (hg_deriv _).comp s
        ((hd_exp.mul_const x).add (hd_sqrt.mul_const y))
    -- Apply Leibniz
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s y => g (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y))
      (F' := fun s y => g' (exp (-s) * x + sqrt (1 - exp (-2 * s)) * y) *
        (-exp (-s) * x + exp (-2 * s) / sqrt (1 - exp (-2 * s)) * y))
      hs_nhds
      (Eventually.of_forall fun s =>
        (hg_cont.measurable.comp (measurable_const.add
          (measurable_const.mul measurable_id))).aestronglyMeasurable)
      hF_int hF'_meas hbound hbound_int hpointwise).2
  -- Step 2: Simplify ∫ F'(t,y) dγ(y) = target
  -- Split: g'(arg)*(-at_ + coeff*y) = -at_*g'(arg) + coeff*(y*g'(arg))
  set coeff := exp (-2 * t) / bt
  -- Integrability of g' composed with affine (bounded g' → integrable)
  have hg'_int : Integrable (fun y => g' (at_ + bt * y)) stdGaussian :=
    MemLp.of_bound ((hg'_cont.measurable.comp
      ((measurable_const.add (measurable_const.mul measurable_id)) :
        Measurable fun y : ℝ => at_ + bt * y)).aestronglyMeasurable)
      C (ae_of_all _ (fun y => hC _)) |>.integrable one_le_two
  have hyg'_int : Integrable (fun y => y * g' (at_ + bt * y)) stdGaussian := by
    -- Since g' is bounded by C, y ↦ y*g'(arg) is in MemLp 1
    -- because y is in MemLp 2 and g'(arg) is in MemLp 2, and 1/2+1/2=1
    have hid_memLp : MemLp (fun y : ℝ => y) 2 stdGaussian :=
      (memLp_congr_ae (ae_of_all _ (fun y => by simp [pow_one]))).mp
        (memLp_pow_id_gaussianReal 1 2 (by simp))
    have hg'comp_memLp : MemLp (fun y => g' (at_ + bt * y)) 2 stdGaussian :=
      MemLp.of_bound ((hg'_cont.measurable.comp
        ((measurable_const.add (measurable_const.mul measurable_id)) :
          Measurable fun y : ℝ => at_ + bt * y)).aestronglyMeasurable)
        C (ae_of_all _ (fun y => hC _))
    have hmul : MemLp ((fun y : ℝ => y) * (fun y => g' (at_ + bt * y))) 1 stdGaussian :=
      hg'comp_memLp.mul hid_memLp
    exact (memLp_congr_ae (ae_of_all _ (fun y => by simp [Pi.mul_apply]))).mp
      hmul |>.integrable le_rfl
  -- Split the integral
  have hsplit : ∫ y, g' (at_ + bt * y) * (-at_ + coeff * y) ∂stdGaussian =
      -at_ * ∫ y, g' (at_ + bt * y) ∂stdGaussian +
      coeff * ∫ y, y * g' (at_ + bt * y) ∂stdGaussian := by
    have : ∀ y, g' (at_ + bt * y) * (-at_ + coeff * y) =
        -at_ * g' (at_ + bt * y) + coeff * (y * g' (at_ + bt * y)) := fun y => by ring
    simp_rw [this]
    rw [integral_add (hg'_int.const_mul _) (hyg'_int.const_mul _),
        integral_const_mul, integral_const_mul]
  -- Apply Stein identity: ∫ y*h(y) dγ = ∫ h'(y) dγ where h(y) = g'(at_ + bt*y)
  have hstein : ∫ y, y * g' (at_ + bt * y) ∂stdGaussian =
      ∫ y, g'' (at_ + bt * y) * bt ∂stdGaussian := by
    exact stein_identity (fun y => g' (at_ + bt * y)) (fun y => g'' (at_ + bt * y) * bt)
      (MemLp.of_bound ((hg'_cont.measurable.comp
        ((measurable_const.add (measurable_const.mul measurable_id)) :
          Measurable fun y : ℝ => at_ + bt * y)).aestronglyMeasurable)
        C (ae_of_all _ (fun y => hC _)))
      (MemLp.of_bound (by
        have hg''_eq : g'' = deriv g' := funext (fun z => (hg'_deriv z).deriv.symm)
        rw [show (fun y => g'' (at_ + bt * y) * bt) = (fun y => deriv g' (at_ + bt * y) * bt) from
          by ext y; rw [hg''_eq]]
        exact ((measurable_deriv g' |>.comp
          ((measurable_const.add (measurable_const.mul measurable_id)) :
            Measurable fun y : ℝ => at_ + bt * y)).mul measurable_const).aestronglyMeasurable)
        (C'' * ‖bt‖) (ae_of_all _ (fun y => by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC'' _) (norm_nonneg _))))
      (fun y => by
        have hchain := (hg'_deriv (at_ + bt * y)).comp y
          ((hasDerivAt_const y at_).add ((hasDerivAt_id y).const_mul bt))
        simp only [mul_one] at hchain
        convert hchain using 1; ring)
  -- Combine: simplify the Stein-rewritten integral to match the target
  have hcoeff_bt : coeff * bt = exp (-2 * t) := by
    simp only [coeff]; exact div_mul_cancel₀ _ hbt_ne
  have hint_g''_bt : ∫ y, g'' (at_ + bt * y) * bt ∂stdGaussian =
      (∫ y, g'' (at_ + bt * y) ∂stdGaussian) * bt := integral_mul_const bt _
  -- The full integral after splitting and Stein:
  have hfull : ∫ y, g' (at_ + bt * y) * (-at_ + coeff * y) ∂stdGaussian =
      exp (-2 * t) * ∫ y, g'' (at_ + bt * y) ∂stdGaussian -
      x * (exp (-t) * ∫ y, g' (at_ + bt * y) ∂stdGaussian) := by
    rw [hsplit, hstein, hint_g''_bt]
    rw [show coeff * ((∫ y, g'' (at_ + bt * y) ∂stdGaussian) * bt) =
        (coeff * bt) * ∫ y, g'' (at_ + bt * y) ∂stdGaussian from by ring, hcoeff_bt]
    simp only [at_]; ring
  exact hLeibniz.congr_deriv (by convert hfull using 2 <;> simp [at_, bt, coeff])

private lemma ouSemigroup_time_deriv (g g' g'' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x, HasDerivAt g' (g'' x) x)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg''_bound : ∃ C, ∀ x, ‖g'' x‖ ≤ C)
    (hg_int : Integrable g stdGaussian)
    (x : ℝ) :
    HasDerivAt (fun s => ouSemigroup s g x) (ouGeneratorAt t g x) t := by
  -- The target value exp(-2t)*P_t(g'')(x) - x*exp(-t)*P_t(g')(x)
  set target := exp (-2 * t) * ouSemigroup t g'' x - x * (exp (-t) * ouSemigroup t g' x)
  -- Step 1: Show ouGeneratorAt t g x = target
  suffices hgen : ouGeneratorAt t g x = target by
    rw [hgen]
    -- Step 2: Show HasDerivAt (fun s => ouSemigroup s g x) target t
    -- via Leibniz rule + Stein identity
    exact ouSemigroup_time_deriv_leibniz g g' g'' t ht hg_deriv hg'_deriv
      hg'_bound hg''_bound hg_int x
  -- Prove ouGeneratorAt = target by unfolding via ouSemigroup_hasDerivAt
  unfold ouGeneratorAt
  -- deriv(P_t g)(x) = exp(-t) * P_t(g')(x)
  -- Integrability of g/g'/g'' composed with affine maps against Gaussian
  -- g' and g'' are bounded, so integrable against any finite measure
  have hg'_meas : Measurable g' := by
    have : g' = deriv g := funext fun z => (hg_deriv z).deriv.symm
    rw [this]; exact measurable_deriv g
  have hg''_meas : Measurable g'' := by
    have : g'' = deriv g' := funext fun z => (hg'_deriv z).deriv.symm
    rw [this]; exact measurable_deriv g'
  have haffine_meas : ∀ z, Measurable (fun y : ℝ => exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y) := fun z =>
    measurable_const.add (measurable_const.mul measurable_id)
  have hg_int_inner : ∀ z, Integrable (fun y => g (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z'
    obtain ⟨C, hC⟩ := hg'_bound
    have hC_nn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
    have hg_diff : Differentiable ℝ g := fun w => (hg_deriv w).differentiableAt
    set Cnn : NNReal := ⟨C, hC_nn⟩
    have hCnn_eq : (Cnn : ℝ) = C := rfl
    have hg_lip : LipschitzWith Cnn g :=
      lipschitzWith_of_nnnorm_deriv_le hg_diff fun w => by
        show ‖deriv g w‖₊ ≤ Cnn
        rw [← NNReal.coe_le_coe, coe_nnnorm, hCnn_eq, (hg_deriv w).deriv]; exact hC w
    set a' := exp (-t) * z'
    set b' := sqrt (1 - exp (-2 * t))
    have hg_meas' : Measurable g := hg_diff.continuous.measurable
    have haffine_meas' : Measurable (fun y : ℝ => a' + b' * y) :=
      measurable_const.add (measurable_const.mul measurable_id)
    have h1 : Integrable (fun _ : ℝ => g 0) stdGaussian := integrable_const _
    have h2 : Integrable (fun y => g (a' + b' * y) - g 0) stdGaussian := by
      have hid_int := IsGaussian.integrable_fun_id (μ := stdGaussian)
      set bound : ℝ → ℝ := fun y => C * |a'| + C * |b'| * ‖y‖
      have hbound_int : Integrable bound stdGaussian :=
        (integrable_const _).add (hid_int.norm.const_mul _)
      have hbound_nn : ∀ y, 0 ≤ bound y := fun y =>
        add_nonneg (mul_nonneg hC_nn (abs_nonneg _))
          (mul_nonneg (mul_nonneg hC_nn (abs_nonneg _)) (norm_nonneg _))
      exact Integrable.mono hbound_int
        ((hg_meas'.comp haffine_meas').sub measurable_const).aestronglyMeasurable
        (ae_of_all _ fun y => by
          have h := hg_lip.norm_sub_le (a' + b' * y) 0
          simp only [sub_zero, hCnn_eq] at h
          rw [show ‖bound y‖ = bound y from Real.norm_of_nonneg (hbound_nn y)]
          calc ‖g (a' + b' * y) - g 0‖ ≤ C * ‖a' + b' * y‖ := h
            _ ≤ C * (|a'| + |b' * y|) := by
                gcongr; rw [Real.norm_eq_abs]; exact abs_add_le _ _
            _ = C * |a'| + C * |b'| * ‖y‖ := by
                rw [abs_mul b' y, Real.norm_eq_abs]; ring)
    have : (fun y => g (a' + b' * y)) = (fun y => g 0 + (g (a' + b' * y) - g 0)) := by
      ext y; abel
    rw [this]; exact h1.add h2
  have hg'_int_inner : ∀ z, Integrable (fun y => g' (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z; obtain ⟨C, hC⟩ := hg'_bound
    exact Integrable.of_bound
      ((hg'_meas.comp (haffine_meas z)).aestronglyMeasurable) C
      (ae_of_all _ fun y => hC _)
  have hg''_int_inner : ∀ z, Integrable (fun y => g'' (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z; obtain ⟨C, hC⟩ := hg''_bound
    exact Integrable.of_bound
      ((hg''_meas.comp (haffine_meas z)).aestronglyMeasurable) C
      (ae_of_all _ fun y => hC _)
  have hderiv1 := ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound hg_int_inner x
  -- So deriv (ouSemigroup t g) x = exp(-t) * ouSemigroup t g' x
  have hd1 : deriv (ouSemigroup t g) x = exp (-t) * ouSemigroup t g' x :=
    hderiv1.deriv
  -- Apply ouSemigroup_hasDerivAt to g' with g''
  have hderiv2 := ouSemigroup_hasDerivAt t g' g'' hg'_deriv hg''_bound hg'_int_inner x
  -- deriv (ouSemigroup t g') x = exp(-t) * ouSemigroup t g'' x
  have hd2 : deriv (ouSemigroup t g') x = exp (-t) * ouSemigroup t g'' x :=
    hderiv2.deriv
  -- Now: deriv(ouSemigroup t g) = fun z => exp(-t) * ouSemigroup t g' z
  -- So deriv(deriv(ouSemigroup t g)) x = deriv(fun z => exp(-t) * ouSemigroup t g' z) x
  --    = exp(-t) * deriv(ouSemigroup t g') x = exp(-t) * exp(-t) * ouSemigroup t g'' x
  --    = exp(-2t) * ouSemigroup t g'' x
  have hd1_eq : deriv (ouSemigroup t g) = fun z => exp (-t) * ouSemigroup t g' z := by
    ext z
    exact (ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound hg_int_inner z).deriv
  have hdd : deriv (deriv (ouSemigroup t g)) x =
      exp (-t) * (exp (-t) * ouSemigroup t g'' x) := by
    rw [hd1_eq]
    have : HasDerivAt (fun z => exp (-t) * ouSemigroup t g' z)
        (exp (-t) * (exp (-t) * ouSemigroup t g'' x)) x := by
      exact hderiv2.const_mul _
    exact this.deriv
  -- Assemble: ouGeneratorAt = deriv(deriv(P_t g)) x - x * deriv(P_t g) x
  rw [hdd, hd1]
  -- Goal: exp(-t) * (exp(-t) * P_t(g'')(x)) - x * (exp(-t) * P_t(g')(x))
  --     = exp(-2*t) * P_t(g'')(x) - x * (exp(-t) * P_t(g')(x))
  congr 1
  rw [← mul_assoc, ← exp_add]
  ring_nf

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
  -- Strategy: apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (parametric Leibniz rule)
  -- with F(s,x) = ouSemigroup s g x * log(ouSemigroup s g x)
  -- and  F'(s,x) = (d/ds ouSemigroup s g x) * (1 + log(ouSemigroup s g x))
  -- The pointwise derivative d/ds [u·log u] = u'·(1 + log u) by chain rule.
  -- Sub-goal 1: AEStronglyMeasurable of F(s,·) near t — from hent_int
  have hF_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable (fun x =>
      ouSemigroup s g x * log (ouSemigroup s g x)) stdGaussian :=
    hent_int.mono (fun s hs => hs.aestronglyMeasurable)
  -- Sub-goal 2: Integrable F(t,·) — from hent_int
  have hent_int_t : Integrable (fun x => ouSemigroup t g x * log (ouSemigroup t g x))
      stdGaussian := hent_int.self_of_nhds
  -- Sub-goal 3: AEStronglyMeasurable of F'(t,·) — from hint
  have hF'_meas : AEStronglyMeasurable (fun x => ouGeneratorAt t g x *
      (1 + log (ouSemigroup t g x))) stdGaussian := hint.aestronglyMeasurable
  -- Sub-goal 4: neighborhood S ∈ nhds t
  have hS : Set.Ioo (t / 2) (2 * t) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  -- Sub-goal 5: uniform bound — needs OU regularity near t (sorry)
  -- For s near t, ‖(d/ds P_s g)(x) * (1 + log(P_s g(x)))‖ ≤ bound(x) with integrable bound.
  -- This requires uniform-in-s bounds on ouGeneratorAt and log(ouSemigroup), which follow from
  -- smoothness of the Gaussian heat kernel but need substantial regularity theory.
  -- The bound function: for each x, sup over s near t of |F'(s,x)|
  let bound : ℝ → ℝ := sorry
  have hbound : ∀ᵐ x ∂stdGaussian, ∀ s ∈ Set.Ioo (t / 2) (2 * t),
      ‖ouGeneratorAt s g x * (1 + log (ouSemigroup s g x))‖ ≤ bound x := sorry
  have hbound_int : Integrable bound stdGaussian := sorry
  -- Sub-goal 6: pointwise HasDerivAt — chain rule d/ds[u·log u] = u'·(1+log u)
  -- where u(s) = ouSemigroup s g x, u'(s) = ouGeneratorAt s g x.
  -- This requires: (a) HasDerivAt for s ↦ ouSemigroup s g x at each s near t (not just at t),
  -- (b) ouSemigroup s g x > 0 for s near t and ae x, (c) chain rule for log.
  have hpointwise : ∀ᵐ x ∂stdGaussian, ∀ s ∈ Set.Ioo (t / 2) (2 * t),
      HasDerivAt (fun s => ouSemigroup s g x * log (ouSemigroup s g x))
        (ouGeneratorAt s g x * (1 + log (ouSemigroup s g x))) s := sorry
  -- Apply the parametric Leibniz rule
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hS hF_meas hent_int_t hF'_meas hbound hbound_int hpointwise).2

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

/-- Pushforward of the standard Gaussian under an affine map. -/
private lemma map_affine_stdGaussian (a b : ℝ) :
    Measure.map (fun y => a + b * y) stdGaussian =
    gaussianReal a ⟨b ^ 2, sq_nonneg b⟩ := by
  simp only [stdGaussian]
  have : (fun y : ℝ => a + b * y) = ((a + ·) ∘ (b * ·)) := by funext _; simp [Function.comp]
  rw [this, ← Measure.map_map (measurable_const_add a) (measurable_const_mul b),
      gaussianReal_map_const_mul, gaussianReal_map_const_add]; simp [mul_zero, mul_one]

/-- The variance parameter of the OU kernel is nonzero for t > 0. -/
private lemma ouVar_ne_zero (t : ℝ) (ht : 0 < t) :
    (⟨(sqrt (1 - exp (-2 * t))) ^ 2, sq_nonneg _⟩ : NNReal) ≠ 0 := by
  intro h; have h1 := congr_arg (fun x : NNReal => (x : ℝ)) h; simp at h1
  linarith [sqrt_eq_zero'.mp h1, exp_lt_one_iff.mpr (show -(2 * t) < 0 by linarith)]

/-- If f(a + b·y) = 0 a.e.(γ) and f is measurable with b² > 0, then f = 0 a.e.(γ).
    Uses mutual absolute continuity of non-degenerate Gaussians. -/
private lemma ae_zero_of_comp_affine (f : ℝ → ℝ) (hf_meas : Measurable f) (a b : ℝ)
    (hv : (⟨b ^ 2, sq_nonneg b⟩ : NNReal) ≠ 0)
    (h : ∀ᵐ y ∂stdGaussian, f (a + b * y) = 0) :
    ∀ᵐ z ∂stdGaussian, f z = 0 := by
  have hφ : AEMeasurable (fun y : ℝ => a + b * y) stdGaussian := by fun_prop
  have h1 : ∀ᵐ z ∂(Measure.map (fun y => a + b * y) stdGaussian), f z = 0 := by
    rw [show (∀ᵐ z ∂(Measure.map (fun y => a + b * y) stdGaussian), f z = 0) ↔
        (∀ᵐ y ∂stdGaussian, f ((fun y => a + b * y) y) = 0) from
      ae_map_iff hφ (hf_meas (measurableSet_singleton 0))]
    exact h
  rw [map_affine_stdGaussian] at h1
  exact ((gaussianReal_absolutelyContinuous 0 one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' a hv)).ae_le h1

/-- The OU semigroup of an integrable function is integrable.
    This follows from Fubini: the Mehler map preserves the Gaussian on the product. -/
private lemma integrable_ouSemigroup (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hf : Integrable f stdGaussian) :
    Integrable (ouSemigroup t f) stdGaussian := by
  simp only [stdGaussian] at *
  set a := exp (-t) with ha_def
  set b := sqrt (1 - exp (-2 * t)) with hb_def
  have hb_nn : 0 ≤ 1 - exp (-2 * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [ha_def, hb_def, sq_sqrt hb_nn]
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, pow_one, ← exp_add]; ring_nf
  have hφ_meas : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
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
  have hfγ : Integrable f (gaussianReal 0 1) := hf
  have hfφ_int : Integrable (fun p : ℝ × ℝ => f (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    rw [show (fun p : ℝ × ℝ => f (a * p.1 + b * p.2)) =
        f ∘ (fun p : ℝ × ℝ => a * p.1 + b * p.2) from rfl]
    rw [← hmap] at hfγ; exact hfγ.comp_measurable hφ_meas
  exact hfφ_int.integral_prod_left

/-- The composition f(ax+by) is integrable on γ⊗γ when f is integrable on γ and a²+b²=1. -/
private lemma integrable_mehler_prod (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ)
    (hf : Integrable f stdGaussian) :
    Integrable (fun p : ℝ × ℝ => f (exp (-t) * p.1 + sqrt (1 - exp (-2 * t)) * p.2))
      (stdGaussian.prod stdGaussian) := by
  simp only [stdGaussian] at *
  set a := exp (-t) with ha_def
  set b := sqrt (1 - exp (-2 * t)) with hb_def
  have hb_nn : 0 ≤ 1 - exp (-2 * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [ha_def, hb_def, sq_sqrt hb_nn]
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, pow_one, ← exp_add]; ring_nf
  have hφ_meas : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  have hmap : Measure.map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = gaussianReal 0 1 := by
    have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) (Prod.snd : ℝ × ℝ → ℝ)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map
        measurable_fst.aemeasurable measurable_snd.aemeasurable]
      simp [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ]
    have hind2 : IndepFun (fun p : ℝ × ℝ => a * p.1) (fun p : ℝ × ℝ => b * p.2)
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
      hind.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
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
  rw [show (fun p : ℝ × ℝ => f (a * p.1 + b * p.2)) =
      f ∘ (fun p : ℝ × ℝ => a * p.1 + b * p.2) from rfl]
  rw [← hmap] at hf; exact hf.comp_measurable hφ_meas

/-- Positivity of the OU semigroup: P_t g > 0 a.e. when g ≥ 0 a.e. and ∫ g > 0.

    Proof strategy: Decompose g = g⁺ - g⁻. Since g ≥ 0 a.e., g⁻ = 0 a.e., so P_t(g⁻) = 0 a.e.
    Hence P_t g = P_t(g⁺) a.e. ≥ 0. By contradiction, if P_t(g⁺)(x₀) = 0 at some point where
    g⁺∘φ_{x₀} is integrable, then g⁺(e^{-t}x₀ + √(1-e^{-2t})y) = 0 a.e.(γ), and the Gaussian
    full support property (mutual absolute continuity of non-degenerate Gaussians) gives g⁺ = 0
    a.e.(γ), contradicting ∫g > 0. -/
private lemma ouSemigroup_pos_ae (g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian) :
    ∀ᵐ x ∂stdGaussian, 0 < ouSemigroup t g x := by
  -- Step 1: Get a measurable nonneg version gmp of g with g =ae gmp
  set gm := hg_int.aestronglyMeasurable.mk g with hgm_def
  have hgm_sm := hg_int.aestronglyMeasurable.stronglyMeasurable_mk
  have hgm_ae : g =ᵐ[stdGaussian] gm := hg_int.aestronglyMeasurable.ae_eq_mk
  set gmp := fun x => max (gm x) 0 with hgmp_def
  have hgmp_meas : Measurable gmp := hgm_sm.measurable.sup measurable_const
  have hgmp_nn : ∀ x, 0 ≤ gmp x := fun x => le_max_right _ _
  have hg_gmp_ae : g =ᵐ[stdGaussian] gmp := by
    filter_upwards [hg_nn, hgm_ae] with x hx_nn hx_eq
    show g x = max (gm x) 0
    rw [← hx_eq]; exact (max_eq_left hx_nn).symm
  have hgmp_int : Integrable gmp stdGaussian := hg_int.congr hg_gmp_ae
  -- Step 2: OU parameters
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hb_nn : 0 ≤ 1 - exp (-2 * t) := sub_nonneg.mpr (exp_le_one_iff.mpr (by linarith))
  have hv : (⟨b ^ 2, sq_nonneg b⟩ : NNReal) ≠ 0 := ouVar_ne_zero t ht
  -- Step 3: gmp = 0 ae(γ) is impossible (would contradict ∫g > 0)
  have hgmp_not_zero : ¬ (∀ᵐ x ∂stdGaussian, gmp x = 0) := by
    intro h_zero
    have : ∫ x, g x ∂stdGaussian = 0 := by
      rw [integral_congr_ae hg_gmp_ae, integral_eq_zero_of_ae h_zero]
    linarith
  -- Step 4: Get product integrability and slice integrability from Fubini
  have hfφ_int : Integrable (fun p : ℝ × ℝ => gmp (a * p.1 + b * p.2))
      (stdGaussian.prod stdGaussian) := integrable_mehler_prod t (le_of_lt ht) gmp hgmp_int
  -- By Fubini: for ae x, the slice y → gmp(ax+by) is integrable under γ
  have hslice_int_ae : ∀ᵐ x ∂stdGaussian, Integrable (fun y => gmp (a * x + b * y)) stdGaussian :=
    hfφ_int.prod_right_ae
  -- Step 5: P_t(gmp) > 0 ae(γ) via full support argument
  -- For ae x (where slice integrable): if P_t(gmp)(x) = 0, then gmp(ax+by) = 0 ae(y),
  -- then by ae_zero_of_comp_affine, gmp = 0 ae(γ), contradicting ∫g > 0
  have hPgmp_pos : ∀ᵐ x ∂stdGaussian, 0 < ouSemigroup t gmp x := by
    filter_upwards [hslice_int_ae] with x₀ hslice_int
    by_contra h_le
    push_neg at h_le
    have h_eq : ouSemigroup t gmp x₀ = 0 :=
      le_antisymm h_le (integral_nonneg (fun y => hgmp_nn _))
    -- gmp(ax₀+by) = 0 ae(γ) (nonneg integrable function with zero integral)
    have hslice_ae : ∀ᵐ y ∂stdGaussian, gmp (a * x₀ + b * y) = 0 := by
      have := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall (fun y => hgmp_nn _)) hslice_int).mp h_eq
      filter_upwards [this] with y hy; exact hy
    exact hgmp_not_zero (ae_zero_of_comp_affine gmp hgmp_meas (a * x₀) b hv hslice_ae)
  -- Step 6: P_t g =ae P_t(gmp) by Fubini (g =ae gmp → slices agree ae)
  -- For ae x (where slice integrable), g(ax+by) =ae gmp(ax+by) in y, so P_t g(x) = P_t(gmp)(x)
  have hPg_eq : ∀ᵐ x ∂stdGaussian, ouSemigroup t g x = ouSemigroup t gmp x := by
    have hfg_int : Integrable (fun p : ℝ × ℝ => g (a * p.1 + b * p.2))
        (stdGaussian.prod stdGaussian) := integrable_mehler_prod t (le_of_lt ht) g hg_int
    have hslice_g_ae : ∀ᵐ x ∂stdGaussian,
        Integrable (fun y => g (a * x + b * y)) stdGaussian := hfg_int.prod_right_ae
    filter_upwards [hslice_int_ae, hslice_g_ae] with x₀ hgmp_slice hg_slice
    simp only [ouSemigroup]
    -- g(ax₀+by) =ae gmp(ax₀+by) under γ via ae_eq_comp'
    have hφ_aem : AEMeasurable (fun y : ℝ => a * x₀ + b * y) stdGaussian := by fun_prop
    have h_ac : (Measure.map (fun y => a * x₀ + b * y) stdGaussian).AbsolutelyContinuous
        stdGaussian := by
      rw [map_affine_stdGaussian]
      exact (gaussianReal_absolutelyContinuous (a * x₀) hv).trans
        (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
    exact integral_congr_ae (ae_eq_comp' hφ_aem hg_gmp_ae h_ac)
  -- Step 7: Combine: P_t g =ae P_t(gmp) > 0 ae
  filter_upwards [hPg_eq, hPgmp_pos] with x hx_eq hx_pos
  rw [hx_eq]; exact hx_pos

/-- Quantitative lower bound for the standard Gaussian measure of a closed interval.
For any `δ > 0` and center `m`, the Gaussian measure of `[m-δ, m+δ]` is bounded below by
a positive constant times `exp(-(|m|+δ)²/2)`.

Proof sketch: `γ(Icc) = ∫ gaussianPDFReal ≥ 2δ · inf_{y∈[m-δ,m+δ]} density(y)
  ≥ 2δ · (√(2π))⁻¹ · exp(-(|m|+δ)²/2)`. -/
private lemma stdGaussian_Icc_lower_bound (m δ : ℝ) (hδ : 0 < δ) :
    2 * δ * (sqrt (2 * π))⁻¹ * exp (-((|m| + δ) ^ 2 / 2)) ≤
      stdGaussian.real (Set.Icc (m - δ) (m + δ)) := by
  show _ ≤ (stdGaussian (Set.Icc (m - δ) (m + δ))).toReal
  rw [show (stdGaussian : Measure ℝ) = gaussianReal 0 1 from rfl]
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
    (fun x _ => gaussianPDFReal_nonneg _ _ x))]
  set c := (sqrt (2 * π))⁻¹ * exp (-((|m| + δ) ^ 2 / 2)) with hc_def
  have hc_lb : ∀ x ∈ Set.Icc (m - δ) (m + δ), c ≤ gaussianPDFReal 0 1 x := by
    intro y hy
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, sub_zero, mul_one]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sqrt_nonneg _))
    apply exp_le_exp.mpr
    linarith [sq_le_sq' (by linarith [neg_abs_le m, hy.1] : -(|m| + δ) ≤ y)
      (by linarith [le_abs_self m, hy.2] : y ≤ |m| + δ)]
  have key : volume.real (Set.Icc (m - δ) (m + δ)) • c ≤
      ∫ x in Set.Icc (m - δ) (m + δ), gaussianPDFReal 0 1 x :=
    setIntegral_ge_of_const_le measurableSet_Icc
      (measure_Icc_lt_top.ne) hc_lb
      (integrable_gaussianPDFReal _ _).integrableOn
  simp only [smul_eq_mul] at key
  have hvol : (volume : Measure ℝ).real (Set.Icc (m - δ) (m + δ)) = 2 * δ := by
    simp [Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at key
  linarith

/-- Gaussian kernel lower bound: for Lipschitz nonneg g with strictly positive integral,
the OU semigroup satisfies P_t g(x) ≥ c₁ · exp(-c₂ · x²) for explicit positive constants.
This follows from: g ≥ ε on some ball (continuity + positivity), the Gaussian kernel
puts positive mass on any ball, and that mass decays at most like exp(-x²). -/
private lemma ouSemigroup_lower_bound (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x, c₁ * exp (-c₂ * x ^ 2) ≤ ouSemigroup t g x := by
  -- Step 1: g is differentiable, continuous, and Lipschitz
  obtain ⟨C, hC⟩ := hg'_bound
  have hC_nn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hg_diff : Differentiable ℝ g := fun w => (hg_deriv w).differentiableAt
  have hg_cont : Continuous g := hg_diff.continuous
  set Cnn : NNReal := ⟨C, hC_nn⟩
  have hg_lip : LipschitzWith Cnn g :=
    lipschitzWith_of_nnnorm_deriv_le hg_diff fun w => by
      show ‖deriv g w‖₊ ≤ Cnn
      rw [← NNReal.coe_le_coe, coe_nnnorm, (hg_deriv w).deriv]; exact hC w
  -- Step 2: ae nonneg + continuous + positive integral → ∃ x₀, g(x₀) > 0
  -- Gaussian has full support, so ae nonneg + continuous → everywhere nonneg
  have hg_nn_all : ∀ x, 0 ≤ g x := by
    have hsupp : (stdGaussian : Measure ℝ).IsOpenPosMeasure :=
      (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
    by_contra h; push_neg at h
    obtain ⟨x, hgx⟩ := h
    -- g(x) < 0, g continuous → g < 0 on some open neighborhood
    have hopen : IsOpen {y | g y < 0} := isOpen_lt hg_cont continuous_const
    have hmem : x ∈ {y | g y < 0} := hgx
    have hne : ({y | g y < 0} : Set ℝ).Nonempty := ⟨x, hmem⟩
    have hU_pos : stdGaussian {y | g y < 0} ≠ 0 :=
      hsupp.open_pos _ hopen hne
    -- ae nonneg means {g < 0} has measure zero
    have : stdGaussian {y | g y < 0} = 0 :=
      measure_mono_null (fun y (hy : g y < 0) => not_le.mpr hy) (ae_iff.mp hg_nn)
    exact hU_pos this
  -- g everywhere nonneg, not ae zero → ∃ x₀, g(x₀) > 0
  have hg_not_zero : ∃ x₀, 0 < g x₀ := by
    by_contra h; push_neg at h
    have : g =ᵐ[stdGaussian] 0 :=
      ae_of_all _ fun x => le_antisymm (h x) (hg_nn_all x)
    linarith [integral_eq_zero_of_ae this]
  obtain ⟨x₀, hx₀⟩ := hg_not_zero
  -- Step 3: g ≥ ε on ball B(x₀, r) using Lipschitz bound
  set ε := g x₀ / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  set K := max C 1 with hK_def
  have hK_pos : 0 < K := lt_max_of_lt_right one_pos
  have hK_ge_C : C ≤ K := le_max_left C 1
  set r := g x₀ / (2 * K) with hr_def
  have hr_pos : 0 < r := by positivity
  have hg_on_ball : ∀ y, |y - x₀| ≤ r → ε ≤ g y := by
    intro y hy
    have h1 : ‖g y - g x₀‖ ≤ (Cnn : ℝ) * ‖y - x₀‖ := hg_lip.norm_sub_le y x₀
    simp only [Real.norm_eq_abs, NNReal.coe_mk] at h1
    have h2 : |g y - g x₀| ≤ K * r := by
      calc |g y - g x₀| ≤ C * |y - x₀| := h1
        _ ≤ C * r := mul_le_mul_of_nonneg_left hy hC_nn
        _ ≤ K * r := mul_le_mul_of_nonneg_right hK_ge_C hr_pos.le
    have h3 : K * r = g x₀ / 2 := by
      rw [hr_def]; field_simp
    rw [h3] at h2
    -- |g y - g x₀| ≤ g x₀ / 2 → g y ≥ g x₀ - g x₀ / 2 = g x₀ / 2 = ε
    have h4 := (abs_le.mp h2).1
    linarith
  -- Step 4: OU semigroup parameters
  set a := exp (-t) with ha_def
  have ha_pos : 0 < a := exp_pos _
  set b := sqrt (1 - exp (-2 * t)) with hb_def
  have hexp_lt : exp (-2 * t) < 1 := by
    rw [exp_lt_one_iff]; linarith
  have hb_pos : 0 < b := sqrt_pos_of_pos (by linarith)
  -- Step 5: For each x, lower bound P_t g(x) by integral over a sub-interval
  have hkey : ∀ x, ε * stdGaussian.real (Set.Icc (((x₀ - r) - a * x) / b)
      (((x₀ + r) - a * x) / b)) ≤ ouSemigroup t g x := by
    intro x
    simp only [ouSemigroup]
    -- The set integral provides a lower bound for the full integral
    calc ε * stdGaussian.real (Set.Icc (((x₀ - r) - a * x) / b)
            (((x₀ + r) - a * x) / b))
        ≤ ∫ y in Set.Icc (((x₀ - r) - a * x) / b) (((x₀ + r) - a * x) / b),
            g (a * x + b * y) ∂stdGaussian := by
          -- ε · μ.real(S) = ∫_S ε ≤ ∫_S g(...) since g(...) ≥ ε on S
          rw [show ε * stdGaussian.real _ = stdGaussian.real _ * ε from mul_comm _ _,
            ← smul_eq_mul, ← setIntegral_const]
          apply setIntegral_mono_on
          · exact integrableOn_const
          · exact (hg_cont.comp (by fun_prop : Continuous
              (fun y => a * x + b * y))).continuousOn.integrableOn_compact isCompact_Icc
          · exact measurableSet_Icc
          · intro y hy
            apply hg_on_ball
            simp only [Set.mem_Icc] at hy
            rw [abs_le]
            have hy1 := (div_le_iff₀ hb_pos).mp hy.1
            have hy2 := (le_div_iff₀ hb_pos).mp hy.2
            constructor <;> linarith
      _ ≤ ∫ y, g (a * x + b * y) ∂stdGaussian := by
          apply setIntegral_le_integral
          · -- Integrability of y ↦ g(ax+by) under Gaussian
            -- Reuse pattern from ouSemigroup_time_deriv_leibniz
            have hg_growth : ∀ z, ‖g z‖ ≤ ‖g 0‖ + C * ‖z‖ := by
              intro z
              have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
                (fun w _ => (hg_deriv w).hasDerivWithinAt) (fun w _ => hC w)
                convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ z)
              simp only [sub_zero] at hmvt
              calc ‖g z‖ = ‖(g z - g 0) + g 0‖ := by ring_nf
                _ ≤ ‖g z - g 0‖ + ‖g 0‖ := norm_add_le _ _
                _ ≤ C * ‖z‖ + ‖g 0‖ := by linarith
                _ = ‖g 0‖ + C * ‖z‖ := by ring
            set a' := a * x; set b' := b
            have hmeas : AEStronglyMeasurable (fun y => g (a' + b' * y)) stdGaussian :=
              (hg_cont.measurable.comp (measurable_const.add
                (measurable_const.mul measurable_id))).aestronglyMeasurable
            have hid_int : Integrable (fun y : ℝ => ‖y‖) stdGaussian :=
              ((memLp_congr_ae (ae_of_all _ (fun y => by simp [pow_one]))).mp
                (memLp_pow_id_gaussianReal 1 2 (by simp))).integrable one_le_two |>.norm
            have hdom_int : Integrable (fun y =>
                ‖g 0‖ + C * (‖a'‖ + ‖b'‖ * ‖y‖)) stdGaussian :=
              (integrable_const _).add (((integrable_const (‖a'‖)).add
                (hid_int.const_mul ‖b'‖)).const_mul C)
            exact hdom_int.mono hmeas (ae_of_all _ fun y => by
              have hnn : 0 ≤ ‖g 0‖ + C * (‖a'‖ + ‖b'‖ * ‖y‖) := by positivity
              simp only [Real.norm_eq_abs] at *
              rw [abs_of_nonneg hnn]
              calc |g (a' + b' * y)| ≤ ‖g 0‖ + C * ‖a' + b' * y‖ := hg_growth _
                _ ≤ ‖g 0‖ + C * (‖a'‖ + ‖b' * y‖) := by gcongr; exact norm_add_le _ _
                _ = ‖g 0‖ + C * (‖a'‖ + ‖b'‖ * ‖y‖) := by rw [norm_mul b' y])
          · exact ae_of_all _ fun y => hg_nn_all _
  -- Step 6: Rewrite the Icc as [m - δ, m + δ]
  set δ := r / b with hδ_def
  have hδ_pos : 0 < δ := div_pos hr_pos hb_pos
  have hIcc_eq : ∀ x, Set.Icc (((x₀ - r) - a * x) / b) (((x₀ + r) - a * x) / b) =
      Set.Icc ((x₀ - a * x) / b - δ) ((x₀ - a * x) / b + δ) := by
    intro x; congr 1 <;> [rw [hδ_def]; rw [hδ_def]] <;> field_simp <;> ring
  -- Step 7: Apply Gaussian Icc lower bound
  have hstep7 : ∀ x, 2 * δ * (sqrt (2 * π))⁻¹ *
      exp (-(( |(x₀ - a * x) / b| + δ) ^ 2 / 2)) ≤
      stdGaussian.real (Set.Icc ((x₀ - a * x) / b - δ) ((x₀ - a * x) / b + δ)) := by
    intro x; exact stdGaussian_Icc_lower_bound ((x₀ - a * x) / b) δ hδ_pos
  -- Step 8: Bound (|m|+δ)²/2 in terms of x²
  set c₂ := (a / b) ^ 2 with hc₂_def
  have hc₂_pos : 0 < c₂ := by positivity
  have hexp_bound : ∀ x, exp (-((|x₀| / b + δ) ^ 2)) * exp (-(c₂ * x ^ 2)) ≤
      exp (-(( |(x₀ - a * x) / b| + δ) ^ 2 / 2)) := by
    intro x
    rw [← exp_add, exp_le_exp]
    -- Need: -((|x₀|/b+δ)² + c₂·x²) ≤ -((|m|+δ)²/2)
    -- i.e., (|m|+δ)²/2 ≤ (|x₀|/b+δ)² + c₂·x²
    have hm_bound : |(x₀ - a * x) / b| + δ ≤ (|x₀| / b + δ) + (a / b) * |x| := by
      rw [abs_div, abs_of_pos hb_pos]
      have htri : |x₀ - a * x| ≤ |x₀| + |a * x| := by
        calc |x₀ - a * x| ≤ |x₀ - 0| + |0 - a * x| := abs_sub_le x₀ 0 (a * x)
          _ = |x₀| + |a * x| := by simp
      rw [abs_mul, abs_of_pos ha_pos] at htri
      have h1 := div_le_div_of_nonneg_right htri hb_pos.le
      rw [add_div] at h1
      have h2 : a * |x| / b = a / b * |x| := by rw [div_mul_eq_mul_div]
      linarith [h1, h2]
    -- (u+v)²/2 ≤ u² + v²
    have hsq : ∀ u v : ℝ, (u + v) ^ 2 / 2 ≤ u ^ 2 + v ^ 2 := by
      intro u v; nlinarith [sq_nonneg (u - v)]
    have h_sq_le : ((|(x₀ - a * x) / b| + δ) ^ 2 / 2) ≤
        (|x₀| / b + δ) ^ 2 + ((a / b) * |x|) ^ 2 := by
      calc ((|(x₀ - a * x) / b| + δ) ^ 2 / 2)
          ≤ ((|x₀| / b + δ) + (a / b) * |x|) ^ 2 / 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < 2).le
            apply pow_le_pow_left₀ (by positivity) hm_bound
        _ ≤ (|x₀| / b + δ) ^ 2 + ((a / b) * |x|) ^ 2 := hsq _ _
    have : ((a / b) * |x|) ^ 2 = c₂ * x ^ 2 := by
      rw [hc₂_def, mul_pow, sq_abs]
    linarith
  -- Step 9: Combine
  set c₁ := ε * (2 * δ * (sqrt (2 * π))⁻¹ * exp (-((|x₀| / b + δ) ^ 2))) with hc₁_def
  have hc₁_pos : 0 < c₁ := by positivity
  exact ⟨c₁, c₂, hc₁_pos, hc₂_pos, fun x => by
    calc c₁ * exp (-c₂ * x ^ 2)
        = ε * (2 * δ * (sqrt (2 * π))⁻¹ *
          (exp (-((|x₀| / b + δ) ^ 2)) * exp (-(c₂ * x ^ 2)))) := by
          simp only [hc₁_def]; ring
      _ ≤ ε * (2 * δ * (sqrt (2 * π))⁻¹ *
          exp (-(( |(x₀ - a * x) / b| + δ) ^ 2 / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hε_pos.le
          apply mul_le_mul_of_nonneg_left (hexp_bound x)
          positivity
      _ ≤ ε * stdGaussian.real (Set.Icc ((x₀ - a * x) / b - δ) ((x₀ - a * x) / b + δ)) :=
          mul_le_mul_of_nonneg_left (hstep7 x) hε_pos.le
      _ = ε * stdGaussian.real (Set.Icc (((x₀ - r) - a * x) / b)
          (((x₀ + r) - a * x) / b)) := by rw [hIcc_eq]
      _ ≤ ouSemigroup t g x := hkey x⟩

private lemma integrable_one_add_log_ouSemigroup (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x) :
    Integrable (fun x => 1 + log (ouSemigroup t g x)) stdGaussian := by
  -- Strategy: split into integrable constant + integrable log part.
  -- For log: bound |log(P_t g(x))| ≤ P_t g(x) + |log c₁| + c₂ x²
  -- using upper bound log y ≤ y and lower bound P_t g(x) ≥ c₁ exp(-c₂ x²).
  -- Step 0: Get the Gaussian lower bound
  obtain ⟨c₁, c₂, hc₁, hc₂, hlow⟩ :=
    ouSemigroup_lower_bound g g' t ht hg_nn hg_int hg_pos_int hg'_bound hg_deriv
  -- Step 1: P_t g > 0 pointwise (from the lower bound)
  have hPt_pos : ∀ x, 0 < ouSemigroup t g x := by
    intro x; calc 0 < c₁ * exp (-c₂ * x ^ 2) := by positivity
      _ ≤ ouSemigroup t g x := hlow x
  -- Step 2: It suffices to show log ∘ (P_t g) is integrable (then add constant 1)
  suffices h : Integrable (fun x => log (ouSemigroup t g x)) stdGaussian by
    exact (integrable_const 1).add h
  -- Step 3: Bound |log(P_t g(x))| pointwise
  -- Upper: log(P_t g(x)) ≤ P_t g(x) (since log y ≤ y for y > 0)
  -- Lower: log(P_t g(x)) ≥ log(c₁) - c₂ x² (from lower bound)
  -- So |log(P_t g(x))| ≤ P_t g(x) + |log c₁| + c₂ x²
  have hPt_int := integrable_ouSemigroup t (le_of_lt ht) g hg_int
  -- Step 4: x² is integrable against Gaussian
  have hx2_int : Integrable (fun x : ℝ => x ^ 2) stdGaussian := by
    have hmem : MemLp (fun x : ℝ => x) 2 stdGaussian := by
      have := memLp_id_gaussianReal (2 : NNReal) (μ := 0) (v := 1)
      simp only [stdGaussian, id] at this ⊢; exact this
    exact hmem.integrable_sq
  -- Step 5: The dominating function D(x) = P_t g(x) + |log c₁| + c₂ x² is integrable
  have hdom_int : Integrable (fun x => ouSemigroup t g x + |log c₁| + c₂ * x ^ 2)
      stdGaussian :=
    (hPt_int.add (integrable_const _)).add (hx2_int.const_mul c₂)
  -- Step 6: Measurability of log ∘ P_t g
  have hg_diff : Differentiable ℝ g := fun w => (hg_deriv w).differentiableAt
  have hg_cont : Continuous g := hg_diff.continuous
  have hPt_cont : Continuous (ouSemigroup t g) := by
    have := ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound
      (fun z => by
        obtain ⟨C, hC⟩ := hg'_bound
        have hC_nn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
        set Cnn : NNReal := ⟨C, hC_nn⟩
        have hg_lip := lipschitzWith_of_nnnorm_deriv_le hg_diff fun w => by
          show ‖deriv g w‖₊ ≤ Cnn
          rw [← NNReal.coe_le_coe, coe_nnnorm, (hg_deriv w).deriv]; exact hC w
        set a := exp (-t) * z; set b := sqrt (1 - exp (-2 * t))
        have h1 : Integrable (fun _ : ℝ => g 0) stdGaussian := integrable_const _
        have h2 : Integrable (fun y => g (a + b * y) - g 0) stdGaussian :=
          Integrable.mono
            ((integrable_const (C * |a|)).add
              ((IsGaussian.integrable_fun_id (μ := stdGaussian)).norm.const_mul (C * |b|)))
            ((hg_cont.measurable.comp (measurable_const.add
              (measurable_const.mul measurable_id))).sub measurable_const).aestronglyMeasurable
            (ae_of_all _ fun y => by
              have h := hg_lip.norm_sub_le (a + b * y) 0
              simp only [sub_zero, show (Cnn : ℝ) = C from rfl] at h
              have hnn : 0 ≤ C * |a| + C * |b| * ‖y‖ :=
                add_nonneg (mul_nonneg hC_nn (abs_nonneg _))
                  (mul_nonneg (mul_nonneg hC_nn (abs_nonneg _)) (norm_nonneg _))
              calc ‖g (a + b * y) - g 0‖ ≤ C * ‖a + b * y‖ := h
                _ ≤ C * (|a| + |b * y|) := by
                    gcongr; rw [Real.norm_eq_abs]; exact abs_add_le _ _
                _ = C * |a| + C * |b| * ‖y‖ := by rw [abs_mul b y, Real.norm_eq_abs]; ring
                _ ≤ ‖(C * |a| + C * |b| * ‖y‖ : ℝ)‖ :=
                    le_of_eq (Real.norm_of_nonneg hnn).symm)
        rw [show (fun y => g (a + b * y)) = (fun y => g 0 + (g (a + b * y) - g 0)) from by
          ext y; abel]
        exact h1.add h2)
    exact Differentiable.continuous fun x => (this x).differentiableAt
  have hPt_meas : Measurable (ouSemigroup t g) := hPt_cont.measurable
  have hlog_meas : AEStronglyMeasurable (fun x => log (ouSemigroup t g x)) stdGaussian :=
    (measurable_log.comp hPt_meas).aestronglyMeasurable
  -- Step 7: Apply Integrable.mono with the dominating function
  exact Integrable.mono hdom_int hlog_meas (ae_of_all _ fun x => by
    have hpos := hPt_pos x
    have hlow_x := hlow x
    -- The dominating function is nonneg, so its norm = itself
    have hdom_nn : 0 ≤ ouSemigroup t g x + |log c₁| + c₂ * x ^ 2 :=
      add_nonneg (add_nonneg (le_of_lt hpos) (abs_nonneg _))
        (mul_nonneg (le_of_lt hc₂) (sq_nonneg x))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdom_nn]
    -- Case split: log(P_t g(x)) ≥ 0 or < 0
    by_cases hlog : 0 ≤ log (ouSemigroup t g x)
    · -- log ≥ 0: |log y| = log y ≤ y ≤ y + |log c₁| + c₂ x²
      rw [abs_of_nonneg hlog]
      have := Real.log_le_self (le_of_lt hpos)
      linarith [abs_nonneg (log c₁), mul_nonneg (le_of_lt hc₂) (sq_nonneg x)]
    · -- log < 0: |log y| = -log y ≤ |log c₁| + c₂ x²
      push_neg at hlog
      rw [abs_of_neg hlog]
      have h1 : log (ouSemigroup t g x) ≥ log (c₁ * exp (-c₂ * x ^ 2)) :=
        Real.log_le_log (by positivity) hlow_x
      have h2 : log (c₁ * exp (-c₂ * x ^ 2)) = log c₁ + (-c₂ * x ^ 2) := by
        rw [Real.log_mul (ne_of_gt hc₁) (ne_of_gt (exp_pos _)), Real.log_exp]
      linarith [neg_abs_le (log c₁), le_of_lt hpos])

/-- `1 + log(P_t g) ∈ L²(γ)` when g ≥ 0 ae, ∫g > 0, g' bounded.
Bound: `|1+log P_t g x| ≤ D + c x²` (Gaussian lower bound + log≤id),
so squared is ≤ C(1 + x⁴), integrable by Gaussian moments. -/
private lemma memLp_two_one_add_log_ouSemigroup (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hg_int_all : ∀ z, Integrable (fun y => g (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian) :
    MemLp (fun x => 1 + log (ouSemigroup t g x)) 2 stdGaussian := by
  -- Get the lower bound: P_t g x ≥ c₁ exp(-c₂ x²)
  obtain ⟨c₁, c₂, hc₁, hc₂, hlow⟩ :=
    ouSemigroup_lower_bound g g' t ht hg_nn hg_int hg_pos_int hg'_bound hg_deriv
  have hPt_pos : ∀ x, 0 < ouSemigroup t g x := by
    intro x; calc 0 < c₁ * exp (-c₂ * x ^ 2) := by positivity
      _ ≤ ouSemigroup t g x := hlow x
  -- Upper bound on P_t g via Lipschitz: |P_t g x| ≤ |P_t g 0| + exp(-t)*M*|x|
  have hg'_bound_save := hg'_bound
  obtain ⟨Mb, hMb⟩ := hg'_bound
  have hMb_nn : 0 ≤ Mb := le_trans (norm_nonneg _) (hMb 0)
  have hPt_g'_bound' : ∀ x, ‖ouSemigroup t g' x‖ ≤ Mb := by
    intro z; simp only [ouSemigroup]
    calc ‖∫ y, g' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y) ∂stdGaussian‖
        ≤ ∫ y, ‖g' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y)‖ ∂stdGaussian :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _, Mb ∂stdGaussian := by
          apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            (integrable_const _) (ae_of_all _ fun y => hMb _)
      _ = Mb := by simp [integral_const]
  have hPt_lip : ∀ x, |ouSemigroup t g x - ouSemigroup t g 0| ≤ exp (-t) * Mb * |x - 0| := by
    intro x
    have hcomm := fun z => ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound_save hg_int_all z
    have hPtg_diff : Differentiable ℝ (ouSemigroup t g) :=
      fun z => (hcomm z).differentiableAt
    set Mnn : NNReal := ⟨exp (-t) * Mb, mul_nonneg (le_of_lt (exp_pos _)) hMb_nn⟩
    have hPt_lipschitz : LipschitzWith Mnn (ouSemigroup t g) := by
      apply lipschitzWith_of_nnnorm_deriv_le hPtg_diff
      intro z
      show ‖deriv (ouSemigroup t g) z‖₊ ≤ Mnn
      rw [← NNReal.coe_le_coe, coe_nnnorm, (hcomm z).deriv]
      show ‖exp (-t) * ouSemigroup t g' z‖ ≤ exp (-t) * Mb
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hPt_g'_bound' z) (le_of_lt (exp_pos _))
    have := hPt_lipschitz.dist_le_mul x 0
    simp only [Real.dist_eq, NNReal.coe_mk] at this
    exact this
  -- Combined bound: |1 + log(P_t g x)| ≤ K₁ + K₂|x| + c₂ x²
  -- (from upper: 1+log ≤ 1+P_t g ≤ 1+|P_t g 0|+exp(-t)*Mb*|x|)
  -- (from lower: 1+log ≥ 1+log c₁ - c₂ x²)
  -- Bound |x| ≤ 1 + x² (from AM-GM: (|x|-1)² ≥ 0)
  have hx_le_sq : ∀ x : ℝ, |x| ≤ 1 + x ^ 2 := by
    intro x; nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  -- Set dominator constant: K + (c₂ + exp(-t)*Mb) x²
  set K := 2 + |ouSemigroup t g 0| + |log c₁| + exp (-t) * Mb with hK_def
  set B := c₂ + exp (-t) * Mb with hB_def
  have hbd : ∀ x, |1 + log (ouSemigroup t g x)| ≤ K + B * x ^ 2 := by
    intro x
    have hpos := hPt_pos x
    have habs_Pt : |ouSemigroup t g x| ≤ |ouSemigroup t g 0| + exp (-t) * Mb * |x| := by
      have hlip := hPt_lip x; simp only [sub_zero] at hlip
      have : ouSemigroup t g x = ouSemigroup t g 0 + (ouSemigroup t g x - ouSemigroup t g 0) := by ring
      rw [this]
      exact le_trans (abs_add_le _ _) (by linarith)
    by_cases hlog : 0 ≤ log (ouSemigroup t g x)
    · rw [abs_of_nonneg (by linarith)]
      calc 1 + log (ouSemigroup t g x) ≤ 1 + ouSemigroup t g x :=
              by linarith [Real.log_le_self (le_of_lt hpos)]
        _ ≤ 1 + |ouSemigroup t g x| := by linarith [le_abs_self (ouSemigroup t g x)]
        _ ≤ 1 + |ouSemigroup t g 0| + exp (-t) * Mb * |x| := by linarith [habs_Pt]
        _ ≤ 1 + |ouSemigroup t g 0| + exp (-t) * Mb * (1 + x ^ 2) := by
            gcongr; exact hx_le_sq x
        _ ≤ K + B * x ^ 2 := by
            rw [hK_def, hB_def]
            nlinarith [abs_nonneg (log c₁), mul_nonneg (le_of_lt hc₂) (sq_nonneg x)]
    · push_neg at hlog
      have h1 : log (ouSemigroup t g x) ≥ log (c₁ * exp (-c₂ * x ^ 2)) :=
        Real.log_le_log (by positivity) (hlow x)
      have h2 : log (c₁ * exp (-c₂ * x ^ 2)) = log c₁ + (-c₂ * x ^ 2) := by
        rw [Real.log_mul (ne_of_gt hc₁) (ne_of_gt (exp_pos _)), Real.log_exp]
      -- |1+log| ≤ 1 + |log| ≤ 1 + |log c₁| + c₂ x² ≤ K + B x²
      have hab : |1 + log (ouSemigroup t g x)| ≤ 1 + |log (ouSemigroup t g x)| :=
        (abs_add_le 1 _).trans (by simp [abs_of_pos])
      have hlog_bound : |log (ouSemigroup t g x)| ≤ |log c₁| + c₂ * x ^ 2 := by
        rw [abs_of_neg hlog]; linarith [neg_abs_le (log c₁)]
      calc |1 + log (ouSemigroup t g x)| ≤ 1 + |log (ouSemigroup t g x)| := hab
        _ ≤ 1 + (|log c₁| + c₂ * x ^ 2) := by linarith [hlog_bound]
        _ ≤ K + B * x ^ 2 := by
            rw [hK_def, hB_def]
            nlinarith [le_of_lt hpos, abs_nonneg (ouSemigroup t g 0),
              mul_nonneg (le_of_lt (exp_pos (-t))) hMb_nn]
  -- Dominator D(x) = K + B x² is in MemLp 2
  -- D² ≤ 2K² + 2B²x⁴, and x⁴ is integrable (id ∈ MemLp 4)
  have hid4 : MemLp (fun x : ℝ => x) 4 stdGaussian := by
    have := memLp_id_gaussianReal (4 : NNReal) (μ := 0) (v := 1)
    simp only [id] at this; exact this
  have hH44 : ENNReal.HolderTriple 4 4 2 := ⟨by
    show (4 : ENNReal)⁻¹ + 4⁻¹ = 2⁻¹
    rw [show (4 : ENNReal) = 2 * 2 from by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤)),
        ← two_mul, mul_comm, mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]⟩
  have hx2_memLp2 : MemLp (fun x : ℝ => x ^ 2) 2 stdGaussian :=
    (hid4.mul' hid4 (hpqr := hH44)).ae_eq (ae_of_all _ fun x => by simp [sq])
  have hdom_memLp2 : MemLp (fun x => K + B * x ^ 2) 2 stdGaussian :=
    (memLp_const K).add (hx2_memLp2.const_mul B)
  -- Measurability of 1 + log(P_t g)
  have hPtg_diff : Differentiable ℝ (ouSemigroup t g) :=
    fun z => (ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound_save hg_int_all z).differentiableAt
  have hasm : AEStronglyMeasurable (fun x => 1 + log (ouSemigroup t g x)) stdGaussian :=
    ((measurable_const.add (measurable_log.comp hPtg_diff.continuous.measurable))).aestronglyMeasurable
  -- Apply MemLp.of_le with the dominator
  exact hdom_memLp2.of_le hasm (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    calc |1 + log (ouSemigroup t g x)| ≤ K + B * x ^ 2 := hbd x
      _ ≤ |K + B * x ^ 2| := le_abs_self _
      _ = ‖(K + B * x ^ 2 : ℝ)‖ := (Real.norm_eq_abs _).symm)

/-! ## Pointwise Cauchy-Schwarz for OU semigroup (moved before entropy_dissipation)

For `g > 0` a.e., `(P_t g')(x)² / P_t g(x) ≤ P_t(g'²/g)(x)`.

This is Jensen's inequality for the convex function `u ↦ u²/a`:
  `(∫ h dν)² / (∫ k dν) ≤ ∫ (h²/k) dν`
when `k > 0` a.e. Equivalently, writing `h = √k · (h/√k)`,
Cauchy-Schwarz gives `(∫ h)² ≤ (∫ k)(∫ h²/k)`. -/

/-- Integral Cauchy-Schwarz in the form `(∫ h)² / (∫ k) ≤ ∫ (h²/k)`
when `k > 0` a.e. under a probability measure.

Proof: set `c = (∫ h)/(∫ k)` and expand `0 ≤ ∫ (h - c·k)²/k`. -/
private lemma integral_sq_div_le' {μ : Measure ℝ} [IsProbabilityMeasure μ]
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

private lemma ouSemigroup_sq_div_le' (g g' : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x) (x : ℝ)
    (hg'_slice : Integrable (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y))
      stdGaussian)
    (hg_slice : Integrable (fun y => g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y))
      stdGaussian)
    (hFisher_slice : Integrable (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ^ 2 /
      g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian) :
    ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
      ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
  by_cases ht0 : t = 0
  · subst ht0; simp [ouSemigroup]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    simp only [ouSemigroup]
    have hg_comp_pos : ∀ᵐ y ∂stdGaussian,
        0 < g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) := by
      set φ := fun y : ℝ => exp (-t) * x + sqrt (1 - exp (-2 * t)) * y
      have hφ_aem : AEMeasurable φ stdGaussian := by fun_prop
      have hv := ouVar_ne_zero t ht_pos
      have h_ac : (Measure.map φ stdGaussian) ≪ stdGaussian := by
        rw [map_affine_stdGaussian]
        exact (gaussianReal_absolutelyContinuous _ hv).trans
          (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
      exact ae_of_ae_map hφ_aem (h_ac.ae_le hg_pos)
    exact integral_sq_div_le' _ _ hg_comp_pos hg'_slice hg_slice hFisher_slice

lemma entropy_dissipation (g g' g'' : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ g x)
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x)
    (hg_int : Integrable g stdGaussian)
    (hg_pos_int : 0 < ∫ x, g x ∂stdGaussian)
    (hg'_int : MemLp g' 2 stdGaussian)
    (hg'_bound : ∃ C, ∀ x, ‖g' x‖ ≤ C)
    (hg_deriv : ∀ x, HasDerivAt g (g' x) x)
    (hg'_deriv : ∀ x, HasDerivAt g' (g'' x) x)
    (hg''_bound : ∃ C, ∀ x, ‖g'' x‖ ≤ C)
    -- integrability of generator term times log (follows from regularity of P_t g)
    (hint_gen : Integrable (fun x => ouGeneratorAt t g x *
      (1 + log (ouSemigroup t g x))) stdGaussian)
    -- Fisher information of g is finite
    (hFisher : Integrable (fun x => g' x ^ 2 / g x) stdGaussian)
    -- MemLp 2 of the Fisher integrand (P_t g')²/(P_t g) under the semigroup
    -- This follows from hypercontractivity or Gaussian lower bounds on P_t g
    (hFisher_memLp2 : MemLp (fun x => deriv (ouSemigroup t g) x *
      (deriv (ouSemigroup t g) x / ouSemigroup t g x)) 2 stdGaussian)
    -- entropy integrable in a neighborhood of t
    (hent_int : ∀ᶠ s in nhds t, Integrable (fun x =>
      ouSemigroup s g x * log (ouSemigroup s g x)) stdGaussian) :
    HasDerivAt (fun s => ∫ x, ouSemigroup s g x * log (ouSemigroup s g x) ∂stdGaussian)
      (-(∫ x, (exp (-t) * ouSemigroup t g' x) ^ 2 / ouSemigroup t g x ∂stdGaussian))
      t := by
  -- Step 0: P_t g > 0 a.e. for t > 0
  have hPt_pos := ouSemigroup_pos_ae g t ht hg_nn hg_int hg_pos_int
  -- Step 1: The OU equation holds pointwise
  have htime := fun x => ouSemigroup_time_deriv g g' g'' t ht hg_deriv hg'_deriv
    hg'_bound hg''_bound hg_int x
  -- Step 2: Leibniz rule gives F'(t) = ∫ L(P_t g) · (1 + log(P_t g)) dγ
  have hleib := entropy_hasDerivAt_of_time_deriv g t ht hg_nn hg_int hPt_pos htime
    hint_gen hent_int
  -- Step 3: Extract regularity sub-results for dirichlet_form_entropy
  have hg_diff : Differentiable ℝ g := fun w => (hg_deriv w).differentiableAt
  have hg_meas : Measurable g := hg_diff.continuous.measurable
  -- g∘affine integrable for ALL x (Lipschitz + Gaussian moments)
  have hg_int_all : ∀ z, Integrable (fun y => g (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z; obtain ⟨C, hC⟩ := hg'_bound
    have hC_nn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
    set Cnn : NNReal := ⟨C, hC_nn⟩
    have hCnn_eq : (Cnn : ℝ) = C := rfl
    have hg_lip := lipschitzWith_of_nnnorm_deriv_le hg_diff fun w => by
      show ‖deriv g w‖₊ ≤ Cnn
      rw [← NNReal.coe_le_coe, coe_nnnorm, hCnn_eq, (hg_deriv w).deriv]; exact hC w
    set a := exp (-t) * z; set b := sqrt (1 - exp (-2 * t))
    have haffine_meas : Measurable (fun y : ℝ => a + b * y) :=
      measurable_const.add (measurable_const.mul measurable_id)
    have h1 : Integrable (fun _ : ℝ => g 0) stdGaussian := integrable_const _
    have h2 : Integrable (fun y => g (a + b * y) - g 0) stdGaussian := by
      exact Integrable.mono
        ((integrable_const (C * |a|)).add
          ((IsGaussian.integrable_fun_id (μ := stdGaussian)).norm.const_mul (C * |b|)))
        ((hg_meas.comp haffine_meas).sub measurable_const).aestronglyMeasurable
        (ae_of_all _ fun y => by
          have h := hg_lip.norm_sub_le (a + b * y) 0
          simp only [sub_zero, hCnn_eq] at h
          have hnn : 0 ≤ C * |a| + C * |b| * ‖y‖ :=
            add_nonneg (mul_nonneg hC_nn (abs_nonneg _))
              (mul_nonneg (mul_nonneg hC_nn (abs_nonneg _)) (norm_nonneg _))
          calc ‖g (a + b * y) - g 0‖ ≤ C * ‖a + b * y‖ := h
            _ ≤ C * (|a| + |b * y|) := by
                gcongr; rw [Real.norm_eq_abs]; exact abs_add_le _ _
            _ = C * |a| + C * |b| * ‖y‖ := by rw [abs_mul b y, Real.norm_eq_abs]; ring
            _ ≤ ‖(C * |a| + C * |b| * ‖y‖ : ℝ)‖ :=
                le_of_eq (Real.norm_of_nonneg hnn).symm)
    rw [show (fun y => g (a + b * y)) = (fun y => g 0 + (g (a + b * y) - g 0)) from by
      ext y; abel]
    exact h1.add h2
  -- g'∘affine integrable for ALL x (bounded derivative)
  have hg'_int_all : ∀ z, Integrable (fun y => g' (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z; obtain ⟨C, hC⟩ := hg'_bound
    have hg'_meas : Measurable g' := by
      have : g' = deriv g := funext fun w => (hg_deriv w).deriv.symm
      rw [this]; exact measurable_deriv g
    exact Integrable.of_bound
      ((hg'_meas.comp (measurable_const.add
        (measurable_const.mul measurable_id))).aestronglyMeasurable) C
      (ae_of_all _ fun y => hC _)
  -- Pointwise positivity of P_t g (all slices integrable via Lipschitz → strengthens ae to ∀)
  have hPt_pos_all : ∀ x, 0 < ouSemigroup t g x := by
    intro x₀; simp only [ouSemigroup]
    have hv := ouVar_ne_zero t ht
    set a' := exp (-t) * x₀; set b' := sqrt (1 - exp (-2 * t))
    have hφ_aem : AEMeasurable (fun y : ℝ => a' + b' * y) stdGaussian := by fun_prop
    have h_ac : (Measure.map (fun y => a' + b' * y) stdGaussian) ≪ stdGaussian := by
      rw [map_affine_stdGaussian]
      exact (gaussianReal_absolutelyContinuous _ hv).trans
        (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
    have hslice_nn : ∀ᵐ y ∂stdGaussian, 0 ≤ g (a' + b' * y) :=
      ae_of_ae_map hφ_aem (h_ac.ae_le hg_nn)
    by_contra h_le; push_neg at h_le
    have h_eq : ∫ y, g (a' + b' * y) ∂stdGaussian = 0 :=
      le_antisymm h_le (integral_nonneg_of_ae hslice_nn)
    have hslice_zero' := ((integral_eq_zero_iff_of_nonneg_ae hslice_nn
      (hg_int_all x₀)).mp h_eq)
    have hslice_zero : ∀ᵐ y ∂stdGaussian, g (a' + b' * y) = 0 := by
      filter_upwards [hslice_zero'] with y hy; exact hy
    linarith [integral_eq_zero_of_ae
      (ae_zero_of_comp_affine g hg_meas a' b' hv hslice_zero)]
  -- Boundedness of P_t g'
  have hPt_g'_bound : ∃ C, ∀ x, ‖ouSemigroup t g' x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg'_bound
    exact ⟨C, fun z => by
      simp only [ouSemigroup]
      calc ‖∫ y, g' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y) ∂stdGaussian‖
          ≤ ∫ y, ‖g' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y)‖ ∂stdGaussian :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _, C ∂stdGaussian := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (integrable_const _) (ae_of_all _ fun y => hC _)
        _ = C := by simp [integral_const, measure_univ]⟩
  -- HasDerivAt for exp(-t) * P_t g' (from ouSemigroup_hasDerivAt applied to g')
  have hPt_hasDerivAt2 : ∀ x, HasDerivAt (fun z => exp (-t) * ouSemigroup t g' z)
      (deriv (fun z => exp (-t) * ouSemigroup t g' z) x) x := by
    intro x
    have h := (ouSemigroup_hasDerivAt t g' g'' hg'_deriv hg''_bound hg'_int_all x).const_mul
      (exp (-t))
    rw [h.deriv]; exact h
  -- Log integrability from helper lemma
  have hlog_int := integrable_one_add_log_ouSemigroup g g' t ht hg_nn hg_int hg_pos_int
    hg'_bound hg_deriv
  -- Derivative identity: deriv(P_t g) = exp(-t) * P_t g'
  have hcomm : ∀ x, HasDerivAt (ouSemigroup t g) (exp (-t) * ouSemigroup t g' x) x :=
    fun x => ouSemigroup_hasDerivAt t g g' hg_deriv hg'_bound hg_int_all x
  have hderiv_eq : deriv (ouSemigroup t g) = fun x => exp (-t) * ouSemigroup t g' x :=
    funext fun x => (hcomm x).deriv
  -- g''∘affine integrable for all x (bounded)
  have hg''_int_all : ∀ z, Integrable (fun y => g'' (exp (-t) * z +
      sqrt (1 - exp (-2 * t)) * y)) stdGaussian := by
    intro z; obtain ⟨C, hC⟩ := hg''_bound
    have hg'_diff : Differentiable ℝ g' := fun w => (hg'_deriv w).differentiableAt
    exact Integrable.of_bound
      (((measurable_deriv g').comp (measurable_const.add
        (measurable_const.mul measurable_id))).aestronglyMeasurable.congr
        (ae_of_all _ fun y => by
          change deriv g' _ = g'' _; exact (hg'_deriv _).deriv)) C
      (ae_of_all _ fun y => hC _)
  -- Second derivative: deriv(deriv(P_t g)) x = exp(-t) * (exp(-t) * P_t g'' x)
  have hcomm2 : ∀ x, HasDerivAt (ouSemigroup t g') (exp (-t) * ouSemigroup t g'' x) x :=
    fun x => ouSemigroup_hasDerivAt t g' g'' hg'_deriv hg''_bound hg'_int_all x
  have hderiv2_eq : ∀ x, deriv (deriv (ouSemigroup t g)) x =
      exp (-t) * (exp (-t) * ouSemigroup t g'' x) := by
    intro x; rw [hderiv_eq]; exact ((hcomm2 x).const_mul (exp (-t))).deriv
  -- Boundedness of P_t g''
  have hPt_g''_bound : ∃ C, ∀ x, ‖ouSemigroup t g'' x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg''_bound
    exact ⟨C, fun z => by
      simp only [ouSemigroup]
      calc ‖∫ y, g'' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y) ∂stdGaussian‖
          ≤ ∫ y, ‖g'' (exp (-t) * z + sqrt (1 - exp (-2 * t)) * y)‖ ∂stdGaussian :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ _, C ∂stdGaussian := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (integrable_const _) (ae_of_all _ fun y => hC _)
        _ = C := by simp [integral_const]⟩
  -- Prove hint_φ''ψ: Integrable (deriv²(P_t g) * (1+log P_t g))
  -- |deriv²(P_t g) x| ≤ exp(-2t)*C'', so bounded * integrable = integrable
  have hint_φ''ψ : Integrable (fun x => deriv (deriv (ouSemigroup t g)) x *
      (1 + log (ouSemigroup t g x))) stdGaussian := by
    obtain ⟨C'', hC''⟩ := hPt_g''_bound
    have hC''_nn : 0 ≤ C'' := le_trans (norm_nonneg _) (hC'' 0)
    have hae_rw : (fun x => exp (-t) * (exp (-t) * ouSemigroup t g'' x) *
        (1 + log (ouSemigroup t g x))) =ᵐ[stdGaussian]
        (fun x => deriv (deriv (ouSemigroup t g)) x *
          (1 + log (ouSemigroup t g x))) :=
      ae_of_all _ fun x => by simp only [hderiv2_eq]
    suffices h : Integrable (fun x => exp (-t) * (exp (-t) * ouSemigroup t g'' x) *
        (1 + log (ouSemigroup t g x))) stdGaussian from h.congr hae_rw
    set M := exp (-t) * (exp (-t) * C'')
    have hM_nn : 0 ≤ M := mul_nonneg (le_of_lt (exp_pos _))
      (mul_nonneg (le_of_lt (exp_pos _)) hC''_nn)
    have hg''_int : Integrable g'' stdGaussian := by
      obtain ⟨Cg, hCg⟩ := hg''_bound
      have hg''_asm : AEStronglyMeasurable g'' stdGaussian := by
        have heq : g'' = deriv g' := funext fun w => (hg'_deriv w).deriv.symm
        rw [heq]; exact (measurable_deriv g').aestronglyMeasurable
      exact Integrable.of_bound hg''_asm Cg (ae_of_all _ fun x => hCg x)
    apply (hlog_int.const_mul M).mono
    · exact (aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul
        (integrable_ouSemigroup t (le_of_lt ht) g'' hg''_int).aestronglyMeasurable)).mul
        hlog_int.aestronglyMeasurable
    · filter_upwards with x
      have h1 : |exp (-t) * (exp (-t) * ouSemigroup t g'' x)| ≤ M := by
        rw [abs_mul, abs_of_pos (exp_pos _), abs_mul, abs_of_pos (exp_pos _)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ hC'' x)
            (le_of_lt (exp_pos _))) (le_of_lt (exp_pos _))
      calc ‖exp (-t) * (exp (-t) * ouSemigroup t g'' x) * (1 + log (ouSemigroup t g x))‖
          = |exp (-t) * (exp (-t) * ouSemigroup t g'' x)| *
            |1 + log (ouSemigroup t g x)| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ M * |1 + log (ouSemigroup t g x)| := by gcongr
        _ = ‖M * (1 + log (ouSemigroup t g x))‖ := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM_nn]
  -- Prove hint_xφψ: Integrable (x * deriv(P_t g) * (1+log P_t g))
  -- ouGeneratorAt = deriv² - x*deriv, so x*deriv*ψ = deriv²*ψ - ouGen*ψ
  have hint_xφψ : Integrable (fun x => x * (deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x)))) stdGaussian := by
    have hae_eq : (fun x => deriv (deriv (ouSemigroup t g)) x * (1 + log (ouSemigroup t g x)) -
        ouGeneratorAt t g x * (1 + log (ouSemigroup t g x))) =ᵐ[stdGaussian]
        (fun x => x * (deriv (ouSemigroup t g) x * (1 + log (ouSemigroup t g x)))) := by
      filter_upwards with x; simp only [ouGeneratorAt]; ring
    exact (hint_φ''ψ.sub hint_gen).congr hae_eq
  -- Dirichlet form gives ∫ L(P_t g)(1+log(P_t g)) dγ = -Fisher
  have hdirich := dirichlet_form_entropy g g' t ht hg_nn hg_int hg'_int hg_deriv hPt_pos
    hg'_bound hg_int_all hg'_int_all hPt_pos_all hPt_g'_bound hPt_hasDerivAt2
    (by -- MemLp (deriv(P_t g) * (1+log P_t g)) 2: bounded × L² = L²
      -- deriv(P_t g) = exp(-t) * P_t g' is bounded
      obtain ⟨Md, hMd⟩ := hPt_g'_bound
      have hMd_nn : 0 ≤ Md := le_trans (norm_nonneg _) (hMd 0)
      -- deriv(P_t g) ∈ MemLp ∞ (bounded on prob measure)
      have hderiv_bound : ∀ x, ‖deriv (ouSemigroup t g) x‖ ≤ exp (-t) * Md := by
        intro x; rw [hderiv_eq, norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hMd x) (le_of_lt (exp_pos _))
      have hderiv_asm : AEStronglyMeasurable (deriv (ouSemigroup t g)) stdGaussian := by
        rw [hderiv_eq]
        exact aestronglyMeasurable_const.mul
          (integrable_ouSemigroup t (le_of_lt ht) g'
            ((hg'_int.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).integrable le_rfl)).aestronglyMeasurable
      have hderiv_top : MemLp (deriv (ouSemigroup t g)) ⊤ stdGaussian :=
        memLp_top_of_bound hderiv_asm _ (ae_of_all _ hderiv_bound)
      -- 1+log(P_t g) ∈ MemLp 2
      have hlog_memLp2 := memLp_two_one_add_log_ouSemigroup g g' t ht hg_nn hg_int hg_pos_int
        hg'_bound hg_deriv hg_int_all
      -- Combine: MemLp 2 × MemLp ∞ → MemLp 2 via Hölder
      have hH : ENNReal.HolderTriple ⊤ 2 2 := ⟨by simp⟩
      exact hlog_memLp2.mul' hderiv_top (hpqr := hH)
      : MemLp (fun x => deriv (ouSemigroup t g) x *
      (1 + log (ouSemigroup t g x))) 2 stdGaussian)
    (by -- MemLp (deriv²(P_t g) * (1+log P_t g) + deriv(P_t g) * (deriv(P_t g)/P_t g)) 2
      -- = Term A + Term B, each in MemLp 2
      -- Term A: bounded × L² via Hölder (same as sorry 1 pattern)
      have hlog_memLp2 := memLp_two_one_add_log_ouSemigroup g g' t ht hg_nn
        hg_int hg_pos_int hg'_bound hg_deriv hg_int_all
      obtain ⟨C'', hC''⟩ := hPt_g''_bound
      have hC''_nn : 0 ≤ C'' := le_trans (norm_nonneg _) (hC'' 0)
      have hderiv2_bound : ∀ x,
          ‖deriv (deriv (ouSemigroup t g)) x‖ ≤ exp (-t) * (exp (-t) * C'') := by
        intro x; rw [hderiv2_eq]
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        gcongr; exact hC'' x
      have hderiv2_asm :
          AEStronglyMeasurable (deriv (deriv (ouSemigroup t g))) stdGaussian := by
        have heq : deriv (deriv (ouSemigroup t g)) =
            fun x => exp (-t) * (exp (-t) * ouSemigroup t g'' x) :=
          funext hderiv2_eq
        rw [heq]
        exact aestronglyMeasurable_const.mul (aestronglyMeasurable_const.mul
          (integrable_ouSemigroup t (le_of_lt ht) g''
            (by obtain ⟨Cg, hCg⟩ := hg''_bound
                exact Integrable.of_bound
                  ((measurable_deriv g').aestronglyMeasurable.congr
                    (ae_of_all _ fun w => by rw [(hg'_deriv w).deriv]))
                  Cg (ae_of_all _ fun x => hCg x))).aestronglyMeasurable)
      have hderiv2_top : MemLp (deriv (deriv (ouSemigroup t g))) ⊤ stdGaussian :=
        memLp_top_of_bound hderiv2_asm _ (ae_of_all _ hderiv2_bound)
      have hH : ENNReal.HolderTriple ⊤ 2 2 := ⟨by simp⟩
      have hTermA : MemLp (fun x => deriv (deriv (ouSemigroup t g)) x *
          (1 + log (ouSemigroup t g x))) 2 stdGaussian :=
        hlog_memLp2.mul' hderiv2_top (hpqr := hH)
      exact hTermA.add hFisher_memLp2
      : MemLp (fun x =>
      deriv (deriv (ouSemigroup t g)) x * (1 + log (ouSemigroup t g x)) +
      deriv (ouSemigroup t g) x * (deriv (ouSemigroup t g) x / ouSemigroup t g x))
      2 stdGaussian)
    hint_xφψ
    (by -- Integrable (fun x => deriv(P_t g) x * (deriv(P_t g) x / P_t g x))
      -- = Integrable ((deriv P_t g)² / P_t g) = e^{-2t} * (P_t g')² / P_t g
      -- Bounded by e^{-2t} * P_t(g'²/g) via Cauchy-Schwarz, which is integrable
      have hg'_int_L1 : Integrable g' stdGaussian :=
        (hg'_int.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).integrable le_rfl
      -- ae slice integrabilities
      have hg'_ae : ∀ᵐ x ∂stdGaussian, Integrable
          (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
        (integrable_mehler_prod t (le_of_lt ht) g' hg'_int_L1).prod_right_ae
      have hg_ae : ∀ᵐ x ∂stdGaussian, Integrable
          (fun y => g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
        (integrable_mehler_prod t (le_of_lt ht) g hg_int).prod_right_ae
      have hF_ae : ∀ᵐ x ∂stdGaussian, Integrable
          (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ^ 2 /
            g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
        (integrable_mehler_prod t (le_of_lt ht) (fun y => g' y ^ 2 / g y) hFisher).prod_right_ae
      -- P_t(g'²/g) is integrable
      have hRHS_int : Integrable (ouSemigroup t (fun y => g' y ^ 2 / g y)) stdGaussian :=
        integrable_ouSemigroup t (le_of_lt ht) _ hFisher
      -- Rewrite as e^{-2t} * (P_t g')² / P_t g
      have hae_rw : (fun x => deriv (ouSemigroup t g) x *
          (deriv (ouSemigroup t g) x / ouSemigroup t g x)) =ᵐ[stdGaussian]
          (fun x => exp (-2 * t) * (ouSemigroup t g' x ^ 2 / ouSemigroup t g x)) := by
        filter_upwards with x
        simp only [hderiv_eq]
        have hpos := hPt_pos_all x
        have hne : ouSemigroup t g x ≠ 0 := ne_of_gt hpos
        -- LHS: e^{-t} * P_t g' x * (e^{-t} * P_t g' x / P_t g x)
        -- RHS: e^{-2t} * (P_t g' x ^ 2 / P_t g x)
        have hne : (ouSemigroup t g x : ℝ) ≠ 0 := ne_of_gt (hPt_pos_all x)
        -- After simp [hderiv_eq], goal is:
        -- e^{-t} * P_t g' x * (e^{-t} * (P_t g' x / P_t g x)) = e^{-2t} * (P_t g' x^2 / P_t g x)
        -- Goal: a * b * (a * b / c) = exp(-2t) * (b^2 / c)
        -- where a = exp(-t), b = P_t g', c = P_t g
        have key : ∀ (a b c : ℝ), c ≠ 0 →
            a * b * (a * b / c) = a ^ 2 * (b ^ 2 / c) := by
          intros a b c hc; rw [mul_div_assoc, ← mul_div_assoc]; ring
        rw [key _ _ _ hne, show (exp (-t) : ℝ) ^ 2 = exp (-2 * t) from by
          rw [← exp_nat_mul]; ring_nf]
      -- ae bound: (P_t g')²/P_t g ≤ P_t(g'²/g) via Cauchy-Schwarz
      have h_ae_bound : ∀ᵐ x ∂stdGaussian,
          ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
            ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
        filter_upwards [hg'_ae, hg_ae, hF_ae] with x hg'x hgx hFx
        exact ouSemigroup_sq_div_le' g g' t (le_of_lt ht) hg_pos x hg'x hgx hFx
      -- Nonnegativity of the integrand
      have hnn_ae : ∀ x, 0 ≤ ouSemigroup t g' x ^ 2 / ouSemigroup t g x :=
        fun x => div_nonneg (sq_nonneg _) (le_of_lt (hPt_pos_all x))
      -- AEStronglyMeasurable for (P_t g')²/(P_t g)
      have hPtg'_aem : AEMeasurable (ouSemigroup t g') stdGaussian :=
        (integrable_ouSemigroup t (le_of_lt ht) g' hg'_int_L1).aestronglyMeasurable.aemeasurable
      have hPtg_aem : AEMeasurable (ouSemigroup t g) stdGaussian :=
        (integrable_ouSemigroup t (le_of_lt ht) g hg_int).aestronglyMeasurable.aemeasurable
      have hasm : AEStronglyMeasurable (fun x => ouSemigroup t g' x ^ 2 / ouSemigroup t g x)
          stdGaussian :=
        ((hPtg'_aem.pow_const 2).div hPtg_aem).aestronglyMeasurable
      -- Integrability via domination by P_t(g'²/g)
      have hint_sq_div : Integrable (fun x => ouSemigroup t g' x ^ 2 / ouSemigroup t g x)
          stdGaussian := by
        apply Integrable.mono hRHS_int hasm
        filter_upwards [h_ae_bound] with x hbound
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn_ae x), Real.norm_eq_abs,
            abs_of_nonneg (le_trans (hnn_ae x) hbound)]
        exact hbound
      exact (hint_sq_div.const_mul (exp (-2 * t))).congr hae_rw.symm
      : Integrable (fun x => deriv (ouSemigroup t g) x *
      (deriv (ouSemigroup t g) x / ouSemigroup t g x)) stdGaussian)
    hint_φ''ψ
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
    (hg_pos : ∀ᵐ x ∂stdGaussian, 0 < g x) (x : ℝ)
    (hg'_slice : Integrable (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y))
      stdGaussian)
    (hg_slice : Integrable (fun y => g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y))
      stdGaussian)
    (hFisher_slice : Integrable (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ^ 2 /
      g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian) :
    ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
      ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
  by_cases ht0 : t = 0
  · -- t = 0: P_0 = id, inequality is trivial
    subst ht0; simp [ouSemigroup]
  · -- t > 0: use ae transfer + Cauchy-Schwarz
    have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    simp only [ouSemigroup]
    have hg_comp_pos : ∀ᵐ y ∂stdGaussian,
        0 < g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) := by
      set φ := fun y : ℝ => exp (-t) * x + sqrt (1 - exp (-2 * t)) * y
      have hφ_aem : AEMeasurable φ stdGaussian := by fun_prop
      have hv := ouVar_ne_zero t ht_pos
      have h_ac : (Measure.map φ stdGaussian) ≪ stdGaussian := by
        rw [map_affine_stdGaussian]
        exact (gaussianReal_absolutelyContinuous _ hv).trans
          (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
      exact ae_of_ae_map hφ_aem (h_ac.ae_le hg_pos)
    exact integral_sq_div_le _ _ hg_comp_pos hg'_slice hg_slice hFisher_slice

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
  -- Obtain slice integrabilities from Fubini
  have hg'_int_L1 : Integrable g' stdGaussian :=
    (hg'_int.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).integrable le_rfl
  have hg'_ae : ∀ᵐ x ∂stdGaussian, Integrable
      (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
    (integrable_mehler_prod t ht g' hg'_int_L1).prod_right_ae
  have hg_ae : ∀ᵐ x ∂stdGaussian, Integrable
      (fun y => g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
    (integrable_mehler_prod t ht g hg_int).prod_right_ae
  have hF_ae : ∀ᵐ x ∂stdGaussian, Integrable
      (fun y => g' (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ^ 2 /
        g (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y)) stdGaussian :=
    (integrable_mehler_prod t ht (fun y => g' y ^ 2 / g y) hFisher).prod_right_ae
  -- Integrability of RHS: P_t(g'²/g)
  have hRHS_int : Integrable (ouSemigroup t (fun y => g' y ^ 2 / g y)) stdGaussian :=
    integrable_ouSemigroup t ht _ hFisher
  -- AEStronglyMeasurable for LHS components
  have hPtg'_int := integrable_ouSemigroup t ht g' hg'_int_L1
  have hPtg_int := integrable_ouSemigroup t ht g hg_int
  -- ae pointwise bound via Cauchy-Schwarz
  have h_ae_bound : ∀ᵐ x ∂stdGaussian,
      ouSemigroup t g' x ^ 2 / ouSemigroup t g x ≤
        ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
    filter_upwards [hg'_ae, hg_ae, hF_ae] with x hg'x hgx hFx
    exact ouSemigroup_sq_div_le g g' t ht hg_pos x hg'x hgx hFx
  -- Nonnegativity of LHS ae
  have hLHS_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ ouSemigroup t g' x ^ 2 / ouSemigroup t g x := by
    by_cases ht0 : t = 0
    · subst ht0
      filter_upwards [hg_pos] with x hx
      simp only [ouSemigroup_zero]
      exact div_nonneg (sq_nonneg _) (le_of_lt hx)
    · apply Filter.Eventually.of_forall; intro x
      apply div_nonneg (sq_nonneg _)
      simp only [ouSemigroup]; apply integral_nonneg_of_ae
      have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      set φ := fun y : ℝ => exp (-t) * x + sqrt (1 - exp (-2 * t)) * y
      have hφ_aem : AEMeasurable φ stdGaussian := by fun_prop
      have hv := ouVar_ne_zero t ht_pos
      have h_ac : (Measure.map φ stdGaussian) ≪ stdGaussian := by
        rw [map_affine_stdGaussian]
        exact (gaussianReal_absolutelyContinuous _ hv).trans
          (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
      exact ae_of_ae_map hφ_aem (h_ac.ae_le (Filter.Eventually.mono hg_pos (fun _ h => le_of_lt h)))
  -- Nonnegativity of RHS ae
  have hRHS_nn : ∀ᵐ x ∂stdGaussian, 0 ≤ ouSemigroup t (fun y => g' y ^ 2 / g y) x := by
    by_cases ht0 : t = 0
    · subst ht0
      filter_upwards [hg_pos] with x hx
      simp only [ouSemigroup_zero]
      exact div_nonneg (sq_nonneg _) (le_of_lt hx)
    · apply Filter.Eventually.of_forall; intro x; simp only [ouSemigroup]
      apply integral_nonneg_of_ae
      have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      set φ := fun y : ℝ => exp (-t) * x + sqrt (1 - exp (-2 * t)) * y
      have hφ_aem : AEMeasurable φ stdGaussian := by fun_prop
      have hv := ouVar_ne_zero t ht_pos
      have h_ac : (Measure.map φ stdGaussian) ≪ stdGaussian := by
        rw [map_affine_stdGaussian]
        exact (gaussianReal_absolutelyContinuous _ hv).trans
          (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
      exact ae_of_ae_map hφ_aem (h_ac.ae_le (Filter.Eventually.mono hg_pos (fun _ h =>
        div_nonneg (sq_nonneg _) (le_of_lt h))))
  -- AEStronglyMeasurable for LHS
  have hLHS_aesm : AEStronglyMeasurable
      (fun x => ouSemigroup t g' x ^ 2 / ouSemigroup t g x) stdGaussian :=
    ((hPtg'_int.aestronglyMeasurable.pow 2).aemeasurable.div
      hPtg_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  -- Integrability of LHS from ae bound + RHS integrability
  have hLHS_int : Integrable (fun x => ouSemigroup t g' x ^ 2 / ouSemigroup t g x)
      stdGaussian := by
    apply Integrable.mono hRHS_int hLHS_aesm
    filter_upwards [h_ae_bound, hLHS_nn, hRHS_nn] with x hle hnn hrnn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hrnn]
    exact hle
  -- Step 2a: Pointwise bound via Cauchy-Schwarz
  calc ∫ x, ouSemigroup t g' x ^ 2 / ouSemigroup t g x ∂stdGaussian
      ≤ ∫ x, ouSemigroup t (fun y => g' y ^ 2 / g y) x ∂stdGaussian := by
        exact integral_mono_ae hLHS_int hRHS_int h_ae_bound
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

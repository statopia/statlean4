import Mathlib
import Statlean.LimitTheorems.CLT

/-! # Influence Functions and Semiparametric Efficiency

Foundations of the influence-function calculus underlying Chernozhukov et al.'s
double / debiased machine-learning (DML) framework. The development is
deliberately minimal: we set up centered L² influence functions, asymptotic
linearity of estimator sequences, asymptotic variance, and a Gateaux-style
formulation of Neyman orthogonality of a moment / score function.

## Contents

* `IsCenteredL2 μ ψ` — `ψ ∈ L²(μ)` with `E_μ[ψ] = 0`.
* `IsCenteredL2.{zero,add,smul,neg}` — algebraic closure of the centered L²
  cone (proved).
* `asymptoticVariance μ ψ := ∫ ψ²` — asymptotic variance of an estimator with
  influence function `ψ`. `asymptoticVariance_nonneg` is proved.
* `IsAsymptoticallyLinear μ T θ₀ ψ` — the estimator sequence `T_n` is
  asymptotically linear at `θ₀` with influence function `ψ` under iid
  sampling from `μ`, i.e. the centered, scaled error and the empirical
  influence sum agree to `o_p(1)`.
* `IsNeymanOrthogonal μ m θ₀ η₀` — Gateaux-form Neyman orthogonality of a
  score `m(W; θ, η)` at `(θ₀, η₀)` against nuisance perturbations.
* `asymptotic_linearity_slutsky` (theorem) — Slutsky combining lemma at the
  characteristic-function level on each `Measure.pi μ^⊗n`. Proved by the
  standard `|exp(it·a) − exp(it·b)| ≤ min(2, |t|·|a−b|)` bound combined with
  the `ε`-mass formulation of remainder convergence in `IsAsymptoticallyLinear`.
* `iid_empirical_sum_clt_axiom` (axiom) — iid CLT on per-`n` `Measure.pi μ^⊗n`
  spaces. Currently axiomatised because Mathlib v4.28-rc1 does not yet expose
  `MemLp 2`-iid CLT under a single named lemma; lifting Statlean's own
  `MemLp 3` CLT through `Measure.infinitePiNat` is mechanical but lengthy.

## References

* Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins (2018),
  "Double/Debiased Machine Learning for Treatment and Structural Parameters",
  *The Econometrics Journal* 21, C1–C68.
* Bickel, Klaassen, Ritov, Wellner (1993), *Efficient and Adaptive Estimation
  for Semiparametric Models*.
* van der Vaart (1998), *Asymptotic Statistics*, Chapter 25.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal Real

namespace Statlean.Semiparametric

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Centered L² influence functions -/

/-- A function `ψ : Ω → ℝ` is **centered L²** under measure `μ` if it is in
`L²(μ)` and integrates to zero. -/
structure IsCenteredL2 (μ : Measure Ω) (ψ : Ω → ℝ) : Prop where
  /-- Square integrability. -/
  memLp_two : MemLp ψ 2 μ
  /-- Zero mean. -/
  mean_zero : ∫ ω, ψ ω ∂μ = 0

namespace IsCenteredL2

/-- The zero function is trivially centered L². -/
theorem zero (μ : Measure Ω) : IsCenteredL2 μ (0 : Ω → ℝ) where
  memLp_two := MemLp.zero
  mean_zero := by simp

/-- Sum of two centered L² functions is centered L² (on a finite measure). -/
theorem add {μ : Measure Ω} [IsFiniteMeasure μ] {ψ φ : Ω → ℝ}
    (hψ : IsCenteredL2 μ ψ) (hφ : IsCenteredL2 μ φ) :
    IsCenteredL2 μ (ψ + φ) where
  memLp_two := hψ.memLp_two.add hφ.memLp_two
  mean_zero := by
    have hψ_int : Integrable ψ μ :=
      hψ.memLp_two.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hφ_int : Integrable φ μ :=
      hφ.memLp_two.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    rw [Pi.add_def, integral_add hψ_int hφ_int, hψ.mean_zero, hφ.mean_zero]
    ring

/-- Scalar multiple of a centered L² function is centered L². -/
theorem smul {μ : Measure Ω} {ψ : Ω → ℝ} (c : ℝ) (hψ : IsCenteredL2 μ ψ) :
    IsCenteredL2 μ (c • ψ) where
  memLp_two := hψ.memLp_two.const_smul c
  mean_zero := by
    change ∫ ω, c • ψ ω ∂μ = 0
    rw [integral_smul, hψ.mean_zero, smul_zero]

/-- Negation preserves centered L². -/
theorem neg {μ : Measure Ω} {ψ : Ω → ℝ} (hψ : IsCenteredL2 μ ψ) :
    IsCenteredL2 μ (-ψ) where
  memLp_two := hψ.memLp_two.neg
  mean_zero := by
    change ∫ ω, -ψ ω ∂μ = 0
    rw [integral_neg, hψ.mean_zero, neg_zero]

end IsCenteredL2

/-! ### Asymptotic variance -/

/-- Asymptotic variance of an estimator with influence function `ψ`:
`E_μ[ψ²]`. For a centered L² ψ this coincides with `Var_μ[ψ]`. -/
noncomputable def asymptoticVariance (μ : Measure Ω) (ψ : Ω → ℝ) : ℝ :=
  ∫ ω, ψ ω ^ 2 ∂μ

/-- Asymptotic variance is nonnegative. -/
theorem asymptoticVariance_nonneg (μ : Measure Ω) (ψ : Ω → ℝ) :
    0 ≤ asymptoticVariance μ ψ :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The asymptotic variance of the zero influence function is zero. -/
theorem asymptoticVariance_zero (μ : Measure Ω) :
    asymptoticVariance μ (0 : Ω → ℝ) = 0 := by
  unfold asymptoticVariance
  simp

/-! ### Asymptotic linearity -/

/-- The estimator sequence `T : (n : ℕ) → (Fin n → Ω) → ℝ` is
**asymptotically linear** at parameter `θ₀` with influence function `ψ` (in
`L²(μ)` and centered) if, under iid sampling from `μ`, the remainder

  `√n · (T_n(X) - θ₀) - (1/√n) Σ_{i<n} ψ(X_i)`

converges to zero in probability. We encode "in probability" directly by the
defining `ε`-mass condition (no extra Mathlib infrastructure required).

We additionally require each `T n` to be measurable on `Measure.pi μ^⊗n`,
since this is what gives a well-defined law for the standardised error and
is needed to apply Fubini/`integral_map` in the Slutsky bridge below. -/
def IsAsymptoticallyLinear (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ) : Prop :=
  IsCenteredL2 μ ψ ∧
  (∀ n, Measurable (T n)) ∧
  ∀ ε > (0 : ℝ),
    Tendsto (fun n =>
      (Measure.pi (fun (_ : Fin n) => μ))
        {X : Fin n → Ω | ε ≤ |Real.sqrt n * (T n X - θ₀)
            - (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i)|})
      atTop (𝓝 0)

/-- An asymptotically linear estimator carries a centered L² influence function. -/
theorem IsAsymptoticallyLinear.isCenteredL2
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : (n : ℕ) → (Fin n → Ω) → ℝ} {θ₀ : ℝ} {ψ : Ω → ℝ}
    (h : IsAsymptoticallyLinear μ T θ₀ ψ) : IsCenteredL2 μ ψ :=
  h.1

/-- Each `T n` is measurable. -/
theorem IsAsymptoticallyLinear.measurable_T
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : (n : ℕ) → (Fin n → Ω) → ℝ} {θ₀ : ℝ} {ψ : Ω → ℝ}
    (h : IsAsymptoticallyLinear μ T θ₀ ψ) : ∀ n, Measurable (T n) :=
  h.2.1

/-- The remainder converges to zero in probability (`ε`-mass form). -/
theorem IsAsymptoticallyLinear.remainder_tendsto
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : (n : ℕ) → (Fin n → Ω) → ℝ} {θ₀ : ℝ} {ψ : Ω → ℝ}
    (h : IsAsymptoticallyLinear μ T θ₀ ψ) :
    ∀ ε > (0 : ℝ),
      Tendsto (fun n =>
        (Measure.pi (fun (_ : Fin n) => μ))
          {X : Fin n → Ω | ε ≤ |Real.sqrt n * (T n X - θ₀)
              - (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i)|})
        atTop (𝓝 0) :=
  h.2.2

/-! ### Neyman orthogonality -/

/-- A score / moment function `m : Ω → Θ → H → ℝ` is **Neyman orthogonal** at
`(θ₀, η₀)` (Gateaux form) if for every nuisance direction `h ∈ H` the map

  `t ↦ ∫ m(ω; θ₀, η₀ + t·h) dμ(ω)`

has derivative zero at `t = 0`. This is the definitional form used in the
debiased / orthogonal-score literature; concrete instances must supply
sufficient regularity (smoothness in `t`, dominated convergence) to verify
the `HasDerivAt` hypothesis. -/
def IsNeymanOrthogonal {Θ H : Type*} [AddCommGroup H] [Module ℝ H]
    (μ : Measure Ω) (m : Ω → Θ → H → ℝ) (θ₀ : Θ) (η₀ : H) : Prop :=
  ∀ h : H,
    HasDerivAt (fun t : ℝ => ∫ ω, m ω θ₀ (η₀ + t • h) ∂μ) 0 0

/-! ### Auxiliary lemmas: pointwise bounds on `cexp(I·t·a)` -/

/-- **Lipschitz bound** for `t ↦ exp(I·t·x)` on real arguments:
`|exp(I·t·a) − exp(I·t·b)| ≤ |t|·|a−b|`. -/
private lemma exp_I_diff_bound (t a b : ℝ) :
    ‖cexp ((t : ℂ) * a * I) - cexp ((t : ℂ) * b * I)‖ ≤ |t| * |a - b| := by
  have hkey : cexp ((t : ℂ) * a * I) - cexp ((t : ℂ) * b * I)
      = cexp ((t : ℂ) * b * I) * (cexp ((t : ℂ) * (a - b) * I) - 1) := by
    rw [mul_sub, mul_one]
    have : cexp ((t : ℂ) * b * I) * cexp ((t : ℂ) * (a - b) * I)
        = cexp ((t : ℂ) * a * I) := by
      rw [← Complex.exp_add]; ring_nf
    rw [this]
  rw [hkey, norm_mul, Complex.norm_exp]
  have h1 : (((t : ℂ) * b * I).re) = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [h1, Real.exp_zero, one_mul]
  have h2 : (t : ℂ) * (a - b) * I = I * ((t * (a - b)) : ℝ) := by
    push_cast; ring
  rw [h2]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * (a - b))
  rw [Real.norm_eq_abs, abs_mul] at this
  exact this

/-- **Trivial bound** for `t ↦ exp(I·t·x)`:
`|exp(I·t·a) − exp(I·t·b)| ≤ 2`. -/
private lemma exp_I_diff_bound_two (t a b : ℝ) :
    ‖cexp ((t : ℂ) * a * I) - cexp ((t : ℂ) * b * I)‖ ≤ 2 := by
  have h1 : ‖cexp ((t : ℂ) * a * I)‖ = 1 := by
    rw [Complex.norm_exp]
    have : (((t : ℂ) * a * I).re) = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have h2 : ‖cexp ((t : ℂ) * b * I)‖ = 1 := by
    rw [Complex.norm_exp]
    have : (((t : ℂ) * b * I).re) = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  calc ‖cexp ((t : ℂ) * a * I) - cexp ((t : ℂ) * b * I)‖
      ≤ ‖cexp ((t : ℂ) * a * I)‖ + ‖cexp ((t : ℂ) * b * I)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

/-- AE-strong measurability of `ω ↦ exp(I·t·f(ω))`. -/
private lemma aestronglyMeasurable_cexp_real_mul
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    AEStronglyMeasurable (fun ω => cexp ((t : ℂ) * f ω * I)) μ := by
  refine Measurable.aestronglyMeasurable ?_
  refine Complex.measurable_exp.comp ?_
  exact ((measurable_const.mul (Complex.measurable_ofReal.comp hf)).mul measurable_const)

/-- Integrability of `ω ↦ exp(I·t·f(ω))` on a probability measure. -/
private lemma integrable_cexp_real_mul
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    Integrable (fun ω => cexp ((t : ℂ) * f ω * I)) μ := by
  refine ⟨aestronglyMeasurable_cexp_real_mul μ f hf t, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.mono (g := fun _ : Ω => (1 : ℝ)) ?_ ?_
  · exact (integrable_const _).hasFiniteIntegral
  · filter_upwards with ω
    rw [norm_one, Complex.norm_exp]
    have : (((t : ℂ) * f ω * I)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]

/-- Express `charFun (μ.map f) t` as `∫ exp(I·t·f) dμ`. -/
private lemma charFun_map_eq_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    charFun (μ.map f) t = ∫ ω, cexp ((t : ℂ) * f ω * I) ∂μ := by
  rw [charFun_apply, integral_map hf.aemeasurable]
  · refine integral_congr_ae ?_
    filter_upwards with ω
    have hinner : (@inner ℝ ℝ _ (f ω) t : ℝ) = t * f ω := by
      simp [RCLike.inner_apply, mul_comm]
    rw [show (((@inner ℝ ℝ _ (f ω) t) : ℝ) : ℂ) = ((t * f ω : ℝ) : ℂ) from by rw [hinner]]
    push_cast
    ring_nf
  · refine Measurable.aestronglyMeasurable ?_
    refine Complex.measurable_exp.comp ?_
    refine .mul ?_ measurable_const
    refine Complex.measurable_ofReal.comp ?_
    have hh : (fun y : ℝ => (@inner ℝ ℝ _ y t : ℝ)) = (fun y => y * t) := by
      ext y
      simp [RCLike.inner_apply]; ring
    rw [hh]
    exact measurable_id.mul measurable_const

/-- **Core charFun-difference bound**: if `f, g : Ω → ℝ` are measurable on
a probability space, then for any `δ > 0`,

  `|charFun (μ.map f) t − charFun (μ.map g) t| ≤ |t|·δ + 2·μ{ω | δ ≤ |f − g|}`. -/
private lemma charFun_map_sub_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (t : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ‖charFun (μ.map f) t - charFun (μ.map g) t‖
      ≤ |t| * δ + 2 * (μ {ω | δ ≤ |f ω - g ω|}).toReal := by
  rw [charFun_map_eq_integral μ f hf t, charFun_map_eq_integral μ g hg t]
  have hint_f := integrable_cexp_real_mul μ f hf t
  have hint_g := integrable_cexp_real_mul μ g hg t
  rw [← integral_sub hint_f hint_g]
  refine (norm_integral_le_integral_norm _).trans ?_
  set A : Set Ω := {ω | δ ≤ |f ω - g ω|} with hA_def
  have hA_meas : MeasurableSet A := measurableSet_le measurable_const (hf.sub hg).abs
  have hAcc_meas : MeasurableSet Aᶜ := hA_meas.compl
  -- Splittability: integrand integrable on the whole space
  have hint_norm : Integrable
      (fun ω => ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖) μ := by
    refine (integrable_norm_iff ?_).mpr (hint_f.sub hint_g)
    exact (aestronglyMeasurable_cexp_real_mul μ f hf t).sub
        (aestronglyMeasurable_cexp_real_mul μ g hg t)
  have h_on_Acompl : ∀ ω ∈ Aᶜ,
      ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖ ≤ |t| * δ := by
    intro ω hω
    simp only [hA_def, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    calc ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖
        ≤ |t| * |f ω - g ω| := exp_I_diff_bound t (f ω) (g ω)
      _ ≤ |t| * δ := mul_le_mul_of_nonneg_left hω.le (abs_nonneg _)
  have h_on_A : ∀ ω ∈ A,
      ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖ ≤ 2 :=
    fun ω _ => exp_I_diff_bound_two t (f ω) (g ω)
  -- Bound on A
  have hbound_A : ∫ ω in A,
        ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖ ∂μ
      ≤ 2 * (μ A).toReal := by
    have hle := setIntegral_mono_on (μ := μ)
        (f := fun ω => ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖)
        (g := fun _ => (2 : ℝ)) hint_norm.integrableOn
        (integrable_const _).integrableOn hA_meas h_on_A
    refine hle.trans ?_
    rw [setIntegral_const]
    rw [show ((μ.real A) : ℝ) = (μ A).toReal from rfl]
    ring_nf
    rfl
  -- Bound on Aᶜ
  have hbound_Acompl : ∫ ω in Aᶜ,
        ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖ ∂μ
      ≤ |t| * δ := by
    have hle := setIntegral_mono_on (μ := μ)
        (f := fun ω => ‖cexp ((t : ℂ) * f ω * I) - cexp ((t : ℂ) * g ω * I)‖)
        (g := fun _ => |t| * δ) hint_norm.integrableOn
        (integrable_const _).integrableOn hAcc_meas h_on_Acompl
    refine hle.trans ?_
    rw [setIntegral_const]
    have hμAcc : (μ Aᶜ).toReal ≤ 1 := by
      rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from rfl]
      refine ENNReal.toReal_mono (by norm_num) ?_
      calc μ Aᶜ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ ≤ 1 := measure_univ.le
    have ht_pos : 0 ≤ |t| * δ := mul_nonneg (abs_nonneg _) hδ.le
    have : (μ.real Aᶜ) * (|t| * δ) ≤ 1 * (|t| * δ) :=
      mul_le_mul_of_nonneg_right hμAcc ht_pos
    simpa using this
  -- Combine via integral_add_compl
  rw [← integral_add_compl hA_meas hint_norm]
  linarith [hbound_A, hbound_Acompl]

/-! ### Bridges to existing infrastructure -/

/-- **Axiom (iid CLT on `Measure.pi`)**: under iid sampling from a probability
measure `μ`, the standardized sum `(1/√n) Σᵢ ψ(Xᵢ)` of a centered L² influence
function converges in distribution to `N(0, E_μ[ψ²])`.

This is the classical iid CLT, but stated directly on the product space
`(Fin n → Ω, Measure.pi μ^⊗n)` — a different ambient space for each `n`.
Mathlib v4.28-rc1 does *not* yet expose a named CLT under `MemLp 2`; the
upcoming `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`
(present in main but absent from v4.28-rc1) will discharge this axiom in a
later Mathlib bump. Statlean's own `central_limit_theorem` requires `MemLp 3`
together with a fixed ambient space; lifting it through
`Measure.infinitePiNat` and then projecting via
`Measure.infinitePiNat_map_restrict` is mechanical but not yet wired.

We axiomatise the conclusion in line with the existing project axioms for
deep weak-convergence results (cf. `stieltjes_continuity_theorem_axiom`
in `Statlean.RandomMatrix.MarchenkoPastur` and `slepian_lemma` in
`Statlean.Gaussian.Gordon`).

Reference: van der Vaart (1998), *Asymptotic Statistics*, Theorem 2.18;
Shao, *Mathematical Statistics*, Theorem 1.4. -/
axiom iid_empirical_sum_clt_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ψ : Ω → ℝ) (_hψ : IsCenteredL2 ν ψ) :
    ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => ν)).map
          (fun X => (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t))

/-- **Slutsky combining theorem on `Measure.pi`** (proved): if `S_n` (defined
as the standardized sum `(1/√n) Σᵢ ψ(Xᵢ)`) converges in distribution to a
Gaussian limit and the remainder `R_n := √n(T_n − θ₀) − S_n` converges to
zero in probability (the `ε`-mass formulation packaged in
`IsAsymptoticallyLinear`), then `√n(T_n − θ₀)` converges in distribution to
the same Gaussian.

The proof works at the characteristic-function level on each
`Measure.pi μ^⊗n` directly (no need to embed into a single ambient space).
The key estimate is `|exp(it·a) − exp(it·b)| ≤ min(2, |t|·|a−b|)`, applied
inside the integral defining the characteristic function: for any `δ > 0`,

  `|charFun_full(t) − charFun_sum(t)| ≤ |t|·δ + 2·μ_pi{|R_n| > δ}`.

Sending `n → ∞` first (so the second term vanishes by `IsAsymptoticallyLinear`)
and then `δ → 0` gives `charFun_full → charFun_sum → charFun_Gaussian`.

Reference: Shao, *Mathematical Statistics*, Theorem 1.11 (Slutsky). -/
theorem asymptotic_linearity_slutsky
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ)
    (hψ_meas : Measurable ψ)
    (hAL : IsAsymptoticallyLinear ν T θ₀ ψ)
    (hSum : ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => ν)).map
          (fun X => (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t))) :
    ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => ν)).map
          (fun X => Real.sqrt n * (T n X - θ₀))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t)) := by
  intro t
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Notation
  set σsq : NNReal := ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩ with hσsq
  set Z : ℂ := charFun (gaussianReal 0 σsq) t with hZ
  -- For each n, define μ_n = Measure.pi (fun _ : Fin n => ν), sum_n, full_n
  let μ_n : (n : ℕ) → Measure (Fin n → Ω) := fun n => Measure.pi (fun _ : Fin n => ν)
  let sum_n : (n : ℕ) → (Fin n → Ω) → ℝ :=
    fun n X => (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i)
  let full_n : (n : ℕ) → (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T n X - θ₀)
  have hT_meas := hAL.measurable_T
  -- Each sum_n and full_n is measurable
  have hsum_meas : ∀ n, Measurable (sum_n n) := by
    intro n
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ ?_
    intro i _
    exact hψ_meas.comp (measurable_pi_apply i)
  have hfull_meas : ∀ n, Measurable (full_n n) := fun n =>
    measurable_const.mul ((hT_meas n).sub measurable_const)
  -- Each μ_n is a probability measure
  haveI : ∀ n, IsProbabilityMeasure (μ_n n) := fun n => by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν))
    infer_instance
  -- charFun convergence of sum_n at point t
  have hSum_t : Tendsto (fun n => charFun ((μ_n n).map (sum_n n)) t) atTop (𝓝 Z) := hSum t
  -- ε/3 from hSum: ∃ N₁, ∀ n ≥ N₁, ‖charFun_sum_n t − Z‖ < ε/3
  rw [Metric.tendsto_nhds] at hSum_t
  obtain ⟨N₁, hN₁⟩ := (eventually_atTop).mp (hSum_t (ε / 2) (by linarith))
  -- Choose δ = ε/(6·max(1,|t|))
  let M : ℝ := max 1 |t|
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ : ℝ := ε / (6 * M)
  have hδ_pos : 0 < δ := by
    have h6M : 0 < 6 * M := by positivity
    exact div_pos hε h6M
  -- Convert the ENNReal limit to ℝ via toReal
  have hRem_real : Tendsto
      (fun n => ((μ_n n) {X : Fin n → Ω | δ ≤ |full_n n X - sum_n n X|}).toReal)
      atTop (𝓝 0) := by
    have hRem := hAL.remainder_tendsto δ hδ_pos
    have hconv : Tendsto
        (fun n => ((μ_n n) {X : Fin n → Ω | δ ≤ |full_n n X - sum_n n X|}).toReal)
        atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hRem
    simpa using hconv
  rw [Metric.tendsto_nhds] at hRem_real
  obtain ⟨N₂, hN₂⟩ := (eventually_atTop).mp (hRem_real (ε / 6) (by linarith))
  -- Combine
  refine eventually_atTop.mpr ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : n ≥ N₁ := le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := le_of_max_le_right hn
  -- Pointwise bound on the charFun difference
  have hT1 : ‖charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t‖
      ≤ |t| * δ + 2 * ((μ_n n) {ω | δ ≤ |full_n n ω - sum_n n ω|}).toReal :=
    charFun_map_sub_le (μ_n n) (full_n n) (sum_n n)
      (hfull_meas n) (hsum_meas n) t δ hδ_pos
  have hT2_dist : dist (charFun ((μ_n n).map (sum_n n)) t) Z < ε / 2 := hN₁ n hn₁
  have hT2 : ‖charFun ((μ_n n).map (sum_n n)) t - Z‖ < ε / 2 := by
    rw [dist_eq_norm] at hT2_dist; exact hT2_dist
  have hT3 : ((μ_n n) {ω | δ ≤ |full_n n ω - sum_n n ω|}).toReal < ε / 6 := by
    have hd := hN₂ n hn₂
    rw [Real.dist_eq, sub_zero,
        abs_of_nonneg ENNReal.toReal_nonneg] at hd
    exact hd
  -- |t|·δ ≤ M·δ = ε/6
  have hbound1 : |t| * δ ≤ ε / 6 := by
    have h1 : |t| ≤ M := le_max_right _ _
    calc |t| * δ ≤ M * δ := mul_le_mul_of_nonneg_right h1 hδ_pos.le
      _ = M * (ε / (6 * M)) := rfl
      _ = ε / 6 := by field_simp
  have hbound2 : 2 * ((μ_n n) {ω | δ ≤ |full_n n ω - sum_n n ω|}).toReal < 2 * (ε / 6) :=
    mul_lt_mul_of_pos_left hT3 (by norm_num)
  -- Combine the two pieces
  have hT1' : ‖charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t‖
      < ε / 6 + 2 * (ε / 6) :=
    lt_of_le_of_lt hT1 (add_lt_add_of_le_of_lt hbound1 hbound2)
  -- Triangle inequality
  have hfinal : ‖charFun ((μ_n n).map (full_n n)) t - Z‖
      ≤ ‖charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t‖
        + ‖charFun ((μ_n n).map (sum_n n)) t - Z‖ := by
    have h := norm_add_le
        (charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t)
        (charFun ((μ_n n).map (sum_n n)) t - Z)
    have hsumeq : (charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t)
        + (charFun ((μ_n n).map (sum_n n)) t - Z)
        = charFun ((μ_n n).map (full_n n)) t - Z := by ring
    rw [hsumeq] at h
    exact h
  rw [dist_eq_norm]
  calc ‖charFun ((μ_n n).map (full_n n)) t - Z‖
      ≤ ‖charFun ((μ_n n).map (full_n n)) t - charFun ((μ_n n).map (sum_n n)) t‖
        + ‖charFun ((μ_n n).map (sum_n n)) t - Z‖ := hfinal
    _ < (ε / 6 + 2 * (ε / 6)) + ε / 2 := add_lt_add hT1' hT2
    _ = ε := by ring

/-- Backwards-compatible alias: `asymptotic_linearity_slutsky_axiom` is now a
proved theorem, delegating to `asymptotic_linearity_slutsky`. -/
theorem asymptotic_linearity_slutsky_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ)
    (hψ_meas : Measurable ψ)
    (hAL : IsAsymptoticallyLinear ν T θ₀ ψ)
    (hSum : ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => ν)).map
          (fun X => (1 / Real.sqrt n) * ∑ i : Fin n, ψ (X i))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t))) :
    ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => ν)).map
          (fun X => Real.sqrt n * (T n X - θ₀))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t)) :=
  asymptotic_linearity_slutsky ν T θ₀ ψ hψ_meas hAL hSum

section Bridge

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Asymptotically linear estimator ⇒ asymptotic normality with variance
`E[ψ²]` (CLT applied to the empirical influence sum + Slutsky for the
remainder).

Combines the iid CLT (axiomatised as `iid_empirical_sum_clt_axiom`) with the
Slutsky bridge (proved as `asymptotic_linearity_slutsky`). The
`Measurable ψ` hypothesis is propagated from the caller; if instead one only
has AE-strong measurability from `MemLp 2`, replace `ψ` by its measurable
representative before applying. -/
theorem influence_function_asymptotic_normality
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ)
    (hψ_meas : Measurable ψ)
    (h : IsAsymptoticallyLinear μ T θ₀ ψ) :
    ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => μ)).map
          (fun X => Real.sqrt n * (T n X - θ₀))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance μ ψ, asymptoticVariance_nonneg μ ψ⟩) t)) :=
  asymptotic_linearity_slutsky (Ω := Ω) μ T θ₀ ψ hψ_meas h
    (iid_empirical_sum_clt_axiom (Ω := Ω) μ ψ h.isCenteredL2)

end Bridge

end Statlean.Semiparametric

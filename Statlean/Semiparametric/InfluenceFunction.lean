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

## References

* Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins (2018),
  "Double/Debiased Machine Learning for Treatment and Structural Parameters",
  *The Econometrics Journal* 21, C1–C68.
* Bickel, Klaassen, Ritov, Wellner (1993), *Efficient and Adaptive Estimation
  for Semiparametric Models*.
* van der Vaart (1998), *Asymptotic Statistics*, Chapter 25.
-/

open MeasureTheory ProbabilityTheory Filter Topology
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
defining `ε`-mass condition (no extra Mathlib infrastructure required). -/
def IsAsymptoticallyLinear (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ) : Prop :=
  IsCenteredL2 μ ψ ∧
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

/-! ### Bridges to existing infrastructure -/

/-- **Axiom (iid CLT on `Measure.pi`)**: under iid sampling from a probability
measure `μ`, the standardized sum `(1/√n) Σᵢ ψ(Xᵢ)` of a centered L² influence
function converges in distribution to `N(0, E_μ[ψ²])`.

This is the classical iid CLT, but stated directly on the product space
`(Fin n → Ω, Measure.pi μ^⊗n)` — a different ambient space for each `n`.
Mathlib's CLT (`Statlean.LimitTheorems.central_limit_theorem`) requires a
*single* ambient space carrying iid copies and `MemLp 3`; transferring it
to the `Measure.pi` setting under `MemLp 2` only requires the Lindeberg
condition together with the iid product structure of `Measure.pi`, neither
of which is yet packaged in Mathlib.

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

/-- **Axiom (Slutsky combining axiom for `Measure.pi`)**: if `S_n` (defined as
the standardized sum `(1/√n) Σᵢ ψ(Xᵢ)`) converges in distribution to a Gaussian
limit and the remainder `R_n := √n(T_n - θ₀) - S_n` converges to zero in
probability (in the `ε`-mass formulation used by `IsAsymptoticallyLinear`),
then `√n(T_n - θ₀)` converges in distribution to the same Gaussian.

This is Slutsky's theorem applied on each `Measure.pi μ^⊗n` space. Mathlib's
Slutsky lemmas (`Statlean.LimitTheorems.slutsky_add` etc.) are stated on a
single ambient space and at the level of weak convergence of probability
measures; transferring them to the per-`n` `Measure.pi` setting at the
charfun level is routine but lengthy, and we package it as an axiom.

Reference: Shao, *Mathematical Statistics*, Theorem 1.11 (Slutsky). -/
axiom asymptotic_linearity_slutsky_axiom
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ)
    (_hAL : IsAsymptoticallyLinear ν T θ₀ ψ)
    (_hSum : ∀ t : ℝ, Tendsto
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
        ⟨asymptoticVariance ν ψ, asymptoticVariance_nonneg ν ψ⟩) t))

section Bridge

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Asymptotically linear estimator ⇒ asymptotic normality with variance
`E[ψ²]` (CLT applied to the empirical influence sum + Slutsky for the
remainder).

This bridges `IsAsymptoticallyLinear` to a CLT-style conclusion stated as a
weak / characteristic-function convergence. The proof combines:

* the iid CLT for `(1/√n) Σ ψ(Xᵢ) →d N(0, σ²)` (axiomatised as
  `iid_empirical_sum_clt_axiom`), and
* Slutsky's theorem absorbing the `o_p(1)` asymptotic-linearity remainder
  (axiomatised as `asymptotic_linearity_slutsky_axiom`).

Both axioms package classical results whose translation to the per-`n`
`Measure.pi μ^⊗n` setting requires substantial Mathlib infrastructure not
yet available. -/
theorem influence_function_asymptotic_normality
    (T : (n : ℕ) → (Fin n → Ω) → ℝ) (θ₀ : ℝ) (ψ : Ω → ℝ)
    (h : IsAsymptoticallyLinear μ T θ₀ ψ) :
    -- the standardized error converges in distribution to N(0, E[ψ²])
    ∀ t : ℝ, Tendsto
      (fun n => charFun
        ((Measure.pi (fun (_ : Fin n) => μ)).map
          (fun X => Real.sqrt n * (T n X - θ₀))) t)
      atTop (𝓝 (charFun (gaussianReal 0
        ⟨asymptoticVariance μ ψ, asymptoticVariance_nonneg μ ψ⟩) t)) :=
  asymptotic_linearity_slutsky_axiom (Ω := Ω) μ T θ₀ ψ h
    (iid_empirical_sum_clt_axiom (Ω := Ω) μ ψ h.isCenteredL2)

end Bridge

end Statlean.Semiparametric

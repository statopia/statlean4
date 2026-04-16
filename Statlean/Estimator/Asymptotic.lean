import Statlean.Estimator.Basic
import Statlean.LimitTheorems.Levy
import Statlean.LimitTheorems.DeltaMethod
import Statlean.Information.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! # Asymptotic Estimator Theory

Definitions and basic properties for asymptotic normality, asymptotic MSE,
asymptotic bias, and asymptotic relative efficiency (ARE).

## Main definitions

* `IsAsymptoticallyNormal P T g v` — charfun convergence to `N(0, v(θ))`
* `HasAsymptoticMSE P T g c` — `(n+1) · E[(T_n - g(θ))²] → c(θ)`
* `HasAsymptoticBias P T g b` — `√(n+1) · (E[T_n] - g(θ)) → b(θ)`
* `ARE v₁ v₂` — asymptotic relative efficiency `v₂ / v₁`

## Main results

* `clt_isAsymptoticallyNormal` — bridge from CLT/Lévy output to `IsAsymptoticallyNormal`
* `asymptotic_mse_decomp` — scaled MSE = scaled Bias² + scaled Var (pointwise in n)
* `asymptotic_mse_eq_var_of_unbiased` — unbiased ⟹ scaled MSE = scaled Var
* `are_inv` — `ARE v₁ v₂ * ARE v₂ v₁ = 1`
* `are_gt_one_iff` — `1 < ARE v₁ v₂ ↔ v₁ < v₂`

## References

* Shao, Jun. *Mathematical Statistics*, Chapter 2.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Statlean.Estimator

variable {Θ Ω : Type*} [MeasurableSpace Ω]

/-! ### Definitions -/

/-- An estimator sequence `T` is **asymptotically normal** at rate `√n` with
asymptotic variance function `v : Θ → NNReal` if the characteristic function of
`√(n+1) · (T_n(ω) - g(θ))` converges pointwise to that of `N(0, v(θ))`.

This is the charfun-level formulation, matching the output of CLT and Lévy
continuity theorem. -/
structure IsAsymptoticallyNormal
    (P : ParametricFamily Θ Ω)
    (T : ℕ → Ω → ℝ) (g : Θ → ℝ) (v : Θ → NNReal) : Prop where
  measurable : ∀ n, Measurable (T n)
  charfun_tendsto : ∀ θ t,
    Tendsto (fun (n : ℕ) => charFun ((P.measure θ).map
      (fun ω => Real.sqrt (↑(n + 1)) * (T n ω - g θ))) t)
      atTop (𝓝 (charFun (gaussianReal 0 (v θ)) t))

/-- The sequence `T` has **asymptotic MSE** `c(θ)` if
`(n+1) · E_θ[(T_n - g(θ))²] → c(θ)` for all θ. -/
structure HasAsymptoticMSE
    (P : ParametricFamily Θ Ω)
    (T : ℕ → Ω → ℝ) (g : Θ → ℝ) (c : Θ → ℝ) : Prop where
  nonneg : ∀ θ, 0 ≤ c θ
  tendsto : ∀ θ, Tendsto (fun (n : ℕ) =>
    (↑(n + 1) : ℝ) * ∫ ω, (T n ω - g θ) ^ 2 ∂(P.measure θ))
    atTop (𝓝 (c θ))

/-- The sequence `T` has **asymptotic bias** `b(θ)` if
`√(n+1) · (E_θ[T_n] - g(θ)) → b(θ)` for all θ. -/
def HasAsymptoticBias
    (P : ParametricFamily Θ Ω)
    (T : ℕ → Ω → ℝ) (g : Θ → ℝ) (b : Θ → ℝ) : Prop :=
  ∀ θ, Tendsto (fun (n : ℕ) =>
    Real.sqrt (↑(n + 1)) * (∫ ω, T n ω ∂(P.measure θ) - g θ))
    atTop (𝓝 (b θ))

/-- **Asymptotic relative efficiency** of two estimators with asymptotic
variances `v₁` and `v₂`: `ARE = v₂ / v₁`. When `ARE > 1`, the first
estimator is more efficient (lower asymptotic variance). -/
def ARE (v₁ v₂ : NNReal) : ℝ := (v₂ : ℝ) / (v₁ : ℝ)

/-! ### Theorems -/

variable {P : ParametricFamily Θ Ω} {T : ℕ → Ω → ℝ} {g : Θ → ℝ}

/-- Bridge from CLT/Lévy output to `IsAsymptoticallyNormal`.

Given weak convergence (as `ProbabilityMeasure ℝ`) of the standardized laws
to a limit whose charfun matches `N(0, v(θ))`, extract pointwise charfun
convergence via `levy_forward`. The user provides the `ProbabilityMeasure`
sequence along with a proof that the underlying measures match the maps. -/
theorem clt_isAsymptoticallyNormal {v : Θ → NNReal}
    (hm : ∀ n, Measurable (T n))
    (h : ∀ θ, ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (↑μ₀ : Measure ℝ) t = charFun (gaussianReal 0 (v θ)) t) ∧
      ∃ (μs : ℕ → ProbabilityMeasure ℝ),
        (∀ n, (↑(μs n) : Measure ℝ) = (P.measure θ).map
          (fun ω => Real.sqrt (↑(n + 1)) * (T n ω - g θ))) ∧
        Tendsto μs atTop (𝓝 μ₀)) :
    IsAsymptoticallyNormal P T g v := by
  refine ⟨hm, fun θ t => ?_⟩
  obtain ⟨μ₀, hcf, μs, heq, htend⟩ := h θ
  have hlev := Statlean.LimitTheorems.levy_forward htend t
  rw [hcf t] at hlev
  have : (fun (n : ℕ) => charFun ((P.measure θ).map
      (fun ω => Real.sqrt (↑(n + 1)) * (T n ω - g θ))) t) =
      (fun i => charFun (↑(μs i)) t) := by
    ext n; rw [heq n]
  rwa [this]

/-- **Scaled MSE decomposition**: at each `n`,
`(n+1) · MSE = (n+1) · Bias² + (n+1) · Var`.

This is `mse_eq_bias_sq_add_variance` scaled by `(n+1)`. -/
theorem asymptotic_mse_decomp
    (hT : ∀ n θ, MemLp (T n) 2 (P.measure θ))
    (θ : Θ) (n : ℕ) :
    (↑(n + 1) : ℝ) * ∫ ω, (T n ω - g θ) ^ 2 ∂(P.measure θ) =
      (↑(n + 1) : ℝ) * (∫ ω, T n ω ∂(P.measure θ) - g θ) ^ 2 +
      (↑(n + 1) : ℝ) * ∫ ω, (T n ω - ∫ ω', T n ω' ∂(P.measure θ)) ^ 2 ∂(P.measure θ) := by
  haveI := P.isProbability θ
  rw [mse_eq_bias_sq_add_variance _ _ (hT n θ), mul_add]

/-- Unbiased estimators have scaled MSE = scaled variance. -/
theorem asymptotic_mse_eq_var_of_unbiased
    (hT : ∀ n θ, MemLp (T n) 2 (P.measure θ))
    (h_unbiased : ∀ n, IsUnbiased P (T n) g)
    (θ : Θ) (n : ℕ) :
    (↑(n + 1) : ℝ) * ∫ ω, (T n ω - g θ) ^ 2 ∂(P.measure θ) =
      (↑(n + 1) : ℝ) * ∫ ω, (T n ω - ∫ ω', T n ω' ∂(P.measure θ)) ^ 2
        ∂(P.measure θ) := by
  haveI := P.isProbability θ
  rw [mse_eq_variance_of_unbiased _ _ (hT n θ) (h_unbiased n θ)]

/-- `ARE v₁ v₂ * ARE v₂ v₁ = 1` when both variances are positive. -/
theorem are_inv {v₁ v₂ : NNReal} (h₁ : (v₁ : ℝ) ≠ 0) (h₂ : (v₂ : ℝ) ≠ 0) :
    ARE v₁ v₂ * ARE v₂ v₁ = 1 := by
  simp only [ARE]
  field_simp

/-- `ARE > 1` iff the second estimator has strictly larger asymptotic variance. -/
theorem are_gt_one_iff {v₁ v₂ : NNReal} (h₁ : 0 < (v₁ : ℝ)) :
    1 < ARE v₁ v₂ ↔ (v₁ : ℝ) < v₂ := by
  simp only [ARE]
  exact one_lt_div h₁

section MLEAsymptotics
/-! ## MLE Large Sample Theory

Definitions for MLE consistency, asymptotic normality, and asymptotic efficiency.
These are statement-level definitions — the proofs require regularity conditions
that vary by setting. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An MLE sequence `θ̂ₙ` is **consistent** for `θ₀` if `θ̂ₙ →ᵖ θ₀`
under `P_{θ₀}` (convergence in probability).

Uses the measure-theoretic formulation: `P_{θ₀}(d(θ̂ₙ, θ₀) > ε) → 0`. -/
def IsMLEConsistent [PseudoMetricSpace Θ]
    (P : ParametricFamily Θ Ω)
    (θ_hat : ℕ → Ω → Θ) (θ₀ : Θ) : Prop :=
  ∀ ε > 0, Filter.Tendsto
    (fun n => (P.measure θ₀) {ω | ε < dist (θ_hat n ω) θ₀})
    Filter.atTop (𝓝 0)

/-- An MLE sequence is **asymptotically normal** with rate `√n` and
asymptotic variance `1/I(θ)` (Fisher information):
`√n(θ̂ₙ - θ) →ᵈ N(0, 1/I(θ))` under `P_θ`. -/
def IsMLEAsymptoticallyNormal
    (P : ParametricFamily ℝ Ω) (logDensity : ℝ → Ω → ℝ)
    (θ_hat : ℕ → Ω → ℝ) : Prop :=
  ∃ v : ℝ → NNReal,
    (∀ θ, fisherInformation P logDensity θ > 0 →
      (v θ : ℝ) = 1 / fisherInformation P logDensity θ) ∧
    IsAsymptoticallyNormal P θ_hat id v

/-- An estimator sequence `Tₙ` is **asymptotically efficient** for `g(θ)` if
its asymptotic variance attains the Cramér-Rao lower bound:
`AsymVar(Tₙ) = (g'(θ))² / I(θ)`. -/
def IsAsymptoticallyEfficient
    (P : ParametricFamily ℝ Ω) (logDensity : ℝ → Ω → ℝ)
    (T : ℕ → Ω → ℝ) (g : ℝ → ℝ) (v : ℝ → NNReal) : Prop :=
  IsAsymptoticallyNormal P T g v ∧
  ∀ θ, fisherInformation P logDensity θ > 0 →
    (v θ : ℝ) = (deriv g θ) ^ 2 / fisherInformation P logDensity θ

/-- **Superefficiency**: an estimator is superefficient at `θ₀` if its
asymptotic variance is strictly less than the CR bound there. By Le Cam's
theorem, the set of superefficiency points has Lebesgue measure zero. -/
def IsSuperefficient
    (P : ParametricFamily ℝ Ω) (logDensity : ℝ → Ω → ℝ)
    (T : ℕ → Ω → ℝ) (g : ℝ → ℝ) (v : ℝ → NNReal) (θ₀ : ℝ) : Prop :=
  IsAsymptoticallyNormal P T g v ∧
  fisherInformation P logDensity θ₀ > 0 ∧
  (v θ₀ : ℝ) < (deriv g θ₀) ^ 2 / fisherInformation P logDensity θ₀

/-- If the MLE is asymptotically normal with variance 1/I(θ), it is
asymptotically efficient for estimating θ itself (g = id). -/
theorem mle_an_implies_efficient
    (P : ParametricFamily ℝ Ω) (logDensity : ℝ → Ω → ℝ)
    (θ_hat : ℕ → Ω → ℝ)
    (h : IsMLEAsymptoticallyNormal P logDensity θ_hat) :
    ∃ v, IsAsymptoticallyEfficient P logDensity θ_hat id v := by
  obtain ⟨v, hv, han⟩ := h
  exact ⟨v, han, fun θ hI => by simp [deriv_id', one_pow, hv θ hI]⟩

end MLEAsymptotics

section Amse

/-! ## Theorem 2.6 (Shao) — Delta method applied to amse (scalar case)

Reference: Shao, *Mathematical Statistics*, Theorem 2.6 (p. 139).

**Statement (Shao)**: Let `g` be a function on `ℝᵏ` differentiable at `θ ∈ ℝᵏ`,
and let `Uₙ` be a `k`-vector of statistics with `aₙ(Uₙ - θ) →ᵈ Y` where
`Y` is a random `k`-vector with `0 < E‖Y‖² < ∞`, and `aₙ → ∞`.
Let `Tₙ = g(Uₙ)`. Then
  `amseTₙ(P) = E{[∇g(θ)]ᵀ Y}² / aₙ²`,
  `asymptotic variance = [∇g(θ)]ᵀ Var(Y) ∇g(θ) / aₙ²`.

**Scope of this formalization**: scalar case `k = 1`. The multivariate case
requires a multivariate delta method, which is not yet in `StatLean`; once
available, the argument is the same with `d · Y` replaced by `⟨∇g(θ), Y⟩`.

Structure of the scalar proof:
1. `amse_delta_method_convergence` — `aₙ(g(Uₙ) - g(θ)) →ᵈ d · Y` via `delta_method`.
2. `amse_delta_method_second_moment` — `E[(d·Y)²] = d² · E[Y²]` (algebra).
3. `amse_delta_method_variance` — `Var(d·Y) = d² · Var(Y)` via `variance_const_mul`.
-/

open Statlean.LimitTheorems

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Theorem 2.6, convergence part (scalar case)**: under delta-method
hypotheses, `aₙ(g(Uₙ) - g(θ)) →ᵈ d · Y`. This is a direct application of
`delta_method` from `Statlean.LimitTheorems.DeltaMethod`. -/
theorem amse_delta_method_convergence
    {U : ℕ → Ω → ℝ} {Y : Ω → ℝ} {θ d : ℝ} {a : ℕ → ℝ}
    (ha_pos : ∀ᶠ n in Filter.atTop, 0 < a n)
    (ha_top : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hconv : TendstoInDistribution (fun n ω => a n * (U n ω - θ)) Filter.atTop Y μ)
    {g : ℝ → ℝ} (hg : HasDerivAt g d θ) (hg_meas : Measurable g)
    (hU_meas : ∀ n, AEMeasurable (U n) μ) :
    TendstoInDistribution (fun n ω => a n * (g (U n ω) - g θ)) Filter.atTop
      (fun ω => d * Y ω) μ :=
  delta_method ha_pos ha_top hconv hg hg_meas hU_meas

omit [IsProbabilityMeasure μ] in
/-- **Theorem 2.6, second moment identity (scalar case)**: if the limiting
random variable `Y` satisfies `E[Y²] = EY2`, then the limit `d · Y` has
second moment `d² · EY2`. This is Shao's amse formula `E{[∇g(θ)]ᵀ Y}²`
specialised to `k = 1`. -/
theorem amse_delta_method_second_moment (d : ℝ) (Y : Ω → ℝ) :
    ∫ ω, (d * Y ω) ^ 2 ∂μ = d ^ 2 * ∫ ω, (Y ω) ^ 2 ∂μ := by
  simp only [mul_pow]
  exact integral_const_mul (d ^ 2) _

omit [IsProbabilityMeasure μ] in
/-- **Theorem 2.6, asymptotic variance identity (scalar case)**: the variance
of the scalar limit `d · Y` is `d² · Var(Y)`. This gives the `asymptotic
variance = [∇g(θ)]ᵀ Var(Y) ∇g(θ) / aₙ²` formula of Shao's Theorem 2.6 in
the `k = 1` case. -/
theorem amse_delta_method_variance (d : ℝ) (Y : Ω → ℝ) :
    ProbabilityTheory.variance (fun ω => d * Y ω) μ =
      d ^ 2 * ProbabilityTheory.variance Y μ :=
  ProbabilityTheory.variance_const_mul d Y μ

/-- **Theorem 2.6 (Shao) — scalar case, packaged form**.
Given:
* a scaling sequence `aₙ → ∞` with `aₙ > 0` eventually,
* a sequence of scalar statistics `Uₙ` with `aₙ(Uₙ - θ) →ᵈ Y`,
* a function `g : ℝ → ℝ` differentiable at `θ` with derivative `d`
  and measurable,

the plug-in estimator `Tₙ := g ∘ Uₙ` satisfies:
* (distribution) `aₙ(Tₙ - g θ) →ᵈ d · Y`;
* (amse formula) the second moment of the limit equals `d² · E[Y²]`;
* (asymptotic variance) the variance of the limit equals `d² · Var(Y)`.

Divided by `aₙ²`, these give exactly the `amseTₙ(P) = d² · E[Y²]/aₙ²` and
`asymptotic variance = d² · Var(Y)/aₙ²` formulas of Shao, Theorem 2.6. -/
theorem amse_delta_method_scalar
    {U : ℕ → Ω → ℝ} {Y : Ω → ℝ} {θ d : ℝ} {a : ℕ → ℝ}
    (ha_pos : ∀ᶠ n in Filter.atTop, 0 < a n)
    (ha_top : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hconv : TendstoInDistribution (fun n ω => a n * (U n ω - θ)) Filter.atTop Y μ)
    {g : ℝ → ℝ} (hg : HasDerivAt g d θ) (hg_meas : Measurable g)
    (hU_meas : ∀ n, AEMeasurable (U n) μ) :
    TendstoInDistribution (fun n ω => a n * (g (U n ω) - g θ)) Filter.atTop
        (fun ω => d * Y ω) μ ∧
      (∫ ω, (d * Y ω) ^ 2 ∂μ = d ^ 2 * ∫ ω, (Y ω) ^ 2 ∂μ) ∧
      ProbabilityTheory.variance (fun ω => d * Y ω) μ =
        d ^ 2 * ProbabilityTheory.variance Y μ :=
  ⟨amse_delta_method_convergence ha_pos ha_top hconv hg hg_meas hU_meas,
    amse_delta_method_second_moment d Y,
    amse_delta_method_variance d Y⟩

end Amse

end Statlean.Estimator

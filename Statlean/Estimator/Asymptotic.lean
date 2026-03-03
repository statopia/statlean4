import Statlean.Estimator.Basic
import Statlean.LimitTheorems.Levy
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

end Statlean.Estimator

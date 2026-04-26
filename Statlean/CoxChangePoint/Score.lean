import Mathlib
import Statlean.CoxChangePoint.Foundation

/-!
# Cox change-point regression — score function components

This file defines the per-coordinate score-function building blocks for the
functional linear Cox change-point model introduced in
`Statlean/CoxChangePoint/Foundation.lean`.

Recall the linear predictor of one subject `obs` under parameter `θ`:

  `g_θ(obs) = γ' obs.Z₁ + I(obs.Z₂ ≤ η)(α' obs.ξ) + I(obs.Z₂ > η)(β' obs.ξ)`,

and the Cox partial log-likelihood

  `l_n(θ) = Σ_{i: δᵢ=1} { g_θ(obsᵢ) − log[Σ_{j ∈ R(Tᵢ)} exp(g_θ(obsⱼ))] }`.

Differentiating `l_n` formally with respect to `(γ, α, β)` (the change-point
`η` enters non-smoothly through indicators and is excluded here) yields the
classical Cox partial score

  `U_γ(θ) = Σ_{i: δᵢ=1} { obs_i.Z₁ − Z̄₁(θ; T_i) }`,

where the risk-set average is

  `Z̄₁(θ; t) = (Σ_{j ∈ R(t)} e^{g_θ(obs_j)} obs_j.Z₁) / (Σ_{j ∈ R(t)} e^{g_θ(obs_j)})`.

The components for `α` and `β` are analogous but use the FPC-score covariate
`ξ` together with the change-point indicator `I(Z₂ ≤ η)` resp. `I(Z₂ > η)`.

This module provides these formulas as `noncomputable def`s.  The formal proof
that the resulting expressions are the actual gradients of
`logPartialLikelihood` (i.e. that `partialScoreGamma θ = ∇_γ l_n(θ)` etc.) is
left as future work; it would require differentiation through `Real.log`,
`Real.exp`, sums and indicator functions, none of which are exercised here.
-/

open Finset

namespace Statlean.CoxChangePoint

variable {p d : ℕ}

/-! ### Per-subject score contributions

These are the partial derivatives of the linear predictor `g_θ(obs)` with
respect to the parameter components, evaluated at one subject `obs`. -/

/-- The γ-gradient of the linear predictor at one subject:
`∂ g_θ(obs) / ∂ γ_j = (obs.Z₁) j`. Independent of `θ`. -/
noncomputable def gammaScoreContribution (obs : CoxObs p d) : Fin p → ℝ :=
  obs.Z₁

/-- The α-gradient of the linear predictor at one subject:
`∂ g_θ(obs) / ∂ α_k = I(obs.Z₂ ≤ θ.η) · (obs.ξ) k`. -/
noncomputable def alphaScoreContribution (θ : CoxParam p d) (obs : CoxObs p d) :
    Fin d → ℝ :=
  fun k => if obs.Z₂ ≤ θ.η then obs.ξ k else 0

/-- The β-gradient of the linear predictor at one subject:
`∂ g_θ(obs) / ∂ β_k = I(obs.Z₂ > θ.η) · (obs.ξ) k`. -/
noncomputable def betaScoreContribution (θ : CoxParam p d) (obs : CoxObs p d) :
    Fin d → ℝ :=
  fun k => if obs.Z₂ > θ.η then obs.ξ k else 0

/-! ### Risk-set weighted sums

Given a sample `data` and a time `t`, these are the risk-set sums
`Σ_{j ∈ R(t)} e^{g_θ(obs_j)} · contribution_j`, taken coordinate-wise. -/

/-- Coordinate-wise risk-set sum of `e^{g_θ} · Z₁`:
`(riskSumWeightedZ₁ θ data t) j = Σ_{k ∈ R(t)} e^{g_θ(obs_k)} · (obs_k.Z₁) j`. -/
noncomputable def riskSumWeightedZ₁ (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin p → ℝ :=
  fun j => ∑ k ∈ atRisk n data t, θ.expG (data k) * (data k).Z₁ j

/-- Coordinate-wise risk-set sum of `e^{g_θ} · I(Z₂ ≤ η) · ξ`:
the α-numerator of the risk-set mean. -/
noncomputable def riskSumWeightedAlpha (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin d → ℝ :=
  fun k => ∑ j ∈ atRisk n data t,
      θ.expG (data j) * alphaScoreContribution θ (data j) k

/-- Coordinate-wise risk-set sum of `e^{g_θ} · I(Z₂ > η) · ξ`:
the β-numerator of the risk-set mean. -/
noncomputable def riskSumWeightedBeta (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin d → ℝ :=
  fun k => ∑ j ∈ atRisk n data t,
      θ.expG (data j) * betaScoreContribution θ (data j) k

/-! ### Risk-set means

Coordinate-wise ratios `riskSumWeighted / riskSum`, with a guard `0` for the
degenerate case `riskSum = 0` (which never occurs in practice since
`expG > 0`, hence `riskSum > 0` whenever the risk set is non-empty). -/

/-- Risk-set mean of `Z₁`:
`(meanZ₁InRiskSet n data θ t) j = (Σ_{k ∈ R(t)} e^{g_θ(obs_k)} · (obs_k.Z₁) j) /
                                    (Σ_{k ∈ R(t)} e^{g_θ(obs_k)})`,
defined to be `0` when `riskSum n data θ t = 0`. -/
noncomputable def meanZ₁InRiskSet (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin p → ℝ :=
  fun j =>
    if riskSum n data θ t = 0 then 0
    else riskSumWeightedZ₁ n data θ t j / riskSum n data θ t

/-- Risk-set mean of `I(Z₂ ≤ η) · ξ`. Defined to be `0` when
`riskSum n data θ t = 0`. -/
noncomputable def meanAlphaInRiskSet (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin d → ℝ :=
  fun k =>
    if riskSum n data θ t = 0 then 0
    else riskSumWeightedAlpha n data θ t k / riskSum n data θ t

/-- Risk-set mean of `I(Z₂ > η) · ξ`. Defined to be `0` when
`riskSum n data θ t = 0`. -/
noncomputable def meanBetaInRiskSet (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : Fin d → ℝ :=
  fun k =>
    if riskSum n data θ t = 0 then 0
    else riskSumWeightedBeta n data θ t k / riskSum n data θ t

/-! ### Partial scores

The classical Cox partial score, per coordinate:

  `U_γ(θ)_j = Σ_{i : δᵢ=1} ((obs_i.Z₁) j − (Z̄₁(θ; T_i)) j)`,
  `U_α(θ)_k = Σ_{i : δᵢ=1} ((alphaScoreContribution θ obs_i) k
                            − (meanAlphaInRiskSet n data θ T_i) k)`,
  `U_β(θ)_k = Σ_{i : δᵢ=1} ((betaScoreContribution θ obs_i) k
                            − (meanBetaInRiskSet n data θ T_i) k)`.
-/

/-- The γ-component of the Cox partial score:
`(partialScoreGamma n data θ) j = Σ_{i : δᵢ} ((data i).Z₁ j − meanZ₁InRiskSet … j)`. -/
noncomputable def partialScoreGamma (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) : Fin p → ℝ :=
  fun j =>
    ∑ i : Fin n,
      if (data i).δ then
        (data i).Z₁ j - meanZ₁InRiskSet n data θ (data i).T j
      else 0

/-- The α-component of the Cox partial score:
`(partialScoreAlpha n data θ) k = Σ_{i : δᵢ}
   (alphaScoreContribution θ (data i) k − meanAlphaInRiskSet … k)`. -/
noncomputable def partialScoreAlpha (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) : Fin d → ℝ :=
  fun k =>
    ∑ i : Fin n,
      if (data i).δ then
        alphaScoreContribution θ (data i) k
          - meanAlphaInRiskSet n data θ (data i).T k
      else 0

/-- The β-component of the Cox partial score:
`(partialScoreBeta n data θ) k = Σ_{i : δᵢ}
   (betaScoreContribution θ (data i) k − meanBetaInRiskSet … k)`. -/
noncomputable def partialScoreBeta (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) : Fin d → ℝ :=
  fun k =>
    ∑ i : Fin n,
      if (data i).δ then
        betaScoreContribution θ (data i) k
          - meanBetaInRiskSet n data θ (data i).T k
      else 0

end Statlean.CoxChangePoint

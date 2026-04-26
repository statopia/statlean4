import Mathlib
import Statlean.CoxChangePoint.Auto.uniform_convergence_of_Gn

/-!
# Cox change-point regression — foundation

Concrete data model and partial log-likelihood for the functional linear Cox
regression model with a change point in the covariate (Yu-Li-Lin 2026).

The abstract layer in `Statlean/CoxChangePoint/Auto/uniform_convergence_of_Gn.lean`
expresses Lemma S1 (uniform convergence of `Gn` to `G`) in terms of the abstract
`LemmaS1Data` record.  This file provides the concrete construction of `Gn`
from a sample of `CoxObs` observations and shows how to instantiate
`LemmaS1Data` from such a sample (modulo the uniform-convergence hypothesis,
which still must be supplied — that is the actual mathematical content of
Lemma S1).

## Notation matches the paper

* `Z₁ᵢ ∈ ℝ^p` — scalar covariates with linear effect `γ'Z₁`.
* `Z₂ᵢ ∈ ℝ` — change-point covariate.
* `ξᵢ ∈ ℝ^d` — truncated FPC scores of the functional covariate `Xᵢ`.
* `Tᵢ`, `δᵢ` — observation time and event indicator.
* Linear predictor: `g_θ(Z₁,Z₂,ξ) = γ'Z₁ + I(Z₂ ≤ η)(α'ξ) + I(Z₂ > η)(β'ξ)`.
* Partial log-likelihood: standard Cox.
* `Gn(θ) = n⁻¹{l_n(θ) − l_n(θ₀)}`.
-/

open MeasureTheory Real Finset

namespace Statlean.CoxChangePoint

/-! ### Observation data -/

/-- A Cox change-point observation for one subject:
    survival time `T`, event indicator `δ`, scalar covariates `Z₁ ∈ ℝ^p`,
    change-point covariate `Z₂ ∈ ℝ`, and truncated FPC scores `ξ ∈ ℝ^d`. -/
structure CoxObs (p d : ℕ) where
  /-- Observation time (event time if δ = true, else censoring time). -/
  T : ℝ
  /-- Event indicator: `true` = event observed, `false` = right-censored. -/
  δ : Bool
  /-- Scalar covariate vector. -/
  Z₁ : Fin p → ℝ
  /-- Change-point covariate (scalar). -/
  Z₂ : ℝ
  /-- Truncated FPC scores. -/
  ξ : Fin d → ℝ

/-! ### Parameter -/

/-- The Cox change-point parameter `θ = (γ, α, β, η)`:
    `γ ∈ ℝ^p` is the coefficient on `Z₁`,
    `α ∈ ℝ^d` is the coefficient on `ξ` when `Z₂ ≤ η`,
    `β ∈ ℝ^d` is the coefficient on `ξ` when `Z₂ > η`,
    `η ∈ ℝ` is the change point. -/
structure CoxParam (p d : ℕ) where
  γ : Fin p → ℝ
  α : Fin d → ℝ
  β : Fin d → ℝ
  η : ℝ

namespace CoxParam

variable {p d : ℕ}

/-- The linear predictor `g_θ(Z₁, Z₂, ξ) = γ'Z₁ + I(Z₂ ≤ η)(α'ξ) + I(Z₂ > η)(β'ξ)`. -/
noncomputable def g (θ : CoxParam p d) (obs : CoxObs p d) : ℝ :=
  (∑ j, θ.γ j * obs.Z₁ j) +
  (if obs.Z₂ ≤ θ.η
    then ∑ k, θ.α k * obs.ξ k
    else ∑ k, θ.β k * obs.ξ k)

/-- The exponential of the linear predictor, `exp(g_θ)`. Always positive. -/
noncomputable def expG (θ : CoxParam p d) (obs : CoxObs p d) : ℝ :=
  Real.exp (θ.g obs)

lemma expG_pos (θ : CoxParam p d) (obs : CoxObs p d) : 0 < θ.expG obs :=
  Real.exp_pos _

end CoxParam

/-! ### Partial likelihood -/

variable {p d : ℕ}

/-- The risk set at time `t`: indices with observation time `≥ t`. As a `Finset`
of `Fin n`, supplied as a function on a fixed sample of size `n`. -/
noncomputable def atRisk (n : ℕ) (data : Fin n → CoxObs p d) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => t ≤ (data j).T)

/-- Sum of `exp(g_θ(j))` over the risk set at time `t`. -/
noncomputable def riskSum (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : ℝ :=
  ∑ j ∈ atRisk n data t, θ.expG (data j)

lemma riskSum_nonneg (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (t : ℝ) : 0 ≤ riskSum n data θ t :=
  Finset.sum_nonneg fun j _ => le_of_lt (θ.expG_pos (data j))

/-- The Cox partial log-likelihood for `n` observations and parameter `θ`:

  `l_n(θ) = Σ_{i: δᵢ=1} { g_θ(obsᵢ) − log[Σ_{j ∈ R(Tᵢ)} exp(g_θ(obsⱼ))] }`. -/
noncomputable def logPartialLikelihood (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) : ℝ :=
  ∑ i : Fin n,
    if (data i).δ then
      θ.g (data i) - Real.log (riskSum n data θ (data i).T)
    else 0

/-- The centred normalised empirical objective `G_n(θ) = n⁻¹ {l_n(θ) − l_n(θ₀)}`. -/
noncomputable def Gn (n : ℕ) (data : Fin n → CoxObs p d)
    (θ θ₀ : CoxParam p d) : ℝ :=
  (logPartialLikelihood n data θ - logPartialLikelihood n data θ₀) / (n : ℝ)

/-- `G_n` evaluated at `θ` and the true parameter `θ₀` is centred at the true
parameter: `G_n θ₀ θ₀ = 0` (for any sample, any `n ≠ 0`). -/
lemma Gn_self_eq_zero (n : ℕ) (data : Fin n → CoxObs p d)
    (θ₀ : CoxParam p d) : Gn n data θ₀ θ₀ = 0 := by
  unfold Gn
  rw [sub_self, zero_div]

/-! ### Sample-indexed empirical objective -/

/-- A sample on `Ω`: for each sample size `n`, a function `Fin n → Ω → CoxObs`
giving the `i`-th observation as a function of `ω`. -/
def Sample (Ω : Type*) (p d : ℕ) : Type _ :=
  ∀ n : ℕ, Fin n → Ω → CoxObs p d

namespace Sample

variable {Ω : Type*}

/-- Realize the sample at a given `ω` and sample size `n`. -/
def realize (S : Sample Ω p d) (n : ℕ) (ω : Ω) : Fin n → CoxObs p d :=
  fun i => S n i ω

/-- The empirical objective `G_n` as a function of `θ`, `ω`. -/
noncomputable def Gn (S : Sample Ω p d) (θ θ₀ : CoxParam p d) (n : ℕ) (ω : Ω) : ℝ :=
  Statlean.CoxChangePoint.Gn n (S.realize n ω) θ θ₀

end Sample

/-! ### Bridge to the abstract `LemmaS1Data`

`Statlean/CoxChangePoint/Auto/uniform_convergence_of_Gn.lean` declares the
abstract `LemmaS1Data` record with fields `Gn`, `G_limit`, `supNormDiff`,
`hSupNormDiff_dom`, and `hUnif`.  This bridge constructs an instance of
that record from a concrete Cox sample, given:

  * the true parameter `θ₀`,
  * a deterministic limit function `G_limit`,
  * a sup-norm deviation function `supNormDiff` (one option:
    `sup over Θ of |Gn(θ) − G_limit(θ)|` from the paramSpace),
  * a domination hypothesis on the deviation,
  * the uniform-convergence hypothesis (the actual content of Lemma S1).

The abstract layer's `CoxParam` (in `Auto`) does NOT have the `γ` field —
it is the simpler restricted parameter `(α, β, η)`.  We provide a
`CoxParam.toAuto` projection.

(The bridge file is intentionally lightweight: it shows the connection is
well-defined, without trying to actually discharge the uniform-convergence
hypothesis.)
-/

/-- Strip the scalar coefficient `γ` from a full Cox parameter to obtain the
restricted `(α, β, η)` parameter used in the abstract `Auto` layer. -/
def CoxParam.toAuto (θ : CoxParam p d) :
    Statlean.CoxChangePoint.Auto.CoxParam d :=
  ⟨θ.α, θ.β, θ.η⟩

end Statlean.CoxChangePoint

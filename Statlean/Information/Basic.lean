import Statlean.Statistic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Information/Basic

Fisher information and score function for parametric statistical models.

The Fisher information `I(θ) = E[(∂/∂θ log f_θ(X))²]` measures
the amount of information about θ contained in an observation.
-/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The score function ∂/∂θ log f_θ(x), defined via the derivative of the
log-density. Here `logDensity θ ω` represents `log f_θ(ω)`. -/
noncomputable def scoreFunction
    (logDensity : ℝ → Ω → ℝ) (θ : ℝ) (ω : Ω) : ℝ :=
  deriv (fun θ' => logDensity θ' ω) θ

/-- Fisher information: `I(θ) = E_θ[(∂/∂θ log f_θ(X))²]`. -/
noncomputable def fisherInformation
    (P : ParametricFamily ℝ Ω) (logDensity : ℝ → Ω → ℝ) (θ : ℝ) : ℝ :=
  ∫ ω, (scoreFunction logDensity θ ω) ^ 2 ∂(P.measure θ)


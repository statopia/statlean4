import Statlean.Statistic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

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

/-! ## Fisher Information for Natural Exponential Families

Shao, Proposition 3.2 (p.187): In a 1D natural exponential family with
log-density `η · T(x) - ζ(η)`, the score function is `T(x) - ζ'(η)`,
and the Fisher information equals `Var_η(T(X))` when `E_η[T(X)] = ζ'(η)`.
-/

section ExpFamilyFisherInfo

/-- Log-density of a 1D natural exponential family: `η · T(x) - ζ(η)`. -/
noncomputable def expFamilyLogDensity (T : Ω → ℝ) (ζ : ℝ → ℝ) : ℝ → Ω → ℝ :=
  fun η x => η * T x - ζ η

/-- **Score function of a 1D NEF**: `∂/∂η log f_η(x) = T(x) - ζ'(η)`.
Shao, Proposition 3.2(i), p.187. -/
theorem expFamily_score_eq {Ω : Type*} (T : Ω → ℝ) (ζ : ℝ → ℝ) (η : ℝ) (x : Ω)
    (hζ : DifferentiableAt ℝ ζ η) :
    scoreFunction (expFamilyLogDensity T ζ) η x = T x - deriv ζ η := by
  simp only [scoreFunction, expFamilyLogDensity]
  have h1 : HasDerivAt (fun η' => η' * T x) (1 * T x) η :=
    (hasDerivAt_id η).mul_const (T x)
  have h2 : HasDerivAt ζ (deriv ζ η) η := hζ.hasDerivAt
  have h3 := (h1.sub h2).deriv
  simpa [one_mul] using h3

/-- **Fisher information for a 1D NEF**: `I(η) = E_η[(T(X) - ζ'(η))²]`.
Shao, Proposition 3.2(ii), p.187. -/
theorem expFamily_fisher_eq (T : Ω → ℝ) (ζ : ℝ → ℝ)
    (P : ParametricFamily ℝ Ω) (η : ℝ)
    (hζ : DifferentiableAt ℝ ζ η) :
    fisherInformation P (expFamilyLogDensity T ζ) η =
      ∫ x, (T x - deriv ζ η) ^ 2 ∂(P.measure η) := by
  unfold fisherInformation
  congr 1; ext x
  rw [expFamily_score_eq T ζ η x hζ]

/-- If `E_η[T(X)] = ζ'(η)` (the mean parameter identity), then
Fisher information equals the variance of T(X).
Shao, Proposition 3.2(iii), p.187. -/
theorem expFamily_fisher_eq_variance (T : Ω → ℝ) (ζ : ℝ → ℝ)
    (P : ParametricFamily ℝ Ω) (η : ℝ)
    (hζ : DifferentiableAt ℝ ζ η)
    (h_mean : ∫ x, T x ∂(P.measure η) = deriv ζ η) :
    fisherInformation P (expFamilyLogDensity T ζ) η =
      ∫ x, (T x - ∫ y, T y ∂(P.measure η)) ^ 2 ∂(P.measure η) := by
  rw [expFamily_fisher_eq T ζ P η hζ, h_mean]

end ExpFamilyFisherInfo


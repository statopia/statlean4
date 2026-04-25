import Mathlib
import Statlean.Information.Basic
import Statlean.Statistic.Basic

/-!
# Proposition 3.2 (Shao, *Mathematical Statistics*, p.187)

For a (one-dimensional) exponential family with natural-parameter density

  `f_η(x) = exp(η · T(x) − ζ(η)) c(x)`

three statements hold:

* **(i)**  The regularity condition (3.3) — i.e. the interchange of
  differentiation and Lebesgue integral — holds for every `h` with
  `E_η|h(X)| < ∞`.
* **(ii)** Under `P_η`, the Fisher information for the natural parameter
  equals `Var_η(T)`.
* **(iii)** Under the reparametrization `ϑ = E_η[T] = ζ'(η)` the Fisher
  information for `ϑ` equals `Var_η(T)⁻¹`.

This file states the three parts as separate theorems in the
one-dimensional setting (`T : Ω → ℝ`, `η, ϑ ∈ ℝ`).  The 1-D form is the
core analytic content; the multivariate generalisation
(`Fin k → ℝ`-valued natural parameter) follows by the standard
component-wise argument and is left for a follow-up file.

Source: Jun Shao, *Mathematical Statistics* (2nd ed.), Springer 2003,
Proposition 3.2, p.187.

Layer: formalization (Web sandbox `jobmoe1utvq3yq5`).
-/

namespace Statlean.Web

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Proposition 3.2(i)** — *Regularity / interchange of derivative and
integral for an exponential family.*

If `f_η(x) = exp(η · T(x) − ζ(η)) c(x)` is the density of `P_η` w.r.t. a
σ-finite reference measure `μ`, and `h : Ω → ℝ` is `P_η`-integrable, then

  `d/dη ∫ h(x) f_η(x) dμ = ∫ h(x) (T(x) − ζ'(η)) f_η(x) dμ`.

(The right-hand side equals `∫ h · score · dP_η`; see
`Statlean.Information.Basic.expFamily_score_eq`.) -/
theorem expFamily_regularity
    (T : Ω → ℝ) (ζ : ℝ → ℝ) (μ : Measure Ω) [SigmaFinite μ]
    (η : ℝ)
    (hζ : DifferentiableAt ℝ ζ η)
    (h : Ω → ℝ)
    (h_int : Integrable
      (fun x => h x * Real.exp (η * T x - ζ η)) μ) :
    HasDerivAt (fun η' : ℝ =>
        ∫ x, h x * Real.exp (η' * T x - ζ η') ∂μ)
      (∫ x, h x * (T x - deriv ζ η) *
              Real.exp (η * T x - ζ η) ∂μ)
      η := by
  sorry

/-- **Proposition 3.2(ii)** — *In an exponential family, Fisher
information equals the variance of the sufficient statistic.*

Let `P` be a parametric family on `Ω` and assume `P.measure η` has the
exponential-family log-density `expFamilyLogDensity T ζ` w.r.t. some
reference measure.  If `E_η[T] = ζ'(η)`, then

  `I(η)  =  Var_{P_η}(T)`. -/
theorem expFamily_variance_eq_fisherInformation
    (T : Ω → ℝ) (ζ : ℝ → ℝ)
    (P : ParametricFamily ℝ Ω) (η : ℝ)
    (hζ : DifferentiableAt ℝ ζ η)
    (h_mean : ∫ x, T x ∂(P.measure η) = deriv ζ η)
    (hT_meas : AEMeasurable T (P.measure η)) :
    fisherInformation P (expFamilyLogDensity T ζ) η =
      variance T (P.measure η) := by
  rw [expFamily_fisher_eq_variance T ζ P η hζ h_mean,
      ← ProbabilityTheory.variance_eq_integral hT_meas]

/-- **Proposition 3.2(iii)** — *Cramér–Rao lower bound is attained under
the mean parametrization.*

Under the reparametrization `ϑ = E_η[T] = ζ'(η)` (assumed to be a local
diffeomorphism near `η`), the Fisher information at the mean parameter
equals the inverse of the variance of `T`:

  `I(ϑ)  =  Var_{P_η}(T)⁻¹`. -/
theorem expFamily_fisherInformation_mean_param_eq_inv_variance
    (T : Ω → ℝ) (ζ : ℝ → ℝ)
    (P : ParametricFamily ℝ Ω) (η : ℝ)
    (Q : ParametricFamily ℝ Ω)
    -- `Q` is the same family reparametrized by `ϑ = ζ'(η)`
    (h_repar : Q.measure (deriv ζ η) = P.measure η)
    (logDensity_Q : ℝ → Ω → ℝ)
    (hζ : DifferentiableAt ℝ ζ η)
    (h_mean : ∫ x, T x ∂(P.measure η) = deriv ζ η)
    (h_var_pos : variance T (P.measure η) ≠ 0) :
    fisherInformation Q logDensity_Q (deriv ζ η) =
      (variance T (P.measure η))⁻¹ := by
  sorry

end Statlean.Web

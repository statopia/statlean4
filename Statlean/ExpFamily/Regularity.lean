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

namespace Statlean.ExpFamily.Regularity

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Proposition 3.2(i)** — *Regularity / interchange of derivative and
integral for an exponential family, in dominated form.*

Let `f_η(x) = exp(η · T(x) − ζ(η)) c(x)` be the density of `P_η` w.r.t. a
σ-finite reference measure `μ`.  Suppose, on an open ball `Ball(η, ε)`:

* `ζ` is differentiable at every point;
* the integrand `h(x) f_η'(x) := h(x) · exp(η' T(x) − ζ(η'))` and its
  formal derivative `h(x) (T(x) − ζ'(η')) f_η'(x)` admit a `μ`-integrable
  dominating function `bound : Ω → ℝ`;

then

  `d/dη ∫ h(x) f_η(x) dμ = ∫ h(x) (T(x) − ζ'(η)) f_η(x) dμ`.

The right-hand side equals `∫ h · score · dP_η`; see
`Statlean.Information.Basic.expFamily_score_eq`. -/
theorem expFamily_regularity
    (T : Ω → ℝ) (ζ : ℝ → ℝ) (μ : Measure Ω) [SigmaFinite μ]
    (η ε : ℝ) (hε : 0 < ε)
    (hζ_local : ∀ η' ∈ Metric.ball η ε, DifferentiableAt ℝ ζ η')
    (h : Ω → ℝ)
    (hh_meas : AEStronglyMeasurable h μ)
    (hT_meas : Measurable T)
    (h_int : Integrable (fun x => h x * Real.exp (η * T x - ζ η)) μ)
    (bound : Ω → ℝ)
    (bound_int : Integrable bound μ)
    (h_dom : ∀ᵐ x ∂μ, ∀ η' ∈ Metric.ball η ε,
      ‖h x * (T x - deriv ζ η') * Real.exp (η' * T x - ζ η')‖ ≤ bound x) :
    HasDerivAt (fun η' : ℝ =>
        ∫ x, h x * Real.exp (η' * T x - ζ η') ∂μ)
      (∫ x, h x * (T x - deriv ζ η) *
              Real.exp (η * T x - ζ η) ∂μ)
      η := by
  -- Apply the Leibniz rule for differentiation under the integral sign
  have leibniz := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ)
    (F := fun η' x => h x * Real.exp (η' * T x - ζ η'))
    (F' := fun η' x => h x * (T x - deriv ζ η') * Real.exp (η' * T x - ζ η'))
    (x₀ := η)
    (s := Metric.ball η ε)
    (bound := bound)
    -- s ∈ nhds η
    (Metric.ball_mem_nhds η hε)
    -- ∀ᶠ η' in nhds η, AEStronglyMeasurable (F η') μ
    (by
      apply Filter.Eventually.of_forall; intro η'
      exact hh_meas.mul (hT_meas.const_mul η' |>.sub measurable_const |>.exp
        |>.aestronglyMeasurable))
    -- Integrable (F η) μ
    h_int
    -- AEStronglyMeasurable (F' η) μ
    (by
      apply AEStronglyMeasurable.mul
      · exact hh_meas.mul (hT_meas.sub measurable_const |>.aestronglyMeasurable)
      · exact (hT_meas.const_mul η |>.sub measurable_const |>.exp
          |>.aestronglyMeasurable))
    -- ∀ᵐ a ∂μ, ∀ η' ∈ s, ‖F' η' a‖ ≤ bound a
    h_dom
    -- Integrable bound μ
    bound_int
    -- ∀ᵐ a ∂μ, ∀ η' ∈ s, HasDerivAt (fun η' => F η' a) (F' η' a) η'
    (by
      apply Filter.Eventually.of_forall
      intro x η' hη'
      have hg : HasDerivAt (fun η => η * T x - ζ η) (T x - deriv ζ η') η' :=
        (hasDerivAt_mul_const (T x)).sub (hζ_local η' hη').hasDerivAt
      have hfull : HasDerivAt (fun η => h x * Real.exp (η * T x - ζ η))
          (h x * (Real.exp (η' * T x - ζ η') * (T x - deriv ζ η'))) η' :=
        hg.exp.const_mul (h x)
      convert hfull using 1; ring)
  exact leibniz.2

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

Under the reparametrization `ϑ = E_η[T] = ζ'(η)`, the Fisher information
at the mean parameter equals the inverse of the variance of `T`:

  `I(ϑ)  =  Var_{P_η}(T)⁻¹`.

The proof relies on two structural facts taken as hypotheses:

* `h_chain` — the **Fisher-information chain rule** under reparametrization
  `ϑ = ζ'(η)`: `I_Q(ϑ) · (ζ''(η))² = I_P(η)`.  This is the standard
  Jacobian identity for log-density scores composed with a smooth
  reparametrization.

* `h_zeta_pp` — the **cumulant-variance identity** `ζ''(η) = Var_η(T)`
  for an exponential family.  This follows from differentiating
  `ζ'(η) = E_η[T]` once more under the integral sign (an application of
  part (i)).

Combined with part (ii), the conclusion follows by algebra:

  `I_Q(ϑ) · Var(T)² = Var(T)`  ⟹  `I_Q(ϑ) = Var(T)⁻¹`. -/
theorem expFamily_fisherInformation_mean_param_eq_inv_variance
    (T : Ω → ℝ) (ζ : ℝ → ℝ)
    (P : ParametricFamily ℝ Ω) (η : ℝ)
    (Q : ParametricFamily ℝ Ω)
    (logDensity_Q : ℝ → Ω → ℝ)
    -- `Q` is the same family reparametrized by `ϑ = ζ'(η)`.
    -- (Documented as a hypothesis; the proof uses the chain-rule
    -- abstraction `h_chain` which encodes the same relationship.)
    (_h_repar : Q.measure (deriv ζ η) = P.measure η)
    (hζ : DifferentiableAt ℝ ζ η)
    (h_mean : ∫ x, T x ∂(P.measure η) = deriv ζ η)
    (hT_meas : AEMeasurable T (P.measure η))
    (h_var_pos : variance T (P.measure η) ≠ 0)
    -- Chain rule:  I_Q(ϑ) · (ζ''(η))² = I_P(η)
    (h_chain : fisherInformation Q logDensity_Q (deriv ζ η)
               * (deriv (deriv ζ) η) ^ 2
               = fisherInformation P (expFamilyLogDensity T ζ) η)
    -- Cumulant-variance identity:  ζ''(η) = Var_η(T)
    (h_zeta_pp : deriv (deriv ζ) η = variance T (P.measure η)) :
    fisherInformation Q logDensity_Q (deriv ζ η) =
      (variance T (P.measure η))⁻¹ := by
  -- Apply (ii) to identify `I_P(η)` with `Var(T)`.
  have hII : fisherInformation P (expFamilyLogDensity T ζ) η =
             variance T (P.measure η) :=
    expFamily_variance_eq_fisherInformation T ζ P η hζ h_mean hT_meas
  -- Rewrite `h_chain` to: `I_Q · V² = V` where `V := Var(T)`.
  rw [h_zeta_pp, hII] at h_chain
  -- From `I_Q · V² = V` and `V ≠ 0`, deduce `I_Q · V = 1`.
  have h_one :
      fisherInformation Q logDensity_Q (deriv ζ η) * variance T (P.measure η) = 1 := by
    have hsq : fisherInformation Q logDensity_Q (deriv ζ η)
               * variance T (P.measure η) * variance T (P.measure η)
             = 1 * variance T (P.measure η) := by
      rw [one_mul, mul_assoc, ← sq]; exact h_chain
    exact mul_right_cancel₀ h_var_pos hsq
  -- `I_Q · V = 1` ⟹ `I_Q = V⁻¹`.
  exact eq_inv_of_mul_eq_one_left h_one

end Statlean.ExpFamily.Regularity

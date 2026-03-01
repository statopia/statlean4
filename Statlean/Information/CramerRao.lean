import Statlean.Information.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # Information/CramerRao

Cramér-Rao lower bound: for any unbiased estimator T of g(θ),
`Var(T(X)) ≥ g'(θ)² / I(θ)` under regularity conditions.
-/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Cramér-Rao Lower Bound**: If T is an unbiased estimator of g(θ)
satisfying the regularity conditions (interchange of differentiation and
integration), then `Var_θ(T) ≥ g'(θ)² / I(θ)`.

The proof uses the Cauchy-Schwarz (covariance) inequality via a
completing-the-square argument: for all t ∈ ℝ,
`0 ≤ ∫((T-gθ) - t·S)² dμ = V - 2t·D + t²·I`.
Substituting `t = D/I` yields `D² ≤ V·I`. -/
theorem cramer_rao (P : ParametricFamily ℝ Ω)
    (logDensity : ℝ → Ω → ℝ) (T : Ω → ℝ) (g : ℝ → ℝ) (θ : ℝ)
    (hI_pos : fisherInformation P logDensity θ > 0)
    (h_regularity : deriv g θ =
      ∫ ω, (T ω - g θ) * scoreFunction logDensity θ ω ∂(P.measure θ))
    (hT_sq_int : Integrable (fun ω => (T ω - g θ) ^ 2) (P.measure θ))
    (hS_sq_int : Integrable (fun ω => (scoreFunction logDensity θ ω) ^ 2) (P.measure θ))
    (hTS_int : Integrable (fun ω => (T ω - g θ) * scoreFunction logDensity θ ω) (P.measure θ)) :
    (∫ ω, (T ω - g θ) ^ 2 ∂(P.measure θ)) ≥
      (deriv g θ) ^ 2 / fisherInformation P logDensity θ := by
  set μ := P.measure θ
  set S := scoreFunction logDensity θ
  set I_val := fisherInformation P logDensity θ with hI_def
  set D := deriv g θ
  set V := ∫ ω, (T ω - g θ) ^ 2 ∂μ
  -- Quadratic form: for all t, 0 ≤ ∫((T-gθ) - t·S)² dμ = V - 2t·D + t²·I
  suffices hCS : D ^ 2 ≤ V * I_val by
    rw [ge_iff_le, div_le_iff₀ hI_pos]
    linarith
  -- Use t = D/I (the minimizer)
  have key : ∀ t : ℝ, 0 ≤ V - 2 * t * D + t ^ 2 * I_val := by
    intro t
    have h_nonneg : 0 ≤ ∫ ω, ((T ω - g θ) - t * S ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    -- Expand the integrand
    have h_eq : ∫ ω, ((T ω - g θ) - t * S ω) ^ 2 ∂μ = V - 2 * t * D + t ^ 2 * I_val := by
      -- Split into three integrals via linearity
      have hi1 := hT_sq_int
      have hi2 : Integrable (fun ω => (-2 * t) * ((T ω - g θ) * S ω)) μ :=
        hTS_int.const_mul _
      have hi3 : Integrable (fun ω => t ^ 2 * (S ω ^ 2)) μ := hS_sq_int.const_mul _
      -- Split integrand into three additive terms
      have hsplit : (fun ω => ((T ω - g θ) - t * S ω) ^ 2) =
          (fun ω => (T ω - g θ) ^ 2 + (-2 * t) * ((T ω - g θ) * S ω) + t ^ 2 * (S ω ^ 2)) :=
        funext fun ω => by ring
      rw [hsplit]
      -- Now split the integral using linearity
      have h12 : ∫ ω, ((T ω - g θ) ^ 2 + (-2 * t) * ((T ω - g θ) * S ω) +
          t ^ 2 * (S ω ^ 2)) ∂μ =
        ∫ ω, ((T ω - g θ) ^ 2 + (-2 * t) * ((T ω - g θ) * S ω)) ∂μ +
        ∫ ω, t ^ 2 * (S ω ^ 2) ∂μ := integral_add (hi1.add hi2) hi3
      have h11 : ∫ ω, ((T ω - g θ) ^ 2 + (-2 * t) * ((T ω - g θ) * S ω)) ∂μ =
        ∫ ω, (T ω - g θ) ^ 2 ∂μ + ∫ ω, (-2 * t) * ((T ω - g θ) * S ω) ∂μ :=
          integral_add hi1 hi2
      rw [h12, h11, integral_const_mul, integral_const_mul, h_regularity, hI_def, fisherInformation]
      ring
    linarith
  -- Substitute t = D / I_val
  have h := key (D / I_val)
  have h_simp : V - 2 * (D / I_val) * D + (D / I_val) ^ 2 * I_val = V - D ^ 2 / I_val := by
    field_simp; ring
  rw [h_simp] at h
  -- Now h : 0 ≤ V - D²/I, i.e., D²/I ≤ V
  -- Multiply both sides by I (> 0)
  -- h : 0 ≤ V - D²/I, so D²/I ≤ V, so D² ≤ V*I
  have hDI : D ^ 2 / I_val ≤ V := by linarith
  have := div_le_iff₀ hI_pos |>.mp hDI
  linarith

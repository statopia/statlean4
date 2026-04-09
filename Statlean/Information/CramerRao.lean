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
  set V := ∫ ω, (T ω - g θ) ^ 2 ∂μ
  set I := fisherInformation P logDensity θ
  set D := deriv g θ
  rw [ge_iff_le, div_le_iff₀ hI_pos]
  have hI_ne : I ≠ 0 := ne_of_gt hI_pos
  suffices h_key : 0 ≤ V - D ^ 2 / I by
    rwa [sub_nonneg, div_le_iff₀ hI_pos] at h_key
  set f := fun ω => T ω - g θ
  set S := fun ω => scoreFunction logDensity θ ω
  set c := D / I
  -- Completing the square: 0 ≤ ∫(f - c·S)²
  have h_quad_nn : 0 ≤ ∫ ω, (f ω - c * S ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  -- Show ∫(f - c·S)² = V - D²/I by splitting the integral
  have h_quad_val : ∫ ω, (f ω - c * S ω) ^ 2 ∂μ = V - D ^ 2 / I := by
    have h_rw : (fun ω => (f ω - c * S ω) ^ 2) =
        (fun ω => f ω ^ 2 + (-2 * c * (f ω * S ω) + c ^ 2 * S ω ^ 2)) := by
      ext ω; ring
    rw [h_rw]
    have h_rest_int : Integrable (fun ω => -2 * c * (f ω * S ω) + c ^ 2 * S ω ^ 2) μ :=
      (hTS_int.const_mul _).add (hS_sq_int.const_mul _)
    rw [integral_add hT_sq_int h_rest_int,
        integral_add (hTS_int.const_mul _) (hS_sq_int.const_mul _),
        integral_const_mul, integral_const_mul]
    change V + (-2 * c * ∫ (ω : Ω), f ω * S ω ∂μ + c ^ 2 * ∫ (ω : Ω), S ω ^ 2 ∂μ) =
        V - D ^ 2 / I
    rw [show ∫ (ω : Ω), f ω * S ω ∂μ = D from h_regularity.symm]
    change V + (-2 * c * D + c ^ 2 * I) = V - D ^ 2 / I
    simp only [c, div_eq_mul_inv]
    field_simp
    ring
  linarith [h_quad_nn, h_quad_val]

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Gauss-Markov Theorem

## Main result

The **Gauss-Markov theorem** (Shao, Theorem 3.9) states that in the linear model
`Y = Xβ + ε` with `E[ε] = 0` and `Cov(ε) = σ²I`, the OLS estimator `β̂ = (X'X)⁻¹X'Y`
is the **Best Linear Unbiased Estimator** (BLUE) — it minimizes variance among all
linear unbiased estimators.

## Formalization approach

The statistical content reduces to a fact from Hilbert space geometry:
the orthogonal projection onto a closed subspace minimizes the norm of the residual.
In the linear model:
- The response vector `Y ∈ ℝⁿ` lives in a real inner product space `E`
- The column space `V` is a subspace with orthogonal projection
- The OLS fitted values `Ŷ = πᵥ(Y)` are the orthogonal projection
- BLUE optimality = projection minimizes `‖Y - v‖` over `v ∈ V`

This is exactly `Submodule.starProjection_minimal` from Mathlib.

## References

- Jun Shao, *Mathematical Statistics*, 2nd ed., Theorem 3.9
- Mathlib: `Mathlib.Analysis.InnerProductSpace.Projection.Basic`
-/

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **linear model**: a subspace `V` of a real inner product space `E`
(the column space of the design matrix), plus the response vector `Y`.
The OLS fitted values are the orthogonal projection of `Y` onto `V`. -/
structure LinearModel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Column space of the design matrix -/
  V : Submodule ℝ E
  /-- The column space admits orthogonal projection -/
  hasProj : V.HasOrthogonalProjection
  /-- Response vector -/
  Y : E

attribute [instance] LinearModel.hasProj

/-- The OLS fitted values: orthogonal projection of `Y` onto the column space `V`. -/
def LinearModel.ols (M : LinearModel E) : E :=
  M.V.starProjection M.Y

/-- The OLS residual vector. -/
def LinearModel.residual (M : LinearModel E) : E :=
  M.Y - M.ols

/-- **Gauss-Markov Theorem** (norm form):
The OLS fitted values minimize the residual norm over the column space.
For any `δ ∈ V`, `‖Y - πᵥ(Y)‖ ≤ ‖Y - δ‖`.

This is the core geometric content: orthogonal projection is the nearest point
in the subspace. In the linear model, this means OLS minimizes the sum of
squared residuals, which implies BLUE optimality. -/
theorem gauss_markov (M : LinearModel E)
    (δ : M.V) :
    ‖M.residual‖ ≤ ‖M.Y - (δ : E)‖ := by
  unfold LinearModel.residual LinearModel.ols
  rw [M.V.starProjection_minimal M.Y]
  exact ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ norm_nonneg _⟩ δ

/-- **Gauss-Markov** (squared form):
The OLS fitted values minimize the squared residual norm over the column space. -/
theorem gauss_markov_sq (M : LinearModel E)
    (δ : M.V) :
    ‖M.residual‖ ^ 2 ≤ ‖M.Y - (δ : E)‖ ^ 2 := by
  exact sq_le_sq' (by linarith [norm_nonneg M.residual, gauss_markov M δ]) (gauss_markov M δ)

/-- The OLS residual is orthogonal to the column space. -/
theorem ols_residual_orthogonal (M : LinearModel E)
    (w : M.V) :
    ⟪M.residual, (w : E)⟫_ℝ = 0 := by
  exact Submodule.inner_left_of_mem_orthogonal w.2
    (M.V.sub_starProjection_mem_orthogonal M.Y)

/-- Pythagorean theorem for OLS: `‖Y‖² = ‖Ŷ‖² + ‖Y - Ŷ‖²`. -/
theorem ols_pythagorean (M : LinearModel E) :
    ‖M.Y‖ ^ 2 = ‖(M.ols : E)‖ ^ 2 + ‖M.residual‖ ^ 2 := by
  have hortho : ⟪(M.ols : E), M.residual⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.coe_mem _)
      (M.V.sub_starProjection_mem_orthogonal M.Y)
  have hdecomp : M.Y = M.ols + M.residual := by
    simp [LinearModel.residual]
  rw [hdecomp, norm_add_sq_real, hortho, mul_zero, add_zero]

end

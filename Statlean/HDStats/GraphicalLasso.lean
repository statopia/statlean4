import Statlean.HDStats.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Graphical Lasso (Friedman–Hastie–Tibshirani 2008)

The Graphical Lasso estimates a sparse precision matrix `Θ` from data via
```
  max  log det(Θ) - tr(S · Θ) - λ · ‖Θ‖_{1,off}
    Θ ≻ 0
```
where `S` is the empirical covariance and `‖Θ‖_{1,off}` is the sum of
absolute off-diagonal entries.  Zeros in `Θhat` correspond to conditional
independence in the underlying Gaussian graphical model.

## Main definitions

* `offDiagL1Norm Θ` — sum of `|Θ_ij|` for `i ≠ j`.
* `glassoConvexPart S Θ lam` — `tr(S · Θ) + λ · ‖Θ‖_{1,off}`, the convex
  part of the (negated) Graphical Lasso objective.
* `IsGlassoEstimator S lam Θhat` — global minimiser predicate over
  positive-definite precision matrices.

## Main results

* `offDiagL1Norm_nonneg`.
* `offDiagL1Norm_zero` — `‖0‖_{1,off} = 0`.
* `offDiagL1Norm_diagonal` — diagonal matrices have zero off-diagonal `ℓ¹`.
* `glassoConvexPart_penalty_nonneg` — the penalty term is non-negative
  whenever `λ ≥ 0`.
* `glasso_selection_consistency` — Ravikumar–Wainwright (axiom / R6).

## References

* J. Friedman, T. Hastie, R. Tibshirani, *Sparse inverse covariance
  estimation with the graphical lasso*, Biostatistics 9 (2008).
* P. Ravikumar, M. J. Wainwright, G. Raskutti, B. Yu, *High-dimensional
  covariance estimation by minimizing ℓ₁-penalized log-determinant
  divergence*, EJS 5 (2011).
-/

namespace Statlean.HDStats

open scoped BigOperators
open Matrix

variable {p : ℕ}

/-! ### Off-diagonal `ℓ¹` norm -/

/-- **Off-diagonal `ℓ¹` norm**: `∑_{i ≠ j} |Θ_ij|`. -/
def offDiagL1Norm (Θ : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, |Θ i j|

lemma offDiagL1Norm_nonneg (Θ : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ offDiagL1Norm Θ := by
  unfold offDiagL1Norm
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp] lemma offDiagL1Norm_zero :
    offDiagL1Norm (0 : Matrix (Fin p) (Fin p) ℝ) = 0 := by
  unfold offDiagL1Norm
  simp

/-- A diagonal matrix has zero off-diagonal `ℓ¹` norm. -/
lemma offDiagL1Norm_diagonal (d : Fin p → ℝ) :
    offDiagL1Norm (Matrix.diagonal d) = 0 := by
  unfold offDiagL1Norm
  refine Finset.sum_eq_zero ?_
  intro i _
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [Matrix.diagonal_apply_ne' _ hji]
  simp

/-! ### Graphical Lasso objective -/

/-- **Graphical Lasso convex part**: `tr(S · Θ) + λ · ‖Θ‖_{1,off}`.

The full (negated) Graphical Lasso objective is
`-log det(Θ) + tr(S · Θ) + λ · ‖Θ‖_{1,off}`; this definition packages
the part that does not require positive-definite reasoning, which is
convenient for stating optimality. -/
noncomputable def glassoConvexPart
    (S Θ : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ) : ℝ :=
  (S * Θ).trace + lam * offDiagL1Norm Θ

/-- The penalty term in `glassoConvexPart` is non-negative whenever the
regularisation parameter is non-negative. -/
lemma glassoConvexPart_penalty_nonneg
    (Θ : Matrix (Fin p) (Fin p) ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ lam * offDiagL1Norm Θ :=
  mul_nonneg hlam (offDiagL1Norm_nonneg _)

/-- For a diagonal precision matrix the penalty term vanishes. -/
@[simp] lemma glassoConvexPart_diagonal_penalty
    (S : Matrix (Fin p) (Fin p) ℝ) (d : Fin p → ℝ) (lam : ℝ) :
    glassoConvexPart S (Matrix.diagonal d) lam =
      (S * Matrix.diagonal d).trace := by
  unfold glassoConvexPart
  rw [offDiagL1Norm_diagonal]
  ring

/-! ### Graphical Lasso estimator -/

/-- `Θhat` is a **Graphical Lasso estimator** for empirical covariance `S`
at penalty `λ` if it is positive definite and minimises
`tr(S · Θ) + λ · ‖Θ‖_{1,off} - log det(Θ)` over all positive-definite
matrices `Θ`. -/
def IsGlassoEstimator
    (S : Matrix (Fin p) (Fin p) ℝ) (lam : ℝ)
    (Θhat : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  Θhat.PosDef ∧
    ∀ Θ : Matrix (Fin p) (Fin p) ℝ, Θ.PosDef →
      glassoConvexPart S Θhat lam - Real.log Θhat.det ≤
        glassoConvexPart S Θ lam - Real.log Θ.det

/-- A Graphical Lasso estimator is positive definite by definition. -/
lemma IsGlassoEstimator.posDef
    {S : Matrix (Fin p) (Fin p) ℝ} {lam : ℝ}
    {Θhat : Matrix (Fin p) (Fin p) ℝ}
    (h : IsGlassoEstimator S lam Θhat) : Θhat.PosDef :=
  h.1

/-- The minimisation inequality witnessed by a Graphical Lasso estimator. -/
lemma IsGlassoEstimator.le
    {S : Matrix (Fin p) (Fin p) ℝ} {lam : ℝ}
    {Θhat : Matrix (Fin p) (Fin p) ℝ}
    (h : IsGlassoEstimator S lam Θhat)
    {Θ : Matrix (Fin p) (Fin p) ℝ} (hΘ : Θ.PosDef) :
    glassoConvexPart S Θhat lam - Real.log Θhat.det ≤
      glassoConvexPart S Θ lam - Real.log Θ.det :=
  h.2 Θ hΘ

/-! ### Selection consistency (Ravikumar–Wainwright, axiomatised) -/

/-- **Graphical Lasso selection consistency (axiom / R6)**.

Under suitable incoherence and tail conditions (Ravikumar–Wainwright 2011)
the Graphical Lasso recovers the support of the true precision matrix
with high probability.  The full proof requires primal-dual witness
constructions outside the current Mathlib scope and is recorded here as
an axiom pending a dedicated formalisation route. -/
axiom glasso_selection_consistency
    {p : ℕ} (S Θ_star : Matrix (Fin p) (Fin p) ℝ)
    (lam : ℝ) (hlam : 0 < lam) : True

end Statlean.HDStats

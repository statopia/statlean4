import Mathlib
import Statlean.ExpFamily.Basic

/-! # Generalized Linear Models (Nelder-Wedderburn 1972)

Generalization of linear regression to exponential family responses with a
**link function** relating the mean parameter to a **linear predictor**
`η_i = x_iᵀ β`.  The classical examples are

* linear regression           — identity link `g(μ) = μ`,
* logistic regression         — logit link    `g(μ) = log(μ/(1-μ))`,
* Poisson log-linear model    — log link      `g(μ) = log μ`.

This file develops the abstract structure (`LinkFunction`,
`LinearPredictor`, `predictedMean`) together with the **identity link**
example.  The logit and log links are partial functions on `(0,1)` and
`(0,∞)` respectively; their formal treatment requires extending the
domain or using a `LocalEquiv`-style packaging and is left for a later
file in the `GLM` directory.

The file is complementary to `Statlean.ExpFamily.Basic`, which develops
the abstract exponential family without any regression structure.

## Main definitions

* `Statlean.GLM.LinkFunction`    — a bijection `μ ↔ η` packaged as a
  pair `(g, g⁻¹)` satisfying both inverse identities.
* `Statlean.GLM.identityLink`    — the identity link, i.e. linear
  regression.
* `Statlean.GLM.LinearPredictor` — `η_i = ∑_j X_{ij} β_j`.
* `Statlean.GLM.predictedMean`   — `μ_i = g⁻¹(x_iᵀ β)`.

## Main results

* `LinearPredictor_zero / _add / _smul` — linearity of the linear
  predictor in `β`.
* `predictedMean_identity` — for the identity link, `μ_i = η_i`.

## References

* Nelder, J.A. and Wedderburn, R.W.M. (1972), *Generalized linear
  models*, J. Roy. Statist. Soc. Ser. A 135, 370-384.
* McCullagh, P. and Nelder, J.A. (1989), *Generalized Linear Models*,
  2nd ed., Chapman & Hall.
* Agresti, A. (2015), *Foundations of Linear and Generalized Linear
  Models*, Wiley.
-/

open scoped BigOperators

namespace Statlean.GLM

/-- A **link function** for a generalized linear model.

Mathematically `g : μ ↦ η` is a strictly monotone differentiable bijection
between the mean-parameter space and the linear-predictor space.  Here we
package it abstractly as a pair `(link, invLink)` of functions on `ℝ`
together with the two inverse identities; smoothness and monotonicity
are imposed by the user as separate hypotheses when needed.

Three classical links are

* `identityLink`           — `g μ = μ`,
* logit link (not in this file) — `g μ = log(μ / (1-μ))`, partial on `(0,1)`,
* log link  (not in this file)  — `g μ = log μ`,            partial on `(0,∞)`.
-/
structure LinkFunction where
  /-- The link `g : μ → η`. -/
  link : ℝ → ℝ
  /-- The inverse link `g⁻¹ : η → μ`. -/
  invLink : ℝ → ℝ
  /-- `g (g⁻¹ η) = η`. -/
  link_invLink : ∀ η : ℝ, link (invLink η) = η
  /-- `g⁻¹ (g μ) = μ`. -/
  invLink_link : ∀ μ : ℝ, invLink (link μ) = μ

/-- The **identity link** `g(μ) = μ`, used in classical linear regression. -/
def identityLink : LinkFunction where
  link    := id
  invLink := id
  link_invLink _ := rfl
  invLink_link _ := rfl

/-- The **linear predictor** `η_i = ∑_j X_{ij} β_j` for design matrix
`X : Fin n → Fin p → ℝ` and coefficient vector `β : Fin p → ℝ`. -/
def LinearPredictor {n p : ℕ} (X : Fin n → Fin p → ℝ) (beta : Fin p → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j : Fin p, X i j * beta j

/-- The **predicted mean** for sample `i` is `μ_i = g⁻¹(η_i)`. -/
def predictedMean {n p : ℕ} (g : LinkFunction) (X : Fin n → Fin p → ℝ)
    (beta : Fin p → ℝ) (i : Fin n) : ℝ :=
  g.invLink (LinearPredictor X beta i)

/-! ### Identity link, basic identities -/

@[simp] lemma identityLink_link_apply (μ : ℝ) :
    identityLink.link μ = μ := rfl

@[simp] lemma identityLink_invLink_apply (η : ℝ) :
    identityLink.invLink η = η := rfl

/-! ### Linearity of the linear predictor in `β` -/

/-- The linear predictor at `β = 0` is `0`. -/
theorem LinearPredictor_zero {n p : ℕ} (X : Fin n → Fin p → ℝ) (i : Fin n) :
    LinearPredictor X (fun _ => 0) i = 0 := by
  unfold LinearPredictor
  simp

/-- The linear predictor is additive in `β`. -/
theorem LinearPredictor_add {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (beta1 beta2 : Fin p → ℝ) (i : Fin n) :
    LinearPredictor X (beta1 + beta2) i
      = LinearPredictor X beta1 i + LinearPredictor X beta2 i := by
  unfold LinearPredictor
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The linear predictor is homogeneous in `β`. -/
theorem LinearPredictor_smul {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (c : ℝ) (beta : Fin p → ℝ) (i : Fin n) :
    LinearPredictor X (c • beta) i = c * LinearPredictor X beta i := by
  unfold LinearPredictor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Predicted mean for the identity link -/

/-- For the identity link the predicted mean coincides with the linear
predictor: `μ_i = η_i`. -/
@[simp] theorem predictedMean_identity {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (beta : Fin p → ℝ) (i : Fin n) :
    predictedMean identityLink X beta i = LinearPredictor X beta i := rfl

/-- Specialisation of `LinearPredictor_zero` to the predicted mean under the
identity link. -/
theorem predictedMean_identity_zero {n p : ℕ} (X : Fin n → Fin p → ℝ)
    (i : Fin n) :
    predictedMean identityLink X (fun _ => 0) i = 0 := by
  rw [predictedMean_identity, LinearPredictor_zero]

end Statlean.GLM

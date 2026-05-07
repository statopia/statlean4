/-
Copyright (c) 2026 Gavin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.Kernel.RKHS

/-! # Gaussian Process Regression and Kernel Ridge Regression

This file develops the basic infrastructure for Gaussian process (GP)
regression and kernel ridge regression (KRR), in the framework where the
kernel `K : X → X → ℝ` is a positive semi-definite kernel on an arbitrary
domain `X` (see `Statlean.Kernel.RKHS`).

A *Gaussian process* with mean zero and covariance kernel `K` is a
stochastic process `(f x)_{x : X}` such that for every finite tuple
`x_1, …, x_n` the random vector `(f x_1, …, f x_n)` is multivariate
Gaussian with covariance matrix `(K x_i x_j)_{i,j}`. Given iid Gaussian
noise `ε_i ∼ 𝒩(0, σ²)` and observations `y_i = f(x_i) + ε_i`, the
posterior mean of `f` at a new test point `x*` is

  μ*(x*) = k*ᵀ (K + σ²I)⁻¹ y,                  k*_i = K(x*, x_i).

Kernel ridge regression solves
  min_α   ‖y - K α‖² + λ αᵀ K α,
with closed-form dual solution `α̂ = (K + λI)⁻¹ y`. A classical observation
(Saunders-Gammerman-Vovk 1998) is that **the GP posterior mean equals the
KRR predictor with `λ = σ²`**. The full equivalence theorem is left as a
statement (`krr_equivalent_to_gp_posterior`), as the formal proof requires
multivariate Gaussian conditioning machinery that is outside the scope of
this file.

## Main definitions

* `Statlean.Kernel.GramMatrix K xs` — the matrix `(K (xs i) (xs j))_{i,j}`.
* `Statlean.Kernel.regularizedGram K xs λ` — `GramMatrix K xs + λ • I`.
* `Statlean.Kernel.krrPredict K xs α x*` — `∑ i α_i · K(x*, xs i)`.

## Main results

* `GramMatrix_apply` — entries of the Gram matrix by definition.
* `GramMatrix_symm` — symmetry of the Gram matrix from kernel symmetry.
* `GramMatrix_psd` — Gram matrix from PSD kernel is PSD as a quadratic form.
* `regularizedGram_symm` — `K + λI` is symmetric whenever `K` is.
* `krrPredict_zero` — the KRR predictor is zero at `α = 0`.
* `krrPredict_add` — additivity of the KRR predictor in `α`.

## References

* Rasmussen & Williams (2006), *Gaussian Processes for Machine Learning*, MIT Press.
* Saunders, Gammerman, Vovk (1998), *Ridge regression learning algorithm
  in dual variables*, Proceedings of ICML.
* Schölkopf & Smola (2002), *Learning with Kernels*, Chapter 16.
-/

open Real Matrix
open scoped Matrix BigOperators

namespace Statlean.Kernel

variable {X : Type*}

/-! ### Gram matrix -/

/-- The **Gram matrix** of a kernel `K` evaluated on a finite sample
`xs : Fin n → X` is the `n × n` real matrix with entry `K (xs i) (xs j)`. -/
def GramMatrix {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => K (xs i) (xs j))

@[simp]
theorem GramMatrix_apply {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X) (i j : Fin n) :
    GramMatrix K xs i j = K (xs i) (xs j) := rfl

/-- The Gram matrix is symmetric whenever the kernel is symmetric. -/
theorem GramMatrix_symm {n : ℕ} {K : X → X → ℝ}
    (hsymm : ∀ x y, K x y = K y x) (xs : Fin n → X) :
    (GramMatrix K xs).IsSymm := by
  ext i j
  simp [GramMatrix_apply, Matrix.transpose_apply, hsymm]

/-- The Gram matrix from a PSD kernel is positive semi-definite as a
quadratic form: for every coefficient vector `cs : Fin n → ℝ`,
`∑ᵢⱼ cᵢ cⱼ Kᵢⱼ ≥ 0`. -/
theorem GramMatrix_psd {n : ℕ} {K : X → X → ℝ}
    (hPSD : IsPSDKernel K) (xs : Fin n → X) (cs : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, cs i * cs j * (GramMatrix K xs i j) := by
  simp only [GramMatrix_apply]
  exact hPSD.2 n xs cs

/-! ### Regularized Gram matrix -/

/-- The **regularized Gram matrix** `K + λ I` used in kernel ridge
regression and as the noise-corrected covariance in GP regression. -/
noncomputable def regularizedGram {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X)
    (lam : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  GramMatrix K xs + lam • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The regularized Gram matrix is symmetric whenever the kernel is
symmetric (the `λI` summand is symmetric, and symmetry is preserved by
addition and scalar multiplication). -/
theorem regularizedGram_symm {n : ℕ} {K : X → X → ℝ}
    (hsymm : ∀ x y, K x y = K y x) (xs : Fin n → X) (lam : ℝ) :
    (regularizedGram K xs lam).IsSymm := by
  unfold regularizedGram
  exact (GramMatrix_symm hsymm xs).add (Matrix.isSymm_one.smul lam)

/-- The diagonal of the regularized Gram matrix shifts the kernel diagonal
by `λ`. -/
@[simp]
theorem regularizedGram_diag {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X)
    (lam : ℝ) (i : Fin n) :
    regularizedGram K xs lam i i = K (xs i) (xs i) + lam := by
  unfold regularizedGram
  simp [GramMatrix_apply]

/-! ### KRR predictor -/

/-- The **KRR predictor** at a new point `xstar`, given dual coefficients
`alpha : Fin n → ℝ`. In the formula `f̂(x*) = ∑ᵢ αᵢ K(x*, xᵢ)` the dual
coefficients `α` are the solution `(K + λI)⁻¹ y` of the regularized normal
equations. We separate the predictor from the dual solver because the
predictor is meaningful (and lemmas about it composable) for *any* `α`. -/
noncomputable def krrPredict {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X)
    (alpha : Fin n → ℝ) (xstar : X) : ℝ :=
  ∑ i, alpha i * K xstar (xs i)

/-- The KRR predictor with zero coefficients vanishes. -/
@[simp]
theorem krrPredict_zero {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X) (xstar : X) :
    krrPredict K xs (fun _ => 0) xstar = 0 := by
  unfold krrPredict
  simp

/-- The KRR predictor is additive in the dual coefficients. -/
theorem krrPredict_add {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X)
    (alpha beta : Fin n → ℝ) (xstar : X) :
    krrPredict K xs (alpha + beta) xstar
      = krrPredict K xs alpha xstar + krrPredict K xs beta xstar := by
  unfold krrPredict
  simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The KRR predictor is homogeneous in the dual coefficients. -/
theorem krrPredict_smul {n : ℕ} (K : X → X → ℝ) (xs : Fin n → X)
    (c : ℝ) (alpha : Fin n → ℝ) (xstar : X) :
    krrPredict K xs (c • alpha) xstar = c * krrPredict K xs alpha xstar := by
  unfold krrPredict
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-! ### GP-KRR equivalence (statement only) -/

/-- **GP-KRR equivalence (Saunders-Gammerman-Vovk 1998)**, statement.
The posterior mean of a Gaussian process with iid Gaussian noise of
variance `σ²` coincides with the kernel ridge regression predictor
using regularization parameter `λ = σ²` and dual coefficients
`α̂ = (K + σ²I)⁻¹ y`.

This file states the equivalence as a *placeholder* (`True`); the full
proof requires multivariate Gaussian conditioning machinery that is not
yet in scope. We keep the statement here as a concrete target for future
formalization, and provide its constituent ingredients
(`GramMatrix`, `regularizedGram`, `krrPredict`) above. -/
theorem krr_equivalent_to_gp_posterior
    {n : ℕ} (_K : X → X → ℝ) (_xs : Fin n → X) (_ys : Fin n → ℝ)
    (_sigsq : ℝ) (_xstar : X) :
    True := trivial

end Statlean.Kernel

import Statlean.Regression.Lasso

/-!
# De-biased / Desparsified Lasso (Javanmard–Montanari 2014; Zhang–Zhang 2014)

The Lasso estimator `bh` is biased toward zero, hampering classical
confidence-interval and hypothesis-testing inference.  The **de-biased
Lasso**
```
  β̂^d := bh + (1/n) · M · Xᵀ (y - X bh)
```
where `M` is a "decorrelation" matrix approximating `(XᵀX/n)⁻¹`, removes
this bias to first order and admits an asymptotic normal distribution
useful for coordinate-wise confidence intervals.

## Bias decomposition

Under the linear model `y = X β* + ε`,
```
  β̂^d - β*  =  (1/n) · M · Xᵀ · ε  +  ((1/n) · M · XᵀX - I) (bh - β*).
```
The first term is asymptotically Gaussian; the second is a "remainder"
controlled by sparsity + low-coherence assumptions on `X`.

## Main definitions

* `debiasedLasso M X y bh` — the de-biased estimator.
* `debiasedNoiseTerm M X ε` — `(1/n) M Xᵀ ε`, the leading Gaussian term.
* `debiasedRemainder M X bh β*` — the second-order remainder.

## Main results

* `debiasedLasso_minus_truth_eq` — basic algebraic identity.
* `debiasedLasso_noiseless` — closed form in the noiseless case.
* `debiased_lasso_asymptotic_normality` — Javanmard–Montanari (axiom / R6).

## References

* A. Javanmard, A. Montanari, *Confidence intervals and hypothesis
  testing for high-dimensional regression*, JMLR 15 (2014).
* C.-H. Zhang, S. S. Zhang, *Confidence intervals for low-dimensional
  parameters in high-dimensional linear models*, JRSS B 76 (2014).
* S. van de Geer, P. Bühlmann, Y. Ritov, R. Dezeure, *On asymptotically
  optimal confidence regions and tests for high-dimensional models*,
  Ann. Statist. 42 (2014).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p : ℕ}

/-- The **de-biased Lasso estimator**:
`(β̂^d)_j := bh_j + (1/n) · ∑_k M_{j,k} · ∑_i X_{i,k} · (y_i - ∑_l X_{i,l} · bh_l)`.

`M` is a user-supplied decorrelation matrix (approximating `(XᵀX/n)⁻¹`),
and `Xᵀ (y - X bh)` is the KKT residual. -/
noncomputable def debiasedLasso (M : Fin p → Fin p → ℝ)
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (bh : Fin p → ℝ) :
    Fin p → ℝ := fun j =>
  bh j + (1 / (n : ℝ)) *
    ∑ k, M j k * ∑ i, X i k * (y i - ∑ l, X i l * bh l)

/-- The **leading Gaussian term** of the de-biased Lasso under the linear
model `y = X β* + ε`: `((1/n) · M · Xᵀ · ε)_j`. -/
noncomputable def debiasedNoiseTerm (M : Fin p → Fin p → ℝ)
    (X : Fin n → Fin p → ℝ) (ε : Fin n → ℝ) : Fin p → ℝ := fun j =>
  (1 / (n : ℝ)) * ∑ k, M j k * ∑ i, X i k * ε i

/-- The **second-order remainder term** `(((1/n)·M·XᵀX - I)·(bh - β*))_j`. -/
noncomputable def debiasedRemainder (M : Fin p → Fin p → ℝ)
    (X : Fin n → Fin p → ℝ) (bh β_star : Fin p → ℝ) :
    Fin p → ℝ := fun j =>
  (1 / (n : ℝ)) *
      (∑ k, M j k * ∑ i, X i k * ∑ l, X i l * (bh l - β_star l))
    - (bh j - β_star j)

/-- **Basic algebraic identity**: the difference `(β̂^d)_j - β*_j`
equals the Lasso residual `bh_j - β*_j` plus the de-biasing correction.
No probabilistic content. -/
lemma debiasedLasso_minus_truth_eq
    (M : Fin p → Fin p → ℝ) (X : Fin n → Fin p → ℝ)
    (y : Fin n → ℝ) (bh β_star : Fin p → ℝ) (j : Fin p) :
    debiasedLasso M X y bh j - β_star j =
      (bh j - β_star j) +
        (1 / (n : ℝ)) *
          ∑ k, M j k * ∑ i, X i k * (y i - ∑ l, X i l * bh l) := by
  unfold debiasedLasso
  ring

/-- **Noiseless case**: when `y = X · β*` exactly, the de-biased Lasso
takes the closed form `bh_j + (1/n) Σₖ M_{j,k} Σᵢ X_{i,k} Σₗ X_{i,l}
(β*_l - bh_l)`.  This isolates the contribution of the design matrix to
the correction term. -/
lemma debiasedLasso_noiseless
    (M : Fin p → Fin p → ℝ) (X : Fin n → Fin p → ℝ)
    (bh β_star : Fin p → ℝ) (j : Fin p) :
    debiasedLasso M X (fun i => ∑ l, X i l * β_star l) bh j =
      bh j + (1 / (n : ℝ)) *
        ∑ k, M j k * ∑ i, X i k *
          (∑ l, X i l * (β_star l - bh l)) := by
  unfold debiasedLasso
  congr 1
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  have hrow :
      (∑ l, X i l * β_star l) - (∑ l, X i l * bh l)
        = ∑ l, X i l * (β_star l - bh l) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _; ring
  rw [← hrow]

/-- **Linearity of the de-biased noise term in `ε`**: scaling the noise
vector scales the noise term by the same constant.  Used to derive
asymptotic normality from CLT-type statements on the rows of `X`. -/
lemma debiasedNoiseTerm_smul
    (M : Fin p → Fin p → ℝ) (X : Fin n → Fin p → ℝ) (ε : Fin n → ℝ)
    (c : ℝ) (j : Fin p) :
    debiasedNoiseTerm M X (fun i => c * ε i) j =
      c * debiasedNoiseTerm M X ε j := by
  unfold debiasedNoiseTerm
  have h : (∑ k, M j k * ∑ i, X i k * (c * ε i))
        = c * ∑ k, M j k * ∑ i, X i k * ε i := by
    rw [show c * ∑ k, M j k * ∑ i, X i k * ε i
          = ∑ k, c * (M j k * ∑ i, X i k * ε i) from
        Finset.mul_sum _ _ _]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [show c * (M j k * ∑ i, X i k * ε i)
          = M j k * (c * ∑ i, X i k * ε i) from by ring,
        show c * (∑ i, X i k * ε i)
          = ∑ i, c * (X i k * ε i) from Finset.mul_sum _ _ _]
    refine congrArg (M j k * ·) ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [h]
  ring

/-- **Zero noise vanishes**: with `ε = 0`, the noise term is zero. -/
@[simp]
lemma debiasedNoiseTerm_zero
    (M : Fin p → Fin p → ℝ) (X : Fin n → Fin p → ℝ) (j : Fin p) :
    debiasedNoiseTerm M X (fun _ => (0 : ℝ)) j = 0 := by
  unfold debiasedNoiseTerm
  simp

/-- **Asymptotic normality of the de-biased Lasso (axiom / R6)** —
Javanmard–Montanari 2014, Zhang–Zhang 2014, van de Geer–Bühlmann–
Ritov–Dezeure 2014.

Under sparsity (`‖β*‖₀ = o(√n / log p)`), low-coherence design (existence
of a row-sparse `M` with `‖(1/n)·M·XᵀX − I‖_∞ = o(1/√(n log p))`), and
sub-Gaussian noise, each coordinate of the de-biased estimator is
asymptotically Gaussian: `√n · ((β̂^d)_j - β*_j) / σ_j → 𝒩(0, 1)` in
distribution.

Stated as opaque pending the full asymptotic infrastructure (matrix
concentration + sub-Gaussian CLT + slow Lasso ℓ¹ rate). -/
axiom debiased_lasso_asymptotic_normality
    {n p : ℕ}
    (_X : Fin n → Fin p → ℝ) (_M : Fin p → Fin p → ℝ)
    (_β_star : Fin p → ℝ) (_j : Fin p) :
    True

end Statlean.Regression

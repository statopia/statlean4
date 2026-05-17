import Statlean.Regression.DebiasedLasso

/-!
# Confidence Intervals for Sparse Linear Regression

Using the de-biased Lasso `β̂^d` (see `DebiasedLasso.lean`), we can build
coordinate-wise confidence intervals for the high-dimensional regression
coefficients `β*_j`.  Under Javanmard–Montanari / Zhang–Zhang asymptotic
normality, the interval

  `[ β̂^d_j - z_{α/2} σ̂_j / √n ,  β̂^d_j + z_{α/2} σ̂_j / √n ]`

attains coverage tending to `1 - α`.

## Main definitions

* `ciHalfWidth q sigma n` — `q · σ / √n` (half-width of CI).
* `confidenceInterval bh_d sigma q n j` — `(lower, upper)` pair.
* `CoversParameter ci β_star j` — true `β*_j` lies in the CI.

## Main results

* `ciHalfWidth_nonneg`.
* `CoversParameter_iff_dist_le` — coverage equivalent to small estimation error.
* `sparse_ci_coverage` — Javanmard–Montanari 2014 (axiom / R6).

## References

* A. Javanmard, A. Montanari, *Confidence intervals and hypothesis
  testing for high-dimensional regression*, JMLR 15 (2014).
* C.-H. Zhang, S. S. Zhang, *Confidence intervals for low-dimensional
  parameters in high-dimensional linear models*, JRSS B 76 (2014).
-/

namespace Statlean.Regression

variable {n p : ℕ}

/-- The **CI half-width** at level `q` (critical value): `q · σ / √n`. -/
noncomputable def ciHalfWidth (q sigma : ℝ) (n : ℕ) : ℝ :=
  q * sigma / Real.sqrt (n : ℝ)

lemma ciHalfWidth_nonneg
    {q sigma : ℝ} (hq : 0 ≤ q) (hsigma : 0 ≤ sigma) (n : ℕ) :
    0 ≤ ciHalfWidth q sigma n := by
  unfold ciHalfWidth
  exact div_nonneg (mul_nonneg hq hsigma) (Real.sqrt_nonneg _)

/-- For `q = 0`, the CI half-width collapses to `0`. -/
lemma ciHalfWidth_zero (sigma : ℝ) (n : ℕ) :
    ciHalfWidth 0 sigma n = 0 := by
  unfold ciHalfWidth
  simp

/-- **Coordinate-wise confidence interval** for `β*_j`.

Returns a pair `(lower, upper)` of bounds. -/
noncomputable def confidenceInterval
    (bh_d : Fin p → ℝ) (sigma : Fin p → ℝ) (q : ℝ) (n : ℕ) (j : Fin p) :
    ℝ × ℝ :=
  (bh_d j - ciHalfWidth q (sigma j) n, bh_d j + ciHalfWidth q (sigma j) n)

/-- The CI lower bound. -/
noncomputable def ciLower
    (bh_d : Fin p → ℝ) (sigma : Fin p → ℝ) (q : ℝ) (n : ℕ) (j : Fin p) : ℝ :=
  (confidenceInterval bh_d sigma q n j).1

/-- The CI upper bound. -/
noncomputable def ciUpper
    (bh_d : Fin p → ℝ) (sigma : Fin p → ℝ) (q : ℝ) (n : ℕ) (j : Fin p) : ℝ :=
  (confidenceInterval bh_d sigma q n j).2

/-- **Coverage predicate**: the true `β*_j` lies in the CI. -/
def CoversParameter
    (bh_d : Fin p → ℝ) (sigma : Fin p → ℝ) (q : ℝ) (n : ℕ)
    (β_star : Fin p → ℝ) (j : Fin p) : Prop :=
  ciLower bh_d sigma q n j ≤ β_star j ∧
    β_star j ≤ ciUpper bh_d sigma q n j

/-- Coverage equivalent to small `|β̂^d_j - β*_j|`. -/
lemma CoversParameter_iff_dist_le
    (bh_d : Fin p → ℝ) (sigma : Fin p → ℝ) (q : ℝ) (n : ℕ)
    (β_star : Fin p → ℝ) (j : Fin p) :
    CoversParameter bh_d sigma q n β_star j ↔
      |bh_d j - β_star j| ≤ ciHalfWidth q (sigma j) n := by
  unfold CoversParameter ciLower ciUpper confidenceInterval
  simp only
  rw [abs_sub_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

/-- Coverage is monotone in the critical value `q`: larger `q` gives a wider CI,
hence preserves coverage (assuming the half-width does not flip sign). -/
lemma CoversParameter.mono_q
    {bh_d : Fin p → ℝ} {sigma : Fin p → ℝ} {q1 q2 : ℝ} {n : ℕ}
    {β_star : Fin p → ℝ} {j : Fin p}
    (h : CoversParameter bh_d sigma q1 n β_star j)
    (hq : q1 ≤ q2) (hsig : 0 ≤ sigma j) :
    CoversParameter bh_d sigma q2 n β_star j := by
  rw [CoversParameter_iff_dist_le] at h ⊢
  refine h.trans ?_
  unfold ciHalfWidth
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hq hsig) (Real.sqrt_nonneg _)

/-- **Sparse CI coverage (axiom / R6)** — Javanmard–Montanari 2014.

Under sparsity + low-coherence design + sub-Gaussian noise + a properly
chosen `q = z_{α/2}` (Gaussian critical value), the de-biased Lasso CI
has asymptotic coverage `1 - α`.  Full formalization requires the
asymptotic normality axiom from `DebiasedLasso.lean`.  Stated as a
placeholder `True` proposition pending R6 infrastructure. -/
axiom sparse_ci_coverage
    {n p : ℕ} (_X : Fin n → Fin p → ℝ) (_M : Fin p → Fin p → ℝ)
    (_β_star : Fin p → ℝ) (_alpha : ℝ) :
    True

end Statlean.Regression

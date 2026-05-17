import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.InnerProductSpace.Basic
import Statlean.HDStats.Basic

/-!
# Lasso: ℓ¹-Regularised Least Squares

This file defines the **Lasso** estimator (Tibshirani 1996) — least
squares with an ℓ¹ penalty — and proves the foundational analytic
results used in oracle-inequality arguments:

1. The **basic inequality** of Bickel–Ritov–Tsybakov (2009): a purely
   algebraic consequence of optimality.
2. The **cone constraint** on the good event
   `𝒜 = { 2 ‖X^Tε / n‖_∞ ≤ λ }`: the error
   `h = bh - β*` lies in the 3-1 cone of the support of `β*`.
3. The **slow-rate prediction error bound** under a Restricted
   Eigenvalue condition `RE(s, κ)`.

## Setup

Design matrix `X : Fin n → Fin p → ℝ` (rows are observations, columns
covariates), response `y : Fin n → ℝ`, and unknown sparse parameter
`β* : Fin p → ℝ` with `s = (support β*).card`.

The (rescaled) least-squares loss with ℓ¹ penalty is
  L(β) = (1 / (2n)) · ‖y - X β‖² + λ · ‖β‖₁
and the Lasso estimator `bh` is any global minimiser of `L`.

## Main definitions

* `Statlean.Regression.l1Norm β` — `∑ i, |β i|`, the ℓ¹ pseudonorm.
* `Statlean.Regression.lassoLoss X y λ β` — the Lasso objective.
* `Statlean.Regression.IsLassoEstimator X y λ bh` — `bh` minimises the
  Lasso objective globally.
* `Statlean.Regression.RestrictedEigenvalue X s κ` — the `RE(s, κ)`
  condition of Bickel–Ritov–Tsybakov.

## Main theorems

* `lasso_basic_inequality` — proved (algebraic identity from optimality).
* `lasso_cone_constraint` — proved (basic inequality + Hölder on the
  error on the good event).
* `lasso_slow_rate` — proved (cone constraint + Cauchy–Schwarz +
  Restricted Eigenvalue → quadratic in `‖h_S‖₁`).

## References

* Bickel, Ritov, Tsybakov, *Simultaneous analysis of Lasso and Dantzig
  selector*, Ann. Statist. **37** (2009), 1705–1732.
* Bühlmann, van de Geer, *Statistics for High-Dimensional Data*, §6
  (Springer 2011).
-/

namespace Statlean.Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

variable {n p : ℕ}

/-! ### The ℓ¹ pseudonorm on `Fin p → ℝ` -/

/-- Sum of absolute values, used as the ℓ¹ regulariser. -/
def l1Norm (β : Fin p → ℝ) : ℝ := ∑ i, |β i|

@[simp] lemma l1Norm_zero : l1Norm (fun _ : Fin p => (0 : ℝ)) = 0 := by
  simp [l1Norm]

lemma l1Norm_nonneg (β : Fin p → ℝ) : 0 ≤ l1Norm β := by
  unfold l1Norm; positivity

/-- ℓ¹ pseudonorm decomposes across a Finset partition `S ∪ Sᶜ`. -/
lemma l1Norm_split (β : Fin p → ℝ) (S : Finset (Fin p)) :
    l1Norm β = (∑ i ∈ S, |β i|) + (∑ i ∈ Finset.univ \ S, |β i|) := by
  unfold l1Norm
  rw [← Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => |β i|),
      add_comm]

/-! ### The Lasso objective and estimator -/

/-- The Lasso objective `L(β) = (1/(2n)) ‖y - X β‖² + λ ‖β‖₁`. -/
noncomputable def lassoLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam * l1Norm β

/-- A vector `bh` is a **Lasso estimator** if it is a global minimiser
of `lassoLoss X y λ`. -/
def IsLassoEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, lassoLoss X y lam bh ≤ lassoLoss X y lam β

/-! ### Restricted Eigenvalue condition (Bickel–Ritov–Tsybakov) -/

/-- The **Restricted Eigenvalue** condition `RE(s, κ)` of
Bickel–Ritov–Tsybakov 2009.  For every vector `h` in the 3-1 cone over
some `s`-sized index set `S`, the empirical quadratic form
`(1/n) ‖X h‖²` dominates `κ² ‖h_S‖²`. -/
def RestrictedEigenvalue (X : Fin n → Fin p → ℝ) (s : ℕ) (κ : ℝ) : Prop :=
  ∀ (h : Fin p → ℝ) (S : Finset (Fin p)), S.card ≤ s →
    (∑ i ∈ Finset.univ \ S, |h i|) ≤ 3 * (∑ i ∈ S, |h i|) →
    κ ^ 2 * (∑ i ∈ S, (h i) ^ 2) ≤
      (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * h j) ^ 2

/-! ### Basic inequality (Bickel–Ritov–Tsybakov 2009) -/

/--
**Lasso basic inequality.** If `bh` minimises the Lasso objective and
`β*` is any reference vector, writing `h = bh - β*` and
`ε i = y i - ∑ j, X i j · β* j` the noise relative to `β*`, then
```
  (1/(2n)) · ‖X h‖² + λ · ‖bh‖₁ ≤ (1/n) · ⟨ε, X h⟩ + λ · ‖β*‖₁ .
```
The proof is a pure algebraic identity from `lassoLoss bh ≤ lassoLoss β*`:
expanding `(y - X bh)² = (ε - X h)² = ε² - 2 ε · X h + (X h)²` and
summing over rows.

This is the starting point of every Lasso oracle inequality.  No
probabilistic assumption is used; it holds deterministically for any
minimiser. -/
theorem lasso_basic_inequality
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (bh β_star : Fin p → ℝ) (hbh : IsLassoEstimator X y lam bh) :
    (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam * l1Norm bh ≤
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j)))
        + lam * l1Norm β_star := by
  -- Specialise optimality to the reference vector β*.
  have hopt := hbh β_star
  unfold lassoLoss l1Norm at hopt
  unfold l1Norm
  -- Algebraic identity for each row: (y - X bh)² = (y - X β*)² - 2(y - X β*)(X h) + (X h)²
  have key : ∀ i,
      (y i - ∑ j, X i j * bh j) ^ 2 =
        (y i - ∑ j, X i j * β_star j) ^ 2
          - 2 * (y i - ∑ j, X i j * β_star j)
                * (∑ j, X i j * (bh j - β_star j))
          + (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    intro i
    have hsum : ∑ j, X i j * bh j =
        (∑ j, X i j * β_star j) + ∑ j, X i j * (bh j - β_star j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _; ring
    rw [hsum]; ring
  simp_rw [key] at hopt
  -- Distribute the sum.
  have hexp :
      ∑ i, ((y i - ∑ j, X i j * β_star j) ^ 2
              - 2 * (y i - ∑ j, X i j * β_star j)
                    * (∑ j, X i j * (bh j - β_star j))
              + (∑ j, X i j * (bh j - β_star j)) ^ 2)
        = (∑ i, (y i - ∑ j, X i j * β_star j) ^ 2)
          - 2 * (∑ i, (y i - ∑ j, X i j * β_star j)
                        * ∑ j, X i j * (bh j - β_star j))
          + ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (fun i => 2 * (y i - ∑ j, X i j * β_star j)
                          * ∑ j, X i j * (bh j - β_star j)) =
            (fun i => 2 * ((y i - ∑ j, X i j * β_star j)
                            * ∑ j, X i j * (bh j - β_star j))) from by
              funext i; ring]
    rw [← Finset.mul_sum]
  rw [hexp] at hopt
  -- Name the three sums.
  set A := ∑ i, (y i - ∑ j, X i j * β_star j) ^ 2 with _hA
  set B := ∑ i, (y i - ∑ j, X i j * β_star j) *
                ∑ j, X i j * (bh j - β_star j) with _hB
  set C := ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 with _hC
  -- Distribute (1/(2n)) and identify (1/(2n))·2 = 1/n.  The identity
  -- holds even at n = 0 (both sides are 0).
  have hsplit :
      (1 / (2 * (n : ℝ))) * (A - 2 * B + C) =
        (1 / (2 * (n : ℝ))) * A - (1 / (n : ℝ)) * B
          + (1 / (2 * (n : ℝ))) * C := by
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  rw [hsplit] at hopt
  linarith

/-! ### Cone constraint and slow-rate bound

The next two results turn the algebraic inequality above into a
geometric / statistical statement by exploiting the structure of `β*`:

* `lasso_cone_constraint`: on the "good event" `𝒜` where the empirical
  noise correlation is uniformly bounded by `λ/2`, the error
  `h = bh - β*` is concentrated on the support `S` of `β*` — more
  precisely, the ℓ¹ mass off `S` is at most `3` times the mass on `S`.
* `lasso_slow_rate`: combining the cone constraint with the Restricted
  Eigenvalue condition yields the optimal `s · λ² / κ²` rate.

These are the textbook "slow rate" steps and follow standard arguments
(Bühlmann–van de Geer §6.2, Bickel–Ritov–Tsybakov §3).  All three results
are proved in this file (cone constraint via basic inequality + Hölder;
slow rate via cone + Cauchy–Schwarz + RE → quadratic-in-`‖h_S‖₁`). -/

/-- **Lasso cone constraint** (Bickel–Ritov–Tsybakov 2009, Lemma B.1).
On the *good event* `𝒜 = { ∀ j, |(1/n) ∑_i X_{ij} ε_i| ≤ λ/2 }`, where
`ε i = y i - ∑ j X_{ij} β*_j`, the error `h = bh - β*` satisfies
`‖h_{Sᶜ}‖₁ ≤ 3 ‖h_S‖₁` where `S = supp(β*)`.

The proof combines the basic inequality (above) with Hölder
`|⟨X^Tε/n, h⟩| ≤ ‖X^Tε/n‖_∞ · ‖h‖₁ ≤ (λ/2) ‖h‖₁` and the decomposition
`‖bh‖₁ = ‖bh_S‖₁ + ‖bh_{Sᶜ}‖₁`, then triangle/reverse triangle on `S`. -/
theorem lasso_cone_constraint
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (_hlam : 0 < lam)
    (bh β_star : Fin p → ℝ) (_hbh : IsLassoEstimator X y lam bh)
    (S : Finset (Fin p)) (_hsupp : ∀ i ∉ S, β_star i = 0)
    (_hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam / 2) :
    (∑ i ∈ Finset.univ \ S, |bh i - β_star i|) ≤
      3 * (∑ i ∈ S, |bh i - β_star i|) := by
  -- Step 1: Apply the basic inequality.
  have hbasic := lasso_basic_inequality X y lam bh β_star _hbh
  -- Step 2: ‖β*‖₁ = ∑_{i ∈ S} |β* i|  (since β* = 0 off S).
  have hbs_split : l1Norm β_star = ∑ i ∈ S, |β_star i| := by
    rw [l1Norm_split β_star S]
    have h_off : ∑ i ∈ Finset.univ \ S, |β_star i| = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      rw [_hsupp i hi, abs_zero]
    rw [h_off, add_zero]
  -- Step 3: Decompose ‖bh‖₁ = ∑_S |bh| + ∑_{Sᶜ} |bh|.
  have hbh_split : l1Norm bh = (∑ i ∈ S, |bh i|) + (∑ i ∈ Finset.univ \ S, |bh i|) :=
    l1Norm_split bh S
  -- Step 4: On Sᶜ, β* = 0, so |bh i| = |bh i - β_star i|.
  have h_eq_off : ∑ i ∈ Finset.univ \ S, |bh i|
                = ∑ i ∈ Finset.univ \ S, |bh i - β_star i| := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    rw [_hsupp i hi, sub_zero]
  -- Step 5: Reverse triangle on S: ∑_S |β*| - ∑_S |bh - β*| ≤ ∑_S |bh|.
  have h_rev_tri :
      (∑ i ∈ S, |β_star i|) - (∑ i ∈ S, |bh i - β_star i|) ≤ ∑ i ∈ S, |bh i| := by
    rw [sub_le_iff_le_add, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hbi : β_star i = bh i - (bh i - β_star i) := by ring
    nth_rewrite 1 [hbi]
    exact abs_sub _ _
  -- Step 6: Cross-term identity.
  -- (1/n) ∑_i (y_i - X·β*)_i · (X(bh-β*))_i = ∑_j ((1/n) ∑_i X_ij · ε_i) · (bh_j - β*_j).
  have hcross_eq :
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j))) =
      ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
              * (bh j - β_star j) := by
    have lhs_eq :
        (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                                (∑ j, X i j * (bh j - β_star j))) =
        ∑ i, ∑ j, (1 / (n : ℝ)) *
            (X i j * (y i - ∑ k, X i k * β_star k) * (bh j - β_star j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have rhs_eq :
        ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                * (bh j - β_star j) =
        ∑ j, ∑ i, (1 / (n : ℝ)) *
            (X i j * (y i - ∑ k, X i k * β_star k) * (bh j - β_star j)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [lhs_eq, rhs_eq, Finset.sum_comm]
  -- Step 7: Hölder bound — the cross term ≤ (λ/2) · ‖bh - β*‖₁.
  have hholder :
      ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
              * (bh j - β_star j)
        ≤ (lam / 2) * ∑ j, |bh j - β_star j| := by
    calc ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)
        ≤ |∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)| := le_abs_self _
      _ ≤ ∑ j, |((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k)|
              * |bh j - β_star j| := Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ ≤ ∑ j, (lam / 2) * |bh j - β_star j| := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (_hε j) (abs_nonneg _))
      _ = (lam / 2) * ∑ j, |bh j - β_star j| := by rw [← Finset.mul_sum]
  -- Step 8: Q := (1/(2n)) ‖X h‖² ≥ 0.
  have hQ_nn : 0 ≤ (1 / (2 * (n : ℝ))) *
                  ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    apply mul_nonneg
    · have : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      positivity
    · apply Finset.sum_nonneg; intros; positivity
  -- Step 9: Combine.
  set hS : ℝ := ∑ i ∈ S, |bh i - β_star i| with hhS_def
  set hSc : ℝ := ∑ i ∈ Finset.univ \ S, |bh i - β_star i| with hhSc_def
  set bS : ℝ := ∑ i ∈ S, |β_star i| with hbS_def
  set bhS : ℝ := ∑ i ∈ S, |bh i| with hbhS_def
  have h_l1 : (∑ j, |bh j - β_star j|) = hS + hSc := by
    have := l1Norm_split (fun i => bh i - β_star i) S
    unfold l1Norm at this
    exact this
  have hbh_split2 : l1Norm bh = bhS + hSc := by
    rw [hbh_split, h_eq_off]
  have h_bh_ge : bS - hS ≤ bhS := h_rev_tri
  rw [hbs_split, hbh_split2] at hbasic
  have hcross_bd :
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j))) ≤ (lam / 2) * (hS + hSc) := by
    rw [hcross_eq]
    have := hholder
    rw [h_l1] at this
    exact this
  -- Combine + drop Q ≥ 0:
  have hkey : lam * (bhS + hSc) ≤ (lam / 2) * (hS + hSc) + lam * bS := by
    linarith [hbasic, hQ_nn, hcross_bd]
  have hmul : lam * ((bS - hS) + hSc) ≤ lam * (bhS + hSc) := by
    apply mul_le_mul_of_nonneg_left _ _hlam.le
    linarith
  have hkey2 : lam * ((bS - hS) + hSc) ≤ (lam / 2) * (hS + hSc) + lam * bS := by linarith
  -- Goal: hSc ≤ 3 · hS.  Multiply through by 2 and divide by lam > 0.
  change hSc ≤ 3 * hS
  nlinarith [hkey2, _hlam]

/-- **Lasso slow rate** (Bickel–Ritov–Tsybakov 2009, Theorem 7.2).
Under the Restricted Eigenvalue condition `RE(s, κ)` and on the good
event from `lasso_cone_constraint`, the prediction error and the ℓ¹
estimation error are jointly bounded by `16 s λ² / κ²`. -/
theorem lasso_slow_rate
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ) (_hlam : 0 < lam)
    (bh β_star : Fin p → ℝ) (s : ℕ) (κ : ℝ) (_hκ : 0 < κ)
    (_hbh : IsLassoEstimator X y lam bh)
    (_hSparse : Statlean.HDStats.IsSparse s β_star)
    (_hRE : RestrictedEigenvalue X s κ)
    (_hε : ∀ j, |(1 / (n : ℝ)) *
                ∑ i, X i j * (y i - ∑ k, X i k * β_star k)| ≤ lam / 2) :
    (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam * l1Norm (fun i => bh i - β_star i) ≤
      16 * s * lam ^ 2 / κ ^ 2 := by
  -- Set support of β*
  set S : Finset (Fin p) := Statlean.HDStats.support β_star with hS_def
  have hS_card : S.card ≤ s := _hSparse
  have hsupp : ∀ i ∉ S, β_star i = 0 := by
    intro i hi
    simp only [hS_def, Statlean.HDStats.support, Finset.mem_filter, Finset.mem_univ,
      true_and, not_not] at hi
    exact hi
  -- Apply cone constraint
  have hcone : (∑ i ∈ Finset.univ \ S, |bh i - β_star i|) ≤
               3 * (∑ i ∈ S, |bh i - β_star i|) :=
    lasso_cone_constraint X y lam _hlam bh β_star _hbh S hsupp _hε
  -- Apply RE
  have hRE_inst : κ ^ 2 * (∑ i ∈ S, (bh i - β_star i) ^ 2) ≤
        (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2 := by
    refine _hRE (fun i => bh i - β_star i) S hS_card ?_
    exact hcone
  -- Abbreviations
  set h : Fin p → ℝ := fun i => bh i - β_star i with hh_def
  set Q : ℝ := (1 / (n : ℝ)) * ∑ i, (∑ j, X i j * h j) ^ 2 with hQ_def
  set hS1 : ℝ := ∑ i ∈ S, |h i| with hhS1_def
  set hSc1 : ℝ := ∑ i ∈ Finset.univ \ S, |h i| with hhSc1_def
  set hS2sq : ℝ := ∑ i ∈ S, (h i) ^ 2 with hhS2sq_def
  -- Reformulate
  have hcone' : hSc1 ≤ 3 * hS1 := hcone
  have hRE' : κ ^ 2 * hS2sq ≤ Q := hRE_inst
  have hQ_nn : 0 ≤ Q := by
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg; intros; positivity
  have hhS1_nn : 0 ≤ hS1 := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hhSc1_nn : 0 ≤ hSc1 := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hhS2sq_nn : 0 ≤ hS2sq := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- ‖h‖₁ = hS1 + hSc1
  have hl1_split : l1Norm h = hS1 + hSc1 := l1Norm_split h S
  -- Cauchy-Schwarz: hS1² ≤ S.card · hS2sq
  have hCS : hS1 ^ 2 ≤ (S.card : ℝ) * hS2sq := by
    have hCS_raw : (∑ i ∈ S, 1 * |h i|) ^ 2 ≤
        (∑ i ∈ S, (1 : ℝ) ^ 2) * (∑ i ∈ S, |h i| ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => 1) (fun i => |h i|)
    have hsimp1 : ∑ i ∈ S, 1 * |h i| = hS1 := by
      simp [hhS1_def]
    have hsimp2 : ∑ i ∈ S, (1 : ℝ) ^ 2 = (S.card : ℝ) := by
      simp
    have hsimp3 : ∑ i ∈ S, |h i| ^ 2 = hS2sq := by
      apply Finset.sum_congr rfl
      intro i _; rw [sq_abs]
    rw [hsimp1, hsimp2, hsimp3] at hCS_raw
    exact hCS_raw
  -- κ² · hS1² ≤ S.card · Q
  have hkey1 : (κ : ℝ) ^ 2 * hS1 ^ 2 ≤ (S.card : ℝ) * Q := by
    calc (κ : ℝ) ^ 2 * hS1 ^ 2
        ≤ κ ^ 2 * ((S.card : ℝ) * hS2sq) := by
          apply mul_le_mul_of_nonneg_left hCS; positivity
      _ = (S.card : ℝ) * (κ ^ 2 * hS2sq) := by ring
      _ ≤ (S.card : ℝ) * Q := by
          apply mul_le_mul_of_nonneg_left hRE'
          exact_mod_cast Nat.zero_le _
  -- κ² · hS1² ≤ s · Q
  have hkey2 : (κ : ℝ) ^ 2 * hS1 ^ 2 ≤ (s : ℝ) * Q := by
    refine hkey1.trans ?_
    apply mul_le_mul_of_nonneg_right _ hQ_nn
    exact_mod_cast hS_card
  -- Oracle inequality: Q + λ‖h‖₁ ≤ 4λ·hS1
  -- Derive via basic inequality.
  have hbasic := lasso_basic_inequality X y lam bh β_star _hbh
  have hbs_split : l1Norm β_star = ∑ i ∈ S, |β_star i| := by
    rw [l1Norm_split β_star S]
    have h_off : ∑ i ∈ Finset.univ \ S, |β_star i| = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      rw [hsupp i hi, abs_zero]
    rw [h_off, add_zero]
  have h_eq_off : ∑ i ∈ Finset.univ \ S, |bh i|
                = ∑ i ∈ Finset.univ \ S, |bh i - β_star i| := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
    rw [hsupp i hi, sub_zero]
  have hbh_split : l1Norm bh = (∑ i ∈ S, |bh i|) + hSc1 := by
    rw [l1Norm_split bh S, h_eq_off]
  have h_rev_tri :
      (∑ i ∈ S, |β_star i|) - hS1 ≤ ∑ i ∈ S, |bh i| := by
    rw [sub_le_iff_le_add, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hbi : β_star i = bh i - (bh i - β_star i) := by ring
    nth_rewrite 1 [hbi]
    exact abs_sub _ _
  -- Cross-term identity
  have hcross_eq :
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j))) =
      ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
              * (bh j - β_star j) := by
    have lhs_eq :
        (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                                (∑ j, X i j * (bh j - β_star j))) =
        ∑ i, ∑ j, (1 / (n : ℝ)) *
            (X i j * (y i - ∑ k, X i k * β_star k) * (bh j - β_star j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    have rhs_eq :
        ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                * (bh j - β_star j) =
        ∑ j, ∑ i, (1 / (n : ℝ)) *
            (X i j * (y i - ∑ k, X i k * β_star k) * (bh j - β_star j)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [lhs_eq, rhs_eq, Finset.sum_comm]
  have hholder :
      ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
              * (bh j - β_star j)
        ≤ (lam / 2) * ∑ j, |bh j - β_star j| := by
    calc ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)
        ≤ |∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)| := le_abs_self _
      _ ≤ ∑ j, |((1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k))
                  * (bh j - β_star j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - ∑ k, X i k * β_star k)|
              * |bh j - β_star j| := Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ ≤ ∑ j, (lam / 2) * |bh j - β_star j| := Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_right (_hε j) (abs_nonneg _))
      _ = (lam / 2) * ∑ j, |bh j - β_star j| := by rw [← Finset.mul_sum]
  have h_l1 : (∑ j, |bh j - β_star j|) = hS1 + hSc1 := by
    have := l1Norm_split (fun i => bh i - β_star i) S
    unfold l1Norm at this
    exact this
  have hcross_bd :
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j))) ≤
      (lam / 2) * (hS1 + hSc1) := by
    rw [hcross_eq]
    have := hholder
    rw [h_l1] at this
    exact this
  have hQ_half_eq : (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
                 = Q / 2 := by
    rw [hQ_def]; ring
  rw [hbs_split, hbh_split] at hbasic
  rw [hQ_half_eq] at hbasic
  have hkey3 : Q / 2 + lam * ((∑ i ∈ S, |bh i|) + hSc1) ≤
                (lam / 2) * (hS1 + hSc1) + lam * (∑ i ∈ S, |β_star i|) := by
    linarith [hbasic, hcross_bd]
  have hkey4 : Q / 2 + lam * (((∑ i ∈ S, |β_star i|) - hS1) + hSc1) ≤
                (lam / 2) * (hS1 + hSc1) + lam * (∑ i ∈ S, |β_star i|) := by
    have hmono : lam * (((∑ i ∈ S, |β_star i|) - hS1) + hSc1) ≤
                  lam * ((∑ i ∈ S, |bh i|) + hSc1) := by
      apply mul_le_mul_of_nonneg_left _ _hlam.le
      linarith
    linarith
  -- Oracle inequality: Q + λ‖h‖₁ ≤ 4λ·hS1
  have hOracle : Q + lam * (hS1 + hSc1) ≤ 4 * lam * hS1 := by
    nlinarith [hkey4, hQ_nn, hhS1_nn, hhSc1_nn, _hlam]
  have hOracle' : Q + lam * l1Norm h ≤ 4 * lam * hS1 := by
    rw [hl1_split]; exact hOracle
  -- Solve the quadratic
  set T : ℝ := Q + lam * l1Norm h with hT_def
  have hT_nn : 0 ≤ T := by
    have : 0 ≤ lam * l1Norm h := mul_nonneg _hlam.le (l1Norm_nonneg h)
    linarith
  have hT_bound : T ≤ 4 * lam * hS1 := hOracle'
  have hT_Q_le : Q ≤ T := by
    have : 0 ≤ lam * l1Norm h := mul_nonneg _hlam.le (l1Norm_nonneg h)
    linarith
  have hs_nn : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le _
  have hκ2_pos : 0 < κ ^ 2 := by positivity
  have hκ2_nn : 0 ≤ κ ^ 2 := hκ2_pos.le
  have hkey5 : (κ : ℝ) ^ 2 * hS1 ^ 2 ≤ (s : ℝ) * T := by
    have step : (κ : ℝ) ^ 2 * hS1 ^ 2 ≤ (s : ℝ) * Q := hkey2
    have : (s : ℝ) * Q ≤ (s : ℝ) * T := mul_le_mul_of_nonneg_left hT_Q_le hs_nn
    linarith
  have hT2 : T ^ 2 ≤ 16 * lam ^ 2 * hS1 ^ 2 := by
    have hsq : T * T ≤ (4 * lam * hS1) * (4 * lam * hS1) :=
      mul_self_le_mul_self hT_nn hT_bound
    have hL : T * T = T ^ 2 := (sq T).symm
    have hR : (4 * lam * hS1) * (4 * lam * hS1) = 16 * lam ^ 2 * hS1 ^ 2 := by ring
    linarith
  -- κ² · T² ≤ 16 s λ² · T
  have hT_quad_κ : κ ^ 2 * T ^ 2 ≤ 16 * s * lam ^ 2 * T := by
    have step_a : κ ^ 2 * T ^ 2 ≤ κ ^ 2 * (16 * lam ^ 2 * hS1 ^ 2) :=
      mul_le_mul_of_nonneg_left hT2 hκ2_nn
    have step_b : κ ^ 2 * (16 * lam ^ 2 * hS1 ^ 2) = 16 * lam ^ 2 * (κ ^ 2 * hS1 ^ 2) := by ring
    have step_c : 16 * lam ^ 2 * (κ ^ 2 * hS1 ^ 2) ≤ 16 * lam ^ 2 * ((s : ℝ) * T) := by
      have hcoef_nn : 0 ≤ 16 * lam ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hkey5 hcoef_nn
    have step_d : 16 * lam ^ 2 * ((s : ℝ) * T) = 16 * s * lam ^ 2 * T := by ring
    linarith
  have hC_nn : 0 ≤ 16 * s * lam ^ 2 / κ ^ 2 := by positivity
  have hT_quad : T ^ 2 ≤ (16 * s * lam ^ 2 / κ ^ 2) * T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ2_pos]
    have h_rw : T ^ 2 * κ ^ 2 = κ ^ 2 * T ^ 2 := by ring
    linarith [hT_quad_κ]
  rcases eq_or_lt_of_le hT_nn with hT_zero | hT_pos
  · rw [← hT_zero]; exact hC_nn
  · have hT_sq : T * T ≤ (16 * s * lam ^ 2 / κ ^ 2) * T := by
      have h_eq : T ^ 2 = T * T := sq T
      linarith [hT_quad]
    have hC_step : T * T ≤ T * (16 * s * lam ^ 2 / κ ^ 2) := by
      have hcomm_R : (16 * s * lam ^ 2 / κ ^ 2) * T = T * (16 * s * lam ^ 2 / κ ^ 2) :=
        mul_comm _ _
      linarith
    exact le_of_mul_le_mul_left hC_step hT_pos

end Statlean.Regression

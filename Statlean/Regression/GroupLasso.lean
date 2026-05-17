import Statlean.Regression.Lasso

/-!
# Group Lasso (Yuan–Lin 2006)

Group Lasso solves
```
  min_β  (1/(2n))‖y - Xβ‖² + λ · ‖β‖_{2,1}
```
where `‖β‖_{2,1} := ∑_g ‖β_{G_g}‖₂` for a partition `G_1, …, G_G ⊆ {1,…,p}`.
The penalty encourages **group sparsity**: entire groups of coefficients
are simultaneously driven to zero.  When every group is a singleton, the
penalty reduces to the ordinary ℓ¹ norm and Group Lasso reduces to Lasso.

## Main definitions

* `restrictedL2Sq β g` — `∑ i ∈ g, (β i)²`, the squared ℓ² norm on `g`.
* `restrictedL2Norm β g` — `√(restrictedL2Sq β g)`.
* `groupL21Norm groups β` — the mixed `ℓ_{2,1}` group penalty.
* `groupLassoLoss X y lam groups β` — full objective.
* `IsGroupLassoEstimator X y lam groups bh` — minimiser predicate.

## Main results

* `groupL21Norm_nonneg`, `groupL21Norm_zero` — basic norm properties.
* `IsGroupLassoEstimator.loss_le` — optimality projection.
* `group_lasso_basic_inequality` — algebraic identity at the optimiser
  (Group Lasso analogue of Bickel–Ritov–Tsybakov).

## References

* Yuan, Lin, *Model selection and estimation in regression with grouped
  variables*, JRSS B (2006).
* Lounici–Pontil–van de Geer–Tsybakov, *Oracle inequalities and optimal
  inference under group sparsity*, Ann. Statist. (2011).
-/

namespace Statlean.Regression

open scoped BigOperators

variable {n p G : ℕ}

/-! ### Group ℓ²-restricted norms -/

/-- Squared ℓ² norm restricted to a subset `g ⊆ Fin p`. -/
def restrictedL2Sq (β : Fin p → ℝ) (g : Finset (Fin p)) : ℝ :=
  ∑ i ∈ g, (β i) ^ 2

@[simp] lemma restrictedL2Sq_nonneg (β : Fin p → ℝ) (g : Finset (Fin p)) :
    0 ≤ restrictedL2Sq β g := by
  unfold restrictedL2Sq; positivity

/-- ℓ² norm restricted to a subset (square root of `restrictedL2Sq`). -/
noncomputable def restrictedL2Norm (β : Fin p → ℝ) (g : Finset (Fin p)) : ℝ :=
  Real.sqrt (restrictedL2Sq β g)

@[simp] lemma restrictedL2Norm_nonneg (β : Fin p → ℝ) (g : Finset (Fin p)) :
    0 ≤ restrictedL2Norm β g := Real.sqrt_nonneg _

@[simp] lemma restrictedL2Norm_zero (g : Finset (Fin p)) :
    restrictedL2Norm (fun _ : Fin p => (0 : ℝ)) g = 0 := by
  unfold restrictedL2Norm restrictedL2Sq
  simp

/-! ### Mixed ℓ_{2,1} group penalty -/

/-- **Mixed `ℓ_{2,1}` group norm**: `∑_g ‖β_{G_g}‖₂`. -/
noncomputable def groupL21Norm
    (groups : Fin G → Finset (Fin p)) (β : Fin p → ℝ) : ℝ :=
  ∑ g, restrictedL2Norm β (groups g)

lemma groupL21Norm_nonneg (groups : Fin G → Finset (Fin p)) (β : Fin p → ℝ) :
    0 ≤ groupL21Norm groups β := by
  unfold groupL21Norm
  exact Finset.sum_nonneg (fun g _ => restrictedL2Norm_nonneg _ _)

@[simp] lemma groupL21Norm_zero (groups : Fin G → Finset (Fin p)) :
    groupL21Norm groups (fun _ : Fin p => (0 : ℝ)) = 0 := by
  unfold groupL21Norm
  simp

/-! ### Group Lasso objective and estimator -/

/-- The Group Lasso objective:
`(1/(2n)) ‖y − Xβ‖² + λ · ‖β‖_{2,1}`. -/
noncomputable def groupLassoLoss (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (groups : Fin G → Finset (Fin p)) (β : Fin p → ℝ) : ℝ :=
  (1 / (2 * (n : ℝ))) * ∑ i, (y i - ∑ j, X i j * β j) ^ 2
    + lam * groupL21Norm groups β

/-- A vector `bh` is a **Group Lasso estimator** if it minimises
`groupLassoLoss X y lam groups`. -/
def IsGroupLassoEstimator (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (groups : Fin G → Finset (Fin p)) (bh : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, groupLassoLoss X y lam groups bh ≤ groupLassoLoss X y lam groups β

/-- **Optimality projection**: a group lasso estimator satisfies
`groupLassoLoss X y λ groups bh ≤ groupLassoLoss X y λ groups β` for every `β`. -/
lemma IsGroupLassoEstimator.loss_le
    {X : Fin n → Fin p → ℝ} {y : Fin n → ℝ} {lam : ℝ}
    {groups : Fin G → Finset (Fin p)} {bh : Fin p → ℝ}
    (h : IsGroupLassoEstimator X y lam groups bh) (β : Fin p → ℝ) :
    groupLassoLoss X y lam groups bh ≤ groupLassoLoss X y lam groups β :=
  h β

/-! ### Basic inequality (Group Lasso analogue of BRT 2009) -/

/-- **Group Lasso basic inequality** (Yuan–Lin 2006; Lounici–Pontil–van de Geer–
Tsybakov 2011). If `bh` minimises the Group Lasso objective and `β*` is any
reference vector, writing `h := bh − β*` and `ε i := y i − ∑ j X_{ij} β*_j` for
the noise relative to `β*`, then
```
  (1/(2n)) · ‖X h‖² + λ · ‖bh‖_{2,1} ≤ (1/n) · ⟨ε, X h⟩ + λ · ‖β*‖_{2,1} .
```
The proof is a pure algebraic identity from `groupLassoLoss bh ≤ groupLassoLoss β*`:
expanding `(y − X bh)² = (ε − X h)² = ε² − 2 ε · X h + (X h)²` row by row.
The group penalty appears linearly with the same coefficient `λ` on both
sides of the optimality bound, so it propagates unchanged to the conclusion
(no analogue of `unfold l1Norm` is required). -/
theorem group_lasso_basic_inequality
    (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (groups : Fin G → Finset (Fin p))
    (bh β_star : Fin p → ℝ)
    (hbh : IsGroupLassoEstimator X y lam groups bh) :
    (1 / (2 * (n : ℝ))) * ∑ i, (∑ j, X i j * (bh j - β_star j)) ^ 2
        + lam * groupL21Norm groups bh ≤
      (1 / (n : ℝ)) * (∑ i, (y i - ∑ j, X i j * β_star j) *
                              (∑ j, X i j * (bh j - β_star j)))
        + lam * groupL21Norm groups β_star := by
  -- Specialise optimality to the reference vector β*.
  have hopt := hbh β_star
  unfold groupLassoLoss at hopt
  -- Algebraic identity for each row.
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
  -- Distribute (1/(2n)) and identify (1/(2n))·2 = 1/n.  Holds even at n = 0.
  have hsplit :
      (1 / (2 * (n : ℝ))) * (A - 2 * B + C) =
        (1 / (2 * (n : ℝ))) * A - (1 / (n : ℝ)) * B
          + (1 / (2 * (n : ℝ))) * C := by
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
  rw [hsplit] at hopt
  linarith

end Statlean.Regression

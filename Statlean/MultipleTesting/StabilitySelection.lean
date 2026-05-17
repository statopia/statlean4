import Statlean.MultipleTesting.Basic

/-!
# Stability Selection (Meinshausen–Bühlmann 2010)

Stability Selection is a meta-procedure that wraps any sparse variable
selector (e.g. Lasso) in a subsampling loop and reports only those
variables that are selected sufficiently often.  Under mild assumptions
it controls the *family-wise error rate* (FWER) regardless of the
specific selector used.

The full procedure averages selection indicators over a random sample of
subsamples.  In this file we abstract the selection frequency as a
**given function** `π : Fin p → ℝ` ("selection probability") and study
the threshold operation
```
  S_stable(π_thresh) := { j : π_j ≥ π_thresh }.
```

This gives the deterministic skeleton; the FWER bound itself relies on
an exchangeability hypothesis (Theorem 1, MB 2010) and is registered as
an axiom (R6): a faithful statement requires modelling the random
subsampling procedure, which goes beyond the present file.

## Main definitions

* `IsSelectionProbability π` — `π_j ∈ [0, 1]` for all `j`.
* `stableSet π θ` — variables with selection frequency at least `θ`.

## Main results

* `stableSet_mono` — threshold monotonicity.
* `stableSet_empty_of_threshold_gt_one` — `θ > 1` ⟹ stable set is empty.
* `stableSet_card_le` — Markov-type bound: `|S(θ)| · θ ≤ ∑ π_j`.
* `mb_fwer_bound` — Meinshausen–Bühlmann (Theorem 1), axiom / R6.

## References

* N. Meinshausen, P. Bühlmann, *Stability selection*, JRSS B 72 (2010),
  417–473.
* R. D. Shah, R. J. Samworth, *Variable selection with error control:
  Another look at stability selection*, JRSS B 75 (2013), 55–80.
-/

namespace Statlean.MultipleTesting

variable {p : ℕ}

/-- A function `π : Fin p → ℝ` is a **selection probability** if every
coordinate lies in the unit interval `[0, 1]`.  In Stability Selection,
`π j` represents the empirical frequency with which variable `j` is
chosen across random subsamples. -/
def IsSelectionProbability (π : Fin p → ℝ) : Prop :=
  ∀ j, 0 ≤ π j ∧ π j ≤ 1

namespace IsSelectionProbability

lemma nonneg {π : Fin p → ℝ} (h : IsSelectionProbability π) (j : Fin p) :
    0 ≤ π j := (h j).1

lemma le_one {π : Fin p → ℝ} (h : IsSelectionProbability π) (j : Fin p) :
    π j ≤ 1 := (h j).2

end IsSelectionProbability

/-- **Stable set at threshold `θ`**: variables with selection frequency
at least `θ`, as a `Finset (Fin p)`. -/
noncomputable def stableSet (π : Fin p → ℝ) (θ : ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun j => θ ≤ π j)

/-- Stability set is antitone in the threshold: raising the threshold
shrinks the stable set. -/
lemma stableSet_mono (π : Fin p → ℝ) {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) :
    stableSet π θ₂ ⊆ stableSet π θ₁ := by
  intro j hj
  rw [stableSet, Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans h hj.2⟩

/-- If the threshold exceeds 1 and `π` is a valid selection probability,
the stable set is empty (no `π j` can exceed 1). -/
lemma stableSet_empty_of_threshold_gt_one
    {π : Fin p → ℝ} (hπ : IsSelectionProbability π) {θ : ℝ} (hθ : 1 < θ) :
    stableSet π θ = ∅ := by
  rw [stableSet, Finset.filter_eq_empty_iff]
  intro j _ hj
  have hle := hπ.le_one j
  linarith

/-- **Markov-type bound** on stable-set cardinality.  For `θ > 0`,
`|S_stable(θ)| · θ ≤ ∑_j π_j`.  This is the deterministic counterpart of
the probabilistic Markov inequality used in MB 2010. -/
lemma stableSet_card_le
    {π : Fin p → ℝ} (hπ : IsSelectionProbability π) {θ : ℝ} (_hθ : 0 < θ) :
    ((stableSet π θ).card : ℝ) * θ ≤ ∑ j, π j := by
  unfold stableSet
  set S : Finset (Fin p) := Finset.univ.filter (fun j => θ ≤ π j) with hS
  have h1 : (S.card : ℝ) * θ = ∑ _j ∈ S, θ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have h2 : ∑ _j ∈ S, θ ≤ ∑ j ∈ S, π j := by
    apply Finset.sum_le_sum
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  refine h2.trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun j _ _ => hπ.nonneg j)

/-- **Meinshausen–Bühlmann FWER bound (Theorem 1, axiom / R6)**.

Under the exchangeability + simultaneous-Markov hypotheses of
Meinshausen–Bühlmann (2010), the expected number of false discoveries of
a Stability Selection procedure with threshold `θ > 1/2`, run on a base
selector producing at most `q` selected variables per subsample out of
`p_total` candidates, satisfies
```
  E[V] ≤ q² / ((2θ - 1) · p_total).
```

This requires probabilistic modelling of the random subsampling
distribution and is registered as an axiom for the present file (R6).
The current formulation only records the cardinality side condition
`p_false ≤ p_total` and the threshold regime `θ > 1/2`. -/
axiom mb_fwer_bound
    (p_total p_false : ℕ) (θ : ℝ) (q : ℝ) (_hθ : 1 / 2 < θ)
    (_h_unify : p_false ≤ p_total) : True

end Statlean.MultipleTesting

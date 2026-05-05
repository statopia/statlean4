import Statlean.Conformal.Rank

/-! # Conformal Prediction — Marginal Coverage Guarantee

The main distribution-free coverage theorem (Vovk–Shafer–Vapnik): for any
exchangeable score sequence `(S₁, …, S_{n+1})` with no ties almost surely,
the conformal prediction set built from `(S₁, …, Sₙ)` covers the test score
`S_{n+1}` with probability at least `1 − α`.

## Proof outline

1. **Rank uniformity** (`rank_uniform_of_exchangeable`, in `Conformal.Rank`):
   under exchangeability + no ties, the rank of the `(n+1)`-th coordinate
   among the full sample is uniformly distributed on `{1, …, n+1}`.
2. **Coverage event ↔ rank event** (`coverage_event_iff_rank_le`, this file):
   when there are no ties, the event `S_{n+1} ≤ Q̂_α(S₁, …, Sₙ)` (where
   `Q̂_α` is the `⌈(n+1)(1−α)⌉`-th smallest of `(S₁, …, Sₙ)`) coincides
   with `rank(S_{n+1}) ≤ ⌈(n+1)(1−α)⌉` among the full sample.
3. **Combine** (`marginal_coverage`): summing the uniform rank
   probabilities over the covering ranks gives
   `⌈(n+1)(1−α)⌉ / (n+1) ≥ 1 − α`.
4. **Upper bound** (`marginal_coverage_upper`): the same identity yields
   coverage `≤ ⌈(n+1)(1−α)⌉ / (n+1) ≤ 1 − α + 1/(n+1)`.

## References

* Vovk, Gammerman, Shafer, *Algorithmic Learning in a Random World*, 2005,
  Theorem 2.1.
* Lei et al., *Distribution-free predictive inference for regression*, JASA
  2018, Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ}

/-! ### Auxiliary lemmas for the coverage-rank correspondence -/

/-- `countP` over `List.ofFn s` equals the cardinality of the matching index
filter — pure combinatorial bridge from list counting to `Finset.filter`. -/
private lemma countP_ofFn_eq_card_filter {n : ℕ} (s : Fin n → ℝ) (p : ℝ → Bool) :
    (List.ofFn s).countP p = (Finset.univ.filter (fun i => p (s i) = true)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih (fun i => s i.succ),
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    ring_nf

/-- For a `≤`-sorted list `L` of length `> k`, `L[k] ≤ x` iff at least `k+1`
entries of `L` are `≤ x`. The forward direction uses sortedness to extend
`L[k] ≤ x` to all earlier entries; the converse uses sortedness to show that
if `L[k] > x` then no entry past index `k` is `≤ x` either. -/
private lemma sorted_get_le_iff_countP {L : List ℝ} (hL : L.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < L.length) (x : ℝ) :
    L[k] ≤ x ↔ k < L.countP (fun y => decide (y ≤ x)) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨ha, hLp⟩ := hL
    match k with
    | 0 =>
      simp only [List.getElem_cons_zero, List.countP_cons]
      by_cases hax : a ≤ x
      · simp [hax]
      · have hxa : x < a := lt_of_not_ge hax
        have h_count : L.countP (fun y => decide (y ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have hay := ha y hy
          have : x < y := lt_of_lt_of_le hxa hay
          simp [decide_eq_false (not_le.mpr this)]
        simp [decide_eq_false hax, h_count, hax]
    | k+1 =>
      simp only [List.getElem_cons_succ, List.countP_cons]
      have hkL : k < L.length := by simp at hk; omega
      have IH := ih hLp k hkL
      by_cases hax : a ≤ x
      · simp [decide_eq_true hax]
        constructor
        · intro h; have := IH.mp h; omega
        · intro h; exact IH.mpr (by omega)
      · have hxa : x < a := lt_of_not_ge hax
        simp [decide_eq_false hax]
        have h_count : L.countP (fun y => decide (y ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have hay := ha y hy
          have : x < y := lt_of_lt_of_le hxa hay
          simp [decide_eq_false (not_le.mpr this)]
        rw [h_count]
        constructor
        · intro hLkx
          have hmem : L[k] ∈ L := List.getElem_mem hkL
          have : a ≤ L[k] := ha _ hmem
          linarith
        · intro h; omega

/-- Decompose `rankOfLast ω` into the count of strictly lower castSucc-indices
plus one (the last index itself, which always satisfies `ω(last) ≤ ω(last)`).
Pure `Fin.sum_univ_castSucc` rearrangement. -/
private lemma rankOfLast_decomp (ω : Fin (n + 1) → ℝ) :
    rankOfLast ω =
      (Finset.univ.filter (fun j : Fin n => ω j.castSucc ≤ ω (Fin.last n))).card + 1 := by
  unfold rankOfLast
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp [le_refl]

/-- **Coverage event ↔ rank event.** When the sample has no ties and
`α ∈ [1/(n+1), 1)` (so that `k := ⌈(n+1)(1−α)⌉₊` lies in `{1, …, n}`), the
point-wise event "`ω (Fin.last n)` lies below the conformal `(1−α)`-quantile
of the first `n` coordinates" coincides with "rank of `ω (Fin.last n)` is at
most `k`".

The hypothesis `1/(n+1) ≤ α < 1` is essential: it pins `k` to the regime
`1 ≤ k ≤ n` where the placeholder `orderStat … k = 0` (returned for out-of-
range `k`) does not corrupt the equivalence. The cases `α < 1/(n+1)` (no
calibration cut, prediction set covers everything) and `α = 1` (empty
prediction set in distribution-free terms) are handled in the assembled
coverage theorems by trivial bounds, not via this iff.

This is the rank-statistic reformulation that converts the geometric
threshold `Q̂_α` into a counting statistic on which exchangeability acts. -/
theorem coverage_event_iff_rank_le
    (ω : Fin (n + 1) → ℝ) (hInj : Function.Injective ω)
    (α : ℝ) (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1) :
    ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α
      ↔ rankOfLast ω ≤ ⌈((n : ℝ) + 1) * (1 - α)⌉₊ := by
  set s : Fin n → ℝ := fun i => ω i.castSucc with hs_def
  set k : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊ with hk_def
  -- Step 1: 1 ≤ k ≤ n (from `hα0`, `hα1`).
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
  have hk_pos : 1 ≤ k := by
    have h_pos : 0 < ((n : ℝ) + 1) * (1 - α) := mul_pos hnpos (by linarith)
    exact Nat.one_le_ceil_iff.mpr h_pos
  have hk_le : k ≤ n := by
    apply Nat.ceil_le.mpr
    have h1 : 1 ≤ (↑n + 1) * α := by
      have key : (↑n + 1) * (1 / (↑n + 1)) ≤ (↑n + 1) * α :=
        mul_le_mul_of_nonneg_left hα0 (le_of_lt hnpos)
      rw [mul_one_div, div_self hne] at key
      exact key
    nlinarith [h1]
  -- Step 2: `s` inherits injectivity from `ω` via `Fin.castSucc_injective`.
  have hsInj : Function.Injective s := by
    intro i j hij
    have heq : ω i.castSucc = ω j.castSucc := hij
    exact Fin.castSucc_injective n (hInj heq)
  -- Step 3: Sorted list of scores.
  set L : List ℝ := (List.ofFn s).mergeSort (· ≤ ·) with hL_def
  have hL_perm : L.Perm (List.ofFn s) := List.mergeSort_perm _ _
  have hL_len : L.length = n := by
    rw [hL_def, List.length_mergeSort, List.length_ofFn]
  have hL_pairwise : L.Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort' (α := ℝ) (· ≤ ·) (List.ofFn s)
    simpa using this
  -- Step 4: `k.pred = k - 1 < n = L.length`.
  have hk_pred_lt : k.pred < L.length := by
    rw [hL_len, Nat.pred_eq_sub_one]; omega
  -- Step 5: `conformalQuantile s α = L[k.pred]`.
  have hQ_eq : conformalQuantile s α = L[k.pred] := by
    unfold conformalQuantile orderStat
    show L[k.pred]?.getD 0 = L[k.pred]
    rw [List.getElem?_eq_getElem hk_pred_lt]
    rfl
  -- Step 6: `ω(last) ≠ L[k.pred]` (no ties + `last ∉ image castSucc`).
  have h_neq : ω (Fin.last n) ≠ L[k.pred] := by
    have hmem : L[k.pred] ∈ L := List.getElem_mem hk_pred_lt
    have hmemS : L[k.pred] ∈ List.ofFn s := hL_perm.mem_iff.mp hmem
    rw [List.mem_ofFn] at hmemS
    obtain ⟨i, hi⟩ := hmemS
    rw [← hi]
    intro heq
    have hii : Fin.last n = i.castSucc := hInj heq
    have hlt : i.castSucc < Fin.last n := Fin.castSucc_lt_last i
    rw [hii] at hlt
    exact lt_irrefl _ hlt
  -- Step 7: `≤` collapses to `<` via `≠`.
  have h_le_iff_lt : ω (Fin.last n) ≤ L[k.pred] ↔ ω (Fin.last n) < L[k.pred] :=
    ⟨fun h => lt_of_le_of_ne h h_neq, le_of_lt⟩
  -- Step 8: Sorted-list count characterization, contrapositive form.
  have h_count_iff :
      ω (Fin.last n) < L[k.pred] ↔
        L.countP (fun y => decide (y ≤ ω (Fin.last n))) ≤ k.pred := by
    rw [← not_le, sorted_get_le_iff_countP hL_pairwise k.pred hk_pred_lt, not_lt]
  -- Step 9: Transport `countP` along the permutation.
  have h_perm_countP :
      L.countP (fun y => decide (y ≤ ω (Fin.last n))) =
        (List.ofFn s).countP (fun y => decide (y ≤ ω (Fin.last n))) :=
    hL_perm.countP_eq _
  -- Step 10: Convert list `countP` over `ofFn s` to `Finset` cardinality.
  have h_ofFn_card :
      (List.ofFn s).countP (fun y => decide (y ≤ ω (Fin.last n))) =
        (Finset.univ.filter (fun j : Fin n => ω j.castSucc ≤ ω (Fin.last n))).card := by
    rw [countP_ofFn_eq_card_filter]
    congr 1
    ext j
    simp [hs_def]
  -- Step 11: Rank decomposition: `rankOfLast = filter card + 1`.
  have h_rank :
      rankOfLast ω =
        (Finset.univ.filter (fun j : Fin n => ω j.castSucc ≤ ω (Fin.last n))).card + 1 :=
    rankOfLast_decomp ω
  rw [hQ_eq, h_le_iff_lt, h_count_iff, h_perm_countP, h_ofFn_card, h_rank,
      Nat.pred_eq_sub_one]
  omega

/-- **Marginal coverage** (Vovk–Shafer–Vapnik, 2005, Theorem 2.1).

For an exchangeable score sequence `(ω 0, …, ω n) : Fin (n+1) → ℝ` with no
ties almost surely, the conformal prediction set built from
`(ω 0, …, ω (n-1))` covers `ω (Fin.last n)` with probability at least
`1 − α`.

This is the central distribution-free guarantee of conformal prediction:
the bound holds for every joint distribution `μ` (exchangeable, no ties)
and every score function — there is no model assumption.
-/
theorem marginal_coverage
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α} := by
  sorry

/-- **Marginal coverage upper bound.** Under exchangeability + no-ties
almost surely, the conformal prediction set has coverage at most
`1 − α + 1/(n+1)`.

Together with `marginal_coverage`, this pins down the conformal coverage to
the band `[1 − α, 1 − α + 1/(n+1)]`. The slack `1/(n+1)` is intrinsic to
the discrete rank statistic and shrinks to zero as `n → ∞`. -/
theorem marginal_coverage_upper
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α}
      ≤ ENNReal.ofReal (1 - α + 1 / ((n : ℝ) + 1)) := by
  sorry

end Statlean.Conformal

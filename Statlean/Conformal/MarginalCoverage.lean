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

/-! ### Helper lemmas: rank decomposition and coverage = k/(n+1) -/

/-- `rankOfLast ω ≥ 1` always: the index `Fin.last n` itself is in the
defining filter (since `ω(last) ≤ ω(last)`). -/
private lemma rankOfLast_pos (ω : Fin (n + 1) → ℝ) : 1 ≤ rankOfLast ω := by
  unfold rankOfLast
  apply Finset.card_pos.mpr
  exact ⟨Fin.last n, by simp⟩

/-- `rankOfLast ω ≤ n + 1`: bounded by the size of the index set. -/
private lemma rankOfLast_le_succ (ω : Fin (n + 1) → ℝ) : rankOfLast ω ≤ n + 1 := by
  unfold rankOfLast
  calc (Finset.univ.filter (fun i : Fin (n + 1) => ω i ≤ ω (Fin.last n))).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = n + 1 := by simp [Finset.card_univ, Fintype.card_fin]

/-- The level set `{ω | rankOfLast ω = m}` is Borel-measurable. We re-prove
this here because `Statlean.Conformal.measurableSet_rankOfLast_eq` is private
to `Conformal.Rank`. The proof decomposes the set as a finite union over all
candidate filter sets `S` of size `m`. -/
private lemma measurableSet_rankOfLast_eq_loc (m : ℕ) :
    MeasurableSet {ω : Fin (n + 1) → ℝ | rankOfLast ω = m} := by
  unfold rankOfLast
  have heq : {ω : Fin (n + 1) → ℝ |
        (Finset.univ.filter (fun i : Fin (n + 1) => ω i ≤ ω (Fin.last n))).card = m}
      = ⋃ (S : Finset (Fin (n + 1))) (_ : S.card = m),
          {ω | ∀ i, (i ∈ S ↔ ω i ≤ ω (Fin.last n))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    refine ⟨fun h => ⟨Finset.univ.filter (fun i => ω i ≤ ω (Fin.last n)), h, ?_⟩,
            ?_⟩
    · intro i; simp [Finset.mem_filter]
    · rintro ⟨S, hS, hSeq⟩
      have hSet : Finset.univ.filter
          (fun i : Fin (n + 1) => ω i ≤ ω (Fin.last n)) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hSeq i).symm
      rw [hSet]; exact hS
  rw [heq]
  refine MeasurableSet.iUnion (fun S => ?_)
  refine MeasurableSet.iUnion (fun _hS => ?_)
  rw [show {ω : Fin (n + 1) → ℝ | ∀ i, (i ∈ S ↔ ω i ≤ ω (Fin.last n))} =
      ⋂ i, {ω | i ∈ S ↔ ω i ≤ ω (Fin.last n)} from by ext ω; simp]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · have heq' : {ω : Fin (n + 1) → ℝ | i ∈ S ↔ ω i ≤ ω (Fin.last n)}
        = {ω | ω i ≤ ω (Fin.last n)} := by ext ω; simp [hi]
    rw [heq']
    exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply (Fin.last n))
  · have heq' : {ω : Fin (n + 1) → ℝ | i ∈ S ↔ ω i ≤ ω (Fin.last n)}
        = {ω | ¬ (ω i ≤ ω (Fin.last n))} := by ext ω; simp [hi]
    rw [heq']
    exact (measurableSet_le (measurable_pi_apply i)
      (measurable_pi_apply (Fin.last n))).compl

/-- Decompose `{rankOfLast ≤ k}` as a disjoint finite union of rank level
sets, indexed by `m ∈ Finset.range k` mapped to `{rankOfLast = m + 1}`. -/
private lemma rankOfLast_le_eq_iUnion (k : ℕ) :
    {ω : Fin (n + 1) → ℝ | rankOfLast ω ≤ k} =
      ⋃ m ∈ Finset.range k, {ω | rankOfLast ω = m + 1} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := rankOfLast_pos ω
    refine ⟨rankOfLast ω - 1, ?_, ?_⟩ <;> omega
  · rintro ⟨m, _, hrank⟩
    omega

/-- Distinct rank level sets are disjoint. -/
private lemma rank_pairwiseDisjoint (k : ℕ) :
    (Finset.range k : Set ℕ).PairwiseDisjoint
      (fun m : ℕ => {ω : Fin (n + 1) → ℝ | rankOfLast ω = m + 1}) := by
  intro m _ m' _ hmm'
  apply Set.disjoint_iff_inter_eq_empty.mpr
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro h1 h2
  apply hmm'
  omega

/-- **Key combinatorial step.** Under exchangeability + no ties, when
`k ≤ n + 1`, the probability that `rankOfLast` is at most `k` equals
`k / (n + 1)`. This follows from rank uniformity
(`rank_uniform_of_exchangeable`) summed over the `k` values `1, …, k`. -/
private lemma measure_rank_le_eq
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) {k : ℕ} (hk : k ≤ n + 1) :
    μ {ω | rankOfLast ω ≤ k} = (k : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) := by
  rw [rankOfLast_le_eq_iUnion k]
  rw [measure_biUnion_finset (rank_pairwiseDisjoint k)
        (fun m _ => measurableSet_rankOfLast_eq_loc (m + 1))]
  have h_each : ∀ m ∈ Finset.range k,
      μ {ω | rankOfLast ω = m + 1} = ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm_lt : m < n + 1 := by omega
    have := rank_uniform_of_exchangeable hExch hNoTies (⟨m, hm_lt⟩ : Fin (n + 1))
    simpa using this
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_const]
  simp [Finset.card_range, ENNReal.div_eq_inv_mul, mul_comm]

/-! ### Main coverage theorems -/

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
  set k : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊ with hk_def
  -- Step 1: rewrite the coverage event as the rank event using `coverage_event_iff_rank_le`
  -- on the no-ties set.
  have h_event_eq :
      μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α}
        = μ {ω | rankOfLast ω ≤ k} := by
    apply measure_congr
    filter_upwards [hNoTies] with ω hω
    have := coverage_event_iff_rank_le ω hω α hα0 hα1
    exact propext this
  rw [h_event_eq]
  -- Step 2: μ {rankOfLast ≤ k} = k / (n + 1). We need k ≤ n + 1.
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
  have hk_le : k ≤ n := by
    apply Nat.ceil_le.mpr
    have h1 : 1 ≤ (↑n + 1) * α := by
      have key : (↑n + 1) * (1 / (↑n + 1)) ≤ (↑n + 1) * α :=
        mul_le_mul_of_nonneg_left hα0 (le_of_lt hnpos)
      rw [mul_one_div, div_self hne] at key
      exact key
    nlinarith [h1]
  rw [measure_rank_le_eq hExch hNoTies (by omega : k ≤ n + 1)]
  -- Step 3: ofReal (1 - α) ≤ k / (n+1) follows from (n+1)(1-α) ≤ k.
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h_ceil : ((n : ℝ) + 1) * (1 - α) ≤ k := by
    rw [hk_def]; exact Nat.le_ceil _
  have h_real : 1 - α ≤ (k : ℝ) / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hnpos]
    nlinarith [h_ceil]
  rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
        simp [ENNReal.ofReal_natCast, ENNReal.ofReal_one]]
  rw [show ((k : ℝ≥0∞)) = ENNReal.ofReal k by
        simp [ENNReal.ofReal_natCast]]
  rw [← ENNReal.ofReal_div_of_pos hnpos]
  exact ENNReal.ofReal_le_ofReal h_real

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
  set k : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊ with hk_def
  -- Step 1: rewrite the coverage event as the rank event.
  have h_event_eq :
      μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α}
        = μ {ω | rankOfLast ω ≤ k} := by
    apply measure_congr
    filter_upwards [hNoTies] with ω hω
    have := coverage_event_iff_rank_le ω hω α hα0 hα1
    exact propext this
  rw [h_event_eq]
  -- Step 2: μ {rankOfLast ≤ k} = k / (n + 1). We need k ≤ n + 1.
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hnpos
  have hk_le : k ≤ n := by
    apply Nat.ceil_le.mpr
    have h1 : 1 ≤ (↑n + 1) * α := by
      have key : (↑n + 1) * (1 / (↑n + 1)) ≤ (↑n + 1) * α :=
        mul_le_mul_of_nonneg_left hα0 (le_of_lt hnpos)
      rw [mul_one_div, div_self hne] at key
      exact key
    nlinarith [h1]
  rw [measure_rank_le_eq hExch hNoTies (by omega : k ≤ n + 1)]
  -- Step 3: k / (n+1) ≤ ofReal (1 - α + 1/(n+1)) follows from k < (n+1)(1-α) + 1.
  have h1mα : (0 : ℝ) ≤ 1 - α := by linarith
  have h_prod_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) * (1 - α) :=
    mul_nonneg (le_of_lt hnpos) h1mα
  have h_ceil_lt : ((k : ℝ)) < ((n : ℝ) + 1) * (1 - α) + 1 := by
    rw [hk_def]; exact Nat.ceil_lt_add_one h_prod_nn
  have h_real : (k : ℝ) / ((n : ℝ) + 1) ≤ (1 - α) + 1 / ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hnpos]
    have hk_le : (k : ℝ) ≤ ((n : ℝ) + 1) * (1 - α) + 1 := le_of_lt h_ceil_lt
    have heq : ((1 - α) + 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1)
        = ((n : ℝ) + 1) * (1 - α) + 1 := by field_simp
    linarith [heq, hk_le]
  rw [show ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
        simp [ENNReal.ofReal_natCast, ENNReal.ofReal_one]]
  rw [show ((k : ℝ≥0∞)) = ENNReal.ofReal k by
        simp [ENNReal.ofReal_natCast]]
  rw [← ENNReal.ofReal_div_of_pos hnpos]
  exact ENNReal.ofReal_le_ofReal h_real

end Statlean.Conformal

import Statlean.Conformal.Basic

/-! # Conformal Prediction — Rank Uniformity

The combinatorial heart of distribution-free conformal coverage: under
exchangeability of the joint law (and absence of ties almost surely), the
rank of any single coordinate is uniformly distributed over `{1, …, n+1}`.

## Contents

* `Statlean.Conformal.rankOfLast` — the rank of `ω (Fin.last n)` among the
  full sample `(ω 0, …, ω n)`, defined as the count of indices `i` with
  `ω i ≤ ω (Fin.last n)`.
* `Statlean.Conformal.rank_uniform_of_exchangeable` — the central
  combinatorial identity: each rank value `k ∈ {1, …, n+1}` has probability
  exactly `1 / (n+1)` under any exchangeable joint law with no ties almost
  surely.

This file isolates the rank-uniformity argument from the assembled coverage
theorems in `Conformal.MarginalCoverage`, both for clarity (rank statistics
is a self-contained probabilistic identity) and to allow parallel proof
work on the two independent leaf lemmas of the conformal coverage DAG.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ}

/-- The **rank** of `ω (Fin.last n)` among the full sample
`(ω 0, …, ω n) : Fin (n+1) → ℝ`, 1-indexed. Defined as the number of
indices `i` with `ω i ≤ ω (Fin.last n)`. Under no ties, this equals
`1 + #{j : ω j < ω (Fin.last n)}`, the standard rank statistic. -/
noncomputable def rankOfLast (ω : Fin (n + 1) → ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) => ω i ≤ ω (Fin.last n))).card

/-! ### Rank uniformity — combinatorial helpers

We isolate a generalized rank `rankOf j ω` indexed by an arbitrary
coordinate `j`, prove its measurability, and the key transposition
identity that lets exchangeability transport the rank-`(k+1)` event
between any two coordinates. -/

/-- The **generalized rank** of `ω j` in the full sample, 1-indexed.
This recovers `rankOfLast` when `j = Fin.last n`. -/
private noncomputable def rankOf (j : Fin (n + 1)) (ω : Fin (n + 1) → ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) => ω i ≤ ω j)).card

/-- Under any permutation `σ`, `rankOfLast (ω ∘ σ) = rankOf (σ (Fin.last n)) ω`.
Proof: bijection `i ↦ σ i` on `Fin (n+1)`. -/
private lemma rankOfLast_comp_perm (σ : Equiv.Perm (Fin (n + 1)))
    (ω : Fin (n + 1) → ℝ) :
    rankOfLast (fun i => ω (σ i)) = rankOf (σ (Fin.last n)) ω := by
  unfold rankOfLast rankOf
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  · intro a _ b _ hab
    exact σ.injective hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨σ.symm b, ?_, ?_⟩
    · simp [hb]
    · exact σ.apply_symm_apply b

/-- Specialization of `rankOfLast_comp_perm` to the swap with `Fin.last n`. -/
private lemma rankOfLast_swap_last (j : Fin (n + 1)) (ω : Fin (n + 1) → ℝ) :
    rankOfLast (fun i => ω (Equiv.swap j (Fin.last n) i)) = rankOf j ω := by
  rw [rankOfLast_comp_perm]
  congr 1
  exact Equiv.swap_apply_right j (Fin.last n)

/-- The level set `{ω | rankOf j ω = m}` is Borel-measurable. -/
private lemma measurableSet_rankOf_eq (j : Fin (n + 1)) (m : ℕ) :
    MeasurableSet {ω : Fin (n + 1) → ℝ | rankOf j ω = m} := by
  -- Decompose the level set as a union over all candidate Finsets `S` of size `m`
  -- of the events `∀ i, i ∈ S ↔ ω i ≤ ω j`.
  have hUnion : {ω : Fin (n + 1) → ℝ | rankOf j ω = m} =
      ⋃ (S : Finset (Fin (n + 1))) (_ : S.card = m),
        {ω | ∀ i : Fin (n + 1), i ∈ S ↔ ω i ≤ ω j} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨Finset.univ.filter (fun i => ω i ≤ ω j), h, ?_⟩
      intro i
      simp [Finset.mem_filter]
    · rintro ⟨S, hS, hSω⟩
      have hS_eq : S = Finset.univ.filter (fun i => ω i ≤ ω j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hSω i
      rw [rankOf, ← hS_eq, hS]
  rw [hUnion]
  refine MeasurableSet.iUnion (fun S => ?_)
  refine MeasurableSet.iUnion (fun _ => ?_)
  -- The "S-realization" event is a finite intersection of pointwise comparisons.
  have hInter : {ω : Fin (n + 1) → ℝ | ∀ i, i ∈ S ↔ ω i ≤ ω j} =
      ⋂ i : Fin (n + 1), {ω | i ∈ S ↔ ω i ≤ ω j} := by
    ext ω
    simp [Set.mem_iInter]
  rw [hInter]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · have heq : {ω : Fin (n + 1) → ℝ | i ∈ S ↔ ω i ≤ ω j} = {ω | ω i ≤ ω j} := by
      ext ω; simp [hi]
    rw [heq]
    exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  · have heq : {ω : Fin (n + 1) → ℝ | i ∈ S ↔ ω i ≤ ω j} = {ω | ¬ (ω i ≤ ω j)} := by
      ext ω; simp [hi]
    rw [heq]
    exact (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)).compl

private lemma measurableSet_rankOfLast_eq (m : ℕ) :
    MeasurableSet {ω : Fin (n + 1) → ℝ | rankOfLast ω = m} :=
  measurableSet_rankOf_eq (Fin.last n) m

/-- Under exchangeability, the rank-`m` event for any coordinate `j` has the
same probability as the rank-`m` event for the last coordinate. -/
private lemma measure_rankOf_eq_measure_rankOfLast
    {μ : Measure (Fin (n + 1) → ℝ)}
    (hExch : Exchangeable μ) (j : Fin (n + 1)) (m : ℕ) :
    μ {ω | rankOf j ω = m} = μ {ω | rankOfLast ω = m} := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j (Fin.last n)
  have hmap : μ.map (fun ω i => ω (σ i)) = μ := hExch σ
  have hMeas : Measurable (fun ω : Fin (n + 1) → ℝ => fun i => ω (σ i)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (σ i)
  have hSet : MeasurableSet {ω : Fin (n + 1) → ℝ | rankOfLast ω = m} :=
    measurableSet_rankOfLast_eq m
  have step : μ {ω | rankOfLast ω = m}
      = μ.map (fun ω i => ω (σ i)) {ω | rankOfLast ω = m} := by
    rw [hmap]
  rw [step, Measure.map_apply hMeas hSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [rankOfLast_swap_last]

/-- Under injectivity of `ω`, the map `j ↦ rankOf j ω` is injective:
distinct points have distinct ranks. -/
private lemma rankOf_injective_of_injective {ω : Fin (n + 1) → ℝ}
    (hω : Function.Injective ω) :
    Function.Injective (fun j : Fin (n + 1) => rankOf j ω) := by
  intro a b hab
  unfold rankOf at hab
  rcases lt_trichotomy (ω a) (ω b) with hlt | heq | hgt
  · exfalso
    have hsub : Finset.univ.filter (fun i => ω i ≤ ω a) ⊆
        Finset.univ.filter (fun i => ω i ≤ ω b) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.trans hlt.le
    have hb_in : b ∈ Finset.univ.filter (fun i => ω i ≤ ω b) := by
      simp [Finset.mem_filter]
    have hb_notin : b ∉ Finset.univ.filter (fun i => ω i ≤ ω a) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le.mpr hlt
    have hcard_lt : (Finset.univ.filter (fun i => ω i ≤ ω a)).card <
        (Finset.univ.filter (fun i => ω i ≤ ω b)).card := by
      apply Finset.card_lt_card
      refine ⟨hsub, ?_⟩
      intro hsubset
      exact hb_notin (hsubset hb_in)
    exact absurd hab (Nat.ne_of_lt hcard_lt)
  · exact hω heq
  · exfalso
    have hsub : Finset.univ.filter (fun i => ω i ≤ ω b) ⊆
        Finset.univ.filter (fun i => ω i ≤ ω a) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi.trans hgt.le
    have ha_in : a ∈ Finset.univ.filter (fun i => ω i ≤ ω a) := by
      simp [Finset.mem_filter]
    have ha_notin : a ∉ Finset.univ.filter (fun i => ω i ≤ ω b) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le.mpr hgt
    have hcard_lt : (Finset.univ.filter (fun i => ω i ≤ ω b)).card <
        (Finset.univ.filter (fun i => ω i ≤ ω a)).card := by
      apply Finset.card_lt_card
      refine ⟨hsub, ?_⟩
      intro hsubset
      exact ha_notin (hsubset ha_in)
    exact absurd hab.symm (Nat.ne_of_lt hcard_lt)

/-- The rank `rankOf j ω` always lies in `{1, …, n+1}`. -/
private lemma rankOf_range (j : Fin (n + 1)) (ω : Fin (n + 1) → ℝ) :
    1 ≤ rankOf j ω ∧ rankOf j ω ≤ n + 1 := by
  unfold rankOf
  refine ⟨?_, ?_⟩
  · apply Finset.card_pos.mpr
    exact ⟨j, by simp [Finset.mem_filter]⟩
  · calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin (n + 1))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = n + 1 := by simp [Finset.card_univ, Fintype.card_fin]

/-- Under no ties, exactly one coordinate `j` achieves a given rank
`m ∈ {1, …, n+1}`. -/
private lemma card_filter_rankOf_eq_one {ω : Fin (n + 1) → ℝ}
    (hω : Function.Injective ω) (m : ℕ) (hm_ge : 1 ≤ m) (hm_le : m ≤ n + 1) :
    (Finset.univ.filter (fun j : Fin (n + 1) => rankOf j ω = m)).card = 1 := by
  classical
  have hInj := rankOf_injective_of_injective hω
  have hImage_eq : Finset.univ.image (fun j : Fin (n + 1) => rankOf j ω) =
      Finset.Icc 1 (n + 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := hx
      simp [Finset.mem_Icc, rankOf_range]
    · rw [Finset.card_image_of_injective _ hInj]
      simp [Nat.card_Icc, Fintype.card_fin]
  have hm_mem : m ∈ Finset.univ.image (fun j : Fin (n + 1) => rankOf j ω) := by
    rw [hImage_eq]
    simp [Finset.mem_Icc, hm_ge, hm_le]
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hm_mem
  obtain ⟨j₀, hj₀⟩ := hm_mem
  rw [Finset.card_eq_one]
  refine ⟨j₀, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    exact hInj (hj.trans hj₀.symm)
  · rintro rfl; exact hj₀

/-- **Rank uniformity under exchangeability.** When the joint law of
`(ω 0, …, ω n)` is exchangeable and ties have probability zero, the rank of
`ω (Fin.last n)` is uniformly distributed on `{1, …, n+1}`.

**Proof sketch.**

* *Rank-`(j+1)` event swaps to rank-`(k+1)` event under transposition.*
  Let `σ_j ∈ S_{n+1}` be the transposition that exchanges the last index
  with the index of the `(j+1)`-th smallest value (well-defined under no
  ties). Then `{rankOfLast ω = j + 1}` is the pre-image of
  `{rankOfLast ω = k + 1}` under the re-indexing map `ω ↦ ω ∘ σ_{j,k}`
  for the appropriate transposition.
* *Exchangeability transports mass.*  By `Exchangeable`, the push-forward
  measure `μ.map (· ∘ σ)` equals `μ`, so the two events have equal mass.
* *Partition.*  Under no ties, the `n+1` rank events
  `{rankOfLast ω = 1}, …, {rankOfLast ω = n+1}` partition the full
  almost-sure event, so each has mass `1 / (n+1)` by `IsProbabilityMeasure`.
-/
theorem rank_uniform_of_exchangeable
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω)
    (k : Fin (n + 1)) :
    μ {ω | rankOfLast ω = (k : ℕ) + 1} = ((n : ℝ≥0∞) + 1)⁻¹ := by
  set L := μ {ω | rankOfLast ω = (k : ℕ) + 1} with hL_def
  -- Step 1: each rankOf-j event has the same μ-mass as the rankOfLast event.
  have step1 : ∀ j : Fin (n + 1), μ {ω | rankOf j ω = (k : ℕ) + 1} = L :=
    fun j => measure_rankOf_eq_measure_rankOfLast hExch j ((k : ℕ) + 1)
  -- Sum step1 over all `n + 1` coordinates: total = (n + 1) * L.
  have step1_sum : (∑ j : Fin (n + 1), μ {ω | rankOf j ω = (k : ℕ) + 1})
      = ((n : ℝ≥0∞) + 1) * L := by
    rw [Finset.sum_congr rfl (fun j _ => step1 j)]
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin]
  -- Step 2: in the no-ties case, exactly one j achieves rank k+1, so the
  -- pointwise sum of indicators equals 1 a.s.
  have hk_le : (k : ℕ) + 1 ≤ n + 1 := by
    have := k.isLt
    omega
  have key : ∀ᵐ ω ∂μ, (∑ j : Fin (n + 1),
      (Set.indicator {x : Fin (n + 1) → ℝ | rankOf j x = (k : ℕ) + 1}
        (fun _ => (1 : ℝ≥0∞))) ω) = 1 := by
    filter_upwards [hNoTies] with ω hω
    have hCount := card_filter_rankOf_eq_one hω ((k : ℕ) + 1)
      (by omega) hk_le
    -- Each indicator at ω equals `if rankOf j ω = k+1 then 1 else 0`.
    have hkey : ∀ j : Fin (n + 1),
        (Set.indicator {x : Fin (n + 1) → ℝ | rankOf j x = (k : ℕ) + 1}
          (fun _ => (1 : ℝ≥0∞))) ω
        = if rankOf j ω = (k : ℕ) + 1 then (1 : ℝ≥0∞) else 0 := by
      intro j
      by_cases hj : rankOf j ω = (k : ℕ) + 1
      · have hmem : ω ∈ {x : Fin (n + 1) → ℝ | rankOf j x = (k : ℕ) + 1} := hj
        rw [Set.indicator_of_mem hmem]
        simp [hj]
      · have hnotmem : ω ∉ {x : Fin (n + 1) → ℝ | rankOf j x = (k : ℕ) + 1} := hj
        rw [Set.indicator_of_notMem hnotmem]
        simp [hj]
    simp_rw [hkey]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
    simp [hCount]
  -- Convert step 2 to the measure form via lintegral.
  have step2 : (∑ j : Fin (n + 1), μ {ω | rankOf j ω = (k : ℕ) + 1}) = 1 := by
    have hsum_lintegral : (∑ j : Fin (n + 1), μ {ω | rankOf j ω = (k : ℕ) + 1})
        = ∫⁻ ω, ∑ j : Fin (n + 1),
          (Set.indicator {x : Fin (n + 1) → ℝ | rankOf j x = (k : ℕ) + 1}
            (fun _ => (1 : ℝ≥0∞))) ω ∂μ := by
      rw [lintegral_finset_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [lintegral_indicator (measurableSet_rankOf_eq j ((k : ℕ) + 1))]
        simp
      · intro j _
        exact measurable_const.indicator
          (measurableSet_rankOf_eq j ((k : ℕ) + 1))
    rw [hsum_lintegral]
    rw [lintegral_congr_ae key]
    simp
  -- Step 3: combine to deduce L = 1/(n+1).
  rw [step1_sum] at step2
  -- step2 : (n + 1) * L = 1
  have hne : (n : ℝ≥0∞) + 1 ≠ 0 := by
    intro h
    have h1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) + 1 := le_add_self
    rw [h] at h1
    exact absurd h1 (by norm_num)
  have htop : (n : ℝ≥0∞) + 1 ≠ ⊤ := by
    simp [ENNReal.add_eq_top]
  have hL_eq : L = ((n : ℝ≥0∞) + 1)⁻¹ * (((n : ℝ≥0∞) + 1) * L) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne htop, one_mul]
  rw [hL_eq, step2, mul_one]

end Statlean.Conformal

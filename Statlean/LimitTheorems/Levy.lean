import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sequences

/-! # Lévy–Cramér Continuity Theorem

The **Lévy continuity theorem** (Shao, Thm 1.9) states:

* **Forward**: If `μₙ →ᵈ μ₀` then `charFun μₙ t → charFun μ₀ t` for every `t`.
* **Reverse**: If `charFun μₙ t → f(t)` pointwise and `f` is continuous at `0`,
  then there exists a probability measure `μ₀` such that `μₙ →ᵈ μ₀` and
  `charFun μ₀ = f`.

## Proof strategy (no Fourier inversion)

The reverse direction uses the following chain:
1. `measureReal_abs_gt_le_integral_charFun` + DCT → `{μₙ}` is tight
2. `isCompact_closure_of_isTightMeasureSet` (Prokhorov) → closure is compact
3. `IsCompact.tendsto_subseq` → every subsequence has a convergent sub-subsequence
4. `levy_forward` on the sub-subsequence → charFun of the limit equals `f`
5. `Measure.ext_of_charFun` → all subsequential limits agree
6. `tendsto_of_subseq_tendsto` → full sequence converges

## References

* Shao, Jun. *Mathematical Statistics*, Theorem 1.9.
-/

open MeasureTheory ProbabilityTheory Filter Topology MeasureTheory.ProbabilityMeasure
open BoundedContinuousFunction

noncomputable section

namespace Statlean.LimitTheorems

/-! ## Helper lemmas for tightness -/

-- Private helper: {μₙ | n < N} is tight (finite range induction)
private theorem isTight_finiteRange
    {μs : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μs n)]
    (N : ℕ) :
    IsTightMeasureSet ({μs n | n < N} : Set (Measure ℝ)) := by
  induction N with
  | zero =>
    simp only [Nat.not_lt_zero, false_and, exists_false]
    exact IsTightMeasureSet.subset (isTightMeasureSet_singleton (μ := μs 0)) (Set.empty_subset _)
  | succ N ih =>
    have hset : {μs n | n < N + 1} = {μs n | n < N} ∪ {μs N} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨n, hn, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
        · exact Or.inl ⟨n, h, rfl⟩
        · exact Or.inr (congrArg μs h)
      · rintro (⟨n, hn, rfl⟩ | rfl)
        · exact ⟨n, Nat.lt_succ_of_lt hn, rfl⟩
        · exact ⟨N, Nat.lt_succ_self N, rfl⟩
    rw [hset]; exact ih.union isTightMeasureSet_singleton

-- Complement of closed interval equals the set where |x| is large
private lemma compl_Icc_eq_abs_gt {r : ℝ} (hr : 0 < r) :
    (Set.Icc (-r) r)ᶜ = {x : ℝ | r < |x|} := by
  ext x; simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · rw [abs_of_neg (h.trans_le (neg_nonpos.mpr hr.le))]; linarith
    · exact h.trans_le (le_abs_self _)
  · intro h
    by_cases hx : 0 ≤ x
    · right; rwa [abs_of_nonneg hx] at h
    · left; push_neg at hx; rw [abs_of_neg hx] at h; linarith

/-! ## Forward direction -/

/-- **Lévy forward**: if `μₙ →ᵈ μ₀` (convergence of probability measures in the weak
topology), then `charFun μₙ t → charFun μ₀ t` for every `t : ℝ`. -/
theorem levy_forward
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (h : Tendsto μs l (𝓝 μ₀)) (t : ℝ) :
    Tendsto (fun i => charFun (μs i : Measure ℝ) t) l (𝓝 (charFun (μ₀ : Measure ℝ) t)) := by
  simp_rw [charFun_eq_integral_innerProbChar]
  exact (tendsto_iff_forall_integral_rclike_tendsto ℂ |>.mp h (innerProbChar t))

/-! ## Tightness from characteristic function convergence -/

/-- If the characteristic functions of a sequence of probability measures on `ℝ` converge
pointwise to a function `f` that satisfies `f 0 = 1` and is continuous at `0`, then the
sequence is tight. -/
theorem isTight_of_charFun_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ}
    {f : ℝ → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop (𝓝 (f t)))
    (hf0 : f 0 = 1)
    (hf_cont : ContinuousAt f 0) :
    IsTightMeasureSet {((μs n : ProbabilityMeasure ℝ) : Measure ℝ) | n : ℕ} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  -- ε = ⊤ is trivial (any compact set works since μ Kᶜ ≤ ⊤ always)
  rcases eq_or_lt_of_le (le_top : ε ≤ ⊤) with rfl | hε_lt
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hε_ne_top : ε ≠ ⊤ := hε_lt.ne
  -- Convert ε to a positive real number
  set ε_r := ε.toReal
  have hε_r_pos : 0 < ε_r := ENNReal.toReal_pos hε.ne' hε_ne_top
  -- Working precision: ε' = ε_r / 4
  set ε' := ε_r / 4 with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  -- Continuity of f at 0: translate to (fun t => 1 - f t) → 0
  have hf_cont' : ContinuousAt (fun t : ℝ => (1 : ℂ) - f t) 0 := hf_cont.const_sub 1
  rw [ContinuousAt, hf0, sub_self, Metric.tendsto_nhds_nhds] at hf_cont'
  -- Find δ > 0 such that dist t 0 < δ → ‖1 - f t‖ < ε'
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_cont' ε' hε'_pos
  -- Set T = δ/2 (so dist t 0 < T implies dist t 0 < δ)
  have hT_pos : 0 < δ / 2 := by positivity
  set T := δ / 2 with hT_def
  -- For t ∈ Set.uIoc(-T, T): ‖1 - f t‖ < ε'
  have hf_small : ∀ t ∈ Set.uIoc (-T) T, ‖(1 : ℂ) - f t‖ < ε' := by
    intro t ht
    rw [Set.uIoc_of_le (neg_le_self hT_pos.le)] at ht
    have hlt : dist t 0 < δ := by
      rw [Real.dist_eq]; simp only [sub_zero]
      exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (by linarith)
    have := hδ hlt; rwa [dist_zero_right] at this
  -- DCT: ∫_{-T}^T (1 - charFun μₙ) → ∫_{-T}^T (1 - f) as n → ∞
  have hdct : Tendsto (fun n => ∫ t in (-T)..T, ((1 : ℂ) - charFun (μs n : Measure ℝ) t)) atTop
      (𝓝 (∫ t in (-T)..T, (1 - f t))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 : ℝ))
    · -- AE strongly measurable: 1 - charFun is measurable
      apply Filter.Eventually.of_forall; intro n
      exact aestronglyMeasurable_const.sub
        (stronglyMeasurable_charFun (μ := (μs n : Measure ℝ))).aestronglyMeasurable
    · -- Dominated by 2: ‖1 - charFun μₙ t‖ ≤ 2
      apply Filter.Eventually.of_forall; intro n
      apply Filter.Eventually.of_forall; intro t _
      exact norm_one_sub_charFun_le_two
    · -- The constant 2 is interval integrable
      exact intervalIntegrable_const
    · -- Pointwise convergence: charFun μₙ t → f t, so 1 - charFun μₙ t → 1 - f t
      apply Filter.Eventually.of_forall; intro t _; exact (hconv t).const_sub 1
  -- ‖∫_{-T}^T (1-f)‖ ≤ 2T · ε' (since ‖1 - f t‖ < ε' on [-T, T])
  have hf_int_bound : ‖∫ t in (-T)..T, ((1 : ℂ) - f t)‖ ≤ 2 * T * ε' :=
    calc ‖∫ t in (-T)..T, ((1 : ℂ) - f t)‖
        ≤ ε' * |T - (-T)| := intervalIntegral.norm_integral_le_of_norm_le_const
            (fun t ht => le_of_lt (hf_small t ht))
      _ = 2 * T * ε' := by rw [abs_of_pos (by linarith)]; ring
  -- Get N₀: for n ≥ N₀, the integrals are within T·ε' of each other
  obtain ⟨N₀, hN₀⟩ :=
    (hdct.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < T * ε'))).exists_forall_of_atTop
  -- For n ≥ N₀: ‖∫(1-φₙ)‖ ≤ 3T·ε' (by triangle inequality + limit bound)
  have htail_int : ∀ n ≥ N₀,
      ‖∫ t in (-T)..T, ((1 : ℂ) - charFun (μs n : Measure ℝ) t)‖ ≤ 3 * T * ε' := by
    intro n hn
    have h1 := hN₀ n hn
    rw [dist_eq_norm] at h1
    linarith [norm_sub_norm_le (∫ t in (-T)..T, ((1 : ℂ) - charFun (μs n : Measure ℝ) t))
                                (∫ t in (-T)..T, ((1 : ℂ) - f t)), hf_int_bound, h1.le]
  -- For n ≥ N₀: μₙ(Icc(-2/T, 2/T)ᶜ) ≤ ε
  -- Strategy: measureReal_abs_gt_le_integral_charFun with r = 2/T, giving interval [-T, T]
  -- Then 2⁻¹ · r · 3T·ε' = (1/T) · 3T·ε' = 3ε' = 3ε_r/4 ≤ ε_r
  have hr_pos : (0 : ℝ) < 2 / T := by positivity
  have htail_measure : ∀ n ≥ N₀, (μs n : Measure ℝ) (Set.Icc (-(2 / T)) (2 / T))ᶜ ≤ ε := by
    intro n hn
    rw [compl_Icc_eq_abs_gt hr_pos,
        ← ofReal_measureReal (s := {x : ℝ | 2 / T < |x|})]
    calc ENNReal.ofReal ((μs n : Measure ℝ).real {x | 2 / T < |x|})
        ≤ ENNReal.ofReal ε_r := by
          apply ENNReal.ofReal_le_ofReal
          -- Use Esseen's integral bound with r = 2/T
          have hbound :=
            measureReal_abs_gt_le_integral_charFun (μ := (μs n : Measure ℝ)) hr_pos
          -- Convert interval endpoints: -2 · r⁻¹ = -T and 2 · r⁻¹ = T
          rw [show (-2 : ℝ) * (2 / T)⁻¹ = -T by field_simp,
              show (2 : ℝ) * (2 / T)⁻¹ = T by field_simp] at hbound
          calc (μs n : Measure ℝ).real {x | 2 / T < |x|}
              ≤ 2⁻¹ * (2 / T) *
                ‖∫ t in (-T)..T, ((1 : ℂ) - charFun (μs n : Measure ℝ) t)‖ := hbound
            _ ≤ 2⁻¹ * (2 / T) * (3 * T * ε') :=
                mul_le_mul_of_nonneg_left (htail_int n hn) (by positivity)
            _ = 3 * ε' := by field_simp  -- 2⁻¹ · (2/T) · 3T · ε' = 3ε'
            _ = 3 * ε_r / 4 := by rw [hε'_def]; ring
            _ ≤ ε_r := by linarith
      _ = ε := ENNReal.ofReal_toReal hε_ne_top
  -- The finite head {μₙ | n < N₀} is tight (each singleton is tight, finite union)
  haveI : ∀ n, IsProbabilityMeasure (μs n : Measure ℝ) := inferInstance
  have hhead := isTight_finiteRange N₀ (μs := fun n => (μs n : Measure ℝ))
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hhead
  obtain ⟨K_head, hK_head_compact, hK_head⟩ := hhead ε hε
  -- Use K = Icc(-2/T, 2/T) ∪ K_head as the compact set
  -- For n ≥ N₀: μₙ(Kᶜ) ≤ μₙ(Icc(-2/T,2/T)ᶜ) ≤ ε
  -- For n < N₀: μₙ(Kᶜ) ≤ μₙ(K_headᶜ) ≤ ε
  refine ⟨Set.Icc (-(2 / T)) (2 / T) ∪ K_head, isCompact_Icc.union hK_head_compact, ?_⟩
  rintro μ ⟨n, rfl⟩
  by_cases hn : N₀ ≤ n
  · -- Tail: Kᶜ ⊆ Icc(-2/T, 2/T)ᶜ
    calc (μs n : Measure ℝ) (Set.Icc (-(2 / T)) (2 / T) ∪ K_head)ᶜ
        ≤ (μs n : Measure ℝ) (Set.Icc (-(2 / T)) (2 / T))ᶜ :=
          measure_mono (Set.compl_subset_compl.mpr Set.subset_union_left)
      _ ≤ ε := htail_measure n hn
  · -- Head: Kᶜ ⊆ K_headᶜ
    push_neg at hn
    calc (μs n : Measure ℝ) (Set.Icc (-(2 / T)) (2 / T) ∪ K_head)ᶜ
        ≤ (μs n : Measure ℝ) K_headᶜ :=
          measure_mono (Set.compl_subset_compl.mpr Set.subset_union_right)
      _ ≤ ε := hK_head (μs n : Measure ℝ) ⟨n, hn, rfl⟩

/-! ## Main theorem -/

-- CharFun equality from subsequential convergence
private lemma charFun_eq_of_subseq
    {μs : ℕ → ProbabilityMeasure ℝ} {f : ℝ → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop (𝓝 (f t)))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {ν : ProbabilityMeasure ℝ} (hν : Tendsto (fun n => μs (φ n)) atTop (𝓝 ν))
    (t : ℝ) : charFun (ν : Measure ℝ) t = f t :=
  tendsto_nhds_unique (levy_forward hν t) ((hconv t).comp hφ)

-- Fourier uniqueness (Measure.ext_of_charFun) requires extra heartbeats
set_option maxHeartbeats 400000 in -- Measure.ext_of_charFun is slow to elaborate
private lemma probMeasure_eq_of_charFun_eq {μ ν : ProbabilityMeasure ℝ}
    (h : ∀ t, charFun (μ : Measure ℝ) t = charFun (ν : Measure ℝ) t) : μ = ν := by
  apply eq_of_forall_toMeasure_apply_eq
  intro s _
  exact congr_arg (· s) (Measure.ext_of_charFun (funext h))

set_option maxHeartbeats 800000 in -- Prokhorov + charFun uniqueness across subsequences
/-- **Lévy continuity theorem** (reverse direction): if the characteristic functions of
a sequence `μₙ` of probability measures on `ℝ` converge pointwise to a function `f`
that is continuous at `0` (with `f(0) = 1`), then there exists a probability measure
`μ₀` such that `charFun μ₀ = f` and `μₙ → μ₀` in the weak topology. -/
theorem levy_continuity
    {μs : ℕ → ProbabilityMeasure ℝ}
    {f : ℝ → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure ℝ) t) atTop (𝓝 (f t)))
    (hf0 : f 0 = 1)
    (hf_cont : ContinuousAt f 0) :
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (μ₀ : Measure ℝ) t = f t) ∧
      Tendsto μs atTop (𝓝 μ₀) := by
  have htight := isTight_of_charFun_tendsto hconv hf0 hf_cont
  have htight' : IsTightMeasureSet
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range μs} := by
    convert htight using 1
    ext x; simp [Set.mem_range]
  have hcompact := isCompact_closure_of_isTightMeasureSet htight'
  obtain ⟨μ₀, -, φ₀, hφ₀_mono, hφ₀⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hcf₀ := charFun_eq_of_subseq hconv hφ₀_mono.tendsto_atTop hφ₀
  refine ⟨μ₀, hcf₀, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨ν, -, ms, hms_mono, hms_conv⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨ns n, rfl⟩)
  have hcf_ν := charFun_eq_of_subseq hconv (hns.comp hms_mono.tendsto_atTop) hms_conv
  have hν_eq := probMeasure_eq_of_charFun_eq (fun t => (hcf_ν t).trans (hcf₀ t).symm)
  exact ⟨ms, hν_eq ▸ hms_conv⟩

end Statlean.LimitTheorems

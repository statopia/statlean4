import Statlean.LimitTheorems.Levy
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Cramér–Wold Device

The **Cramér–Wold device** (Shao, Theorem 1.9(iii)) states: for random vectors in a
finite-dimensional real inner product space `E`,

**Xₙ →ᵈ X ⟺ ∀ c ∈ E, ⟪c, Xₙ⟫ →ᵈ ⟪c, X⟫**.

We also prove the multivariate Lévy continuity theorem (`cramer_wold_charFun`):
pointwise charFun convergence implies weak convergence in finite-dimensional spaces.

## Main results

* `cramer_wold_forward`: weak convergence implies convergence of all 1D projections.
* `cramer_wold_reverse`: convergence of all 1D projections implies weak convergence.
* `cramer_wold_iff`: the iff combining both directions.
* `cramer_wold_charFun`: multivariate Lévy continuity (charFun convergence → weak).

## References

* Shao, Jun. *Mathematical Statistics*, Theorem 1.9(iii).
-/

open MeasureTheory ProbabilityTheory Filter Topology MeasureTheory.ProbabilityMeasure
open BoundedContinuousFunction Statlean.LimitTheorems Complex Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

namespace Statlean.LimitTheorems.CramerWold

/-! ## Projection formula -/

set_option maxHeartbeats 400000 in
omit [SecondCountableTopology E] in
-- charFun of a pushforward measure along inner product projection
lemma charFun_map_innerSL (μ : Measure E) [IsFiniteMeasure μ] (c : E) (s : ℝ) :
    charFun (μ.map (innerSL ℝ c)) s = charFun μ (s • c) := by
  rw [charFun_map_eq_charFunDual_smul, charFun_eq_charFunDual_toDualMap]
  congr 1; ext y
  simp [InnerProductSpace.toDualMap_apply_apply,
    innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.smul_apply]

/-! ## Continuity of characteristic functions -/

set_option maxHeartbeats 400000 in
omit [SecondCountableTopology E] in
-- charFun is continuous on inner product spaces (DCT with bound 1)
lemma continuous_charFun (μ : Measure E) [IsFiniteMeasure μ] :
    Continuous (fun t : E => charFun μ t) := by
  simp only [charFun_apply]
  apply continuous_of_dominated (bound := fun _ => 1)
  · intro t; exact (by fun_prop : Continuous _).aestronglyMeasurable
  · intro t; exact Eventually.of_forall fun x => by
      simp only [norm_exp_ofReal_mul_I]; exact le_refl _
  · exact integrable_const 1
  · exact Eventually.of_forall fun x => by fun_prop

/-! ## Forward direction -/

omit [SecondCountableTopology E] in
/-- **Lévy forward** for inner product spaces: if `μₙ → μ₀` weakly then
`charFun μₙ t → charFun μ₀ t` for every `t : E`. -/
theorem levy_forward_inner
    {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (h : Tendsto μs l (𝓝 μ₀)) (t : E) :
    Tendsto (fun i => charFun (μs i : Measure E) t) l
      (𝓝 (charFun (μ₀ : Measure E) t)) := by
  simp_rw [charFun_eq_integral_innerProbChar]
  exact (tendsto_iff_forall_integral_rclike_tendsto ℂ |>.mp h (innerProbChar t))

omit [SecondCountableTopology E] in
/-- **Cramér–Wold forward**: weak convergence `μₙ → μ₀` implies convergence of all
1D projections `⟪c, ·⟫♯μₙ → ⟪c, ·⟫♯μ₀`. -/
theorem cramer_wold_forward
    {μs : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (h : Tendsto μs atTop (𝓝 μ₀)) (c : E) :
    Tendsto (fun n => ProbabilityMeasure.map (μs n)
      (innerSL ℝ c).continuous.measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map μ₀
        (innerSL ℝ c).continuous.measurable.aemeasurable)) :=
  (continuous_map (innerSL ℝ c).continuous).continuousAt.tendsto.comp h

/-! ## Helpers for multivariate Lévy -/

omit [SecondCountableTopology E] in
-- CharFun equality from subsequential convergence
lemma charFun_eq_of_subseq_inner [CompleteSpace E]
    {μs : ℕ → ProbabilityMeasure E} {f : E → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure E) t) atTop (𝓝 (f t)))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {ν : ProbabilityMeasure E} (hν : Tendsto (fun n => μs (φ n)) atTop (𝓝 ν))
    (t : E) : charFun (ν : Measure E) t = f t :=
  tendsto_nhds_unique (levy_forward_inner hν t) ((hconv t).comp hφ)

set_option maxHeartbeats 400000 in
-- Fourier uniqueness for ProbabilityMeasure
lemma probMeasure_eq_of_charFun_eq_inner [CompleteSpace E]
    {μ ν : ProbabilityMeasure E}
    (h : ∀ t, charFun (μ : Measure E) t = charFun (ν : Measure E) t) : μ = ν := by
  apply eq_of_forall_toMeasure_apply_eq
  intro s _
  exact congr_arg (· s) (Measure.ext_of_charFun (funext h))

/-! ## Tightness from charFun convergence -/

set_option maxHeartbeats 1600000 in
omit [SecondCountableTopology E] in
-- tightness in finite dimensions from charFun convergence
lemma isTight_of_charFun_tendsto_inner [FiniteDimensional ℝ E]
    {μs : ℕ → ProbabilityMeasure E}
    {f : E → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure E) t) atTop (𝓝 (f t)))
    (hf0 : f 0 = 1)
    (hf_cont : ContinuousAt f 0) :
    IsTightMeasureSet {((μs n : ProbabilityMeasure E) : Measure E) | n : ℕ} := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  let ob := stdOrthonormalBasis ℝ E
  -- Per-coordinate pushforward ProbabilityMeasure on ℝ
  let π : Fin (finrank ℝ E) → ℕ → ProbabilityMeasure ℝ := fun i n =>
    ProbabilityMeasure.map (μs n) (innerSL ℝ (ob i)).continuous.measurable.aemeasurable
  -- Per-coordinate 1D tightness via Lévy
  have htight_i : ∀ i, IsTightMeasureSet
      {((π i n : ProbabilityMeasure ℝ) : Measure ℝ) | n : ℕ} := by
    intro i
    apply isTight_of_charFun_tendsto (f := fun (s : ℝ) => f (s • ob i))
    · intro s
      change Tendsto (fun n => charFun ((↑(μs n) : Measure E).map (innerSL ℝ (ob i))) s)
        atTop (𝓝 (f (s • ob i)))
      simp only [charFun_map_innerSL]
      exact hconv (s • ob i)
    · rw [zero_smul]; exact hf0
    · refine ContinuousAt.comp ?_ ((continuous_id.smul continuous_const).continuousAt)
      simp only [zero_smul]; exact hf_cont
  -- Unpack to compact sets
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_lt_of_le (le_top : ε ≤ ⊤) with rfl | hε_lt
  · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  -- Handle d = 0 (E is trivial)
  by_cases hd : finrank ℝ E = 0
  · refine ⟨{0}, isCompact_singleton, ?_⟩
    rintro μ ⟨n, rfl⟩
    have : ({0} : Set E)ᶜ = ∅ := by
      ext x; simp [finrank_zero_iff_forall_zero.mp hd x]
    rw [this, measure_empty]; exact zero_le _
  -- d > 0: per-coordinate radius extraction
  have hd_pos : 0 < finrank ℝ E := Nat.pos_of_ne_zero hd
  have hε_div : (0 : ENNReal) < ε / (finrank ℝ E) :=
    ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.natCast_ne_top _⟩
  -- For each i, get compact K_i with (π i n)(K_iᶜ) ≤ ε/d, then extract radius
  have hchoice : ∀ i : Fin (finrank ℝ E), ∃ R : ℝ, 0 < R ∧
      ∀ n, (π i n : Measure ℝ) (Metric.closedBall 0 R)ᶜ ≤ ε / (finrank ℝ E) := by
    intro i
    have hi := htight_i i
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hi
    obtain ⟨K, hK, hbound⟩ := hi (ε / (finrank ℝ E)) hε_div
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
    refine ⟨max R 1, by positivity, fun n => ?_⟩
    calc (π i n : Measure ℝ) (Metric.closedBall 0 (max R 1))ᶜ
        ≤ (π i n : Measure ℝ) Kᶜ :=
          measure_mono (Set.compl_subset_compl.mpr
            (hR.trans (Metric.ball_subset_ball (le_max_left R 1))
              |>.trans Metric.ball_subset_closedBall))
      _ ≤ ε / (finrank ℝ E) := hbound _ ⟨n, rfl⟩
  choose R hR_pos hR_bound using hchoice
  -- Take R_max = sup of all radii
  let R_max := Finset.univ.sup' ⟨⟨0, hd_pos⟩, Finset.mem_univ _⟩ R
  have hR_max_pos : 0 < R_max :=
    lt_of_lt_of_le (hR_pos ⟨0, hd_pos⟩) (Finset.le_sup' R (Finset.mem_univ _))
  -- Uniform bound: (π i n)(closedBall 0 R_max ᶜ) ≤ ε/d for all i, n
  have hR_max_bound : ∀ (i : Fin (finrank ℝ E)) (n : ℕ),
      (π i n : Measure ℝ) (Metric.closedBall 0 R_max)ᶜ ≤ ε / (finrank ℝ E) := by
    intro i n
    exact le_trans (measure_mono (Set.compl_subset_compl.mpr
      (Metric.closedBall_subset_closedBall (Finset.le_sup' R (Finset.mem_univ i)))))
      (hR_bound i n)
  -- Compact set: closedBall 0 (R_max * √d)
  let R_E := R_max * Real.sqrt (finrank ℝ E)
  refine ⟨Metric.closedBall 0 R_E, isCompact_closedBall 0 R_E, ?_⟩
  rintro μ ⟨n, rfl⟩
  -- Parseval pigeonhole: ‖x‖ > R_E ⟹ ∃ i, ‖⟪eᵢ,x⟫‖ > R_max
  have hpigeonhole : (Metric.closedBall (0 : E) R_E)ᶜ ⊆
      ⋃ i : Fin (finrank ℝ E),
        (innerSL ℝ (ob i)) ⁻¹' (Metric.closedBall 0 R_max)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_exists, not_not] at h
    have hle : ‖x‖ ^ 2 ≤ (finrank ℝ E : ℝ) * R_max ^ 2 := by
      rw [← (ob.sum_sq_norm_inner_right x)]
      calc ∑ i : Fin (finrank ℝ E), ‖@inner ℝ E _ (ob i) x‖ ^ 2
          ≤ ∑ _ : Fin (finrank ℝ E), R_max ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            have hi := h i; rw [innerSL_apply_apply] at hi
            exact pow_le_pow_left₀ (norm_nonneg _) hi 2
        _ = (finrank ℝ E : ℝ) * R_max ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hR_E_pos : 0 < R_E :=
      mul_pos hR_max_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd_pos))
    have h_sq : R_E ^ 2 < ‖x‖ ^ 2 := pow_lt_pow_left₀ hx hR_E_pos.le two_ne_zero
    have h_eq : R_E ^ 2 = (finrank ℝ E : ℝ) * R_max ^ 2 := by
      change (R_max * Real.sqrt ↑(finrank ℝ E)) ^ 2 = _
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg' (finrank ℝ E))]; ring
    linarith
  -- Measure bound: union bound + pushforward + sum = ε
  calc (μs n : Measure E) (Metric.closedBall 0 R_E)ᶜ
      ≤ (μs n : Measure E) (⋃ i : Fin (finrank ℝ E),
          (innerSL ℝ (ob i)) ⁻¹' (Metric.closedBall 0 R_max)ᶜ) :=
        measure_mono hpigeonhole
    _ ≤ ∑ i : Fin (finrank ℝ E),
          (μs n : Measure E) ((innerSL ℝ (ob i)) ⁻¹' (Metric.closedBall 0 R_max)ᶜ) :=
        measure_iUnion_fintype_le _ _
    _ = ∑ i : Fin (finrank ℝ E),
          (μs n : Measure E).map (innerSL ℝ (ob i)) (Metric.closedBall 0 R_max)ᶜ := by
        congr 1; ext i
        exact (Measure.map_apply (innerSL ℝ (ob i)).measurable
          Metric.isClosed_closedBall.measurableSet.compl).symm
    _ = ∑ i : Fin (finrank ℝ E),
          (π i n : Measure ℝ) (Metric.closedBall 0 R_max)ᶜ := by rfl
    _ ≤ ∑ _ : Fin (finrank ℝ E), ε / (finrank ℝ E) :=
        Finset.sum_le_sum fun i _ => hR_max_bound i n
    _ = ε := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact ENNReal.mul_div_cancel (Nat.cast_ne_zero.mpr hd) (ENNReal.natCast_ne_top _)

/-! ## Multivariate Lévy continuity -/

set_option maxHeartbeats 1600000 in
-- Prokhorov + charFun uniqueness across subsequences
/-- **Multivariate Lévy continuity theorem**: if the characteristic functions of a sequence
`μₙ` of probability measures on a finite-dimensional inner product space converge pointwise
to a function `f` with `f(0) = 1` and `f` continuous at `0`, then `μₙ` converges weakly. -/
theorem cramer_wold_charFun [FiniteDimensional ℝ E]
    {μs : ℕ → ProbabilityMeasure E}
    {f : E → ℂ}
    (hconv : ∀ t, Tendsto (fun n => charFun (μs n : Measure E) t) atTop (𝓝 (f t)))
    (hf0 : f 0 = 1)
    (hf_cont : ContinuousAt f 0) :
    ∃ μ₀ : ProbabilityMeasure E,
      (∀ t, charFun (μ₀ : Measure E) t = f t) ∧
      Tendsto μs atTop (𝓝 μ₀) := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have htight := isTight_of_charFun_tendsto_inner hconv hf0 hf_cont
  have htight' : IsTightMeasureSet
      {((μ : ProbabilityMeasure E) : Measure E) | μ ∈ Set.range μs} := by
    convert htight using 1; ext x; simp [Set.mem_range]
  have hcompact := isCompact_closure_of_isTightMeasureSet htight'
  obtain ⟨μ₀, -, φ₀, hφ₀_mono, hφ₀⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hcf₀ := charFun_eq_of_subseq_inner hconv hφ₀_mono.tendsto_atTop hφ₀
  refine ⟨μ₀, hcf₀, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨ν, -, ms, hms_mono, hms_conv⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure ⟨ns n, rfl⟩)
  have hcf_ν := charFun_eq_of_subseq_inner hconv (hns.comp hms_mono.tendsto_atTop) hms_conv
  have hν_eq := probMeasure_eq_of_charFun_eq_inner (fun t => (hcf_ν t).trans (hcf₀ t).symm)
  exact ⟨ms, hν_eq ▸ hms_conv⟩

/-! ## Reverse direction -/

set_option maxHeartbeats 1600000 in
-- charFun convergence from projection convergence + Prokhorov
/-- **Cramér–Wold reverse**: if all 1D projections `⟪c, ·⟫♯μₙ → ⟪c, ·⟫♯μ₀` converge
weakly, then `μₙ → μ₀` weakly. -/
theorem cramer_wold_reverse [FiniteDimensional ℝ E]
    {μs : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E}
    (h : ∀ c : E, Tendsto (fun n => ProbabilityMeasure.map (μs n)
      (innerSL ℝ c).continuous.measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map μ₀
        (innerSL ℝ c).continuous.measurable.aemeasurable))) :
    Tendsto μs atTop (𝓝 μ₀) := by
  -- Step 1: charFun convergence from projection convergence
  have hconv : ∀ t : E, Tendsto (fun n => charFun (μs n : Measure E) t) atTop
      (𝓝 (charFun (μ₀ : Measure E) t)) := by
    intro t
    have hproj := levy_forward (h t) (1 : ℝ)
    simp only [ProbabilityMeasure.toMeasure_map, charFun_map_innerSL, one_smul] at hproj
    exact hproj
  -- Step 2: Apply multivariate Lévy
  have hf0 : charFun (μ₀ : Measure E) 0 = 1 := by
    rw [charFun_zero]; simp [Measure.real]
  have hf_cont : ContinuousAt (fun t => charFun (μ₀ : Measure E) t) 0 :=
    (continuous_charFun _).continuousAt
  obtain ⟨μ₁, hcf₁, hμ₁⟩ := cramer_wold_charFun hconv hf0 hf_cont
  have heq : μ₁ = μ₀ := probMeasure_eq_of_charFun_eq_inner (fun t => hcf₁ t)
  exact heq ▸ hμ₁

/-! ## Iff characterization -/

/-- **Cramér–Wold device** (Shao, Theorem 1.9(iii)): for probability measures on a
finite-dimensional real inner product space, `μₙ → μ₀` weakly if and only if all 1D
projections `⟪c, ·⟫♯μₙ → ⟪c, ·⟫♯μ₀` converge weakly. -/
theorem cramer_wold_iff [FiniteDimensional ℝ E]
    {μs : ℕ → ProbabilityMeasure E} {μ₀ : ProbabilityMeasure E} :
    Tendsto μs atTop (𝓝 μ₀) ↔
    ∀ c : E, Tendsto (fun n => ProbabilityMeasure.map (μs n)
      (innerSL ℝ c).continuous.measurable.aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map μ₀
        (innerSL ℝ c).continuous.measurable.aemeasurable)) :=
  ⟨fun h c => cramer_wold_forward h c, cramer_wold_reverse⟩

end Statlean.LimitTheorems.CramerWold

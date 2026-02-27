import Statlean.LimitTheorems.USLLNProved
/-!
# Uniform Strong Law of Large Numbers — Main Theorem

Proof: ε/3 argument using oscillation SLLN bound.
Base infrastructure is in `USLLNProved.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function Set Metric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α]
variable {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-! ### Key oscillation infrastructure

**Oscillation SLLN bound**: For any θ₀ and η > 0, there exists r > 0 such that
a.s. eventually (1/n)Σⱼ ‖U(Xⱼ,θ)-U(Xⱼ,θ₀)‖ < η for ALL θ in B(θ₀,r) simultaneously.

Proof sketch: Define Φ(x) = ⨆_{d∈D∩B(θ₀,r)} ‖U(x,d)-U(x,θ₀)‖ via countable dense D.
- Φ measurable (countable iSup), Φ ≤ 2M (domination)
- Φ_δ(x) → 0 as δ → 0 by continuity of U(x,·)
- E[Φ_δ(X₀)] → 0 by DCT, so choose r with E[Φ_r(X₀)] < η
- ‖U(x,θ)-U(x,θ₀)‖ ≤ Φ_r(x) for d(θ,θ₀) < r (density + continuity)
- SLLN for Φ_r ∘ Xⱼ gives (1/n)Σ Φ_r(Xⱼ) → E[Φ_r] < η a.s. -/

/-- The oscillation envelope: sup of ‖U(x,d)-U(x,θ₀)‖ over dense points d near θ₀.
Equal to the true sup by density + continuity. -/
private noncomputable def oscEnvelope (U : α → Θ → ℝ) (θ₀ : Θ) (δ : ℝ) (x : α) : ℝ :=
  ⨆ (k : ℕ) (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ), ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖

/-- The oscillation envelope dominates pointwise: for any θ near θ₀,
‖U(x,θ)-U(x,θ₀)‖ ≤ oscEnvelope U θ₀ δ x. -/
private lemma le_oscEnvelope
    {U : α → Θ → ℝ} (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    {θ₀ : Θ} {δ : ℝ} (hδ : 0 < δ) {θ : Θ} (hθ : dist θ θ₀ < δ) (x : α) :
    ‖U x θ - U x θ₀‖ ≤ oscEnvelope U θ₀ δ x := by
  sorry

/-- The oscillation envelope is bounded by 2M. -/
private lemma oscEnvelope_le_two_mul
    {U : α → Θ → ℝ} {M : α → ℝ} (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    {θ₀ : Θ} {δ : ℝ} (x : α) :
    oscEnvelope U θ₀ δ x ≤ 2 * M x := by
  sorry

/-- The oscillation envelope tends to 0 pointwise as δ → 0. -/
private lemma oscEnvelope_tendsto_zero
    {U : α → Θ → ℝ} (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (θ₀ : Θ) (x : α) :
    Tendsto (fun n : ℕ => oscEnvelope U θ₀ (1 / (↑n + 1)) x) atTop (𝓝 0) := by
  sorry

/-- The oscillation envelope is measurable (countable iSup of measurable functions). -/
private lemma oscEnvelope_measurable
    {U : α → Θ → ℝ} (hU_meas : ∀ θ, Measurable (fun x => U x θ)) (θ₀ : Θ) (δ : ℝ) :
    Measurable (oscEnvelope U θ₀ δ) := by
  sorry

private lemma slln_oscillation_bound
    {X : ℕ → Ω → α} {U : α → Θ → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    {M : α → ℝ} (_hM_meas : Measurable M)
    (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (_hM_nn : ∀ x, 0 ≤ M x)
    (θ₀ : Θ) {η : ℝ} (_hη : 0 < η) :
    ∃ r > 0, ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ, dist θ θ₀ < r →
      (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θ₀‖) / (↑n : ℝ) < η := by
  sorry

/-! ### Main theorem -/

/-- **Uniform Strong Law of Large Numbers (USLLN)**.
For i.i.d. samples from P, if U(x,θ) is continuous in θ on compact Θ
and dominated by integrable M(x), then
  sup_θ ‖(1/n)Σ U(Xⱼ,θ) - E[U(X,θ)]‖ → 0  a.s. -/
theorem uniform_slln
    (X : ℕ → Ω → α) (U : α → Θ → ℝ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    (M : α → ℝ) (hM_meas : Measurable M)
    (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (hM_nn : ∀ x, 0 ≤ M x) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ,
        ‖sampleAvg X U n ω θ - popMean (P := P) X U θ‖ < ε := by
  -- Abbreviations
  set μ := fun θ => popMean (P := P) X U θ
  set SA := fun n ω θ => sampleAvg X U n ω θ
  -- Continuity results
  have hμ_cont : Continuous μ :=
    popMean_continuous hX_meas hU_cont hU_meas hM_meas hM_int hM_bound
  have hμ_uc : UniformContinuous μ :=
    CompactSpace.uniformContinuous_of_continuous hμ_cont
  -- === Step 1: Reduce to countable ε = 1/(m+1) ===
  suffices h : ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ,
      ‖SA n ω θ - μ θ‖ < 1 / (↑m + 1) by
    filter_upwards [h] with ω hω ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    obtain ⟨N, hN⟩ := hω m
    exact ⟨N, fun n hn θ => lt_trans (hN n hn θ) (by
      have hm1 : (0 : ℝ) < ↑m + 1 := by positivity
      rw [div_lt_comm₀ hm1 hε]
      linarith)⟩
  rw [ae_all_iff]; intro m
  set ε : ℝ := 1 / (↑m + 1); have hε : 0 < ε := by positivity
  -- === Step 2: Get δ_μ from uniform continuity of μ ===
  obtain ⟨δ_μ, hδ_μ_pos, hδ_μ⟩ := Metric.uniformContinuous_iff.mp hμ_uc (ε / 3) (by linarith)
  -- === Step 3: For each θ₀, get oscillation radius via DCT ===
  have hE_osc : ∀ θ₀ : Θ, ∃ r > 0, ∀ᵐ ω ∂P, ∃ N, ∀ n, N ≤ n →
      ∀ θ, dist θ θ₀ < r →
        (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θ₀‖) / (↑n : ℝ) < ε / 3 :=
    fun θ₀ => slln_oscillation_bound hX_meas hX_indep hX_ident hU_cont hU_meas
      hM_meas hM_int hM_bound hM_nn θ₀ (by linarith)
  -- === Step 4: Finite cover from compactness ===
  let R : Θ → ℝ := fun θ₀ => min δ_μ (hE_osc θ₀).choose
  have hR_pos : ∀ θ₀, 0 < R θ₀ :=
    fun θ₀ => lt_min hδ_μ_pos (hE_osc θ₀).choose_spec.1
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun θ₀ => ball θ₀ (R θ₀)) (fun _ => isOpen_ball)
    (fun θ _ => mem_iUnion.mpr ⟨θ, mem_ball_self (hR_pos θ)⟩)
  -- Net point lookup
  have hnet : ∀ θ : Θ, ∃ θᵢ ∈ S, dist θ θᵢ < R θᵢ := by
    intro θ; have h := hS (mem_univ θ)
    simp only [mem_iUnion, mem_ball] at h
    obtain ⟨i, hi_mem, hi_dist⟩ := h
    exact ⟨i, hi_mem, hi_dist⟩
  -- Net point properties
  have hμ_net : ∀ θᵢ ∈ S, ∀ θ, dist θ θᵢ < R θᵢ → dist (μ θ) (μ θᵢ) < ε / 3 :=
    fun θᵢ _ θ hθ => hδ_μ (lt_of_lt_of_le hθ (min_le_left _ _))
  -- Oscillation a.e. events for net points
  have hE_net_osc : ∀ θᵢ ∈ S, ∀ᵐ ω ∂P, ∃ N, ∀ n, N ≤ n →
      ∀ θ, dist θ θᵢ < R θᵢ →
        (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3 := by
    intro θᵢ _
    have h_ae := (hE_osc θᵢ).choose_spec.2
    filter_upwards [h_ae] with ω hω
    obtain ⟨N, hN⟩ := hω
    exact ⟨N, fun n hn θ hθ => hN n hn θ (lt_of_lt_of_le hθ (min_le_right _ _))⟩
  -- === Step 5: SLLN events ===
  -- (A) sampleAvg → μ at net points, with ε/3 bound
  have hslln_eps : ∀ᵐ ω ∂P, ∀ θᵢ ∈ S, ∃ N, ∀ n, N ≤ n →
      ‖SA n ω θᵢ - μ θᵢ‖ < ε / 3 := by
    have hslln := slln_finset_ae hX_meas hX_indep hX_ident hU_meas hM_int hM_bound hM_nn S
    filter_upwards [hslln] with ω hω θᵢ hθᵢ
    have htend := hω θᵢ hθᵢ
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend (ε / 3) (by linarith)
    exact ⟨N, fun n hn => by
      have hd := hN n hn
      rw [Real.dist_eq] at hd
      rw [Real.norm_eq_abs]
      exact hd⟩
  -- (B) Oscillation SLLN at net points
  have hslln_osc : ∀ᵐ ω ∂P, ∀ θᵢ ∈ S, ∃ N, ∀ n, N ≤ n → ∀ θ, dist θ θᵢ < R θᵢ →
      (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3 := by
    have : ∀ θᵢ ∈ (S : Set Θ), ∀ᵐ ω ∂P, ∃ N, ∀ n, N ≤ n → ∀ θ, dist θ θᵢ < R θᵢ →
        (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3 :=
      fun θᵢ hθᵢ => hE_net_osc θᵢ hθᵢ
    exact (ae_ball_iff (Finset.countable_toSet S)).mpr this
  -- === Step 6: Assembly ===
  filter_upwards [hslln_eps, hslln_osc] with ω hω_net hω_osc
  -- Merge into combined bound for each θᵢ ∈ S
  have hcombined : ∀ θᵢ ∈ S, ∃ N, ∀ n, N ≤ n →
      (‖SA n ω θᵢ - μ θᵢ‖ < ε / 3) ∧
      (∀ θ, dist θ θᵢ < R θᵢ →
        (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3) := by
    intro θᵢ hθᵢ
    obtain ⟨N₁, hN₁⟩ := hω_net θᵢ hθᵢ
    obtain ⟨N₂, hN₂⟩ := hω_osc θᵢ hθᵢ
    exact ⟨max N₁ N₂, fun n hn =>
      ⟨hN₁ n (le_of_max_le_left hn), hN₂ n (le_of_max_le_right hn)⟩⟩
  -- Take max N over finite S via List induction
  obtain ⟨N, hN⟩ : ∃ N, ∀ θᵢ ∈ S, ∀ n, N ≤ n →
      (‖SA n ω θᵢ - μ θᵢ‖ < ε / 3) ∧
      (∀ θ, dist θ θᵢ < R θᵢ →
        (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3) := by
    suffices ∀ (L : List Θ), (∀ x ∈ L, x ∈ S) → ∃ N, ∀ θᵢ ∈ L, ∀ n, N ≤ n →
        (‖SA n ω θᵢ - μ θᵢ‖ < ε / 3) ∧
        (∀ θ, dist θ θᵢ < R θᵢ →
          (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θᵢ‖) / (↑n : ℝ) < ε / 3) by
      obtain ⟨N, hN⟩ := this S.val.toList (fun x hx => by
        rwa [Multiset.mem_toList] at hx)
      exact ⟨N, fun θᵢ hθᵢ => hN θᵢ (by rwa [Multiset.mem_toList])⟩
    intro L
    induction L with
    | nil => exact fun _ => ⟨0, fun _ h => absurd h (by simp)⟩
    | cons a t ih =>
      intro hL
      obtain ⟨Nt, hNt⟩ := ih (fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
      obtain ⟨Na, hNa⟩ := hcombined a (hL a (List.mem_cons.mpr (Or.inl rfl)))
      exact ⟨max Na Nt, fun θᵢ hθᵢ n hn => by
        rcases List.mem_cons.mp hθᵢ with rfl | h
        · exact hNa n (le_of_max_le_left hn)
        · exact hNt θᵢ h n (le_of_max_le_right hn)⟩
  -- Final: for any θ, triangle inequality
  exact ⟨N, fun n hn θ => by
    obtain ⟨θᵢ, hθᵢ_mem, hθᵢ_dist⟩ := hnet θ
    obtain ⟨h_net, h_osc_fn⟩ := hN θᵢ hθᵢ_mem n hn
    have h_osc := h_osc_fn θ hθᵢ_dist
    have h_mu := hμ_net θᵢ hθᵢ_mem θ hθᵢ_dist
    rw [Real.dist_eq] at h_mu
    -- sampleAvg oscillation: ‖SA(θ)-SA(θᵢ)‖ ≤ (1/n)Σ‖U(Xⱼ,θ)-U(Xⱼ,θᵢ)‖ < ε/3
    have hSA : ‖SA n ω θ - SA n ω θᵢ‖ < ε / 3 := by
      apply lt_of_le_of_lt _ h_osc
      change ‖sampleAvg X U n ω θ - sampleAvg X U n ω θᵢ‖ ≤ _
      unfold sampleAvg
      have h_eq : (∑ j ∈ range n, U (X j ω) θ) / (↑n : ℝ) -
            (∑ j ∈ range n, U (X j ω) θᵢ) / (↑n : ℝ) =
            (∑ j ∈ range n, (U (X j ω) θ - U (X j ω) θᵢ)) / (↑n : ℝ) := by
        rw [← sub_div, ← Finset.sum_sub_distrib]
      rw [h_eq, norm_div, Real.norm_natCast]
      exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)
    -- popMean oscillation
    have hμ' : ‖μ θᵢ - μ θ‖ < ε / 3 := by
      rw [Real.norm_eq_abs, abs_sub_comm]; exact h_mu
    -- Triangle inequality
    calc ‖SA n ω θ - μ θ‖
        = ‖(SA n ω θ - SA n ω θᵢ) + (SA n ω θᵢ - μ θᵢ) + (μ θᵢ - μ θ)‖ := by
          congr 1; ring
      _ ≤ ‖SA n ω θ - SA n ω θᵢ‖ + ‖SA n ω θᵢ - μ θᵢ‖ + ‖μ θᵢ - μ θ‖ := by
          linarith [norm_add_le (SA n ω θ - SA n ω θᵢ) (SA n ω θᵢ - μ θᵢ),
            norm_add_le (SA n ω θ - SA n ω θᵢ + (SA n ω θᵢ - μ θᵢ)) (μ θᵢ - μ θ)]
      _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hSA h_net) hμ'
      _ = ε := by ring⟩

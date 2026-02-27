import Mathlib
/-!
# Uniform Strong Law of Large Numbers (USLLN)

**Zero sorry** — fully proved.

## Contents

### Basic definitions
- `sampleAvg` — sample average (1/n)Σ U(Xⱼ, θ)
- `popMean` — population mean E[U(X₁, θ)]

### Infrastructure lemmas (zero sorry)
- `integrable_U_comp_X` — domination integrability
- `sampleAvg_continuous` — continuity of sample average in θ
- `slln_pointwise` — pointwise SLLN via `strong_law_ae_real`
- `slln_finset_ae` — SLLN at finitely many points (finite intersection)
- `popMean_continuous` — continuity of population mean via DCT

### Oscillation machinery (zero sorry)
- `oscEnvelope` — oscillation envelope via dense sequence
- `le_oscEnvelope` — pointwise domination
- `oscEnvelope_le_two_mul` — 2M bound
- `oscEnvelope_tendsto_zero` — DCT convergence
- `oscEnvelope_measurable` — measurability
- `slln_oscillation_bound` — oscillation SLLN bound

### Main theorem
- `uniform_slln` — Uniform SLLN: sup_θ ‖(1/n)Σ U(Xⱼ,θ) - E[U(X,θ)]‖ → 0 a.s.
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function Set Metric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α]
variable {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-! ### Basic definitions and infrastructure -/

/-- The sample average of U(Xⱼ, θ) over the first n samples. -/
noncomputable def sampleAvg (X : ℕ → Ω → α) (U : α → Θ → ℝ) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (∑ j ∈ range n, U (X j ω) θ) / n

/-- The population mean μ(θ) = E[U(X₁, θ)] under the distribution of X₀. -/
noncomputable def popMean (X : ℕ → Ω → α) (U : α → Θ → ℝ) (θ : Θ) : ℝ :=
  ∫ a, U a θ ∂(P.map (X 0))

omit [IsProbabilityMeasure P] [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] in
/-- For each fixed θ, ω ↦ U(X₀(ω), θ) is integrable (by domination). -/
lemma integrable_U_comp_X
    {X : ℕ → Ω → α} {U : α → Θ → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    {M : α → ℝ} (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (_hM_nn : ∀ x, 0 ≤ M x)
    (θ : Θ) : Integrable (fun ω => U (X 0 ω) θ) P := by
  apply Integrable.mono hM_int
    ((hU_meas θ).comp (hX_meas 0)).aestronglyMeasurable
  filter_upwards with ω
  simp only [comp_apply, Real.norm_eq_abs]
  exact le_trans (hM_bound (X 0 ω) θ) (le_abs_self _)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [MeasurableSpace α]
    [CompactSpace Θ] [Nonempty Θ] in
/-- The sample average θ ↦ sampleAvg X U n ω θ is continuous
    (finite sum of continuous functions). -/
lemma sampleAvg_continuous
    (X : ℕ → Ω → α) (U : α → Θ → ℝ)
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (n : ℕ) (ω : Ω) : Continuous (fun θ => sampleAvg X U n ω θ) := by
  unfold sampleAvg
  apply Continuous.div_const
  apply continuous_finset_sum
  intro j _
  exact hU_cont (X j ω)

omit [IsProbabilityMeasure P] [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] in
/-- For each fixed θ, the standard SLLN gives a.s. convergence of sample averages.
This is a direct application of Mathlib's `strong_law_ae_real`. -/
lemma slln_pointwise
    {X : ℕ → Ω → α} {U : α → Θ → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    {M : α → ℝ} (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (hM_nn : ∀ x, 0 ≤ M x)
    (θ : Θ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => sampleAvg X U n ω θ) atTop
      (𝓝 (popMean (P := P) X U θ)) := by
  let Y : ℕ → Ω → ℝ := fun n ω => U (X n ω) θ
  have hY_int : Integrable (Y 0) P :=
    integrable_U_comp_X hX_meas hU_meas hM_int hM_bound hM_nn θ
  have hY_indep : Pairwise ((· ⟂ᵢ[P] ·) on Y) := by
    intro i j hij
    exact (hX_indep hij).comp (hU_meas θ) (hU_meas θ)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    intro n; exact (hX_ident n).comp (hU_meas θ)
  have key := strong_law_ae_real Y hY_int hY_indep hY_ident
  filter_upwards [key] with ω hω
  simp only [Y] at hω
  change Tendsto (fun n => (∑ j ∈ range n, U (X j ω) θ) / (n : ℝ)) atTop
    (𝓝 (∫ a, U a θ ∂(P.map (X 0))))
  rw [show (∫ a, U a θ ∂(P.map (X 0))) = ∫ ω, U (X 0 ω) θ ∂P from
    integral_map (hX_meas 0).aemeasurable
      (hU_meas θ).aestronglyMeasurable]
  exact hω

omit [IsProbabilityMeasure P] [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] in
/-- Pointwise SLLN at finitely many θ values simultaneously (a.s.).
This is a finite intersection of measure-one events. -/
lemma slln_finset_ae
    {X : ℕ → Ω → α} {U : α → Θ → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    {M : α → ℝ} (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (hM_nn : ∀ x, 0 ≤ M x)
    (S : Finset Θ) :
    ∀ᵐ ω ∂P, ∀ θ ∈ S, Tendsto (fun n => sampleAvg X U n ω θ) atTop
      (𝓝 (popMean (P := P) X U θ)) := by
  have : ∀ θ ∈ S, ∀ᵐ ω ∂P, Tendsto (fun n => sampleAvg X U n ω θ) atTop
      (𝓝 (popMean (P := P) X U θ)) :=
    fun θ _ => slln_pointwise hX_meas hX_indep hX_ident hU_meas hM_int hM_bound hM_nn θ
  exact (ae_ball_iff (Finset.countable_toSet S)).mpr this

/-- The population mean θ ↦ E[U(X, θ)] is continuous.
    Proof: dominated convergence + continuity of U in θ + domination by M. -/
lemma popMean_continuous
    {X : ℕ → Ω → α} {U : α → Θ → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    {M : α → ℝ} (hM_meas : Measurable M)
    (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x) :
    Continuous (fun θ => popMean (P := P) X U θ) := by
  unfold popMean
  apply continuous_of_dominated (F := fun θ a => U a θ) (bound := M)
  · intro θ
    exact (hU_meas θ).aestronglyMeasurable
  · intro θ
    exact ae_of_all _ (fun a => hM_bound a θ)
  · exact (integrable_map_measure hM_meas.aestronglyMeasurable
      (hX_meas 0).aemeasurable).mpr hM_int
  · exact ae_of_all _ (fun a => hU_cont a)

/-! ### Key oscillation infrastructure

**Oscillation SLLN bound**: For any θ₀ and η > 0, there exists r > 0 such that
a.s. eventually (1/n)Σⱼ ‖U(Xⱼ,θ)-U(Xⱼ,θ₀)‖ < η for ALL θ in B(θ₀,r) simultaneously.

Proof sketch: Define Φ(x) = ⨆_{d∈D∩B(θ₀,r)} ‖U(x,d)-U(x,θ₀)‖ via countable dense D.
- Φ measurable (countable iSup), Φ ≤ 2M (domination)
- Φ_δ(x) → 0 as δ → 0 by continuity of U(x,·)
- E[Φ_δ(X₀)] → 0 by DCT, so choose r with E[Φ_r(X₀)] < η
- ‖U(x,θ)-U(x,θ₀)‖ ≤ Φ_r(x) for d(θ,θ₀) < r (density + continuity)
- SLLN for Φ_r ∘ Xⱼ gives (1/n)Σ Φ_r(Xⱼ) → E[Φ_r] < η a.s. -/

/-- Helper: iSup over a Prop condition is ≤ bound when the value is ≤ bound and bound ≥ 0. -/
private lemma iSup_prop_le {P : Prop} {v b : ℝ} (hv : v ≤ b) (hb : 0 ≤ b) :
    (⨆ (_ : P), v) ≤ b := by
  by_cases hP : P
  · haveI : Nonempty P := ⟨hP⟩
    exact ciSup_le fun _ => hv
  · haveI : IsEmpty P := not_nonempty_iff.mp (fun ⟨p⟩ => hP p)
    simp [iSup_of_empty]
    exact hb

/-- The oscillation envelope: sup of ‖U(x,d)-U(x,θ₀)‖ over dense points d near θ₀.
Equal to the true sup by density + continuity. -/
private noncomputable def oscEnvelope (U : α → Θ → ℝ) (θ₀ : Θ) (δ : ℝ) (x : α) : ℝ :=
  ⨆ (k : ℕ) (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ), ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖

/-- The oscillation envelope dominates pointwise: for any θ near θ₀,
‖U(x,θ)-U(x,θ₀)‖ ≤ oscEnvelope U θ₀ δ x.
Proof: approximate θ by dense sequence, use continuity. -/
private lemma le_oscEnvelope
    {U : α → Θ → ℝ} (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    {M : α → ℝ} (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    {θ₀ : Θ} {δ : ℝ} (hδ : 0 < δ) {θ : Θ} (hθ : dist θ θ₀ < δ) (x : α) :
    ‖U x θ - U x θ₀‖ ≤ oscEnvelope U θ₀ δ x := by
  -- 2M bound for BddAbove
  have h2M : ∀ k : ℕ, ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ ≤ 2 * M x :=
    fun k => (norm_sub_le _ _).trans (by linarith [hM_bound x (TopologicalSpace.denseSeq Θ k), hM_bound x θ₀])
  have h2M_nn : (0 : ℝ) ≤ 2 * M x := by linarith [norm_nonneg (U x θ₀), hM_bound x θ₀]
  -- BddAbove for the inner conditional iSup
  have hbdd_inner : ∀ k, BddAbove (Set.range fun (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ) =>
      ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) :=
    fun k => ⟨2 * M x, fun _ ⟨_, he⟩ => he ▸ h2M k⟩
  -- BddAbove for the outer iSup
  have hbdd : BddAbove (Set.range fun k =>
      ⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ),
        ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) :=
    ⟨2 * M x, fun _ ⟨k, hk⟩ => hk ▸ iSup_prop_le (h2M k) h2M_nn⟩
  -- Continuity of the norm function
  have hcont_norm : Continuous (fun θ' => ‖U x θ' - U x θ₀‖) :=
    continuous_norm.comp ((hU_cont x).sub continuous_const)
  -- Approximation: for any ε > 0, find dense d_k near θ with d(d_k,θ₀) < δ
  suffices h : ∀ ε > 0, ‖U x θ - U x θ₀‖ ≤ oscEnvelope U θ₀ δ x + ε from
    le_of_forall_pos_le_add fun ε hε => h ε hε
  intro ε hε
  obtain ⟨η, hη_pos, hη⟩ := Metric.continuousAt_iff.mp hcont_norm.continuousAt ε hε
  have hgap : 0 < δ - dist θ θ₀ := sub_pos.mpr hθ
  set r := min η (δ - dist θ θ₀) with hr_def
  have hr_pos : 0 < r := lt_min hη_pos hgap
  obtain ⟨k, hk_dist⟩ := (TopologicalSpace.denseRange_denseSeq Θ).exists_dist_lt θ hr_pos
  -- hk_dist: dist θ (denseSeq k) < r
  have hk_dist' : dist (TopologicalSpace.denseSeq Θ k) θ < r := by rwa [dist_comm]
  have hk_near : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ := by
    calc dist (TopologicalSpace.denseSeq Θ k) θ₀
        ≤ dist (TopologicalSpace.denseSeq Θ k) θ + dist θ θ₀ := dist_triangle _ _ _
      _ < r + dist θ θ₀ := by gcongr
      _ ≤ (δ - dist θ θ₀) + dist θ θ₀ := by gcongr; exact min_le_right _ _
      _ = δ := sub_add_cancel δ _
  -- Closeness: |‖U x d_k - U x θ₀‖ - ‖U x θ - U x θ₀‖| < ε
  have hclose := hη (lt_of_lt_of_le hk_dist' (min_le_left _ _))
  rw [Real.dist_eq] at hclose
  -- ‖U x d_k - U x θ₀‖ ≤ oscEnvelope (one term of the sup)
  have hle_osc : ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ ≤ oscEnvelope U θ₀ δ x := by
    unfold oscEnvelope
    calc ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖
        ≤ ⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ),
            ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ := by
          exact le_ciSup_of_le (hbdd_inner k) hk_near le_rfl
      _ ≤ ⨆ k', ⨆ (_ : dist (TopologicalSpace.denseSeq Θ k') θ₀ < δ),
            ‖U x (TopologicalSpace.denseSeq Θ k') - U x θ₀‖ :=
          le_ciSup hbdd k
  have key : ‖U x θ - U x θ₀‖ - ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ < ε := by
    calc ‖U x θ - U x θ₀‖ - ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖
        ≤ |‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ - ‖U x θ - U x θ₀‖| := by
          rw [abs_sub_comm]; exact le_abs_self _
      _ < ε := hclose
  linarith

/-- The oscillation envelope is bounded by 2M. -/
private lemma oscEnvelope_le_two_mul
    {U : α → Θ → ℝ} {M : α → ℝ} (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    {θ₀ : Θ} {δ : ℝ} (x : α) :
    oscEnvelope U θ₀ δ x ≤ 2 * M x := by
  unfold oscEnvelope
  have h2M_nn : (0 : ℝ) ≤ 2 * M x := by
    linarith [norm_nonneg (U x θ₀), hM_bound x θ₀]
  have hterm : ∀ k : ℕ,
      (⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ),
        ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) ≤ 2 * M x := by
    intro k
    apply iSup_prop_le _ h2M_nn
    calc ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖
        ≤ ‖U x (TopologicalSpace.denseSeq Θ k)‖ + ‖U x θ₀‖ := norm_sub_le _ _
      _ ≤ M x + M x := add_le_add (hM_bound x _) (hM_bound x _)
      _ = 2 * M x := by ring
  exact ciSup_le hterm

/-- The oscillation envelope tends to 0 pointwise as δ → 0. -/
private lemma oscEnvelope_tendsto_zero
    {U : α → Θ → ℝ} (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (θ₀ : Θ) (x : α) :
    Tendsto (fun n : ℕ => oscEnvelope U θ₀ (1 / (↑n + 1)) x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Continuity of U(x,·) at θ₀ with bound ε/2
  obtain ⟨η, hη_pos, hη⟩ := Metric.continuousAt_iff.mp (hU_cont x).continuousAt (ε/2) (by linarith)
  -- For n large, 1/(n+1) < η
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hn1_pos : (0 : ℝ) < ↑n + 1 := by positivity
  have hn_small : 1 / (↑n + 1 : ℝ) < η := by
    rw [div_lt_iff₀ hn1_pos]
    have h1 : 1 < ↑N * η := by rwa [div_lt_iff₀ hη_pos] at hN
    have h2 : (↑N : ℝ) ≤ ↑n := by exact_mod_cast hn
    nlinarith
  -- Helper: inner iSup = value or 0
  have hinner_eq : ∀ k, (⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ <
      1 / (↑n + 1)), ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) =
      if dist (TopologicalSpace.denseSeq Θ k) θ₀ < 1 / (↑n + 1)
      then ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖ else 0 := by
    intro k
    split
    · next hk =>
      haveI : Nonempty (dist (TopologicalSpace.denseSeq Θ k) θ₀ < 1 / (↑n + 1)) := ⟨hk⟩
      exact ciSup_const
    · next hk =>
      haveI : IsEmpty (dist (TopologicalSpace.denseSeq Θ k) θ₀ < 1 / (↑n + 1)) :=
        not_nonempty_iff.mp (fun ⟨h⟩ => hk h)
      exact Real.iSup_of_isEmpty _
  -- Each inner iSup is nonneg
  have hterm_nn : ∀ k, 0 ≤ (⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ <
      1 / (↑n + 1)), ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) := by
    intro k; rw [hinner_eq]; split <;> simp
  -- Each inner iSup is ≤ ε/2
  have hterm_le : ∀ k, (⨆ (_ : dist (TopologicalSpace.denseSeq Θ k) θ₀ <
      1 / (↑n + 1)), ‖U x (TopologicalSpace.denseSeq Θ k) - U x θ₀‖) ≤ ε / 2 := by
    intro k; rw [hinner_eq]; split
    · next hk => exact le_of_lt (by have := hη (lt_trans hk hn_small); rwa [Real.dist_eq] at this)
    · linarith
  -- oscEnvelope ≤ ε/2
  have hosc_le : oscEnvelope U θ₀ (1 / (↑n + 1)) x ≤ ε / 2 := by
    unfold oscEnvelope; exact ciSup_le hterm_le
  -- oscEnvelope ≥ 0
  have hosc_nn : 0 ≤ oscEnvelope U θ₀ (1 / (↑n + 1)) x := by
    unfold oscEnvelope
    exact le_ciSup_of_le ⟨ε / 2, fun _ ⟨k, hk⟩ => hk ▸ hterm_le k⟩ 0 (hterm_nn 0)
  -- |oscEnvelope| = oscEnvelope ≤ ε/2 < ε
  rw [abs_of_nonneg hosc_nn]; linarith

/-- The oscillation envelope is measurable (countable iSup of measurable functions). -/
private lemma oscEnvelope_measurable
    {U : α → Θ → ℝ} (hU_meas : ∀ θ, Measurable (fun x => U x θ)) (θ₀ : Θ) (δ : ℝ) :
    Measurable (oscEnvelope U θ₀ δ) := by
  unfold oscEnvelope
  apply Measurable.iSup; intro k
  by_cases hk : dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ
  · haveI : Nonempty (dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ) := ⟨hk⟩
    simp only [ciSup_const]
    exact ((hU_meas _).sub (hU_meas _)).norm
  · haveI : IsEmpty (dist (TopologicalSpace.denseSeq Θ k) θ₀ < δ) :=
      not_nonempty_iff.mp (fun ⟨h⟩ => hk h)
    simp [Real.iSup_of_isEmpty]

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
    (θ₀ : Θ) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ, dist θ θ₀ < r →
      (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θ₀‖) / (↑n : ℝ) < η := by
  -- Abbreviation: Φ_δ = oscEnvelope U θ₀ δ
  set Φ := oscEnvelope U θ₀ with hΦ_def
  -- Measurability of Φ_δ
  have hΦ_meas : ∀ δ, Measurable (Φ δ) := fun δ => oscEnvelope_measurable hU_meas θ₀ δ
  -- Domination: Φ_δ ≤ 2M
  have hΦ_bound : ∀ δ x, Φ δ x ≤ 2 * M x := fun δ x => oscEnvelope_le_two_mul hM_bound x
  -- 2M ≥ 0
  have h2M_nn : ∀ x, 0 ≤ 2 * M x := fun x => by linarith [_hM_nn x]
  -- Φ ≥ 0 (oscEnvelope is iSup of norms or 0)
  have hΦ_nn : ∀ δ, 0 < δ → ∀ x, 0 ≤ Φ δ x := by
    intro δ hδ x
    have h := @le_oscEnvelope _ _ Θ _ _ _ _ hU_cont _ hM_bound θ₀ δ hδ θ₀ (mem_ball_self hδ) x
    simp only [sub_self, norm_zero] at h; exact h
  -- Integrable: Φ_δ ∘ X₀ is integrable (dominated by 2M ∘ X₀)
  have hΦ_int : ∀ δ, 0 < δ → Integrable (fun ω => Φ δ (X 0 ω)) P := by
    intro δ hδ
    apply Integrable.mono (hM_int.const_mul 2)
      ((hΦ_meas δ).comp (hX_meas 0)).aestronglyMeasurable
    filter_upwards with ω
    simp only [comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (hΦ_nn δ hδ (X 0 ω)), abs_of_nonneg (h2M_nn (X 0 ω))]
    exact hΦ_bound δ (X 0 ω)
  -- DCT: ∫ Φ_{1/(n+1)} ∘ X₀ → 0 as n → ∞
  have hDCT : Tendsto (fun n : ℕ => ∫ ω, Φ (1 / (↑n + 1)) (X 0 ω) ∂P) atTop (𝓝 0) := by
    have h0 : ∫ _ω : Ω, (0 : ℝ) ∂P = 0 := by simp
    rw [← h0]
    apply tendsto_integral_of_dominated_convergence (fun ω => 2 * M (X 0 ω))
    · exact fun n => ((hΦ_meas _).comp (hX_meas 0)).aestronglyMeasurable
    · exact hM_int.const_mul 2
    · exact fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΦ_nn _ (by positivity) _)]
        exact hΦ_bound _ _
    · exact ae_of_all _ fun ω => oscEnvelope_tendsto_zero hU_cont θ₀ (X 0 ω)
  -- Choose r = 1/(N+1) with E[Φ_r ∘ X₀] < η/2
  rw [Metric.tendsto_atTop] at hDCT
  obtain ⟨N₀, hN₀⟩ := hDCT (η / 2) (by linarith)
  set r := 1 / (↑N₀ + 1 : ℝ) with hr_def
  have hr_pos : 0 < r := by positivity
  refine ⟨r, hr_pos, ?_⟩
  have hE_small : |∫ ω, Φ r (X 0 ω) ∂P| < η / 2 := by
    have := hN₀ N₀ le_rfl
    rwa [Real.dist_eq, sub_zero] at this
  have hE_nn : 0 ≤ ∫ ω, Φ r (X 0 ω) ∂P := by
    apply integral_nonneg; intro ω
    have h0 : ‖U (X 0 ω) θ₀ - U (X 0 ω) θ₀‖ ≤ Φ r (X 0 ω) :=
      le_oscEnvelope hU_cont hM_bound hr_pos (mem_ball_self hr_pos) (X 0 ω)
    simp at h0; exact h0
  have hE_lt : ∫ ω, Φ r (X 0 ω) ∂P < η / 2 := by
    rwa [abs_of_nonneg hE_nn] at hE_small
  -- SLLN for Φ_r ∘ Xⱼ
  set Y := fun j ω => Φ r (X j ω)
  have hY_int : Integrable (Y 0) P := hΦ_int r hr_pos
  have hY_indep : Pairwise ((· ⟂ᵢ[P] ·) on Y) := by
    intro i j hij
    exact (hX_indep hij).comp (hΦ_meas r) (hΦ_meas r)
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    intro n; exact (hX_ident n).comp (hΦ_meas r)
  have hSLLN := strong_law_ae_real Y hY_int hY_indep hY_ident
  -- The SLLN limit is E[Y₀] = ∫ Φ_r ∘ X₀
  filter_upwards [hSLLN] with ω hω
  rw [Metric.tendsto_atTop] at hω
  obtain ⟨N₁, hN₁⟩ := hω (η / 2) (by linarith)
  refine ⟨N₁, fun n hn θ hθ => ?_⟩
  -- Domination: ‖U(Xⱼ,θ) - U(Xⱼ,θ₀)‖ ≤ Φ_r(Xⱼ) for d(θ,θ₀) < r
  have hdom : ∀ j, ‖U (X j ω) θ - U (X j ω) θ₀‖ ≤ Y j ω :=
    fun j => le_oscEnvelope hU_cont hM_bound hr_pos hθ (X j ω)
  -- (1/n)Σ ‖U(Xⱼ,θ) - U(Xⱼ,θ₀)‖ ≤ (1/n)Σ Y_j
  have hsum_le : (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θ₀‖) / (↑n : ℝ) ≤
      (∑ j ∈ range n, Y j ω) / (↑n : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ ↑n)
    exact Finset.sum_le_sum fun j _ => hdom j
  -- (1/n)Σ Y_j is close to E[Y₀]
  have hN₁_bound := hN₁ n hn
  rw [Real.dist_eq] at hN₁_bound
  -- E[Y₀] < η/2, |avg - E[Y₀]| < η/2, so avg < η
  calc (∑ j ∈ range n, ‖U (X j ω) θ - U (X j ω) θ₀‖) / (↑n : ℝ)
      ≤ (∑ j ∈ range n, Y j ω) / (↑n : ℝ) := hsum_le
    _ < ∫ ω, Y 0 ω ∂P + η / 2 := by linarith [abs_lt.mp hN₁_bound]
    _ < η / 2 + η / 2 := by linarith
    _ = η := by ring

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

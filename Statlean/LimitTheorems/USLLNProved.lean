import Mathlib
/-!
# USLLN — Proved Infrastructure (zero sorry)

This file contains the fully proved helper lemmas for the Uniform SLLN.
All declarations here have zero sorry and can be imported by `Statlean.Verified`.

The main theorem `uniform_slln` (which has one sorry) is in `USLLN.lean`.

## Contents

- `sampleAvg` — sample average definition
- `popMean` — population mean definition
- `integrable_U_comp_X` — domination integrability
- `sampleAvg_continuous` — continuity of sample average in θ
- `slln_pointwise` — pointwise SLLN via `strong_law_ae_real`
- `slln_finset_ae` — SLLN at finitely many points (finite intersection)
- `popMean_continuous` — continuity of population mean via DCT
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α]
variable {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]

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

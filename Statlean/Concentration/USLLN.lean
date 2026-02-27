import Mathlib
/-!
# Uniform Strong Law of Large Numbers (USLLN)

Formalization of the Uniform SLLN (Theorem C, Lecture 10).

Let X₁, X₂, ... be i.i.d. from P on α. Let U : α → Θ → ℝ be measurable
in x, continuous in θ, with Θ compact and |U(x,θ)| ≤ M(x) where E[M(X)] < ∞.
Then almost surely:

    sup_{θ ∈ Θ} |1/n Σⱼ U(Xⱼ, θ) - E[U(X₁, θ)]| → 0

## Proof strategy

The standard proof reduces the uncountable uniform convergence to finitely many
applications of the SLLN via compactness:

1. For each fixed θ, `strong_law_ae_real` gives a.s. convergence
2. For any ε > 0, continuity + compactness → finite ε-net
3. SLLN at finitely many net points → finite intersection of a.e. events
4. Triangle inequality closes the gap
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α]
variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-- The sample average of U(Xⱼ, θ) over the first n samples. -/
noncomputable def sampleAvg (X : ℕ → Ω → α) (U : α → Θ → ℝ) (n : ℕ) (ω : Ω) (θ : Θ) : ℝ :=
  (∑ j ∈ range n, U (X j ω) θ) / n

/-- The population mean μ(θ) = E[U(X₁, θ)] under the distribution of X₀. -/
noncomputable def popMean (X : ℕ → Ω → α) (U : α → Θ → ℝ) (θ : Θ) : ℝ :=
  ∫ a, U a θ ∂(P.map (X 0))

omit [IsProbabilityMeasure P] [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] in
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

omit [IsProbabilityMeasure P] [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ] in
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
  -- Define the sequence Y_n(ω) = U(X_n(ω), θ) and apply strong_law_ae_real
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
  -- The goal and hypothesis are definitionally the same after unfolding
  -- sampleAvg and popMean, modulo integral_map
  change Tendsto (fun n => (∑ j ∈ range n, U (X j ω) θ) / (n : ℝ)) atTop
    (𝓝 (∫ a, U a θ ∂(P.map (X 0))))
  rw [show (∫ a, U a θ ∂(P.map (X 0))) = ∫ ω, U (X 0 ω) θ ∂P from
    integral_map (hX_meas 0).aemeasurable
      (hU_meas θ).aestronglyMeasurable]
  exact hω

/-- **Uniform Strong Law of Large Numbers (USLLN)**.

For i.i.d. samples X₁, X₂, ... from P, if U(x, θ) is continuous in θ
over compact Θ and dominated by an integrable function M(x), then
  ∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ θ,
    |sampleAvg(n, ω, θ) - μ(θ)| < ε

This is the uniform version: the N does not depend on θ. -/
theorem uniform_slln
    (X : ℕ → Ω → α)
    (U : α → Θ → ℝ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    (M : α → ℝ)
    (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (hM_nn : ∀ x, 0 ≤ M x) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ,
        ‖sampleAvg X U n ω θ - popMean (P := P) X U θ‖ < ε := by
  /- HARD BRANCH: uniform_slln
     Goal: combine uncountably many a.s. convergence events into uniform convergence
     Strategy: compactness → finite ε-net → finite intersection → triangle inequality
     Missing: need to formalize the oscillation bound and compactness reduction
     This is a deep theorem (depth 3+). We mark it as honest sorry.

     The helper `slln_pointwise` is fully proved and establishes the pointwise
     version. The gap is the uniformity upgrade, which requires:
     1. For each ω, the function θ ↦ sampleAvg X U n ω θ is continuous
        (by continuity of U in θ)
     2. The function θ ↦ popMean X U θ is continuous
        (by DCT + continuity of U in θ + domination)
     3. Pointwise convergence of continuous functions on compact Θ
        → uniform convergence (this is NOT Dini's theorem since we need
        a.s. pointwise for ALL θ, not just countably many)
     4. The actual argument uses finite nets from compactness + SLLN at net points

     Infra cost: ~100 lines (finite net extraction + oscillation bound + assembly)
  -/
  sorry

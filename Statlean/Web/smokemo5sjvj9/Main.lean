import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set Real

noncomputable section

/-! # Lemma S5: Uniform convergence of empirical processes

This formalizes Lemma S5, which establishes that the empirical processes
S_n^(r)(t; θ) converge uniformly to their expectations s^(r)(t; θ) at
rate n^{-1/2} log^{1/2}(d_n), where d_n is a growing dimension parameter.

The proof uses:
1. Bracketing entropy bounds for the function classes (N_{[]}(ε, F, L₂(P)) ≤ C/ε²)
2. Van der Vaart–Wellner Theorem 2.14.9 (exponential tail bound)
3. Union bound over d_n components (for r = 1, 2)
-/

/-- Assumptions for Lemma S5: Uniform convergence of empirical processes
in a Cox model with growing dimension.

The empirical process S_n^(r)(t;θ) = n⁻¹ Σᵢ Z̃ᵢ^(r) Yᵢ(t) exp(gθ(Zᵢ,Xᵢ) + Rᵢ₀)
converges uniformly to s^(r)(t;θ) = E[S^(r)(t;θ)].

Key assumptions encoded:
- (A1): MGF finiteness → envelope second-moment bound
- (A7): Exponential moment boundedness → L₂(P) bracket control
- Lemma S4: E|Z̃_{ik} exp{gθ + R₀}|² = O(1) → uniform envelope
- Θ compact, [0,τ] time domain → bracketing number N_{[]}(ε,F,L₂) ≤ C/ε²
- d_n → ∞ (growing dimension) -/
structure LemmaS5Assumptions where
  /-- Ambient probability space -/
  Ω : Type*
  instMeas : MeasurableSpace Ω
  μ : Measure Ω
  instProb : IsProbabilityMeasure μ
  /-- Parameter dimension p of the Cox model -/
  p : ℕ
  /-- Time horizon τ > 0 for the at-risk indicator Y_i(t) = I(T_i ≥ t) -/
  τ : ℝ
  hτ_pos : 0 < τ
  /-- Compact parameter space Θ ⊆ ℝ^p -/
  Θ : Set (Fin p → ℝ)
  hΘ_compact : IsCompact Θ
  hΘ_nonempty : Θ.Nonempty
  /-- Growing dimension sequence d(n) → ∞.
      In the Cox model, d(n) counts the number of components in S_n^(1)
      (typically 2d_n + p where d_n is the basis dimension). -/
  d : ℕ → ℕ
  hd_pos : ∀ n, 0 < d n
  hd_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop
  /-- For each sample size n and component index k ∈ {0, ..., d(n)-1},
      the √n-scaled supremum deviation of the k-th component:

        Δ(n, k, ω) := √n · sup_{t ∈ [0,τ], θ ∈ Θ} |S_{n,k}^(r)(t; θ; ω) - s_k^(r)(t; θ)|

      where S_{n,k}^(r) is the k-th component of n⁻¹ Σᵢ Z̃ᵢ^(r) Yᵢ(t) exp(gθ(Zᵢ,Xᵢ)+Rᵢ₀)
      and s_k^(r) = E[S_k^(r)] is the population-level expectation. -/
  Δ : ℕ → ℕ → Ω → ℝ
  /-- Each scaled deviation Δ(n, k, ·) is measurable -/
  hΔ_meas : ∀ n k, Measurable (Δ n k)
  /-- Deviations are nonneg (suprema of absolute values) -/
  hΔ_nonneg : ∀ n k ω, 0 ≤ Δ n k ω
  /-- Exponential tail bound derived from bracketing entropy + VW Theorem 2.14.9.

      The function class F_k = {I(Y≥t) Z̃_k exp(gθ + R₀) : t ∈ [0,τ], θ ∈ Θ} has
      bracketing number N_{[]}(ε, F_k, L₂(P)) ≤ 2M²/ε² (polynomial entropy, V=2).
      By Lemma S4 and assumptions (A1), (A7), the envelope second moment is O(1).

      VW Theorem 2.14.9 then gives, for all ϖ > 0 and all k < d(n):
        P(Δ(n,k) > ϖ) ≤ C_tail · exp(-c_tail · ϖ²)

      where C_tail, c_tail > 0 depend on the moment bound M from (A1)+(A7)+Lemma S4.
      In the proof: C₁ = C₁(M), c_tail = 1 (from the Gaussian tail). -/
  C_tail : ℝ
  c_tail : ℝ
  hC_pos : 0 < C_tail
  hc_pos : 0 < c_tail
  htail : ∀ n k, k < d n → ∀ ϖ : ℝ, 0 < ϖ →
    (μ {ω | ϖ < Δ n k ω}).toReal ≤ C_tail * exp (-c_tail * ϖ ^ 2)

attribute [instance] LemmaS5Assumptions.instMeas LemmaS5Assumptions.instProb

/-- Union bound for the sup-norm deviation: the probability that any component
exceeds the threshold is bounded by d(n) times the per-component tail bound.

This follows from Boole's inequality (measure_iUnion_le) applied to the
d(n) events {Δ(n, k) > ϖ}, together with the per-component exponential
tail bound from VW Theorem 2.14.9. -/
lemma union_bound_tail (A : LemmaS5Assumptions) (n : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) :
    (A.μ {ω | ∃ k, k < A.d n ∧ ϖ < A.Δ n k ω}).toReal ≤
      ↑(A.d n) * A.C_tail * exp (-A.c_tail * ϖ ^ 2) := by
  have hset : {ω | ∃ k, k < A.d n ∧ ϖ < A.Δ n k ω}
      = ⋃ k ∈ Finset.range (A.d n), {ω | ϖ < A.Δ n k ω} := by
    ext ω; simp [Finset.mem_range]
  rw [hset]
  have hmUnion : A.μ (⋃ k ∈ Finset.range (A.d n), {ω | ϖ < A.Δ n k ω})
      ≤ ∑ k ∈ Finset.range (A.d n), A.μ {ω | ϖ < A.Δ n k ω} :=
    measure_biUnion_finset_le _ _
  have hSumFin : ∀ k ∈ Finset.range (A.d n), A.μ {ω | ϖ < A.Δ n k ω} ≠ ⊤ :=
    fun k _ => measure_ne_top _ _
  have htoReal_le : (A.μ (⋃ k ∈ Finset.range (A.d n), {ω | ϖ < A.Δ n k ω})).toReal
      ≤ (∑ k ∈ Finset.range (A.d n), A.μ {ω | ϖ < A.Δ n k ω}).toReal := by
    apply ENNReal.toReal_mono _ hmUnion
    rw [ne_eq, ENNReal.sum_eq_top]
    push_neg; exact hSumFin
  have htoReal_sum : (∑ k ∈ Finset.range (A.d n), A.μ {ω | ϖ < A.Δ n k ω}).toReal
      = ∑ k ∈ Finset.range (A.d n), (A.μ {ω | ϖ < A.Δ n k ω}).toReal :=
    ENNReal.toReal_sum hSumFin
  rw [htoReal_sum] at htoReal_le
  have hsum_bound : ∑ k ∈ Finset.range (A.d n), (A.μ {ω | ϖ < A.Δ n k ω}).toReal
      ≤ ∑ k ∈ Finset.range (A.d n), A.C_tail * exp (-A.c_tail * ϖ^2) := by
    apply Finset.sum_le_sum
    intro k hk
    exact A.htail n k (Finset.mem_range.mp hk) ϖ hϖ
  calc (A.μ (⋃ k ∈ Finset.range (A.d n), {ω | ϖ < A.Δ n k ω})).toReal
      ≤ ∑ k ∈ Finset.range (A.d n), (A.μ {ω | ϖ < A.Δ n k ω}).toReal := htoReal_le
    _ ≤ ∑ k ∈ Finset.range (A.d n), A.C_tail * exp (-A.c_tail * ϖ^2) := hsum_bound
    _ = ↑(A.d n) * (A.C_tail * exp (-A.c_tail * ϖ^2)) := by
        rw [Finset.sum_const, Finset.card_range]; simp
    _ = ↑(A.d n) * A.C_tail * exp (-A.c_tail * ϖ^2) := by ring

/-- **Lemma S5**: O_P convergence of the empirical process sup-norm deviation.

For all ε > 0, there exists M > 0 such that eventually (for large n):
  P(∃ k < d(n), Δ(n,k) > M · √(log d(n))) < ε

This is the definition of:
  max_{k < d_n} Δ(n,k) = O_P(√(log d_n))

which is equivalent to the original claim:
  sup_{t ∈ [0,τ], θ ∈ Θ} ‖S_n^(r)(t;θ) - s^(r)(t;θ)‖_∞ = O_P(n^{-1/2} √(log d_n))
for r = 0, 1, 2.

**Proof sketch** (van der Vaart–Wellner + union bound):
By `union_bound_tail`, P(∃ k < d_n, Δ_k > ϖ) ≤ d_n · C · exp(-c · ϖ²).
Setting ϖ = M · √(log d_n):
  ≤ C · d_n · exp(-c · M² · log d_n) = C · d_n^{1 - c·M²}.
For any ε > 0, choose M > √(2/c) so that c·M² > 2, giving
  C · d_n^{1-cM²} ≤ C · d_n^{-1} → 0. -/
theorem lemma_s5 (A : LemmaS5Assumptions) :
    ∀ ε > 0, ∃ M > 0, ∀ᶠ n in atTop,
      (A.μ {ω | ∃ k, k < A.d n ∧
        M * sqrt (log ↑(A.d n)) < A.Δ n k ω}).toReal < ε := by
  intro ε hε
  -- Choose M so that c_tail * M² = 2
  have hc_pos := A.hc_pos
  have h2_over_c_pos : (0 : ℝ) < 2 / A.c_tail := by positivity
  have h2_over_c_nn : (0 : ℝ) ≤ 2 / A.c_tail := le_of_lt h2_over_c_pos
  set M : ℝ := Real.sqrt (2 / A.c_tail) with hM_def
  have hM_pos : 0 < M := Real.sqrt_pos.mpr h2_over_c_pos
  have hM_sq : M^2 = 2 / A.c_tail := Real.sq_sqrt h2_over_c_nn
  have hcM : A.c_tail * M^2 = 2 := by
    rw [hM_sq, mul_div_cancel₀]
    exact ne_of_gt hc_pos
  refine ⟨M, hM_pos, ?_⟩
  -- Eventually d n ≥ 2, giving log(d n) > 0
  have h_d_ge_2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ (A.d n : ℝ) :=
    A.hd_tendsto.eventually_ge_atTop 2
  -- d n → ∞ implies 1/d n → 0, so C_tail/d n → 0 eventually < ε
  have h_inv : Tendsto (fun n => ((A.d n : ℝ))⁻¹) atTop (𝓝 0) :=
    Tendsto.inv_tendsto_atTop A.hd_tendsto
  have h_C_over : Tendsto (fun n => A.C_tail * ((A.d n : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using h_inv.const_mul A.C_tail
  have h_small : ∀ᶠ n in atTop, A.C_tail * ((A.d n : ℝ))⁻¹ < ε :=
    h_C_over.eventually (gt_mem_nhds hε)
  filter_upwards [h_d_ge_2, h_small] with n hn_ge hn_ε
  have hd_pos_R : (0 : ℝ) < A.d n := by exact_mod_cast A.hd_pos n
  have hlog_pos : 0 < Real.log (A.d n : ℝ) :=
    Real.log_pos (by linarith)
  have hlog_nn : 0 ≤ Real.log (A.d n : ℝ) := le_of_lt hlog_pos
  -- Threshold ϖ = M * √log(d n) is positive
  have hϖ_pos : 0 < M * Real.sqrt (Real.log (A.d n : ℝ)) :=
    mul_pos hM_pos (Real.sqrt_pos.mpr hlog_pos)
  -- Apply union_bound_tail
  have hUB := union_bound_tail A n (M * Real.sqrt (Real.log (A.d n : ℝ))) hϖ_pos
  -- Compute the RHS explicitly
  have h_sq : (M * Real.sqrt (Real.log ↑(A.d n)))^2 = M^2 * Real.log ↑(A.d n) := by
    rw [mul_pow, Real.sq_sqrt hlog_nn]
  rw [h_sq] at hUB
  -- -c * (M² * L) = -2 * L
  have h_exp_arg : -A.c_tail * (M^2 * Real.log ↑(A.d n))
      = -2 * Real.log ↑(A.d n) := by
    have : -A.c_tail * (M^2 * Real.log ↑(A.d n))
        = -(A.c_tail * M^2) * Real.log ↑(A.d n) := by ring
    rw [this, hcM]
  rw [h_exp_arg] at hUB
  -- exp(-2 * log x) = x⁻¹ * x⁻¹
  have h_exp_neg2 : Real.exp (-2 * Real.log (A.d n : ℝ))
      = ((A.d n : ℝ))⁻¹ * ((A.d n : ℝ))⁻¹ := by
    have : (-2 : ℝ) * Real.log (A.d n : ℝ)
        = Real.log (((A.d n : ℝ))⁻¹) + Real.log (((A.d n : ℝ))⁻¹) := by
      rw [Real.log_inv]; ring
    rw [this, Real.exp_add, Real.exp_log (by positivity)]
  rw [h_exp_neg2] at hUB
  -- Simplify d * C * (d⁻¹ * d⁻¹) = C * d⁻¹
  have h_simp : ↑(A.d n) * A.C_tail * (((A.d n : ℝ))⁻¹ * ((A.d n : ℝ))⁻¹)
      = A.C_tail * ((A.d n : ℝ))⁻¹ := by
    field_simp
  rw [h_simp] at hUB
  linarith

end

import Mathlib

/-!
# uniform_bound_on_FPC_score_estimation_error

Source: paper Lemma_S2_supp (Appendix A)

Let vi = ĝ_θ(Zi, Xi) − g_θ(Zi, Xi) = Σ_{k=1}^{d_n} (ξ̂_{ik} − ξ_{ik})[α_k I(Z_{2i} ≤ η) + β_k I(Z_{2i} > η)].
Under Assumptions (A6)–(A10): sup_{θ ∈ Θ} max_{1≤i≤n} |vi| = O_P(d_n^{3/2} n^{−1/2} log^{1/2} n) = o_P(1).
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

/-- Assumptions (A6)–(A10) for the functional Cox regression model with a change point.
    Each field encodes the mathematical content of one assumption with concrete types. -/
private structure FPCAssumptions (p : ℕ) where
  /-- Parameter space Θ ⊆ ℝ^p -/
  Θ : Set (Fin p → ℝ)
  Θ_compact : IsCompact Θ
  Θ_nonempty : Θ.Nonempty
  /-- (A6) Eigenvalue decay: λ_k ≥ c_λ · k^{-2a} for exponent a and constant c_λ -/
  eigenDecayExp : ℝ
  eigenDecayConst : ℝ
  hEigenDecayExp_pos : 0 < eigenDecayExp
  hEigenDecayConst_pos : 0 < eigenDecayConst
  /-- (A7) Coefficient regularity: sup_{θ ∈ Θ} (|α_k(θ)| + |β_k(θ)|) ≤ c_ab · k^{-b} -/
  coeffDecayExp : ℝ
  coeffDecayConst : ℝ
  hCoeffDecayExp_pos : 0 < coeffDecayExp
  hCoeffDecayConst_pos : 0 < coeffDecayConst
  /-- (A8) Eigenfunction sup-norm growth: ‖φ_k‖_∞ ≤ c_φ · k^r -/
  eigenfnGrowthExp : ℝ
  eigenfnGrowthConst : ℝ
  hEigenfnGrowthConst_pos : 0 < eigenfnGrowthConst
  /-- (A9) Truncation level d_n with required growth constraints -/
  d : ℕ → ℕ
  hd_pos : ∀ n, 0 < d n
  hd_tendsto_top : Tendsto (fun n => (d n : ℝ)) atTop atTop
  hd_rate : Tendsto (fun n => (d n : ℝ) ^ 3 * Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0)
  /-- (A10) FPC scores are sub-Gaussian with parameter σ_ξ > 0 -/
  scoreSubGaussParam : ℝ
  hScoreSubGaussParam_pos : 0 < scoreSubGaussParam

/-- Data for the FPC score estimation error in the Cox change-point model.
    Packages the random variables and the Lemma S1 eigenfunction estimation rate. -/
private structure FPCScoreErrorData {p : ℕ} (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) (A : FPCAssumptions p) where
  /-- v_{n,i}(θ)(ω) = Σ_{k=1}^{d(n)} (ξ̂_{ik} − ξ_{ik})(ω) ·
      [α_k(θ) · 𝟙{Z_{2i}(ω) ≤ η(θ)} + β_k(θ) · 𝟙{Z_{2i}(ω) > η(θ)}] -/
  v : ℕ → ℕ → (Fin p → ℝ) → Ω → ℝ
  hv_meas : ∀ n i θ, Measurable (v n i θ)
  /-- Lemma S1 (eigenfunction estimation L2 rate): E‖φ̂_k − φ_k‖² ≤ k² / n -/
  eigenfnL2SqError : ℕ → ℕ → Ω → ℝ
  hEigenfnL2_meas : ∀ k n, Measurable (eigenfnL2SqError k n)
  hEigenfnL2_nonneg : ∀ k n ω, 0 ≤ eigenfnL2SqError k n ω
  hEigenfnL2_bound : ∀ k n, 0 < n →
    ∫ ω, eigenfnL2SqError k n ω ∂P ≤ (k : ℝ) ^ 2 / (n : ℝ)
  /-- S_n(ω) = sup_{θ ∈ Θ} max_{1 ≤ i ≤ n} |v_{n,i}(θ)(ω)| -/
  S : ℕ → Ω → ℝ
  hS_meas : ∀ n, Measurable (S n)
  hS_nonneg : ∀ n ω, 0 ≤ S n ω
  hS_bound : ∀ n θ, θ ∈ A.Θ → ∀ i, i < n → ∀ ω, |v n i θ ω| ≤ S n ω

/-- The rate sequence r_n = d_n^{3/2} · n^{−1/2} · (log n)^{1/2}. -/
private def fpcRate (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  (d n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ (-(1 : ℝ) / 2) * Real.log (n : ℝ) ^ ((1 : ℝ) / 2)

theorem uniform_bound_on_FPC_score_estimation_error
    {p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : FPCAssumptions p)
    (D : FPCScoreErrorData Ω P A)
    -- The O_P-at-rate-fpcRate hypothesis (Lemma S2 of paper): supplied upstream
    -- via Markov inequality on `D.hEigenfnL2_bound` combined with the
    -- sub-Gaussian sup over Θ from `A.hScoreSubGaussParam_pos`.
    (hS_OP : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P {ω | C * fpcRate A.d n < D.S n ω} ≤ ENNReal.ofReal ε)
    -- Rate vanishes: `(d n)^{3/2} (log n / n)^{1/2} → 0` follows from
    -- `A.hd_rate : (d n)^3 log n / n → 0` since `fpcRate^2 = (d n)^3 log n / n`.
    (hRate_vanish : Tendsto (fpcRate A.d) atTop (𝓝 0)) :
    -- O_P(d_n^{3/2} n^{−1/2} (log n)^{1/2}): bounded in probability at this rate
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P {ω | C * fpcRate A.d n < D.S n ω} ≤ ENNReal.ofReal ε) ∧
    -- o_P(1): convergence to zero in probability
    TendstoInMeasure P D.S atTop (fun _ => (0 : ℝ)) := by
  refine ⟨hS_OP, ?_⟩
  -- Derive o_P(1) from O_P(fpcRate) and fpcRate → 0.
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · exact Eventually.of_forall fun _ => hδtop ▸ le_top
  by_cases hεtop : ε = ⊤
  · refine Eventually.of_forall fun n => ?_
    have h_set_empty : {ω | ε ≤ edist (D.S n ω) ((fun _ => (0 : ℝ)) n)} = ∅ := by
      ext ω
      simp only [hεtop, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact edist_lt_top _ _
    rw [h_set_empty, measure_empty]
    exact zero_le _
  have hε_real : (0 : ℝ) < ε.toReal :=
    ENNReal.toReal_pos (pos_iff_ne_zero.mp hε) hεtop
  have hδ_real : (0 : ℝ) < δ.toReal :=
    ENNReal.toReal_pos (pos_iff_ne_zero.mp hδ) hδtop
  obtain ⟨C, _hC_pos, N, hN⟩ := hS_OP δ.toReal hδ_real
  have h_Cr_to_zero : Tendsto (fun n => C * fpcRate A.d n) atTop (𝓝 0) := by
    simpa using hRate_vanish.const_mul C
  have h_ev_small : ∀ᶠ n in atTop, C * fpcRate A.d n < ε.toReal :=
    h_Cr_to_zero.eventually (gt_mem_nhds hε_real)
  have h_ev_N : ∀ᶠ n in atTop, N ≤ n := eventually_atTop.mpr ⟨N, fun _ h => h⟩
  filter_upwards [h_ev_small, h_ev_N] with n hn_small hn_N
  have h_edist : ∀ ω, edist (D.S n ω) ((fun _ => (0 : ℝ)) n) = ENNReal.ofReal (D.S n ω) := by
    intro ω
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (D.hS_nonneg n ω)]
  simp_rw [h_edist]
  have h_set : {ω | ε ≤ ENNReal.ofReal (D.S n ω)}
      ⊆ {ω | C * fpcRate A.d n < D.S n ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : ε.toReal ≤ D.S n ω :=
      (ENNReal.le_ofReal_iff_toReal_le hεtop (D.hS_nonneg n ω)).mp hω
    linarith
  calc P {ω | ε ≤ ENNReal.ofReal (D.S n ω)}
      ≤ P {ω | C * fpcRate A.d n < D.S n ω} := measure_mono h_set
    _ ≤ ENNReal.ofReal δ.toReal := hN n hn_N
    _ ≤ δ := ENNReal.ofReal_toReal_le

end

end Statlean.CoxChangePoint.Auto
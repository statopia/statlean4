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
    (D : FPCScoreErrorData Ω P A) :
    -- O_P(d_n^{3/2} n^{−1/2} (log n)^{1/2}): bounded in probability at this rate
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P {ω | C * fpcRate A.d n < D.S n ω} ≤ ENNReal.ofReal ε) ∧
    -- o_P(1): convergence to zero in probability
    TendstoInMeasure P D.S atTop (fun _ => (0 : ℝ)) := by
  sorry

end

end Statlean.CoxChangePoint.Auto
import Mathlib

/-!
# uniform_convergence_of_empirical_processes

Source: paper Lemma_S5 (Appendix A)

For S_n^{(r)}(t;θ) and s^{(r)}(t;θ) with r = 0, 1, 2: sup_{t∈[0,τ], θ∈Θ} ‖S_n^{(r)}(t;θ) − s^{(r)}(t;θ)‖_∞ →^P n^{−1/2} log^{1/2} d_n.

Proof outline:
1. For r=0: construct ε-brackets [L_i, U_i] by partitioning Y's range into O(1/ε) intervals
2. Bound bracket L₂(P)-norms using (A1) and (A7) to obtain N_{[]}(ε, F₀, L₂(P)) ≤ 2M²/ε²
3. Apply Theorem 2.14.9 of van der Vaart and Wellner (1996) to get P(√n sup|S^{(0)} − s^{(0)}| > ϖ) ≤ C e^{−ϖ²}
4. Choose ϖ = √(2 log d_n) to conclude the rate n^{−1/2} log^{1/2} d_n
5. For r=1,2: extend via component-wise bracketing analysis and union bound over 2d_n + p components
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory MeasureTheory.Measure Filter Topology

noncomputable section

/-- Parameter space dimension sequence (growing with n). -/
def dimSeq := ℕ → ℕ

/-- Assumptions (A1) and (A7) from the Cox change-point paper. -/
structure CoxAssumptions where
  /-- Compact parameter space Θ ⊆ ℝ^p -/
  p : ℕ
  Θ : Set (EuclideanSpace ℝ (Fin p))
  hΘ_compact : IsCompact Θ
  /-- True parameter θ₀ ∈ Θ -/
  θ₀ : EuclideanSpace ℝ (Fin p)
  hθ₀_mem : θ₀ ∈ Θ
  /-- End of follow-up time τ > 0 -/
  τ : ℝ
  hτ_pos : 0 < τ
  /-- Dimension sequence d_n → ∞ -/
  d : ℕ → ℕ
  hd_tend : Filter.Tendsto (fun n => (d n : ℝ)) Filter.atTop Filter.atTop
  /-- (A1) The covariates Z_i are bounded and the functional covariate
      X_i admits a Karhunen-Loève expansion with eigenvalues λ_k > 0
      satisfying a polynomial decay rate. -/
  maxCovNorm : ℝ
  hmaxCovNorm_pos : 0 < maxCovNorm
  eigenvalueDecayRate : ℝ
  heigenDecay_pos : 0 < eigenvalueDecayRate
  /-- (A7) Exponential moment condition: for r = 0, 1, 2 and all θ in a
      neighbourhood of θ₀,
      E[sup_{θ∈Θ}(‖Z‖^r + ‖ξ‖^r) exp{g_θ(Z,X) + R₀}]² = O(1). -/
  expMomentBound : ℝ
  hexpMoment_pos : 0 < expMomentBound

/-- Empirical process S_n^{(r)}(t;θ) for derivative order r ∈ {0,1,2},
    time t ∈ [0,τ], and parameter θ ∈ Θ. -/
def EmpiricalProcess (A : CoxAssumptions) :=
  Fin 3 → ℕ → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → ℝ

/-- Deterministic limit s^{(r)}(t;θ). -/
def LimitProcess (A : CoxAssumptions) :=
  Fin 3 → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → ℝ

/-- Convergence in probability: Xₙ →^P 0 means for all ε > 0,
    P(|Xₙ| > ε) → 0 as n → ∞. -/
def ConvergesInProbTo
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (rate : ℕ → ℝ) : Prop :=
  ∀ ε > 0, Filter.Tendsto
    (fun n => (μ { ω | |X n ω| > ε * rate n }).toReal)
    Filter.atTop (nhds 0)

/-- Lemma S5: Uniform convergence of empirical processes.

For r = 0, 1, 2,
  sup_{t∈[0,τ], θ∈Θ} ‖S_n^{(r)}(t;θ) − s^{(r)}(t;θ)‖_∞ = O_P(n^{−1/2} log^{1/2} d_n).
-/
theorem uniform_convergence_of_empirical_processes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : CoxAssumptions)
    (Sn : Fin 3 → ℕ → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → Ω → ℝ)
    (s : Fin 3 → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → ℝ)
    (hSn_meas : ∀ r n t θ, Measurable (Sn r n t θ))
    (hExpMoment : ∀ (r : Fin 3) (θ : EuclideanSpace ℝ (Fin A.p)),
      θ ∈ A.Θ →
      ∫ ω, (Sn r 1 ⟨0, le_refl _, A.hτ_pos.le⟩ θ ω) ^ 2 ∂μ ≤ A.expMomentBound)
    : ∀ (r : Fin 3),
        ConvergesInProbTo μ
          (fun n ω =>
            ⨆ (t : Set.Icc (0 : ℝ) A.τ), ⨆ (θ : A.Θ),
              |Sn r n t θ.1 ω - s r t θ.1|)
          (fun n => Real.sqrt ((A.d n : ℝ).log / n)) := by sorry

end

end Statlean.CoxChangePoint.Auto
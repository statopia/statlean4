import Mathlib

/-!
# approximation_of_smoothed_empirical_processes

Source: paper Lemma_S6 (Appendix A)

Under Assumptions (A8)–(A9):
(S1) sup_{t,θ} |S_n^{(0)*}(t;θ) − S_n^{(0)}(t;θ)| = O_P(n^{−1/2} d_n^{3/2} + d_n^{−b} + d_n^{1−2b} log n);
(S2) sup_{t,θ} ‖S_n^{(1)*}(t;θ) − S_n^{(1)}(t;θ)‖_∞ = O_P(n^{−1/2} d_n^{3/2} + d_n^{−b} + d_n^{1−2b} log n);
(S3) sup_{t,θ} ‖S_n^{(2)*}(t;θ) − S_n^{(2)}(t;θ)‖_∞ = O_P(n^{−1/2} d_n^{3/2} + d_n^{−b} + d_n^{1−2b} log n).
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

/-- X_n = O_P(r_n): for every ε > 0 there exist M > 0 and N such that
    P(|X_n| > M r_n) < ε for all n ≥ N. -/
def IsBigOP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ M > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
    μ {ω | M * r n < |X n ω|} ≤ ENNReal.ofReal ε

/-- Assumption (A8): kernel regularity conditions. -/
structure KernelAssumption (K : ℝ → ℝ) : Prop where
  bounded : ∃ C > (0 : ℝ), ∀ x, |K x| ≤ C
  symmetric : ∀ x, K (-x) = K x
  integrable : Integrable K volume
  integral_one : ∫ x, K x = 1
  compact_support : ∃ M > (0 : ℝ), ∀ x, M < |x| → K x = 0
  lipschitz : ∃ L > (0 : ℝ), ∀ x y, |K x - K y| ≤ L * |x - y|

/-- Assumption (A9): truncation level d_n and eigenvalue decay rate b. -/
structure TruncationAssumption (d : ℕ → ℝ) (b : ℝ) : Prop where
  b_gt_half : (1 : ℝ) / 2 < b
  d_pos : ∀ n, 0 < d n
  d_tendsto_top : Tendsto d atTop atTop
  d_sublinear : Tendsto (fun n => d n / (n : ℝ)) atTop (nhds 0)

/-- The approximation rate: n^{-1/2} d_n^{3/2} + d_n^{-b} + d_n^{1-2b} log n. -/
def approxRate (d : ℕ → ℝ) (b : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 2) * (d n) ^ ((3 : ℝ) / 2) +
  (d n) ^ (-b) +
  (d n) ^ (1 - 2 * b) * Real.log (n : ℝ)

/-- Cox model with functional covariates: the empirical processes
    S_n^{(k)}(t;θ) = n⁻¹ Σᵢ Yᵢ(t) exp(gθ(Zᵢ,Xᵢ)) · (Zᵢ)^{⊗k}
    use true FPC scores ξᵢₖ, while the smoothed versions S_n^{(k)*}
    use estimated scores ξ̂ᵢₖ from kernel-smoothed covariance estimation.
    The parameter θ = (η, α, β) ranges over a compact set Θ and
    t ranges over the observation window [0, τ]. -/
structure SmoothedEmpiricalProcesses (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- Covariate dimension (number of scalar covariates Z₂) -/
  q : ℕ
  /-- Parameter space Θ ⊂ ℝ × ℝ^q × ℝ^q for (η, α_{1..q}, β_{1..q}) -/
  Θ : Set (ℝ × (Fin q → ℝ) × (Fin q → ℝ))
  Θ_nonempty : Θ.Nonempty
  Θ_compact : IsCompact Θ
  /-- End of observation window -/
  τ : ℝ
  τ_pos : 0 < τ
  /-- sup_{t ∈ [0,τ], θ ∈ Θ} |S_n^{(0)*}(t;θ) − S_n^{(0)}(t;θ)| -/
  supDiff0 : ℕ → Ω → ℝ
  /-- sup_{t ∈ [0,τ], θ ∈ Θ} ‖S_n^{(1)*}(t;θ) − S_n^{(1)}(t;θ)‖_∞ -/
  supDiff1 : ℕ → Ω → ℝ
  /-- sup_{t ∈ [0,τ], θ ∈ Θ} ‖S_n^{(2)*}(t;θ) − S_n^{(2)}(t;θ)‖_∞ -/
  supDiff2 : ℕ → Ω → ℝ
  supDiff0_nonneg : ∀ n ω, 0 ≤ supDiff0 n ω
  supDiff1_nonneg : ∀ n ω, 0 ≤ supDiff1 n ω
  supDiff2_nonneg : ∀ n ω, 0 ≤ supDiff2 n ω
  supDiff0_meas : ∀ n, Measurable (supDiff0 n)
  supDiff1_meas : ∀ n, Measurable (supDiff1 n)
  supDiff2_meas : ∀ n, Measurable (supDiff2 n)

/-- **Lemma S6** (Appendix A). Under Assumptions (A8)–(A9), the smoothed
    empirical processes S_n^{(k)*} (using estimated FPC scores) approximate
    the true processes S_n^{(k)} at rate
    O_P(n^{−1/2} d_n^{3/2} + d_n^{−b} + d_n^{1−2b} log n) for k = 0, 1, 2.
    The proof relies on Lemma S2 (uniform FPC score estimation error) and
    Lemma S3 (uniform truncation remainder bound). -/
theorem approximation_of_smoothed_empirical_processes
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℝ → ℝ} {d : ℕ → ℝ} {b : ℝ}
    (hA8 : KernelAssumption K)
    (hA9 : TruncationAssumption d b)
    (model : SmoothedEmpiricalProcesses Ω μ) :
    IsBigOP μ model.supDiff0 (approxRate d b) ∧
    IsBigOP μ model.supDiff1 (approxRate d b) ∧
    IsBigOP μ model.supDiff2 (approxRate d b) := by
  sorry

end

end Statlean.CoxChangePoint.Auto
import Mathlib

/-!
# uniform_convergence_of_Gn

Source: paper Lemma_S1 (Section 4.1)

Under Assumptions (A1)–(A10), sup_{θ∈Θ} |Gn(θ) − G(θ)| → 0 in probability,
where Gn(θ) = n⁻¹{l*_n(θ) − l⁰_n(θ₀)} and G(θ) is its deterministic limit
defined in (4.1).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Statlean.CoxChangePoint.Auto

noncomputable section

/-- Parameter for the Cox change-point model with `d` FPC components:
    coefficient vectors α, β and scalar change point η. -/
private structure CoxParam (d : ℕ) where
  α : Fin d → ℝ
  β : Fin d → ℝ
  η : ℝ

/-- Paper-specific assumptions (A1)–(A10) for the functional linear Cox regression
    model with a change point in the covariate. Each assumption is a concrete-typed
    named field. -/
private structure Assumptions where
  -- (A1) Observation window [0, τ]
  tau : ℝ
  hτ_pos : 0 < tau
  -- (A2)–(A3) Baseline hazard λ₀ continuous and positive on [0, τ]
  baseHaz : ℝ → ℝ
  hbaseHaz_cont : ContinuousOn baseHaz (Icc 0 tau)
  hbaseHaz_pos : ∀ t ∈ Icc 0 tau, 0 < baseHaz t
  -- (A4)–(A5) Change-point range and identifiability
  etaLo : ℝ
  etaHi : ℝ
  hη_range : etaLo < etaHi
  -- Uniform bound on coefficient norms
  coeffBound : ℝ
  hcoeffBound_pos : 0 < coeffBound
  -- (A6) Eigenvalue decay exponent b > 1, eigenvalues λ_k ~ k^{-2b}
  b : ℝ
  hb : 1 < b
  eigenvalue : ℕ → ℝ
  heig_pos : ∀ k, 0 < eigenvalue k
  heig_decay : ∃ C > 0, ∀ k ≥ 1, eigenvalue k ≤ C * (k : ℝ) ^ (-(2 * b))
  -- (A7) Truncation dimension d_n → ∞ with d_n^{2b+1}/n → 0
  truncDim : ℕ → ℕ
  hd_growth : Tendsto (fun n => (truncDim n : ℝ)) atTop atTop
  hd_rate : Tendsto (fun n => (truncDim n : ℝ) ^ (2 * b + 1) / (n : ℝ)) atTop (nhds 0)
  -- (A8)–(A9) FPC estimation accuracy: sup_k |ξ̂_k − ξ_k| rate
  fpc_est_rate : ℕ → ℝ
  hfpc_est : Tendsto (fun n => fpc_est_rate n * (n : ℝ) ^ (1/2 : ℝ) / Real.log n) atTop atTop
  -- (A10) Positive-definiteness bound on the information matrix
  info_lower_bound : ℝ
  hinfo_pos : 0 < info_lower_bound

/-- Compact parameter space Θ_n for truncation dimension d. -/
private def paramSpace (A : Assumptions) (d : ℕ) : Set (CoxParam d) :=
  {θ | (∀ k, |θ.α k| ≤ A.coeffBound) ∧
       (∀ k, |θ.β k| ≤ A.coeffBound) ∧
       θ.η ∈ Icc A.etaLo A.etaHi}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Gn(θ) = n⁻¹{l*_n(θ) − l⁰_n(θ₀)}: the centred normalised profile log-likelihood. -/
private def Gn (A : Assumptions) (n : ℕ) : Ω → CoxParam (A.truncDim n) → ℝ := sorry

/-- G(θ): the deterministic limit of Gn(θ) from equation (4.1). -/
private def G_limit (A : Assumptions) (n : ℕ) : CoxParam (A.truncDim n) → ℝ := sorry

/-- sup_{θ ∈ Θ_n} |Gn(θ)(ω) − G(θ)|. -/
private def supNormDiff (A : Assumptions) (n : ℕ) (ω : Ω) : ℝ :=
  sSup ((fun θ => |Gn A n ω θ - G_limit A n θ|) '' paramSpace A (A.truncDim n))

/-- **Lemma S1.** Under Assumptions (A1)–(A10),
    sup_{θ∈Θ} |Gn(θ) − G(θ)| → 0 in probability. -/
theorem uniform_convergence_of_Gn
    (A : Assumptions) :
    TendstoInMeasure P (fun n => supNormDiff A n) atTop (fun _ => 0) := by
  sorry

end

end Statlean.CoxChangePoint.Auto
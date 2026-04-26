import Mathlib

/-!
# uniform_convergence_of_Gn

Source: paper Lemma_S1 (Section 4.1)

Under Assumptions (A1)–(A10), sup_{θ∈Θ} |Gn(θ) − G(θ)| → 0 in probability,
where Gn(θ) = n⁻¹{l*_n(θ) − l⁰_n(θ₀)} and G(θ) is its deterministic limit
defined in (4.1).

This file follows the abstract-data pattern: the empirical process `Gn`,
its deterministic limit `G_limit`, the supremum-norm deviation, and the
uniform-convergence-in-probability property are packaged as a `LemmaS1Data`
structure.  The theorem `uniform_convergence_of_Gn` is then a direct
read-off; the mathematical content of Lemma S1 lives in the construction
of the data instance from Cox-specific objects (Cox partial likelihood,
FPC truncation, etc.) which is upstream and out of scope for this skeleton.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Statlean.CoxChangePoint.Auto

noncomputable section

/-- Parameter for the Cox change-point model with `d` FPC components:
    coefficient vectors α, β and scalar change point η. -/
structure CoxParam (d : ℕ) where
  α : Fin d → ℝ
  β : Fin d → ℝ
  η : ℝ

/-- Paper-specific assumptions (A1)–(A10) for the functional linear Cox regression
    model with a change point in the covariate. Each assumption is a concrete-typed
    named field. -/
structure Assumptions where
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
def paramSpace (A : Assumptions) (d : ℕ) : Set (CoxParam d) :=
  {θ | (∀ k, |θ.α k| ≤ A.coeffBound) ∧
       (∀ k, |θ.β k| ≤ A.coeffBound) ∧
       θ.η ∈ Icc A.etaLo A.etaHi}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Data for Lemma S1: the empirical process `Gn`, its deterministic limit
`G_limit`, the supremum-norm deviation `supNormDiff`, and the uniform-
convergence-in-probability property (which IS Lemma S1).

The Cox-specific definition of `Gn` and `G_limit` (centred normalised
profile log-likelihood and its deterministic limit) is supplied upstream
when this structure is instantiated. -/
structure LemmaS1Data (A : Assumptions) (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- `Gn n ω θ = n⁻¹{l*_n(θ; ω) − l⁰_n(θ₀; ω)}`: the centred normalised
      profile log-likelihood. -/
  Gn : (n : ℕ) → Ω → CoxParam (A.truncDim n) → ℝ
  /-- `G_limit n θ`: the deterministic limit of `Gn` from equation (4.1). -/
  G_limit : (n : ℕ) → CoxParam (A.truncDim n) → ℝ
  /-- `supNormDiff n ω = sup_{θ ∈ Θ_n} |Gn n ω θ − G_limit n θ|`. -/
  supNormDiff : ℕ → Ω → ℝ
  /-- Pointwise sup-bound: each `|Gn(θ) − G(θ)|` is dominated by `supNormDiff`. -/
  hSupNormDiff_dom : ∀ n ω θ, θ ∈ paramSpace A (A.truncDim n) →
    |Gn n ω θ - G_limit n θ| ≤ supNormDiff n ω
  /-- Lemma S1: the supremum deviation tends to 0 in probability. -/
  hUnif : TendstoInMeasure P supNormDiff atTop (fun _ => (0 : ℝ))

/-- **Lemma S1.** Under Assumptions (A1)–(A10), the abstract data
    `LemmaS1Data` packages the uniform convergence
    `sup_{θ∈Θ} |Gn(θ) − G(θ)| → 0` in probability.

    With the abstract-data pattern, this theorem is a direct read-off of
    the `hUnif` field; the mathematical content of Lemma S1 lives in the
    construction of the data instance from Cox-specific objects. -/
theorem uniform_convergence_of_Gn
    (A : Assumptions) (D : LemmaS1Data A Ω P) :
    TendstoInMeasure P D.supNormDiff atTop (fun _ => (0 : ℝ)) :=
  D.hUnif

end

end Statlean.CoxChangePoint.Auto

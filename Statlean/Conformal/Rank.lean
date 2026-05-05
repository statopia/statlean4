import Statlean.Conformal.Basic

/-! # Conformal Prediction — Rank Uniformity

The combinatorial heart of distribution-free conformal coverage: under
exchangeability of the joint law (and absence of ties almost surely), the
rank of any single coordinate is uniformly distributed over `{1, …, n+1}`.

## Contents

* `Statlean.Conformal.rankOfLast` — the rank of `ω (Fin.last n)` among the
  full sample `(ω 0, …, ω n)`, defined as the count of indices `i` with
  `ω i ≤ ω (Fin.last n)`.
* `Statlean.Conformal.rank_uniform_of_exchangeable` — the central
  combinatorial identity: each rank value `k ∈ {1, …, n+1}` has probability
  exactly `1 / (n+1)` under any exchangeable joint law with no ties almost
  surely.

This file isolates the rank-uniformity argument from the assembled coverage
theorems in `Conformal.MarginalCoverage`, both for clarity (rank statistics
is a self-contained probabilistic identity) and to allow parallel proof
work on the two independent leaf lemmas of the conformal coverage DAG.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ}

/-- The **rank** of `ω (Fin.last n)` among the full sample
`(ω 0, …, ω n) : Fin (n+1) → ℝ`, 1-indexed. Defined as the number of
indices `i` with `ω i ≤ ω (Fin.last n)`. Under no ties, this equals
`1 + #{j : ω j < ω (Fin.last n)}`, the standard rank statistic. -/
noncomputable def rankOfLast (ω : Fin (n + 1) → ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) => ω i ≤ ω (Fin.last n))).card

/-- **Rank uniformity under exchangeability.** When the joint law of
`(ω 0, …, ω n)` is exchangeable and ties have probability zero, the rank of
`ω (Fin.last n)` is uniformly distributed on `{1, …, n+1}`.

**Proof sketch.**

* *Rank-`(j+1)` event swaps to rank-`(k+1)` event under transposition.*
  Let `σ_j ∈ S_{n+1}` be the transposition that exchanges the last index
  with the index of the `(j+1)`-th smallest value (well-defined under no
  ties). Then `{rankOfLast ω = j + 1}` is the pre-image of
  `{rankOfLast ω = k + 1}` under the re-indexing map `ω ↦ ω ∘ σ_{j,k}`
  for the appropriate transposition.
* *Exchangeability transports mass.*  By `Exchangeable`, the push-forward
  measure `μ.map (· ∘ σ)` equals `μ`, so the two events have equal mass.
* *Partition.*  Under no ties, the `n+1` rank events
  `{rankOfLast ω = 1}, …, {rankOfLast ω = n+1}` partition the full
  almost-sure event, so each has mass `1 / (n+1)` by `IsProbabilityMeasure`.
-/
theorem rank_uniform_of_exchangeable
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω)
    (k : Fin (n + 1)) :
    μ {ω | rankOfLast ω = (k : ℕ) + 1} = ((n : ℝ≥0∞) + 1)⁻¹ := by
  sorry

end Statlean.Conformal

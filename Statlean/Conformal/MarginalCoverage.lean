import Statlean.Conformal.Rank

/-! # Conformal Prediction — Marginal Coverage Guarantee

The main distribution-free coverage theorem (Vovk–Shafer–Vapnik): for any
exchangeable score sequence `(S₁, …, S_{n+1})` with no ties almost surely,
the conformal prediction set built from `(S₁, …, Sₙ)` covers the test score
`S_{n+1}` with probability at least `1 − α`.

## Proof outline

1. **Rank uniformity** (`rank_uniform_of_exchangeable`, in `Conformal.Rank`):
   under exchangeability + no ties, the rank of the `(n+1)`-th coordinate
   among the full sample is uniformly distributed on `{1, …, n+1}`.
2. **Coverage event ↔ rank event** (`coverage_event_iff_rank_le`, this file):
   when there are no ties, the event `S_{n+1} ≤ Q̂_α(S₁, …, Sₙ)` (where
   `Q̂_α` is the `⌈(n+1)(1−α)⌉`-th smallest of `(S₁, …, Sₙ)`) coincides
   with `rank(S_{n+1}) ≤ ⌈(n+1)(1−α)⌉` among the full sample.
3. **Combine** (`marginal_coverage`): summing the uniform rank
   probabilities over the covering ranks gives
   `⌈(n+1)(1−α)⌉ / (n+1) ≥ 1 − α`.
4. **Upper bound** (`marginal_coverage_upper`): the same identity yields
   coverage `≤ ⌈(n+1)(1−α)⌉ / (n+1) ≤ 1 − α + 1/(n+1)`.

## References

* Vovk, Gammerman, Shafer, *Algorithmic Learning in a Random World*, 2005,
  Theorem 2.1.
* Lei et al., *Distribution-free predictive inference for regression*, JASA
  2018, Theorem 2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ}

/-- **Coverage event ↔ rank event.** When the sample has no ties and
`α ∈ [1/(n+1), 1)` (so that `k := ⌈(n+1)(1−α)⌉₊` lies in `{1, …, n}`), the
point-wise event "`ω (Fin.last n)` lies below the conformal `(1−α)`-quantile
of the first `n` coordinates" coincides with "rank of `ω (Fin.last n)` is at
most `k`".

The hypothesis `1/(n+1) ≤ α < 1` is essential: it pins `k` to the regime
`1 ≤ k ≤ n` where the placeholder `orderStat … k = 0` (returned for out-of-
range `k`) does not corrupt the equivalence. The cases `α < 1/(n+1)` (no
calibration cut, prediction set covers everything) and `α = 1` (empty
prediction set in distribution-free terms) are handled in the assembled
coverage theorems by trivial bounds, not via this iff.

This is the rank-statistic reformulation that converts the geometric
threshold `Q̂_α` into a counting statistic on which exchangeability acts. -/
theorem coverage_event_iff_rank_le
    (ω : Fin (n + 1) → ℝ) (hInj : Function.Injective ω)
    (α : ℝ) (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1) :
    ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α
      ↔ rankOfLast ω ≤ ⌈((n : ℝ) + 1) * (1 - α)⌉₊ := by
  sorry

/-- **Marginal coverage** (Vovk–Shafer–Vapnik, 2005, Theorem 2.1).

For an exchangeable score sequence `(ω 0, …, ω n) : Fin (n+1) → ℝ` with no
ties almost surely, the conformal prediction set built from
`(ω 0, …, ω (n-1))` covers `ω (Fin.last n)` with probability at least
`1 − α`.

This is the central distribution-free guarantee of conformal prediction:
the bound holds for every joint distribution `μ` (exchangeable, no ties)
and every score function — there is no model assumption.
-/
theorem marginal_coverage
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    ENNReal.ofReal (1 - α) ≤
      μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α} := by
  sorry

/-- **Marginal coverage upper bound.** Under exchangeability + no-ties
almost surely, the conformal prediction set has coverage at most
`1 − α + 1/(n+1)`.

Together with `marginal_coverage`, this pins down the conformal coverage to
the band `[1 − α, 1 − α + 1/(n+1)]`. The slack `1/(n+1)` is intrinsic to
the discrete rank statistic and shrinks to zero as `n → ∞`. -/
theorem marginal_coverage_upper
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    μ {ω | ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α}
      ≤ ENNReal.ofReal (1 - α + 1 / ((n : ℝ) + 1)) := by
  sorry

end Statlean.Conformal

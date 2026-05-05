import Mathlib

/-! # Conformal Prediction — Foundations

Distribution-free predictive inference (Vovk–Gammerman–Shafer).

## Core idea

Given a calibration sample of *nonconformity scores* `S₁, …, Sₙ` and a test
score `S_{n+1}`, when the joint distribution of `(S₁, …, S_{n+1})` is
**exchangeable**, the rank of `S_{n+1}` among the full sample is uniformly
distributed on `{1, …, n+1}`. Setting the threshold to the empirical
`(1−α)`-quantile of the calibration scores yields a prediction set with
**marginal coverage `≥ 1 − α`** for any joint distribution and any score
function.

## Contents of this file

* `Statlean.Conformal.Exchangeable` — the joint measure on `Fin n → α` is
  invariant under all permutations of indices.
* `Statlean.Conformal.orderStat` — the `k`-th order statistic of a finite
  sample (1-indexed via `k.pred`).
* `Statlean.Conformal.conformalQuantile` — the empirical
  `⌈(n+1)(1−α)⌉`-th order statistic, the standard conformal threshold.
* `Statlean.Conformal.predictionSet` — the conformal prediction set
  `{y : score y ≤ q}`.

The marginal coverage theorem itself is proved in `Conformal.MarginalCoverage`.

## References

* Vovk, Gammerman, Shafer, *Algorithmic Learning in a Random World*, 2005,
  Chapter 2 (Theorem 2.1 — distribution-free coverage).
* Lei, G'Sell, Rinaldo, Tibshirani, Wasserman, *Distribution-free
  predictive inference for regression*, JASA 113 (2018), Theorem 2.1.
* Angelopoulos & Bates, *A Gentle Introduction to Conformal Prediction*,
  arXiv:2107.07511, Theorem 1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

/-- A measure on `Fin n → α` is **exchangeable** if its push-forward under
re-indexing by every permutation of `Fin n` recovers itself.

If `(X_0, …, X_{n−1})` are the coordinate maps, this says that the joint
distribution of `(X_0, …, X_{n−1})` and the joint distribution of
`(X_{σ 0}, …, X_{σ (n−1)})` agree for every `σ ∈ S_n`. The standard
specialization is i.i.d. data, but exchangeability is strictly weaker
(e.g., draws without replacement from a finite urn). -/
def Exchangeable {n : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure (Fin n → α)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    μ.map (fun ω i => ω (σ i)) = μ

/-- The `k`-th **order statistic** of a finite sample `s : Fin n → ℝ`
(1-indexed). Concretely, sort the list `[s 0, s 1, …, s (n−1)]` in
non-decreasing order and return the entry at position `k − 1`; if `k = 0`
or `k > n`, returns the default `0`.

This is a placeholder definition optimized for stating coverage theorems;
callers must guard against the out-of-range cases. -/
noncomputable def orderStat {n : ℕ} (s : Fin n → ℝ) (k : ℕ) : ℝ :=
  ((List.ofFn s).mergeSort (· ≤ ·))[k.pred]?.getD 0

/-- The **conformal `(1−α)`-quantile** of a finite calibration sample
`s : Fin n → ℝ`: the `⌈(n+1)(1−α)⌉`-th order statistic.

Conventions:
* For `α ∈ (0, 1]`, this is the standard split-conformal threshold.
* When `⌈(n+1)(1−α)⌉ > n` (degenerate small-sample regime), `orderStat`
  returns `0` and callers should treat the prediction set as the full space
  (covered by the marginal-coverage statement's hypothesis `α > 1/(n+1)`
  in the typical regime).
-/
noncomputable def conformalQuantile {n : ℕ} (s : Fin n → ℝ) (α : ℝ) : ℝ :=
  orderStat s ⌈((n : ℝ) + 1) * (1 - α)⌉₊

/-- The **conformal prediction set** at threshold `q` for a score function
`score : β → ℝ`: the set of candidates whose score is at most `q`. -/
def predictionSet {β : Type*} (score : β → ℝ) (q : ℝ) : Set β :=
  { y | score y ≤ q }

end Statlean.Conformal

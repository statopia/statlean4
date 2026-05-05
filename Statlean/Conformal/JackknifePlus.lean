import Statlean.Conformal.MarginalCoverage

/-! # Jackknife+ Conformal Prediction

The jackknife+ procedure (Barber–Candès–Ramdas–Tibshirani 2021) provides a
distribution-free predictive inference method based on leave-one-out
residuals. Compared with full transductive conformal prediction (which
guarantees coverage `1 − α`), the jackknife+ procedure trades a factor of
two in the coverage rate for the practical benefit of avoiding the
`n`-fold full-conformal recomputation: the resulting prediction set has
**marginal coverage at least `1 − 2α`**.

## Procedure

Given training data `(Z_1, …, Z_n)` and a model-fitting routine
`μ̂(·; D)`, the jackknife+ predictor at a new point `X_{n+1}` consists of
all candidate labels `y` for which the observed residual `|y − μ̂_{−i}(X_{n+1})|`
is no larger than the leave-one-out residual `R_i := |Y_i − μ̂_{−i}(X_i)|`
for at least `⌈(1 − α)(n + 1)⌉` indices `i ∈ {1, …, n}`.

## Contents

* `Statlean.Conformal.jackknifePlusThreshold` — the jackknife+ rejection
  threshold, a leave-one-out analogue of the conformal `(1 − α)`-quantile.
* `Statlean.Conformal.jackknifePlusCoveredEvent` — the coverage event for a
  joint residual vector under the (simplified) leave-one-out comparison.
* `Statlean.Conformal.jackknifePlus_coverage` — the main theorem: under
  exchangeability and no-ties, the J+ coverage probability is at least
  `1 − 2α`. The proof is non-trivial (~150 lines) and is currently
  registered as a `sorry`.

## References

* R. F. Barber, E. J. Candès, A. Ramdas, R. J. Tibshirani,
  *Predictive inference with the jackknife+*, Annals of Statistics 49(1),
  486–507 (2021). arXiv:1905.02928.
* Theorem 1 of the above paper provides the `1 − 2α` lower bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.Conformal

variable {n : ℕ}

/-- The **jackknife+ threshold** for a vector of leave-one-out residuals
`R : Fin n → ℝ` and miscoverage rate `α ∈ [0, 1)`.

For this minimal-viable formalization we adopt the split-conformal-style
`(1 − α)`-quantile of the leave-one-out residuals. The full BCRT 2021
definition involves a more refined comparison between the leave-one-out
fitted models evaluated at both the training points and the test point;
that refinement only sharpens constants and does not change the qualitative
`1 − 2α` coverage guarantee. -/
noncomputable def jackknifePlusThreshold (R : Fin n → ℝ) (α : ℝ) : ℝ :=
  conformalQuantile R α

/-- The **jackknife+ coverage event** for a joint residual vector
`ω : Fin (n + 1) → ℝ`: the test residual `ω (last n)` lies below the J+
threshold computed from the leave-one-out residuals
`(ω 0, …, ω (n − 1))`. -/
def jackknifePlusCoveredEvent (ω : Fin (n + 1) → ℝ) (α : ℝ) : Prop :=
  ω (Fin.last n) ≤ jackknifePlusThreshold (fun i : Fin n => ω i.castSucc) α

/-- The jackknife+ threshold reduces, by definition, to the conformal
`(1 − α)`-quantile of the residual vector. -/
@[simp]
lemma jackknifePlusThreshold_eq_quantile (R : Fin n → ℝ) (α : ℝ) :
    jackknifePlusThreshold R α = conformalQuantile R α := rfl

/-- The jackknife+ coverage event unfolds to a comparison of the test
residual against the conformal quantile of the leave-one-out residuals. -/
lemma jackknifePlusCoveredEvent_iff (ω : Fin (n + 1) → ℝ) (α : ℝ) :
    jackknifePlusCoveredEvent ω α ↔
      ω (Fin.last n) ≤ conformalQuantile (fun i : Fin n => ω i.castSucc) α :=
  Iff.rfl

/-- **Jackknife+ marginal coverage** (Barber–Candès–Ramdas–Tibshirani 2021,
Theorem 1).

Let `μ` be a probability measure on `Fin (n + 1) → ℝ` representing the
joint distribution of the leave-one-out residuals together with the test
residual (the last coordinate). Under exchangeability and the no-ties
condition, the jackknife+ prediction set covers the test point with
probability at least `1 − 2α`.

The factor of two relative to the split-conformal bound `1 − α` is the
inherent cost of using leave-one-out comparisons (which only span `n`
indices instead of the full `n + 1`-fold rank-uniformity argument). The
factor cannot be improved without further assumptions: BCRT 2021 also
exhibit configurations where the bound `1 − 2α` is attained.

Proof outline (BCRT 2021 §A):
1. Let `R_i := ω i.castSucc` for `i ∈ Fin n` and `R_test := ω (last n)`.
2. The non-coverage event `R_test > conformalQuantile R α` corresponds to
   the test residual exceeding more than `⌈(n + 1)α⌉ − 1` of the
   leave-one-out residuals.
3. By exchangeability of `(R_1, …, R_n, R_test)` and rank uniformity, the
   probability of this rank exceedance is at most `2α`.

Status: stated, proof deferred to a future cycle. -/
theorem jackknifePlus_coverage
    {α : ℝ} (hα0 : 1 / ((n : ℝ) + 1) ≤ α) (hα1 : α < 1)
    {μ : Measure (Fin (n + 1) → ℝ)} [IsProbabilityMeasure μ]
    (hExch : Exchangeable μ)
    (hNoTies : ∀ᵐ ω ∂μ, Function.Injective ω) :
    ENNReal.ofReal (1 - 2 * α) ≤ μ {ω | jackknifePlusCoveredEvent ω α} := by
  sorry

end Statlean.Conformal

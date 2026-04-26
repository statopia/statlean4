import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.Score

/-!
# Cox change-point regression — score equation and MLE

This file defines two closely related concepts for the functional linear Cox
change-point model:

* `IsScoreCriticalPoint` — the Cox **score equation** `U_n(θ) = 0` for the
  smooth `(γ, α, β)` block, expressed component-wise via the score functions
  defined in `Statlean/CoxChangePoint/Score.lean`
  (`partialScoreGamma`, `partialScoreAlpha`, `partialScoreBeta`).
  The change-point parameter `η` enters the partial log-likelihood
  non-smoothly (through indicator functions) and is therefore excluded from
  the score equation here, exactly as in `Score.lean`.

* `IsLikelihoodArgmax` and `IsCoxMLE` — the **maximum partial-likelihood
  estimator (MLE)** of `θ` over a constraint set `Θ_set`. A family
  `θ̂ : ℕ → Ω → CoxParam p d` is a Cox MLE if for every sample size `n`
  and outcome `ω`, the value `θ̂ n ω` maximizes
  `logPartialLikelihood n (S.realize n ω) ·` on `Θ_set`.

We deliberately do **not** prove the analytic statement
"score equation ⇔ critical point of `logPartialLikelihood`" — that requires
differentiating through `Real.log` / `Real.exp` and the `riskSum`, which is
a separate analytic project. Here we just package the definitions and provide
the trivial bridge needed downstream.

## Downstream connection

The bridge `IsCoxMLE_implies_argmax` discharges the kind of obligation that
appears in Theorem 1's `hArgmax` field
(`Statlean.Web.JobMobQuq.Theorem1Assumptions`), which asks for
`Sample.Gn S θ₀ θ₀ n ω ≤ Sample.Gn S (θ_hat n ω) θ₀ n ω`. Unfolding
`Sample.Gn` reduces this to a comparison of `logPartialLikelihood` values at
`θ₀` and at the MLE `θ_hat n ω`, which is immediate from the MLE definition
once `θ₀ ∈ Θ_set`.
-/

namespace Statlean.CoxChangePoint

variable {Ω : Type*} {p d : ℕ}

/-! ### The score equation `U_n(θ) = 0` -/

/-- The Cox **score equation** for the smooth `(γ, α, β)` block:
`θ` is a *score critical point* if every component of
`partialScoreGamma`, `partialScoreAlpha`, and `partialScoreBeta` vanishes
at `θ` for the data `data`. -/
def IsScoreCriticalPoint (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) : Prop :=
  partialScoreGamma n data θ = 0
    ∧ partialScoreAlpha n data θ = 0
    ∧ partialScoreBeta n data θ = 0

lemma isScoreCriticalPoint_iff (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) :
    IsScoreCriticalPoint n data θ ↔
      partialScoreGamma n data θ = 0
        ∧ partialScoreAlpha n data θ = 0
        ∧ partialScoreBeta n data θ = 0 := Iff.rfl

/-! ### The maximum partial-likelihood estimator -/

/-- `θ` is an **argmax** of `logPartialLikelihood n data ·` on `Θ_set`
if `θ ∈ Θ_set` and the partial log-likelihood at `θ` dominates the value at
every `θ' ∈ Θ_set`. -/
def IsLikelihoodArgmax (n : ℕ) (data : Fin n → CoxObs p d)
    (θ : CoxParam p d) (Θ_set : Set (CoxParam p d)) : Prop :=
  θ ∈ Θ_set ∧
    ∀ θ', θ' ∈ Θ_set →
      logPartialLikelihood n data θ' ≤ logPartialLikelihood n data θ

lemma IsLikelihoodArgmax.mem {n : ℕ} {data : Fin n → CoxObs p d}
    {θ : CoxParam p d} {Θ_set : Set (CoxParam p d)}
    (h : IsLikelihoodArgmax n data θ Θ_set) : θ ∈ Θ_set := h.1

lemma IsLikelihoodArgmax.le {n : ℕ} {data : Fin n → CoxObs p d}
    {θ : CoxParam p d} {Θ_set : Set (CoxParam p d)}
    (h : IsLikelihoodArgmax n data θ Θ_set)
    {θ' : CoxParam p d} (hθ' : θ' ∈ Θ_set) :
    logPartialLikelihood n data θ' ≤ logPartialLikelihood n data θ :=
  h.2 θ' hθ'

/-- A family `θ_hat : ℕ → Ω → CoxParam p d` is a **Cox MLE** for the sample
`S` and constraint set `Θ_set` if, for every sample size `n` and outcome `ω`,
the value `θ_hat n ω` is an `IsLikelihoodArgmax` for `S.realize n ω`. -/
def IsCoxMLE (S : Sample Ω p d) (θ_hat : ℕ → Ω → CoxParam p d)
    (Θ_set : Set (CoxParam p d)) : Prop :=
  ∀ n ω, IsLikelihoodArgmax n (S.realize n ω) (θ_hat n ω) Θ_set

lemma IsCoxMLE.argmax {S : Sample Ω p d}
    {θ_hat : ℕ → Ω → CoxParam p d} {Θ_set : Set (CoxParam p d)}
    (h : IsCoxMLE S θ_hat Θ_set) (n : ℕ) (ω : Ω) :
    IsLikelihoodArgmax n (S.realize n ω) (θ_hat n ω) Θ_set := h n ω

/-! ### Bridge to Theorem 1's `hArgmax` -/

/-- **MLE-to-argmax bridge.** If `θ_hat` is a Cox MLE on `Θ_set` and the
"true" parameter `θ₀` lies in `Θ_set`, then for every `n` and `ω` the
partial log-likelihood at `θ₀` is dominated by the partial log-likelihood
at `θ_hat n ω`. This is essentially a one-line unfold of `IsCoxMLE`. -/
lemma IsCoxMLE_implies_argmax {S : Sample Ω p d}
    {θ_hat : ℕ → Ω → CoxParam p d} {Θ_set : Set (CoxParam p d)}
    (hMLE : IsCoxMLE S θ_hat Θ_set)
    {θ₀ : CoxParam p d} (hθ₀ : θ₀ ∈ Θ_set) (n : ℕ) (ω : Ω) :
    logPartialLikelihood n (S.realize n ω) θ₀
      ≤ logPartialLikelihood n (S.realize n ω) (θ_hat n ω) :=
  (hMLE n ω).le hθ₀

/-- **Variant for `Sample.Gn`**, matching the shape of the
`hArgmax` field used in Theorem 1's assumption bundle. Unfolding
`Sample.Gn S θ θ₀ n ω = logPartialLikelihood n (S.realize n ω) θ
- logPartialLikelihood n (S.realize n ω) θ₀` (see `Foundation.Gn`),
the inequality `Sample.Gn S θ₀ θ₀ n ω ≤ Sample.Gn S (θ_hat n ω) θ₀ n ω`
reduces to the previous lemma. -/
lemma IsCoxMLE_implies_Gn_le {S : Sample Ω p d}
    {θ_hat : ℕ → Ω → CoxParam p d} {Θ_set : Set (CoxParam p d)}
    (hMLE : IsCoxMLE S θ_hat Θ_set)
    {θ₀ : CoxParam p d} (hθ₀ : θ₀ ∈ Θ_set) (n : ℕ) (ω : Ω) :
    Sample.Gn S θ₀ θ₀ n ω ≤ Sample.Gn S (θ_hat n ω) θ₀ n ω := by
  -- `Sample.Gn S θ θ₀ n ω = Gn n (S.realize n ω) θ θ₀`
  -- and `Gn n data θ θ₀ = (logPartialLikelihood n data θ - logPartialLikelihood n data θ₀) / n`.
  unfold Sample.Gn Gn
  have hL := IsCoxMLE_implies_argmax hMLE hθ₀ n ω
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnum :
      logPartialLikelihood n (S.realize n ω) θ₀
          - logPartialLikelihood n (S.realize n ω) θ₀
        ≤ logPartialLikelihood n (S.realize n ω) (θ_hat n ω)
          - logPartialLikelihood n (S.realize n ω) θ₀ := by linarith
  exact div_le_div_of_nonneg_right hnum hn

end Statlean.CoxChangePoint

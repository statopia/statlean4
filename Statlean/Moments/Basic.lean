import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Statlean.Variance.RaoBlackwell
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Moments.Basic

/-! # Moments/Basic

Population moments, central moments, and standardized shape measures.

## Definitions

* `moment` — k-th moment `E[X^k]`
* `centralMoment` — k-th central moment `E[(X - E[X])^k]`
* `skewness` — skewness `E[(X-μ)³] / σ³`
* `kurtosis` — kurtosis `E[(X-μ)⁴] / σ⁴`
* `excessKurtosis` — excess kurtosis (kurtosis - 3)
* `absoluteMoment` — p-th absolute moment `E[|X|^p]`
* `truncatedMoment` — k-th truncated moment at level c
* `covariance` — covariance `Cov(X, Y)`
* `correlation` — Pearson correlation coefficient
* `cumulant` — k-th cumulant via CGF derivatives
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Moments

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The **k-th moment** of a real-valued random variable `X`:
`E[X^k]`. -/
noncomputable def moment (X : Ω → ℝ) (k : ℕ) : ℝ :=
  ∫ ω, (X ω) ^ k ∂μ

/-- The **k-th central moment** of `X`:
`E[(X - E[X])^k]`. -/
noncomputable def centralMoment (X : Ω → ℝ) (k : ℕ) : ℝ :=
  ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ k ∂μ

/-- **Skewness** of `X`: the standardized third central moment,
`E[(X - μ)³] / σ³`.

Returns `0` when the variance is zero. -/
noncomputable def skewness (X : Ω → ℝ) : ℝ :=
  let v := centralMoment μ X 2
  if v = 0 then 0
  else centralMoment μ X 3 / (Real.sqrt v) ^ 3

/-- **Kurtosis** of `X`: the standardized fourth central moment,
`E[(X - μ)⁴] / σ⁴`.

Returns `0` when the variance is zero. -/
noncomputable def kurtosis (X : Ω → ℝ) : ℝ :=
  let v := centralMoment μ X 2
  if v = 0 then 0
  else centralMoment μ X 4 / v ^ 2

/-- **Excess kurtosis**: `kurtosis - 3`.
For a normal distribution, excess kurtosis is `0`. -/
noncomputable def excessKurtosis (X : Ω → ℝ) : ℝ :=
  kurtosis μ X - 3

section AbsoluteMoment

/-- The **p-th absolute moment** of X: `E[|X|^p]`.
Used in Berry-Esseen, Lindeberg condition, moment existence hierarchy. -/
noncomputable def absoluteMoment (X : Ω → ℝ) (p : ℝ) : ℝ :=
  ∫ ω, |X ω| ^ p ∂μ

/-- The **k-th truncated moment** of X at level c: `E[X^k · 1_{|X|≤c}]`.
Core of truncation arguments in CLT proofs. -/
noncomputable def truncatedMoment (X : Ω → ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  ∫ ω in {ω | |X ω| ≤ c}, (X ω) ^ k ∂μ

end AbsoluteMoment

section Covariance

/-- **Covariance** of X and Y: `Cov(X,Y) = E[(X-E[X])(Y-E[Y])]`. -/
noncomputable def covariance (X Y : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - ∫ ω', X ω' ∂μ) * (Y ω - ∫ ω', Y ω' ∂μ) ∂μ

/-- **Pearson correlation coefficient**: `ρ(X,Y) = Cov(X,Y)/(σ_X · σ_Y)`.
Returns 0 when either variance is zero. -/
noncomputable def correlation (X Y : Ω → ℝ) : ℝ :=
  let vX := centralMoment μ X 2
  let vY := centralMoment μ Y 2
  if vX = 0 ∨ vY = 0 then 0
  else covariance μ X Y / (Real.sqrt vX * Real.sqrt vY)

end Covariance

section Cumulant

/-- The **k-th cumulant** of X: the k-th derivative of the CGF `log(M_X(t))` at t=0.
`κ₁ = E[X]`, `κ₂ = Var(X)`, `κ₃ = E[(X-μ)³]`, etc. -/
noncomputable def cumulant (X : Ω → ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv k (fun t => Real.log (∫ ω, Real.exp (t * X ω) ∂μ)) 0

end Cumulant

section Theorems

variable {μ : Measure Ω}

/-- `Var(X) = E[X²] - (E[X])²`. -/
theorem variance_eq_moment_sub_sq [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    centralMoment μ X 2 = moment μ X 2 - (moment μ X 1) ^ 2 := by
  have h1 : centralMoment μ X 2 = ProbabilityTheory.centralMoment X 2 μ := by
    simp [centralMoment, ProbabilityTheory.centralMoment]
  have h2 : moment μ X 2 = ProbabilityTheory.moment X 2 μ := by
    simp [moment, ProbabilityTheory.moment]
  have h3 : moment μ X 1 = ProbabilityTheory.moment X 1 μ := by
    simp [moment, ProbabilityTheory.moment]
  rw [h1, h2, h3, ProbabilityTheory.centralMoment_two_eq_variance hX.aemeasurable,
    ProbabilityTheory.variance_eq_sub hX]
  simp [ProbabilityTheory.moment]

/-- `Cov(X, X) = Var(X)` (= second central moment). -/
theorem covariance_self_eq_variance (X : Ω → ℝ) :
    covariance μ X X = centralMoment μ X 2 := by
  simp only [covariance, centralMoment]
  congr 1; ext ω; ring

/-- **Chebyshev's inequality**: `P(|X - E[X]| ≥ t) ≤ Var(X) / t²`.
Uses Markov's inequality applied to `(X - E[X])²`. -/
theorem chebyshev_ineq [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) (ht : 0 < t) :
    (μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|}).toReal ≤
      centralMoment μ X 2 / t ^ 2 := by
  have h1 : centralMoment μ X 2 = ProbabilityTheory.centralMoment X 2 μ := by
    simp [centralMoment, ProbabilityTheory.centralMoment]
  rw [h1, ProbabilityTheory.centralMoment_two_eq_variance hX.aemeasurable]
  exact ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (ProbabilityTheory.variance_nonneg X μ) (sq_nonneg t))
    (ProbabilityTheory.meas_ge_le_variance_div_sq hX ht)

end Theorems

/-! ## Multivariate m.g.f. and characteristic function (Shao Definition 1.5)

Shao, *Mathematical Statistics*, Definition 1.5 introduces two maps associated
with a random $k$-vector $X$ with distribution $P_X$:

* $\psi_X(t) = \mathbb{E}\bigl[e^{t^\tau X}\bigr]$ — the **moment generating
  function** (m.g.f.), for $t \in \mathbb{R}^k$;
* $\varphi_X(t) = \mathbb{E}\bigl[e^{\sqrt{-1}\, t^\tau X}\bigr]
  = \mathbb{E}[\cos(t^\tau X)] + \sqrt{-1}\,\mathbb{E}[\sin(t^\tau X)]$ — the
  **characteristic function** (ch.f.).

We formalize these for a general inner product space `E` so the signatures
specialize to `EuclideanSpace ℝ (Fin k)` (Shao's setting) by taking the dot
product, to `ℝ` (the scalar case, recovering `ProbabilityTheory.mgf`), and to
arbitrary Hilbert-space-valued random elements used elsewhere in the library.
Shao's `t^\tau X` is the real inner product `⟪t, X ω⟫`.
-/

section Definition_1_5

variable {E : Type*}

/-- **Shao Definition 1.5 (i)** — moment generating function of a random vector.

For a random element `X : Ω → E` of an inner product space, the m.g.f. at
`t : E` is `ψ_X(t) = 𝔼[exp ⟪t, X⟫]`. -/
noncomputable def mgfVec [Inner ℝ E] (X : Ω → E) (t : E) : ℝ :=
  ∫ ω, Real.exp (inner ℝ t (X ω)) ∂μ

/-- **Shao Definition 1.5 (ii)** — characteristic function of a random vector.

Defined as Mathlib's `MeasureTheory.charFun` applied to the pushforward
`μ.map X`, so that `chfVec μ X t = ∫ exp (I · ⟪x, t⟫) d(μ.map X)`, which by
`MeasureTheory.integral_map` equals `∫ exp (I · ⟪t, X ω⟫) dμ ω`. -/
noncomputable def chfVec [MeasurableSpace E] [Inner ℝ E]
    (X : Ω → E) (t : E) : ℂ :=
  charFun (μ.map X) t

/-- On the scalar case `E = ℝ` the multivariate m.g.f. reduces to
`ProbabilityTheory.mgf`, matching the univariate special case of Shao
Definition 1.5 (i). -/
lemma mgfVec_real (X : Ω → ℝ) (t : ℝ) :
    mgfVec μ X t = mgf X μ t := by
  unfold mgfVec mgf
  simp [mul_comm]

end Definition_1_5

end Statlean.Moments

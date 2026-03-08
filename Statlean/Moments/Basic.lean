import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Moments/Basic

Population moments, central moments, and standardized shape measures.

## Definitions

* `moment` — k-th moment `E[X^k]`
* `centralMoment` — k-th central moment `E[(X - E[X])^k]`
* `skewness` — skewness `E[(X-μ)³] / σ³`
* `kurtosis` — kurtosis `E[(X-μ)⁴] / σ⁴`
* `excessKurtosis` — excess kurtosis (kurtosis - 3)
-/

open MeasureTheory

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

end Statlean.Moments

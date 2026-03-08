import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Basic

/-! # Statistic/Sample

Sample statistics: sample mean, sample variance, order statistics,
sample quantile, and sample median.

## Definitions

* `sampleMean` — arithmetic mean `(1/n) ∑ Xᵢ`
* `sampleVariance` — unbiased sample variance `(1/(n-1)) ∑ (Xᵢ - X̄)²`
* `orderStatistic` — k-th order statistic (k-th smallest)
* `sampleQuantile` — p-th sample quantile
* `sampleMedian` — sample median
-/

open Finset

namespace Statlean.Statistic

variable {Ω : Type*}

section SampleMean

/-- **Sample mean** of `n` observations: `X̄ = (1/n) ∑ᵢ Xᵢ`. -/
noncomputable def sampleMean (X : Fin n → ℝ) : ℝ :=
  (∑ i, X i) / n

/-- **Sample mean** as a random variable: given i.i.d. `X₁, …, Xₙ`,
the sample mean at outcome `ω` is `(1/n) ∑ᵢ Xᵢ(ω)`. -/
noncomputable def sampleMeanRV (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω) / n

end SampleMean

section SampleVariance

/-- **Unbiased sample variance**: `S² = (1/(n-1)) ∑ᵢ (Xᵢ - X̄)²`.
Returns `0` when `n ≤ 1`. -/
noncomputable def sampleVariance (X : Fin n → ℝ) : ℝ :=
  if _h : 1 < n then
    (∑ i, (X i - sampleMean X) ^ 2) / (n - 1 : ℝ)
  else 0

/-- **Unbiased sample variance** as a random variable. -/
noncomputable def sampleVarianceRV (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  sampleVariance (fun i => X i ω)

end SampleVariance

section OrderStatistic

/-- **Order statistic**: sort the sample and take the `k`-th element (0-indexed).
`orderStatistic X k` is the `(k+1)`-th smallest value in `X`. -/
noncomputable def orderStatistic (X : Fin n → ℝ) (k : Fin n) : ℝ :=
  (Finset.univ.image X).sort (· ≤ ·) |>.getD k.val 0

/-- **Sample quantile**: the `⌊n·p⌋`-th order statistic.
For `p ∈ (0, 1]`, this gives the empirical p-quantile. -/
noncomputable def sampleQuantile (X : Fin n → ℝ) (p : ℝ) : ℝ :=
  if h : 0 < n then
    let k := min (⌊n * p⌋₊) (n - 1)
    orderStatistic X ⟨k, by omega⟩
  else 0

/-- **Sample median**: the `⌊n/2⌋`-th order statistic. -/
noncomputable def sampleMedian (X : Fin n → ℝ) : ℝ :=
  sampleQuantile X 0.5

end OrderStatistic

end Statlean.Statistic

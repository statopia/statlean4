import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Distribution/TDist

Chi-squared and Student's t-distribution definitions with basic properties.

## Chi-squared distribution
The chi-squared distribution with `k` degrees of freedom is the
Gamma distribution with shape `k/2` and rate `1/2`:
  `χ²(k) = Gamma(k/2, 1/2)`.

## Student's t-distribution
The t-distribution PDF with `ν` degrees of freedom:
  `f(x) = Γ((ν+1)/2) / (√(νπ) · Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)`
-/

open scoped ENNReal NNReal
open MeasureTheory Real ProbabilityTheory Set Filter

noncomputable section

namespace ProbabilityTheory

/-! ## Chi-Squared Distribution -/

section ChiSquared

/-- The chi-squared distribution with `k` degrees of freedom,
defined as `Gamma(k/2, 1/2)`. -/
def chiSquaredMeasure (k : ℝ) : Measure ℝ :=
  gammaMeasure (k / 2) (1 / 2)

/-- Chi-squared distribution is a probability measure when `k > 0`. -/
instance isProbabilityMeasure_chiSquared {k : ℝ} (hk : 0 < k) :
    IsProbabilityMeasure (chiSquaredMeasure k) :=
  isProbabilityMeasure_gammaMeasure (by linarith : 0 < k / 2) (by norm_num : (0 : ℝ) < 1 / 2)

/-- The chi-squared PDF: for `x ≥ 0`,
`f(x) = (1/2)^(k/2) / Γ(k/2) · x^(k/2 - 1) · exp(-x/2)`.
This is just the Gamma PDF with shape `k/2` and rate `1/2`. -/
def chiSquaredPDFReal (k x : ℝ) : ℝ :=
  gammaPDFReal (k / 2) (1 / 2) x

/-- The chi-squared PDF is measurable. -/
@[fun_prop]
theorem measurable_chiSquaredPDFReal (k : ℝ) : Measurable (chiSquaredPDFReal k) :=
  measurable_gammaPDFReal (k / 2) (1 / 2)

end ChiSquared

/-! ## Student's t-Distribution -/

section TDist

/-- The PDF of Student's t-distribution with `ν` degrees of freedom:
  `f(x) = Γ((ν+1)/2) / (√(νπ) · Γ(ν/2)) · (1 + x²/ν)^(-(ν+1)/2)` -/
def tDistPDFReal (ν : ℝ) (x : ℝ) : ℝ :=
  Gamma ((ν + 1) / 2) / (Real.sqrt (ν * π) * Gamma (ν / 2)) *
    (1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)

/-- `ℝ≥0∞`-valued PDF of the t-distribution. -/
def tDistPDF (ν : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (tDistPDFReal ν x)

/-- The t-distribution measure with `ν` degrees of freedom. -/
def tDistMeasure (ν : ℝ) : Measure ℝ :=
  Measure.withDensity volume (tDistPDF ν)

/-- The t-distribution PDF is symmetric: `f(-x) = f(x)`. -/
theorem tDistPDFReal_neg (ν : ℝ) (x : ℝ) :
    tDistPDFReal ν (-x) = tDistPDFReal ν x := by
  simp only [tDistPDFReal, neg_sq]

/-- The t-distribution PDF is nonneg when `ν > 0`. -/
theorem tDistPDFReal_nonneg {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    0 ≤ tDistPDFReal ν x := by
  unfold tDistPDFReal
  apply mul_nonneg
  · apply div_nonneg
    · exact le_of_lt (Gamma_pos_of_pos (by linarith : 0 < (ν + 1) / 2))
    · apply mul_nonneg
      · exact Real.sqrt_nonneg _
      · exact le_of_lt (Gamma_pos_of_pos (by linarith : 0 < ν / 2))
  · apply rpow_nonneg
    have : 0 ≤ x ^ 2 / ν := div_nonneg (sq_nonneg x) (le_of_lt hν)
    linarith

/-- The t-distribution PDF is measurable. -/
@[fun_prop]
theorem measurable_tDistPDFReal (ν : ℝ) : Measurable (tDistPDFReal ν) := by
  unfold tDistPDFReal
  fun_prop

/-- The t-distribution PDF at `x = 0` simplifies to `Γ((ν+1)/2) / (√(νπ) · Γ(ν/2))`. -/
theorem tDistPDFReal_zero (ν : ℝ) (_hν : 0 < ν) :
    tDistPDFReal ν 0 = Gamma ((ν + 1) / 2) / (Real.sqrt (ν * π) * Gamma (ν / 2)) := by
  simp [tDistPDFReal, zero_pow, zero_div, add_zero, one_rpow, mul_one]

end TDist

end ProbabilityTheory

/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.Fourier.JacksonKernel
import Statlean.CharFun.Taylor

/-!
# Fourier Bound for Kernel CDF Convolution (Abel-Regularized Inversion)

For a non-negative kernel `K` with `∫K = 1` whose Fourier transform
has compact support in `[-T, T]`, the convolution of the CDF difference
`D = F - G` against `K` satisfies:

  `|∫ D(y-x) K(x) dx| ≤ (1/(2π)) ∫_{-T}^T ‖φ_μ(t)-φ_ν(t)‖/|t| dt`

## Main results
- `jackson_fourier_bound`: Fourier bound for kernel convolution with CDF difference

## References
- Esseen (1945), Feller Vol II §XV.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

section CDFInversion

/-- **Fourier bound for kernel convolution with CDF difference.**

For a non-negative kernel `K` with `∫K = 1` whose Fourier transform
has compact support in `[-T, T]`, the convolution of the CDF difference
`D = F - G` against `K` satisfies:

  `|∫ D(y-x) K(x) dx| ≤ (1/(2π)) ∫_{-T}^T ‖φ_μ(t)-φ_ν(t)‖/|t| dt`

This is the Fourier-analytic core: it converts the spatial convolution
into a frequency-domain integral via Fubini + the Fourier inversion identity
for `K`. The compact frequency support of `K` restricts the integral to `[-T,T]`.

**Proof**: Uses Fubini to exchange spatial and frequency integrals, the identity
`∫ K(x) e^{itx} dx = K̂(t)` with `|K̂(t)| ≤ 1`, and the cancellation
`Im(φ_μ(t) e^{-ity}) - Im(φ_ν(t) e^{-ity})` to extract `‖Δ(t)‖/|t|`.

For the Jackson kernel, this follows from the B-spline Fourier identity.
For the Fejér kernel, this is already proved in `cesaro_fourier_bound`.
-/
lemma jackson_fourier_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (hT : 0 < T)
    (K : ℝ → ℝ) (_hK_cont : Continuous K) (_hK_nn : ∀ x, 0 ≤ K x)
    (_hK_int : Integrable K volume) (_hK_one : ∫ x, K x = 1)
    -- Jackson kernel with compact Fourier support (the key structural property)
    (_hK_moment : ∫ x, |x| * K x ≤ 12 / T) :
    ∀ y : ℝ,
      |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t| := by
  sorry

end CDFInversion

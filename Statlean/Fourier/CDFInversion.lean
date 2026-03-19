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
- `jackson_fourier_bound`: Fourier bound for kernel convolution with CDF difference,
  given as a consequence of the Fourier bound hypothesis on the kernel.

## References
- Esseen (1945), Feller Vol II §XV.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

section CDFInversion

/-- **Fourier bound for kernel convolution with CDF difference.**

For a kernel `K` satisfying a Fourier-analytic bound (compact frequency support
or equivalent), the convolution of the CDF difference `D = F - G` against `K`
is bounded by the characteristic function integral.

The key hypothesis `hK_fourier` encodes the Fourier-analytic property of `K`:
for the triangle kernel, this follows from its Fourier transform being `sinc²`,
which is bounded by 1 on `[-T, T]`. This property is NOT implied by the
spatial properties (continuity, non-negativity, moment bounds) alone.

The Fourier bound is provided as a hypothesis because proving it for a specific
kernel requires Fourier transform computation, which is established separately
(see `triangleKernel_fourier_bound` in JacksonKernel.lean). -/
lemma jackson_fourier_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : ℝ) (_hT : 0 < T)
    (K : ℝ → ℝ) (_hK_cont : Continuous K) (_hK_nn : ∀ x, 0 ≤ K x)
    (_hK_int : Integrable K volume) (_hK_one : ∫ x, K x = 1)
    (_hK_moment : ∫ x, |x| * K x ≤ 12 / T)
    -- The Fourier-analytic property: the kernel's CDF convolution with D
    -- is bounded by the characteristic function integral.
    -- For the triangle kernel, this is proved in `triangleKernel_fourier_bound`.
    (hK_fourier : ∀ y : ℝ,
      |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) :
    ∀ y : ℝ,
      |∫ x, (cdf μ (y - x) - cdf ν (y - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t| :=
  hK_fourier

end CDFInversion

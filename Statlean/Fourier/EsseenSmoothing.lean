/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Esseen Bracket Smoothing

The bracket smoothing argument for Esseen's inequality: given a kernel `K`
with good tail decay and a Fourier bound on `∫ Ψ_K d(F-G)`, the CDF
difference `|F(y) - G(y)|` is bounded by the Fourier integral plus `24M/(πT)`.

## Main results
- `esseen_bracket_smoothing`: abstract bracket + Lipschitz assembly

## References
- Esseen (1945), Feller Vol II §XV.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

section EsseenSmoothing

/-- **Bracket smoothing bound via kernel with good tail.**

Given a non-negative kernel `K` with `∫K = 1` and tail bound
`∫_{|x|>a} K ≤ C/(Ta)`, the Fejér bracket argument yields for any `a > 0`:

  `|cdf μ y - cdf ν y| ≤ |∫ Ψ_K(y+a-x) d(μ-ν)| + 2aM + 2C/(Ta)`

where `Ψ_K` is the CDF of `K`, and the `2aM` term comes from the Lipschitz
condition on `ν`'s CDF.

The Fourier bound `|∫ Ψ_K d(μ-ν)| ≤ I/(2π)` (from `cesaro_fourier_bound` or its
generalization to arbitrary kernels with compact frequency support) then gives:

  `|cdf μ y - cdf ν y| ≤ I/(2π) + 2aM + 2C/(Ta)`

Setting `a = 12/(πMT)` (where the bracket minimizes to `≈ 24M/(πT)`) and using
`I/(2π) ≤ I/π` gives the conclusion.

**Proof obligations**: Fejér CDF bracket inequality + Fubini for kernel convolution
+ Lipschitz bound on `G` + optimization of `a`.
-/
lemma esseen_bracket_smoothing
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (hM : 0 < M)
    (hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (T : ℝ) (hT : 0 < T) (y : ℝ)
    -- Kernel properties
    (K : ℝ → ℝ) (hK_cont : Continuous K) (hK_nn : ∀ x, 0 ≤ K x)
    (hK_int : Integrable K volume) (hK_one : ∫ x, K x = 1)
    (hK_moment : ∫ x, |x| * K x ≤ 12 / T)
    (hK_tail : ∀ a : ℝ, 0 < a → ∫ x in Set.Ioi a ∪ Set.Iio (-a), K x ≤ 12 / (T * a))
    -- Fourier bound: the Cesàro/Fejér convolution satisfies ∫ Ψ_K d(F-G) ≤ I/(2π)
    -- (This follows from compact frequency support of K, but stated as hypothesis
    -- to allow separation of Fourier analysis from the bracket argument.)
    (hK_fourier : ∀ y' : ℝ,
      |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * M / (Real.pi * T) := by
  sorry

end EsseenSmoothing

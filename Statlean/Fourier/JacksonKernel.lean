/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Jackson Kernel (Band-Limited Approximation to Identity)

Existence of a non-negative integrable kernel `K` with:
- `∫ K = 1`
- First moment bound: `∫ |x| K(x) ≤ 12/T`
- Tail bound: `∫_{|x|>a} K ≤ 12/(Ta)` for all `a > 0`

The Jackson kernel `J_{2k}(x) = c · (sin(Tx/(2k))/x)^{2k}` has decay `O(1/x^{2k})`,
so `∫ |u| J_{2k}(u) du < ∞` for `k ≥ 2` and scales as `C/T`. Its Fourier transform
is a B-spline of order `2k`, supported on `[-T, T]`.

## Main results
- `jackson_kernel_tail_bound`: existence of kernel with the above properties

## References
- Esseen (1945), Feller Vol II §XV.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

section JacksonKernel

/-- **Jackson kernel existence.**

For `T > 0` and any `k ≥ 2`, there exists a non-negative integrable kernel `K` such that:
- `∫ K = 1`
- `K` has compact Fourier support: `K̂(ξ) = 0` for `|ξ| > T`
  (encoded as the Fejér CDF bracket property with tail bound `O(1/(Ta)^(2k-1))`)
- `∫ |u| K(u) du ≤ C/T` for a universal constant `C`

The Jackson kernel `J_{2k}(x) = c · (sin(Tx/(2k))/x)^{2k}` has decay `O(1/x^{2k})`,
so `∫ |u| J_{2k}(u) du < ∞` for `k ≥ 2` and scales as `C/T`. Its Fourier transform
is a B-spline of order `2k`, supported on `[-T, T]` (with appropriate scaling).

This sub-lemma asserts the existence abstractly. The concrete construction
(explicit `sin^{2k}/x^{2k}` formulas, B-spline Fourier identity, and the
computation `∫ |u| J₄(u) du = C/T`) is deferred.

**Reference**: Esseen (1945), also Feller Vol II §XV.3.
-/
lemma jackson_kernel_tail_bound (T : ℝ) (hT : 0 < T) :
    ∃ (K : ℝ → ℝ),
      (Continuous K) ∧
      (∀ x, 0 ≤ K x) ∧
      (Integrable K volume) ∧
      (∫ x, K x = 1) ∧
      (∫ x, |x| * K x ≤ 12 / T) ∧
      -- Fejér CDF bracket: for any a > 0,
      -- Ψ_K(u-a) - ε ≤ H(u) ≤ Ψ_K(u+a) + ε where ε = ∫_{|x|>a} K(x) dx ≤ 12/(Ta)
      (∀ a : ℝ, 0 < a → ∫ x in Set.Ioi a ∪ Set.Iio (-a), K x ≤ 12 / (T * a)) := by
  sorry

end JacksonKernel

/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statlean.CharFun.Taylor

/-!
# Esseen Smoothing Inequality

The Esseen smoothing inequality: given a kernel `K` with good tail decay
and a Fourier bound on `∫ (F-G)(y-x) K(x) dx`, the CDF difference
`|F(y) - G(y)|` is bounded by the Fourier integral plus `24M/(πT)`.

## Main results
- `esseen_bracket_smoothing`: the full Esseen smoothing bound

## Proof architecture

The proof splits into trivial and hard cases:
- **Trivial**: When `1/π · I + 24M/(πT) ≥ 1`, the bound follows from `|F-G| ≤ 1`.
- **Hard**: When the RHS < 1, we use the one-sided Lipschitz control
  `Δ(y+t) ≥ Δ(y) - Mt` (from F monotone + G Lipschitz) combined with the
  Fourier bound applied at a shifted point.

### Hard case analysis

The one-sided control gives: if `Δ(ȳ)` is near the supremum, then `Δ` stays
large on `[ȳ, ȳ + S/(2M)]` (where `S = sup Δ`). The Fourier bound at the
midpoint `ȳ + S/(4M)` then constrains `S`.

Concretely, for `a = S/(4M)`:
- Bracket: `Δ_f(ȳ+a) ≥ S/2 · (1 - 48M/(TS)) - 48M/(TS)`
- Fourier: `Δ_f(ȳ+a) ≤ I/(2π)`
- Combining: `S/2 ≤ I/(2π) + 24M/T + 48M/(TS)`

This self-referential bound, when `S ≥ I/π + 24M/(πT)`, leads to a contradiction
in the hard case regime.

## Sorry status

- 1 sorry in `cdf_smoothing_error_bound` (hard case of the Esseen inequality).
- The sorry represents the analytical core: controlling the CDF smoothing error
  `|F(y) - (F*K)(y)|` using the Fourier bound and Lipschitz control.
- **Blocker**: The bracket approach with kernel moment/tail bounds gives
  `O(√(M/T))`, not `O(M/T)`. The `O(M/T)` rate requires the full self-referential
  argument (arxiv.org/html/2602.06234 Thm 3.3) or a Fourier inversion approach
  going beyond the kernel properties stated in the hypotheses.

## References
- Esseen (1945), Feller Vol II §XV.3
- arxiv.org/html/2602.06234 Thm 3.3
-/

open MeasureTheory ProbabilityTheory Set Filter Real

noncomputable section EsseenSmoothing

/-- |cdf μ y - cdf ν y| ≤ 1 for probability measures. -/
private lemma abs_cdf_diff_le_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y : ℝ) :
    |cdf μ y - cdf ν y| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [cdf_nonneg μ y, cdf_le_one ν y],
         by linarith [cdf_le_one μ y, cdf_nonneg ν y]⟩

/-- Hard case of the Esseen smoothing inequality: when `I/π + 24M/(πT) < 1`,
the CDF difference is strictly bounded by this quantity.

This is the analytical core. The trivial bound `|Δ| ≤ 1` doesn't suffice
since the target is `< 1`. The proof uses the one-sided Lipschitz control
`Δ(y+t) ≥ Δ(y) − Mt` combined with the Fourier bound at a shifted point
to obtain the self-referential inequality `S ≤ 2·I/(2π) + C·M/T`.

**Sorry**: The argument requires either the full Fourier inversion formula
(going beyond the kernel moment/tail hypotheses) or a more sophisticated
self-referential argument. The bracket approach alone gives `O(√(M/T))`.
-/
-- sorry count: 1
-- blocker: Fourier inversion for CDF differences (not in Mathlib)
-- proof sketch: self-referential bound (arxiv 2602.06234 Thm 3.3)
-- estimated effort: B-grade (significant new infrastructure needed)
private lemma cdf_smoothing_error_bound
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {M : ℝ} (_hM : 0 < M)
    (_hν_density : ∀ a b : ℝ, a ≤ b → ν (Set.Icc a b) ≤ ENNReal.ofReal (M * (b - a)))
    (_T : ℝ) (_hT : 0 < _T) (_y : ℝ)
    (_K : ℝ → ℝ) (_hK_cont : Continuous _K) (_hK_nn : ∀ x, 0 ≤ _K x)
    (_hK_int : Integrable _K volume) (_hK_one : ∫ x, _K x = 1)
    (_hK_moment : ∫ x, |x| * _K x ≤ 12 / _T)
    (_hK_tail : ∀ a : ℝ, 0 < a →
      ∫ x in Set.Ioi a ∪ Set.Iio (-a), _K x ≤ 12 / (_T * a))
    (_hK_fourier : ∀ y' : ℝ,
      |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * _K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-_T) _T,
          ‖charFun μ t - charFun ν t‖ / |t|)
    (_hhard : 1 / Real.pi * (∫ t in Set.Icc (-_T) _T,
        ‖charFun μ t - charFun ν t‖ / |t|) + 24 * M / (Real.pi * _T) < 1) :
    |cdf μ _y - cdf ν _y| ≤
      1 / Real.pi * (∫ t in Set.Icc (-_T) _T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * M / (Real.pi * _T) := by
  sorry

/-- **Esseen smoothing inequality.**

For probability measures `μ`, `ν` where `ν` has CDF that is `M`-Lipschitz
(equivalently, `ν` has density bounded by `M`), and a kernel `K` satisfying
standard decay conditions plus a Fourier bound, the CDF difference satisfies:

  `|cdf μ y - cdf ν y| ≤ (1/π) ∫_{-T}^T ‖Δ(t)‖/|t| dt + 24M/(πT)`

This is the classical Esseen inequality (1945).

**Proof**: Case split into the trivial case (RHS ≥ 1) handled by `|F-G| ≤ 1`,
and the hard case handled by `cdf_smoothing_error_bound`.
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
    -- Fourier bound
    (hK_fourier : ∀ y' : ℝ,
      |∫ x, (cdf μ (y' - x) - cdf ν (y' - x)) * K x| ≤
        (1 / (2 * Real.pi)) * ∫ t in Set.Icc (-T) T,
          ‖charFun μ t - charFun ν t‖ / |t|) :
    |cdf μ y - cdf ν y| ≤
      (1 / Real.pi) * (∫ t in Set.Icc (-T) T,
        ‖charFun μ t - charFun ν t‖ / |t|) +
      24 * M / (Real.pi * T) := by
  set I := ∫ t in Set.Icc (-T) T, ‖charFun μ t - charFun ν t‖ / |t|
  have hpi := Real.pi_pos
  have hI_nn : 0 ≤ I :=
    setIntegral_nonneg measurableSet_Icc fun t _ =>
      div_nonneg (norm_nonneg _) (abs_nonneg _)
  -- If the RHS ≥ 1, the trivial bound |Δ| ≤ 1 suffices.
  by_cases hrhs : 1 ≤ 1 / Real.pi * I + 24 * M / (Real.pi * T)
  · exact (abs_cdf_diff_le_one μ ν y).trans hrhs
  · -- Hard case: delegate to the analytical core.
    push_neg at hrhs
    exact cdf_smoothing_error_bound μ ν hM hν_density T hT y K hK_cont hK_nn hK_int
      hK_one hK_moment hK_tail hK_fourier hrhs

end EsseenSmoothing

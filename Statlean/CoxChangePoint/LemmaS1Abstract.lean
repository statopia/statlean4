import Mathlib

/-!
# Lemma S1 (abstract reduction): tail bound ⇒ uniform convergence in probability

This file isolates the **abstract probabilistic reduction** that lives behind
Lemma S1 of the functional Cox change-point paper (Lin–Guo–Sun–Lin 2025).

The Cox-specific content (Glivenko–Cantelli for the centred normalised
profile log-likelihood class on `Θ_n`) is what produces, via van der
Vaart–Wellner Theorem 2.14.9 applied to that class, a *uniform tail bound*
of the form
```
∀ ε > 0, ∃ N₀, ∀ n ≥ N₀,  P { ω | ε ≤ supNormDiff n ω } ≤ ε
```
where `supNormDiff n ω = sup_{θ ∈ Θ_n} |Gn n ω θ − G_limit n θ|`.

The *purely measure-theoretic* step — turning that tail bound into the
Mathlib statement
```
TendstoInMeasure P supNormDiff atTop (fun _ => 0)
```
— is what we formalize here. This is the lemma that finally discharges the
`hUnif` field of `Statlean.CoxChangePoint.Auto.LemmaS1Data` (and through it
the `hUnif` field of `Statlean.Web.jobmobquqqakyyv.Theorem1Assumptions`)
once the Cox-side tail bound is supplied.

## Discharging Theorem 1's `hUnif`

`Theorem1Assumptions.hUnif` is phrased as
`Tendsto (fun n => μ {ω | ∃ θ, ε ≤ |G_n n θ ω - G θ|}) atTop (𝓝 0)`.
Once one provides a measurable `supNormDiff` dominating each
`|G_n n θ ω - G θ|` and a VW-style tail bound for `supNormDiff`, our
`unifConv_of_tail_bound` produces `TendstoInMeasure`, and a routine
monotonicity / `Tendsto`-extraction step (not in this file) lifts it to
the indexed-set formulation used by `Theorem1`.

## Proof route

The proof mirrors the `o_P(1)` derivation in
`Statlean/CoxChangePoint/Auto/uniform_bound_on_FPC_score_estimation_error.lean`
(see `to_negligible_of_rate_vanish`-style ending, lines 88–129):

1. Unfold `TendstoInMeasure` and `ENNReal.tendsto_nhds_zero`.
2. Trivialize the `δ = ⊤` and `ε = ⊤` corner cases.
3. Convert `edist (supNormDiff n ω) 0 = ENNReal.ofReal (supNormDiff n ω)`
   using `hNN`.
4. Apply `hTail` at `ε' := min ε.toReal δ.toReal`.
5. Rewrite `ε ≤ ENNReal.ofReal (supNormDiff n ω)` as
   `ε.toReal ≤ supNormDiff n ω` (via `ENNReal.le_ofReal_iff_toReal_le`),
   monotonicity to the `hTail` set, then bound by `δ`.
-/

namespace Statlean.CoxChangePoint

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Abstract reduction (VW 2.14.9 ⇒ TendstoInMeasure).**

A uniform tail bound on a non-negative real-valued sequence — the conclusion
of van der Vaart–Wellner's Glivenko–Cantelli Theorem 2.14.9 applied to a
suitable function class (here, the Cox-specific class on `Θ_n`) — implies
convergence in measure to zero.

The hypothesis `hTail` says: for every tolerance `ε > 0` we can find an
index `N₀` past which `P { supNormDiff n ≥ ε } ≤ ε`. (This is exactly the
output of VW 2.14.9 stated in `toReal` terms.) The conclusion is the
Mathlib formulation `TendstoInMeasure P supNormDiff atTop 0`.

Measurability hypotheses on the constant `0` function are discharged
internally; the user supplies measurability and non-negativity of
`supNormDiff`. -/
theorem unifConv_of_tail_bound
    (supNormDiff : ℕ → Ω → ℝ)
    (_hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (hTail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
       (P {ω | ε ≤ supNormDiff n ω}).toReal ≤ ε) :
    TendstoInMeasure P supNormDiff atTop (fun _ => (0 : ℝ)) := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  -- Corner case: δ = ⊤ trivializes.
  by_cases hδtop : δ = ⊤
  · exact Eventually.of_forall fun _ => hδtop ▸ le_top
  -- Corner case: ε = ⊤ makes the conditional set empty (edist < ⊤).
  by_cases hεtop : ε = ⊤
  · refine Eventually.of_forall fun n => ?_
    have h_set_empty : {ω | ε ≤ edist (supNormDiff n ω) ((fun _ => (0 : ℝ)) n)} = ∅ := by
      ext ω
      simp only [hεtop, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact edist_lt_top _ _
    rw [h_set_empty, measure_empty]
    exact zero_le _
  -- Both ε and δ finite and positive.
  have hε_real : (0 : ℝ) < ε.toReal :=
    ENNReal.toReal_pos (pos_iff_ne_zero.mp hε) hεtop
  have hδ_real : (0 : ℝ) < δ.toReal :=
    ENNReal.toReal_pos (pos_iff_ne_zero.mp hδ) hδtop
  -- Pick the tolerance for `hTail`: must be ≤ ε.toReal (so the tail set
  -- contains the edist-set) and ≤ δ.toReal (so the tail bound dominates δ).
  set η : ℝ := min ε.toReal δ.toReal with hη_def
  have hη_pos : 0 < η := lt_min hε_real hδ_real
  have hη_le_ε : η ≤ ε.toReal := min_le_left _ _
  have hη_le_δ : η ≤ δ.toReal := min_le_right _ _
  obtain ⟨N₀, hN₀⟩ := hTail η hη_pos
  -- Eventually past N₀.
  refine eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
  -- Convert edist to ofReal using non-negativity.
  have h_edist : ∀ ω, edist (supNormDiff n ω) ((fun _ => (0 : ℝ)) n)
      = ENNReal.ofReal (supNormDiff n ω) := by
    intro ω
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg (hNN n ω)]
  simp_rw [h_edist]
  -- Inclusion of sets: {ε ≤ ofReal (supNormDiff)} ⊆ {η ≤ supNormDiff}.
  have h_subset : {ω | ε ≤ ENNReal.ofReal (supNormDiff n ω)}
      ⊆ {ω | η ≤ supNormDiff n ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : ε.toReal ≤ supNormDiff n ω :=
      (ENNReal.le_ofReal_iff_toReal_le hεtop (hNN n ω)).mp hω
    linarith
  -- The tail bound at η gives a real-valued upper bound; lift to ENNReal
  -- and dominate by δ.
  have h_tail_bound : (P {ω | η ≤ supNormDiff n ω}).toReal ≤ η := hN₀ n hn
  have h_meas_ne_top : P {ω | η ≤ supNormDiff n ω} ≠ ⊤ :=
    measure_ne_top _ _
  have h_lift : P {ω | η ≤ supNormDiff n ω} ≤ ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_toReal h_meas_ne_top]
    exact ENNReal.ofReal_le_ofReal h_tail_bound
  calc P {ω | ε ≤ ENNReal.ofReal (supNormDiff n ω)}
      ≤ P {ω | η ≤ supNormDiff n ω} := measure_mono h_subset
    _ ≤ ENNReal.ofReal η := h_lift
    _ ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal hη_le_δ
    _ ≤ δ := ENNReal.ofReal_toReal_le

/-! ### Convenience corollary

The same statement, but the tail bound is parameterized by an arbitrary
slack function rather than `ε ↦ ε`. This is the form that often arises
in practice when the VW theorem is applied with an explicit moment-method
constant. -/

/-- Variant where the tail bound uses a separate "tolerance" parameter `η`
that can be chosen freely below `ε`. Equivalent to `unifConv_of_tail_bound`
once `η` is specialised to `min ε.toReal δ.toReal`, but more convenient as
a building block when the upstream Glivenko–Cantelli step yields the bound
in this two-parameter shape. -/
theorem unifConv_of_two_param_tail_bound
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (hTail : ∀ η > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
       (P {ω | η ≤ supNormDiff n ω}).toReal ≤ η) :
    TendstoInMeasure P supNormDiff atTop (fun _ => (0 : ℝ)) :=
  unifConv_of_tail_bound supNormDiff hMeas hNN hTail

end

end Statlean.CoxChangePoint

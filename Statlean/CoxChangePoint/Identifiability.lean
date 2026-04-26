import Mathlib

/-!
# Well-separated maximum lemma (identifiability)

This file provides a general lemma that discharges the **well-separated maximum**
hypothesis appearing in M-estimator consistency proofs.

The classical statement (van der Vaart, *Asymptotic Statistics*, Thm 5.7;
also our Cox change-point Theorem 1's `hWellSep` field — see
`Statlean/Web/jobmobquqqakyyv/Theorem1.lean`) is:

> Let `Θ` be a compact metric space and `G : Θ → ℝ` a continuous function with a
> unique maximum at `θ₀`.  Then `θ₀` is **well separated**: for every `ε > 0`
> there exists `δ > 0` such that
> `G θ + δ ≤ G θ₀`  whenever  `dist θ θ₀ ≥ ε`.

The proof is a routine extreme value theorem argument:

1. Let `K := {θ ∈ Θ : ε ≤ dist θ θ₀}`.  Then `K` is closed (preimage of
   `[ε, ∞)` under the continuous map `θ ↦ dist θ θ₀`), hence compact in the
   compact ambient space `Θ`.
2. If `K` is empty, the conclusion is vacuous (any `δ > 0` works).
3. Otherwise, `G` attains its maximum on `K` at some `θ_max ∈ K`.  Since
   `dist θ_max θ₀ ≥ ε > 0`, we have `θ_max ≠ θ₀`, so by uniqueness
   `G θ_max < G θ₀`.  Choosing `δ := (G θ₀ - G θ_max) / 2 > 0` works.

## Application

This lemma is the canonical way to construct the `hWellSep` argument when
verifying the assumptions of Cox change-point Theorem 1.  See the trailing
comment at the end of this file for the construction sketch.
-/

namespace Statlean.CoxChangePoint

open Set

/-- **Well-separated maximum lemma.**  On a compact (pseudo-)metric space `Θ`,
a continuous function `G : Θ → ℝ` with a unique maximum at `θ₀` is well
separated: for every `ε > 0` there is `δ > 0` such that `G θ + δ ≤ G θ₀`
whenever `dist θ θ₀ ≥ ε`. -/
theorem wellSeparated_of_compact_of_unique_max
    {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ]
    (G : Θ → ℝ) (hG_cont : Continuous G)
    (θ₀ : Θ) (hMax : ∀ θ, G θ ≤ G θ₀)
    (hUnique : ∀ θ, G θ = G θ₀ → θ = θ₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ θ : Θ, ε ≤ dist θ θ₀ → G θ + δ ≤ G θ₀ := by
  intro ε hε
  -- The "far-from-θ₀" sublevel set.
  set K : Set Θ := {θ | ε ≤ dist θ θ₀} with hK_def
  -- `K` is closed: it is the preimage of `[ε, ∞)` under the continuous map
  -- `θ ↦ dist θ θ₀`.
  have hK_closed : IsClosed K := by
    have hcont : Continuous (fun θ : Θ => dist θ θ₀) :=
      continuous_id.dist continuous_const
    exact isClosed_le continuous_const hcont
  -- A closed subset of a compact space is compact.
  have hK_compact : IsCompact K := hK_closed.isCompact
  -- Case split on whether `K` is empty.
  by_cases hK_empty : K = ∅
  · -- Vacuous case: no `θ` satisfies the hypothesis `ε ≤ dist θ θ₀`.
    refine ⟨1, one_pos, ?_⟩
    intro θ hθ
    exfalso
    have hθK : θ ∈ K := hθ
    rw [hK_empty] at hθK
    exact hθK.elim
  · -- Nonempty case: extract an extremal point.
    have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    -- `G` attains its max on the compact set `K`.
    obtain ⟨θ_max, hθ_max_mem, hθ_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne hG_cont.continuousOn
    -- `θ_max ≠ θ₀` because `dist θ_max θ₀ ≥ ε > 0`.
    have hne : θ_max ≠ θ₀ := by
      intro heq
      have hd : ε ≤ dist θ_max θ₀ := hθ_max_mem
      rw [heq, dist_self] at hd
      linarith
    -- By uniqueness, `G θ_max < G θ₀` (strict).
    have hlt : G θ_max < G θ₀ := by
      have hle : G θ_max ≤ G θ₀ := hMax θ_max
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (hUnique θ_max h) hne
    -- Choose `δ := (G θ₀ - G θ_max) / 2 > 0`.
    refine ⟨(G θ₀ - G θ_max) / 2, by linarith, ?_⟩
    intro θ hθ
    have hθK : θ ∈ K := hθ
    have hθ_le : G θ ≤ G θ_max := hθ_max hθK
    linarith

/-- Convenience reformulation taking the contrapositive form: if `G θ` is
within `δ` of the maximum, then `θ` is within `ε` of `θ₀`.  This is the form
most often invoked in M-estimator consistency arguments (van der Vaart Thm 5.7,
Step 2). -/
theorem dist_lt_of_near_max
    {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ]
    (G : Θ → ℝ) (hG_cont : Continuous G)
    (θ₀ : Θ) (hMax : ∀ θ, G θ ≤ G θ₀)
    (hUnique : ∀ θ, G θ = G θ₀ → θ = θ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ θ : Θ, G θ₀ - δ < G θ → dist θ θ₀ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    wellSeparated_of_compact_of_unique_max G hG_cont θ₀ hMax hUnique ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro θ hG_close
  by_contra hθ_far
  push_neg at hθ_far
  have := hδ θ hθ_far
  linarith

/-!
## Connection to Cox change-point Theorem 1

The file `Statlean/Web/jobmobquqqakyyv/Theorem1.lean` carries a structure
`Theorem1Assumptions` whose field `hWellSep` requires exactly the conclusion of
`wellSeparated_of_compact_of_unique_max`:

```
hWellSep : ∀ ε > 0, ∃ δ > 0,
  ∀ θ : ParamSpace, ε ≤ dist θ θ₀ → G θ + δ ≤ G θ₀
```

To discharge this hypothesis, supply:

* `[CompactSpace ParamSpace]` (typically a closed bounded box of finite-dim
  Euclidean parameters);
* `Continuous G` (continuity of the limiting partial-likelihood criterion);
* `∀ θ, G θ ≤ G θ₀` (`θ₀` is a maximizer of the population criterion);
* `∀ θ, G θ = G θ₀ → θ = θ₀` (uniqueness of the maximizer — the *identifiability*
  hypothesis of the Cox change-point model).

Then `wellSeparated_of_compact_of_unique_max G hG_cont θ₀ hMax hUnique` is a
term of the required type. -/

end Statlean.CoxChangePoint

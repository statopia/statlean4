import Statlean.MultipleTesting.Basic

/-!
# Model-X Knockoffs (Barber–Candès 2015)

Knockoffs is a general framework for controlling the False Discovery Rate
(FDR) in variable selection.  For each candidate variable `X_j` a knockoff
`X̃_j` is constructed satisfying two key properties:

1. **Exchangeability**: the joint distribution of `(X_j, X̃_j)` swapping is
   invariant.
2. **Conditional independence**: `X̃ ⊥ Y | X`.

A *signed* statistic `W_j` is computed (often `|β̂_j|² − |β̃_j|²` from a
joint Lasso fit) and a data-dependent threshold `T̂` is chosen such that

```
  Ŝ := { j : W_j ≥ T̂ }  ⟹  FDR(Ŝ) ≤ q.
```

## Main definitions

* `knockoffSelection W T` — the selection set `{ j : W_j ≥ T }`.
* `knockoffNegCount`, `knockoffPosCount` — left/right tail cardinalities of
  the signed statistic.
* `knockoffFdrHat W T` — the BC 2015 FDR estimate
  `(1 + #{W_j ≤ -T}) / max(1, #{W_j ≥ T})`.

## Main results

* `knockoffSelection_antitone` — selection is decreasing in `T`.
* `knockoffSelection_subset_pos` — for `T > 0`, every selected variable has
  `W_j > 0`.
* `knockoffFdrHat_nonneg` — the FDR estimate is non-negative.
* `knockoff_fdr_control` — **Theorem 3.4 (BC 2015, axiom / R6)**: expected
  FDR ≤ `q` under exchangeable knockoffs.

## References

* R. F. Barber, E. J. Candès, *Controlling the False Discovery Rate via
  Knockoffs*, Ann. Statist. 43 (2015), 2055–2085.
* E. J. Candès, Y. Fan, L. Janson, J. Lv, *Panning for gold: Model-X
  knockoffs for high-dimensional controlled variable selection*,
  JRSS B 80 (2018), 551–577.
-/

namespace Statlean.MultipleTesting

open scoped BigOperators

variable {p : ℕ}

/-- **Knockoff selection** at threshold `T`: variables with `W_j ≥ T`. -/
noncomputable def knockoffSelection (W : Fin p → ℝ) (T : ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun j => T ≤ W j)

/-- The **negative-side count**: number of indices with `W_j ≤ -T`. -/
noncomputable def knockoffNegCount (W : Fin p → ℝ) (T : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => W j ≤ -T)).card

/-- The **positive-side count**: number of indices with `W_j ≥ T`. -/
noncomputable def knockoffPosCount (W : Fin p → ℝ) (T : ℝ) : ℕ :=
  (Finset.univ.filter (fun j => T ≤ W j)).card

/-- Knockoff selection is antitone in `T`: a larger threshold yields a
smaller selection. -/
lemma knockoffSelection_antitone (W : Fin p → ℝ) {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    knockoffSelection W T₂ ⊆ knockoffSelection W T₁ := by
  intro j hj
  rw [knockoffSelection, Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, le_trans h hj.2⟩

/-- For `T > 0`, the knockoff selection consists of variables with strictly
positive `W`. -/
lemma knockoffSelection_subset_pos
    (W : Fin p → ℝ) {T : ℝ} (hT : 0 < T) :
    knockoffSelection W T ⊆ Finset.univ.filter (fun j => 0 < W j) := by
  intro j hj
  rw [knockoffSelection, Finset.mem_filter] at hj
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, lt_of_lt_of_le hT hj.2⟩

/-- The **knockoff FDR estimate**:
`F̂DR(T) := (1 + #{j : W_j ≤ -T}) / max(1, #{j : W_j ≥ T})`. -/
noncomputable def knockoffFdrHat (W : Fin p → ℝ) (T : ℝ) : ℝ :=
  ((knockoffNegCount W T : ℝ) + 1) /
    max 1 (knockoffPosCount W T : ℝ)

/-- The knockoff FDR estimate is non-negative. -/
lemma knockoffFdrHat_nonneg (W : Fin p → ℝ) (T : ℝ) :
    0 ≤ knockoffFdrHat W T := by
  unfold knockoffFdrHat
  apply div_nonneg
  · have h1 : (0 : ℝ) ≤ (knockoffNegCount W T : ℝ) := by positivity
    linarith
  · have : (1 : ℝ) ≤ max 1 (knockoffPosCount W T : ℝ) := le_max_left _ _
    linarith

/-- **Knockoff selection at level `q`** (skeleton — placeholder threshold).
The full Barber–Candès threshold is
`T̂ := min { t > 0 : knockoffFdrHat W t ≤ q }`, which requires `csInf` and
non-emptiness arguments.  For now we expose the selection at a *user-given*
threshold and defer the threshold construction to a follow-up. -/
noncomputable def knockoffSelectionAtLevel (W : Fin p → ℝ) (T : ℝ) :
    Finset (Fin p) := knockoffSelection W T

/-- **Knockoff FDR control (Theorem 3.4, BC 2015) — axiom / R6**.
Under exchangeable knockoffs and a data-driven threshold `T̂` satisfying
`knockoffFdrHat W T̂ ≤ q`, the expected FDR of `knockoffSelection W T̂` is
bounded by `q`.  Stated as `True` placeholder pending probabilistic
modelling of the exchangeability property. -/
axiom knockoff_fdr_control
    (p : ℕ) (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1) : True

end Statlean.MultipleTesting

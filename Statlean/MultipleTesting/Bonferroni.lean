import Statlean.MultipleTesting.Basic

/-! # Bonferroni FWER Control

The classical Bonferroni multiple-testing correction: at level `α` over
`m` hypotheses, reject `H_i` iff `P_i ≤ α / m`. The family-wise error rate
is then bounded by `α` regardless of the joint distribution of the
p-values — the union bound is the entire proof.

## Main result

* `Statlean.MultipleTesting.bonferroni_fwer_le` — under valid p-values for
  the true nulls, FWER ≤ α.

## Proof sketch

Let `B_i := {ω | P_i ω ≤ α/m}` be the rejection event for hypothesis `i`.
Then the false-rejection event is

```
{ω | ∃ i ∈ nulls, B_i ω} = ⋃_{i ∈ nulls} B_i
```

By countable subadditivity (`measure_biUnion_finset_le`):

```
μ(⋃_{i ∈ nulls} B_i) ≤ ∑_{i ∈ nulls} μ(B_i) ≤ |nulls| · (α/m) ≤ α.
```

The last inequality uses `|nulls| ≤ m`.

## References

Bonferroni, C.E., *Teoria statistica delle classi e calcolo delle
probabilità*, Pubbl. R. Ist. Sup. Sci. Econ. Comm. Firenze 8 (1936).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bonferroni FWER control.** If every p-value associated with a true
null is valid in the sense of `IsValidPValue`, then the Bonferroni
procedure at level `α ∈ [0, 1]` controls the family-wise error rate at
`α`, regardless of the dependence structure between p-values. -/
theorem bonferroni_fwer_le
    {m : ℕ} (hm : 1 ≤ m)
    {μ : Measure Ω}
    (P : Fin m → Ω → ℝ) (nulls : Finset (Fin m))
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hValid : ∀ i ∈ nulls, IsValidPValue μ (P i)) :
    fwer μ (bonferroniReject P α) nulls ≤ ENNReal.ofReal α := by
  -- `m > 0` as a real, with `α/m ∈ [0,1]`.
  have hm_pos : (0 : ℝ) < m := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hα_div_nn : 0 ≤ α / m := div_nonneg hα (Nat.cast_nonneg m)
  have hα_div_le : α / m ≤ 1 := by
    rw [div_le_one hm_pos]
    exact hα1.trans (by exact_mod_cast hm)
  -- Step 1: rewrite the false-rejection event as a finite union.
  have h_event_eq :
      {ω | ∃ i ∈ nulls, bonferroniReject P α i ω}
        = ⋃ i ∈ nulls, {ω | P i ω ≤ α / m} := by
    ext ω
    simp [bonferroniReject, Set.mem_iUnion]
  -- Step 2: each event has probability at most `α / m`.
  have h_each : ∀ i ∈ nulls,
      μ {ω | P i ω ≤ α / m} ≤ ENNReal.ofReal (α / m) :=
    fun i hi => (hValid i hi).prob_le _ hα_div_nn hα_div_le
  -- Step 3: union bound + sum estimate.
  unfold fwer
  rw [h_event_eq]
  calc μ (⋃ i ∈ nulls, {ω | P i ω ≤ α / m})
      ≤ ∑ i ∈ nulls, μ {ω | P i ω ≤ α / m} :=
        measure_biUnion_finset_le nulls _
    _ ≤ ∑ i ∈ nulls, ENNReal.ofReal (α / m) := Finset.sum_le_sum h_each
    _ = nulls.card • ENNReal.ofReal (α / m) := by rw [Finset.sum_const]
    _ ≤ (m : ℕ) • ENNReal.ofReal (α / m) := by
        gcongr
        exact (nulls.card_le_univ).trans (by simp)
    _ = ENNReal.ofReal ((m : ℝ) * (α / m)) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast m,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    _ = ENNReal.ofReal α := by
        congr 1
        field_simp

end Statlean.MultipleTesting

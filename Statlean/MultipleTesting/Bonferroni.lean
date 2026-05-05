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
  sorry

end Statlean.MultipleTesting

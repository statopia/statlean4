import Statlean.MultipleTesting.Basic

/-! # Benjamini–Hochberg FDR Control

The Benjamini–Hochberg (BH) procedure (1995) and its FDR-control guarantee.

Unlike Bonferroni, BH controls the *expected* false-discovery proportion
rather than the *probability* of any false discovery. This trades a uniform
worst-case guarantee (FWER) for adaptive power: BH typically rejects more
hypotheses while still keeping the *average* fraction of false rejections
below `α`.

## Main result (skeleton)

* `Statlean.MultipleTesting.bh_fdr_le` — under independence of the p-values
  associated with true nulls, the BH procedure at level `α` satisfies
  `FDR ≤ (m₀ / m) · α ≤ α`, where `m₀ = |nulls|`.

The proof is registered as a sorry. Sketch:

1. Condition on `R = k`, the size of the BH rejection set; show
   `R ≥ 1` ⇒ the cutoff is `k·α/m`.
2. Decompose `FDP = (number of rejected nulls) / R = ∑_{i ∈ nulls} 𝟙{P_i ≤ k·α/m} / k`.
3. Use the leave-one-out / martingale argument of Benjamini–Yekutieli or
   the Storey "self-consistency" identity to show
   `E[𝟙{P_i ≤ τ_i} / R] ≤ α/m`, where `τ_i = k_i · α/m` is the cutoff
   computed without `P_i`.
4. Sum over `i ∈ nulls` to get `FDR ≤ m₀ · α / m ≤ α`.

The full Lean proof requires (a) a clean definition of "the rejection set
on the leave-one-out p-vector", (b) independence transferred through
permutation-invariant statistics, and (c) integration of step-function
processes. Estimated 250–400 lines once Mathlib's `iIndepFun` API is
adapted; expected to require an R6 cycle (WebSearch + sub-lemma DAG).

## References

* Benjamini & Hochberg, *Controlling the false discovery rate*, JRSS-B
  57 (1995).
* Storey, *A direct approach to false discovery rates*, JRSS-B 64 (2002).
* Benjamini & Yekutieli, *The control of the false discovery rate in
  multiple testing under dependency*, Ann. Stat. 29 (2001).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Benjamini–Hochberg FDR control** under independence of the true-null
p-values. The expected false-discovery proportion is bounded by
`(|nulls| / m) · α ≤ α`, regardless of the joint distribution of the
non-null p-values.

This is the central FDR-control theorem of Benjamini & Hochberg (1995). -/
theorem bh_fdr_le
    {m : ℕ} (hm : 1 ≤ m)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Fin m → Ω → ℝ) (nulls : Finset (Fin m))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hValid : ∀ i ∈ nulls, IsValidPValue μ (P i))
    (hIndep : ProbabilityTheory.iIndepFun (fun i : Fin m => P i) μ) :
    fdr μ (bhReject P α) nulls ≤ ((nulls.card : ℝ) / m) * α := by
  sorry

end Statlean.MultipleTesting

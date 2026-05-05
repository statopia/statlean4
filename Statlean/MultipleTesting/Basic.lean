import Mathlib

/-! # Multiple Hypothesis Testing — Foundations

Core definitions for multiple testing: valid p-values, family-wise error
rate (FWER), false-discovery proportion (FDP) and rate (FDR), and the
two canonical procedures — Bonferroni (FWER control) and Benjamini–Hochberg
(FDR control).

## Contents

* `Statlean.MultipleTesting.IsValidPValue` — `μ {P ≤ t} ≤ t` for all
  `t ∈ [0, 1]` (the standard validity definition under the null).
* `Statlean.MultipleTesting.fwer` — probability of at least one false rejection.
* `Statlean.MultipleTesting.fdp` — false-discovery proportion as a function
  of the rejection set and the true-null set.
* `Statlean.MultipleTesting.bonferroniReject` — reject `H_i` iff `P_i ≤ α/m`.
* `Statlean.MultipleTesting.bhRejectionCount` — Benjamini–Hochberg threshold
  index: largest `k` such that the `k`-th order statistic of p-values
  satisfies `P_(k) ≤ k·α/m`.

Theorems proving the actual error-rate guarantees live in
`MultipleTesting.Bonferroni` (FWER ≤ α — union bound, easy) and
`MultipleTesting.BenjaminiHochberg` (FDR ≤ α — Storey/Benjamini–Yekutieli
martingale argument, hard).

## References

* Bonferroni, C.E., *Teoria statistica delle classi e calcolo delle
  probabilità*, 1936 — original union-bound argument.
* Benjamini & Hochberg, *Controlling the false discovery rate*, JRSS-B
  57 (1995), 289–300 — original BH theorem under independence.
* Benjamini & Yekutieli, *The control of the false discovery rate in
  multiple testing under dependency*, Ann. Stat. 29 (2001), 1165–1188 —
  PRDS extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A p-value `P : Ω → ℝ` is **valid** for measure `μ` if it is measurable
and stochastically dominates the uniform distribution on `[0, 1]`:
`μ {ω | P ω ≤ t} ≤ t` for every `t ∈ [0, 1]`.

Under a true null with continuous test statistic, equality holds; the
inequality form covers discrete tests and conservative p-values. -/
structure IsValidPValue (μ : Measure Ω) (P : Ω → ℝ) : Prop where
  measurable : Measurable P
  /-- Stochastic dominance over uniform on `[0, 1]`. -/
  prob_le : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | P ω ≤ t} ≤ ENNReal.ofReal t

/-- The **family-wise error rate (FWER)** of a multiple-testing procedure:
the probability that at least one true null is rejected.

`reject i ω` is the event "hypothesis `i` is rejected on outcome `ω`".
`nulls` is the (typically unknown) set of indices where the null is true. -/
noncomputable def fwer {m : ℕ} (μ : Measure Ω)
    (reject : Fin m → Ω → Prop) [∀ i ω, Decidable (reject i ω)]
    (nulls : Finset (Fin m)) : ℝ≥0∞ :=
  μ {ω | ∃ i ∈ nulls, reject i ω}

/-- The **false-discovery proportion (FDP)** at outcome `ω`: ratio of false
rejections (rejected true nulls) to total rejections, with the convention
`0/0 = 0`. -/
noncomputable def fdp {m : ℕ} (reject : Fin m → Ω → Prop) [∀ i ω, Decidable (reject i ω)]
    (nulls : Finset (Fin m)) (ω : Ω) : ℝ :=
  let rejected := Finset.univ.filter (fun i : Fin m => reject i ω)
  let falseRejs := rejected.filter (fun i => i ∈ nulls)
  if rejected.card = 0 then 0 else (falseRejs.card : ℝ) / rejected.card

/-- The **false-discovery rate (FDR)**: expected FDP under measure `μ`. -/
noncomputable def fdr {m : ℕ} (μ : Measure Ω)
    (reject : Fin m → Ω → Prop) [∀ i ω, Decidable (reject i ω)]
    (nulls : Finset (Fin m)) : ℝ :=
  ∫ ω, fdp reject nulls ω ∂μ

/-! ### The Bonferroni rejection rule -/

/-- **Bonferroni rejection rule**: at level `α` and `m` hypotheses, reject
`H_i` iff its p-value satisfies `P_i ≤ α / m`.

The Bonferroni rule controls FWER at `α` regardless of dependence between
p-values — see `Bonferroni.bonferroni_fwer_le`. -/
noncomputable def bonferroniReject {m : ℕ} (P : Fin m → Ω → ℝ) (α : ℝ)
    (i : Fin m) (ω : Ω) : Prop :=
  P i ω ≤ α / m

/-- The Bonferroni event is decidable when scores are real-valued. -/
noncomputable instance bonferroniReject_decidable {m : ℕ} (P : Fin m → Ω → ℝ)
    (α : ℝ) (i : Fin m) (ω : Ω) : Decidable (bonferroniReject P α i ω) :=
  Classical.dec _

/-! ### The Benjamini–Hochberg rejection rule

Given p-values `P_1, …, P_m`, sort them as `P_(1) ≤ … ≤ P_(m)`. The BH
threshold at level `α` is the largest `k ∈ {0, …, m}` such that
`P_(k) ≤ k·α/m`; reject the `k` smallest p-values.

We define `bhRejectionCount` as a function of the unsorted p-value vector
and return `0` when the procedure rejects nothing. The actual
indicator-of-rejection is `bhReject`, which selects indices whose original
p-value is at most the chosen cutoff. -/

/-- The **BH cutoff value** at level `α`: the largest entry of
`{α/m, 2α/m, …, α}` that is matched by some p-value at the corresponding
order. Returns `0` when no rejection occurs (the empty BH set). -/
noncomputable def bhCutoff {m : ℕ} (P : Fin m → ℝ) (α : ℝ) : ℝ :=
  let sorted := (List.ofFn P).mergeSort (· ≤ ·)
  -- For each k ∈ {1, …, m}, check whether sorted[k-1] ≤ k·α/m.
  -- Take the largest such k as the BH threshold; cutoff = k·α/m.
  let qualifies : Finset ℕ :=
    (Finset.range m).filter (fun k =>
      decide (sorted[k]?.getD 0 ≤ ((k : ℝ) + 1) * α / m))
  if h : qualifies.Nonempty then
    let kmax := qualifies.max' h
    ((kmax : ℝ) + 1) * α / m
  else 0

/-- The **BH rejection rule**: reject `H_i` iff its p-value is ≤ the BH
cutoff. -/
noncomputable def bhReject {m : ℕ} (P : Fin m → Ω → ℝ) (α : ℝ)
    (i : Fin m) (ω : Ω) : Prop :=
  P i ω ≤ bhCutoff (fun j => P j ω) α

/-- The BH event is decidable (via classical choice — `bhCutoff` involves
a noncomputable sort). -/
noncomputable instance bhReject_decidable {m : ℕ} (P : Fin m → Ω → ℝ)
    (α : ℝ) (i : Fin m) (ω : Ω) : Decidable (bhReject P α i ω) :=
  Classical.dec _

end Statlean.MultipleTesting

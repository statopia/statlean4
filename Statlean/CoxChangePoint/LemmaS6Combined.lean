import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# Cox Lemma S6 — combined rate via triangle decomposition

Abstract form of Lemma S6 of
"Functional linear Cox regression model with a change-point in the covariate"
(Yu, Li, Lin 2026).

The smoothed empirical process satisfies
`|S_n^{(k)*} - S_n^{(k)}| = O_P(n^{-1/2} d^{3/2} + d^{-b} + d^{1-2b} log n)`.

The paper's argument decomposes the difference as
`S_n^{(k)*} - S_n^{(k)} = (FPC score estimation error term) +
                          (FPC truncation remainder term)`
and bounds each piece separately.  The first term is `O_P(n^{-1/2} d^{3/2})`
(Lemma S2_supp) and the second is `O_P(d^{-b} + d^{1-2b} log n)` (Lemma S3).
The combined bound follows by triangle inequality + a sum decomposition on
the rates.

This file isolates the **abstract triangle inequality step**:
given a sequence `D` dominated pointwise by `|A| + |B|` with abstract `O_P`
bounds on `A` and `B` at distinct rates `rate_A` and `rate_B`, conclude
`D = O_P(rate_A + rate_B)`.

This generalises `ProbabilityTheory.IsBoundedInProbability.add`, which assumes
both summands share the same rate.

## Main results
- `isOP_of_triangle_decomp`: the abstract triangle decomposition lemma.
- `LemmaS6Hypotheses`: bundle of hypotheses matching the paper's setup.
- `LemmaS6Hypotheses.D_isOP`: combined `O_P` bound, applied to the bundle.
-/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================
section TriangleDecomposition
-- ============================================================

/-- **Abstract triangle inequality decomposition for `O_P`.**

If `|D n ω| ≤ |A n ω| + |B n ω|` pointwise, the rates `rate_A` and `rate_B`
are nonneg, and `A` is `O_P(rate_A)`, `B` is `O_P(rate_B)`, then `D` is
`O_P(rate_A + rate_B)`.

This generalises `IsBoundedInProbability.add` to the case of two summands with
distinct rates, and handles the dominating sequence `D` via a pointwise bound
rather than equality.

The nonnegativity hypothesis on the rates is essential: without it the
set inclusion

  `{M · |rate_A + rate_B| < |D|} ⊆ {M · |rate_A| < |A|} ∪ {M · |rate_B| < |B|}`

fails (counterexample: `rate_A = 1, rate_B = -1` makes the LHS all of `Ω`
while the RHS may be empty).  For typical statistical rates such as
`n^{-1/2}`, `d^{-b}`, `d^{1-2b} log n`, nonnegativity is automatic. -/
theorem isOP_of_triangle_decomp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D A B : ℕ → Ω → ℝ) (rate_A rate_B : ℕ → ℝ)
    (h_decomp : ∀ n ω, |D n ω| ≤ |A n ω| + |B n ω|)
    (hrate_A_nn : ∀ n, 0 ≤ rate_A n) (hrate_B_nn : ∀ n, 0 ≤ rate_B n)
    (hA_OP : IsBoundedInProbability μ A rate_A)
    (hB_OP : IsBoundedInProbability μ B rate_B) :
    IsBoundedInProbability μ D (fun n => rate_A n + rate_B n) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨M_A, hM_A, hA'⟩ := hA_OP (ε / 2) hε2
  obtain ⟨M_B, hM_B, hB'⟩ := hB_OP (ε / 2) hε2
  -- Pick a single threshold that dominates both `M_A` and `M_B`.
  set M : ℝ := max M_A M_B with hM_def
  have hM_pos : 0 < M := lt_max_of_lt_left hM_A
  have hM_nn : 0 ≤ M := hM_pos.le
  have hM_A_le : M_A ≤ M := le_max_left _ _
  have hM_B_le : M_B ≤ M := le_max_right _ _
  refine ⟨M, hM_pos, ?_⟩
  filter_upwards [hA', hB'] with n hnA hnB
  -- Under nonnegativity of the rates,
  -- `|rate_A n + rate_B n| = rate_A n + rate_B n = |rate_A n| + |rate_B n|`.
  have hrA_abs : |rate_A n| = rate_A n := abs_of_nonneg (hrate_A_nn n)
  have hrB_abs : |rate_B n| = rate_B n := abs_of_nonneg (hrate_B_nn n)
  have hr_sum_nn : 0 ≤ rate_A n + rate_B n := add_nonneg (hrate_A_nn n) (hrate_B_nn n)
  have hr_sum_abs : |rate_A n + rate_B n| = rate_A n + rate_B n :=
    abs_of_nonneg hr_sum_nn
  -- The bad set for `D` at threshold `M` and rate `rate_A + rate_B`
  -- is contained in the union of the bad sets for `A` and `B` at
  -- thresholds `M` and rates `rate_A`, `rate_B` respectively.
  have hsub :
      {ω : Ω | M * |rate_A n + rate_B n| < |D n ω|} ⊆
      {ω | M * |rate_A n| < |A n ω|} ∪ {ω | M * |rate_B n| < |B n ω|} := by
    intro ω hω
    simp only [mem_setOf_eq, mem_union] at *
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨hA_le, hB_le⟩ := hcontra
    have h_D_le : |D n ω| ≤ |A n ω| + |B n ω| := h_decomp n ω
    -- `M * (rate_A n + rate_B n) = M * rate_A n + M * rate_B n`
    --                            = M * |rate_A n| + M * |rate_B n|
    --                            ≥ |A n ω| + |B n ω| ≥ |D n ω|`
    have h_chain : M * |rate_A n + rate_B n| ≥ |D n ω| := by
      rw [hr_sum_abs]
      calc |D n ω|
          ≤ |A n ω| + |B n ω| := h_D_le
        _ ≤ M * |rate_A n| + M * |rate_B n| := by linarith
        _ = M * (rate_A n + rate_B n) := by rw [hrA_abs, hrB_abs]; ring
    linarith
  -- Now bound the bad set for `D` at thresholds `M_A` and `M_B`
  -- (smaller thresholds yield larger bad sets).
  have hA_set_sub :
      {ω : Ω | M * |rate_A n| < |A n ω|} ⊆
      {ω | M_A * |rate_A n| < |A n ω|} := by
    intro ω hω
    simp only [mem_setOf_eq] at *
    have : M_A * |rate_A n| ≤ M * |rate_A n| :=
      mul_le_mul_of_nonneg_right hM_A_le (abs_nonneg _)
    linarith
  have hB_set_sub :
      {ω : Ω | M * |rate_B n| < |B n ω|} ⊆
      {ω | M_B * |rate_B n| < |B n ω|} := by
    intro ω hω
    simp only [mem_setOf_eq] at *
    have : M_B * |rate_B n| ≤ M * |rate_B n| :=
      mul_le_mul_of_nonneg_right hM_B_le (abs_nonneg _)
    linarith
  calc μ {ω | M * |rate_A n + rate_B n| < |D n ω|}
      ≤ μ ({ω | M * |rate_A n| < |A n ω|} ∪ {ω | M * |rate_B n| < |B n ω|}) :=
        measure_mono hsub
    _ ≤ μ {ω | M * |rate_A n| < |A n ω|} + μ {ω | M * |rate_B n| < |B n ω|} :=
        measure_union_le _ _
    _ ≤ μ {ω | M_A * |rate_A n| < |A n ω|} + μ {ω | M_B * |rate_B n| < |B n ω|} :=
        add_le_add (measure_mono hA_set_sub) (measure_mono hB_set_sub)
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hnA hnB
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end TriangleDecomposition

-- ============================================================
section LemmaS6Bundle
-- ============================================================

/-- Bundle of hypotheses matching the paper's Lemma S6 decomposition.

`D` is the smoothed empirical process difference `S_n^{(k)*} - S_n^{(k)}`,
decomposed into `A` (FPC score estimation error term) and `B` (FPC truncation
remainder term).  Each piece is `O_P` at its own rate. -/
structure LemmaS6Hypotheses
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] where
  /-- The smoothed empirical process difference `S_n^{(k)*} - S_n^{(k)}`. -/
  D : ℕ → Ω → ℝ
  /-- FPC score estimation error term (rate `~ n^{-1/2} d^{3/2} log^{1/2} n`). -/
  A : ℕ → Ω → ℝ
  /-- FPC truncation remainder term (rate `~ d^{-b} + d^{1-2b} log n`). -/
  B : ℕ → Ω → ℝ
  /-- Rate for the FPC score estimation error term. -/
  rate_A : ℕ → ℝ
  /-- Rate for the FPC truncation remainder term. -/
  rate_B : ℕ → ℝ
  /-- Pointwise triangle decomposition `|D| ≤ |A| + |B|`. -/
  h_decomp : ∀ n ω, |D n ω| ≤ |A n ω| + |B n ω|
  /-- The FPC score error rate is nonnegative. -/
  hrate_A_nn : ∀ n, 0 ≤ rate_A n
  /-- The FPC truncation remainder rate is nonnegative. -/
  hrate_B_nn : ∀ n, 0 ≤ rate_B n
  /-- `O_P` bound on the FPC score estimation error term. -/
  hA_OP : IsBoundedInProbability μ A rate_A
  /-- `O_P` bound on the FPC truncation remainder term. -/
  hB_OP : IsBoundedInProbability μ B rate_B

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Lemma S6 (abstract form)**: under the bundled hypotheses, the smoothed
empirical process difference is `O_P(rate_A + rate_B)`. -/
theorem LemmaS6Hypotheses.D_isOP (H : LemmaS6Hypotheses Ω μ) :
    IsBoundedInProbability μ H.D (fun n => H.rate_A n + H.rate_B n) :=
  isOP_of_triangle_decomp μ H.D H.A H.B H.rate_A H.rate_B
    H.h_decomp H.hrate_A_nn H.hrate_B_nn H.hA_OP H.hB_OP

end LemmaS6Bundle

end ProbabilityTheory

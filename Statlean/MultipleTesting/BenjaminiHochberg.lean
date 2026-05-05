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

## Status

Statement registered, proof deferred. R6 candidate, ~350 lines. Engineering
route researched 2026-05-06 — see below.

## R6 Engineering Route (researched 2026-05-06)

### Existing formalizations (literature scan)

A targeted scan (Lean Zulip, Mathlib4 docs, Isabelle AFP, Coq packages,
arXiv 2025-2026) returned **no prior formalization** of BH-FDR control in any
mainstream proof assistant. Mathlib4 contains the prerequisites
(`ProbabilityTheory.iIndepFun`, integral/expectation API,
`List.mergeSort` + `List.Pairwise` for order statistics) but no multiple
testing module. We are therefore writing the first formal proof.

### Recommended proof strategy: Wang–Ramdas "Second Proof"

We follow the **Second Proof** of Theorem 1 of Wang & Ramdas, *Elementary
proofs of several results on false discovery rate*, arXiv:2201.09350v3
(2022). Among published BH proofs this is the most amenable to formalization:

* No martingale / optional stopping (avoids `Filtration` + stopping-time API).
* No measure-theoretic conditioning (avoids `condExp` Radon–Nikodym).
* Reduces to a single algebraic identity (the *replacement lemma*) plus
  textbook independence factorization `E[𝟙_A · 𝟙_B] = ℙ(A)·ℙ(B)`.

Alternatives considered and rejected:

* **Storey 2002 (martingale)**: requires backward filtration of order
  statistics + optional stopping. Mathlib's stopping-time API is geared to
  Doob's theorem and lacks the reverse-time variant we'd need.
* **Benjamini–Yekutieli 2001 (PRDS)**: stronger result (PRDS dependence)
  but the proof is ~3× longer and assumes a structural lattice on
  rejection regions that needs separate development.
* **Direct Lebesgue-Stieltjes integration of the empirical CDF**: clean
  on paper but needs `MeasureTheory.lintegral_eq_sum_disjoint` machinery
  on step functions which is not yet ergonomic in Mathlib.

The Wang–Ramdas argument, transcribed for our notation
(`m` = total hypotheses, `nulls : Finset (Fin m)` = true nulls,
`R(ω)` = `(bhReject P α · ω).toFinset.card`,
`F(ω)` = `(bhReject P α · ω ∩ nulls).card`,
`α_r := r · α / m`):

```
FDR = E[F / R · 𝟙{R ≥ 1}]
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R = r}]   -- (decomp)
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R_k = r}] -- (replacement)
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · ℙ(P_k ≤ α_r) · ℙ(R_k = r)    -- (indep)
    ≤ ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · α_r · ℙ(R_k = r)             -- (validity)
    = (α / m) · ∑_{k ∈ nulls} ∑_{r=1}^{m} ℙ(R_k = r)                 -- (α_r/r = α/m)
    ≤ (α / m) · |nulls|                                              -- (∑ ℙ ≤ 1)
```

where `R_k(ω)` is the BH rejection count on the modified p-vector with
`P_k` replaced by `0`. The crucial observation is the **replacement
identity**: on the event `{P_k ≤ α_r, R = r}`, replacing `P_k` by `0`
keeps `R = r` (cf. monotonicity of the BH cutoff in each coordinate
restricted below the rejection threshold). This decouples `P_k` from the
rejection-count event, so independence applies coordinate-wise.

### Sub-lemma DAG (~350 lines total)

```
                ┌─ L1: bhCutoff_take_values ─┐
                ├─ L2: bhRejectionCount      ─┤
                │                             │
L0: bhReplaced ─┼─ L3: replacement_eventEq    ┼─→ L7: indep_factor ─┐
                │                             │                      │
                ├─ L4: bhReplaced_measurable ─┤                      │
                │                             │                      ├─→ L9: BH-FDR ≤ m₀α/m
                └─ L5: indep_loo (loo from   ─┘                      │
                       iIndepFun)                                    │
                                                                     │
                L6: pvalue_validity_ofReal ─────────────────────────┤
                                                                     │
                L8: sum_one_pmf (∑_r ℙ(R_k=r) ≤ 1) ──────────────────┘
```

Detailed sub-lemma list (file: `Statlean/MultipleTesting/BenjaminiHochberg.lean`,
all in namespace `Statlean.MultipleTesting`):

1. **L0 `bhReplaced`** — `def bhReplaced (P : Fin m → Ω → ℝ) (k : Fin m) :
   Fin m → Ω → ℝ := fun i ω => if i = k then 0 else P i ω`. Trivial. **~5 lines**.

2. **L1 `bhCutoff_take_values`** — `bhCutoff (fun j => P j ω) α ∈ {0} ∪
   {(r·α)/m | r ∈ Finset.Icc 1 m}`. Direct from the definition (the cutoff
   is `((kmax+1)·α/m)` with `kmax+1 ∈ [1,m]`). **~25 lines**.

3. **L2 `bhRejectionCount`** —
   `def bhRejectionCount (P : Fin m → Ω → ℝ) (α : ℝ) (ω : Ω) : ℕ :=
   (Finset.univ.filter (fun i => bhReject P α i ω)).card`.
   Plus a lemma: rejection count `= r` iff cutoff is `r·α/m` and exactly
   `r` p-values are below cutoff. Reuses the `sorted_get_le_iff_countP`
   pattern from `Statlean.Conformal.MarginalCoverage`. **~40 lines**.

4. **L3 `bhReplaced_eventEq`** — *the replacement identity*. For every
   `k ∈ nulls`, `r ∈ {1, …, m}`, almost surely on
   `{ω | P k ω ≤ r·α/m ∧ bhRejectionCount P α ω = r}` we have
   `bhRejectionCount (bhReplaced P k) α ω = r`. The only delicate step:
   monotonicity of `bhCutoff` when one coordinate is decreased
   *below* the cutoff value. **~80 lines** — the longest sub-lemma.

5. **L4 `bhReplaced_measurable`** — `bhRejectionCount (bhReplaced P k) α`
   is `(σ {P j | j ≠ k})`-measurable. Reduces to `bhCutoff` being
   continuous in its inputs (it's a finite combination of `min`/`max`/comparison),
   plus the standard `Measurable.ite` lemma. **~30 lines**.

6. **L5 `indep_loo`** — leave-one-out independence: from `iIndepFun (fun i =>
   P i)`, deduce `IndepFun (P k) (fun ω => bhRejectionCount (bhReplaced P k) α ω)
   μ`. Use Mathlib's `iIndepFun.indepFun_finset` + L4 to push measurability
   through `bhRejectionCount`. **~25 lines**.

7. **L6 `pvalue_validity_ofReal`** — for valid `P_k`, `0 ≤ r·α/m ≤ 1` (under
   `α ≤ 1`), so `μ {ω | P k ω ≤ r·α/m} ≤ ENNReal.ofReal (r·α/m)`. Direct
   from `IsValidPValue.prob_le`. **~10 lines**.

8. **L7 `indep_factor`** — using L5: `μ ({P_k ≤ r·α/m} ∩ {R_k = r}) =
   μ {P_k ≤ r·α/m} · μ {R_k = r}`. Apply `IndepFun.measure_inter_eq_mul`
   (Mathlib has this for two-fn independence). **~25 lines**.

9. **L8 `sum_pmf_le_one`** — for any random `r : Ω → ℕ` taking values in
   `Finset.Icc 1 m`, `∑_{r=1}^m μ {ω | r ω = r} ≤ 1`. Trivial via
   `MeasureTheory.measure_iUnion_le` on disjoint events plus
   `IsProbabilityMeasure`. **~15 lines**.

10. **L9 (main) `bh_fdr_le`** — assemble L0–L8 along the chain shown
    above. Open the `fdr` definition, expand `fdp` via the indicator
    decomposition, swap `Σ` and `∫` (Tonelli on a finite sum, trivial
    `Finset.sum_comm`), apply L3 + L7 + L6 + L8 in sequence, simplify
    `r·α/(m·r) = α/m`, conclude. **~80 lines** of bookkeeping.

Total: ~335 lines + 15 lines of imports/scaffolding ≈ **350 lines**.

### Mathlib API gaps

* No `bhRejectionCount` or `bhReplaced` — defined locally (L0, L2 above).
* No "leave-one-out" lemma for `iIndepFun`. Workaround: `iIndepFun.indepFun_finset`
  applied to the partition `{k}` vs `Finset.univ.erase k`, post-composed with
  the measurable `bhRejectionCount ∘ bhReplaced`.
* Replacement-monotonicity of BH cutoff (L3) is *bespoke*; no analogue in
  Mathlib (no order-statistic monotonicity API for `mergeSort`).
* `IndepFun.measure_inter_eq_mul`: present in Mathlib as
  `ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul`; need to
  unfold to specific events.

### Reuse from existing Statlean

* `Statlean.Conformal.MarginalCoverage.sorted_get_le_iff_countP` — counts
  list entries `≤ x` via order statistics; **directly reusable** for L2
  (counting p-values below the BH cutoff).
* `Statlean.Conformal.Basic` — `mergeSort`-based quantile of a `Fin n → ℝ`
  vector (`bhCutoff` already uses the same pattern).
* `Statlean.MultipleTesting.Basic.IsValidPValue` — supplies L6 directly.
* `Statlean.MultipleTesting.Bonferroni` (already proved) — the
  `IsValidPValue` + union-bound idiom there is the analogue for L6/L8 here.

### Risk register

* **L3 (replacement identity)** is the proof's keystone. If the cutoff
  monotonicity argument bogs down, fall back to *integration form*: show
  the indicator equality holds μ-a.e. via direct case-analysis on
  `bhCutoff`'s finite range from L1 (every cutoff value `r·α/m` factors
  through one of `m` candidate sets). This converts the geometric monotonicity
  into a finite disjunction. Cost: +30 lines.
* **L4 (measurability)** will need `Measurable.maxFinset` / `Measurable.argmax`.
  If absent, prove `bhCutoff` measurable directly from finite-`max` + `Measurable.ite`.
* **`fdp` as `0` on `R = 0`**: handled cleanly because the `R = 0` slice
  contributes `0` to the integral (by definition of `fdp`).

### References

* **Primary**: Wang & Ramdas, *Elementary proofs of several results on
  false discovery rate*, arXiv:2201.09350v3 (2022) — Theorem 1, Second
  Proof. The route above transcribes this proof.
* **Foundational**: Benjamini & Hochberg, *Controlling the false discovery
  rate*, JRSS-B 57 (1995), 289–300.
* **Alternative martingale proof**: Storey, *A direct approach to false
  discovery rates*, JRSS-B 64 (2002), 479–498; Storey, Taylor & Siegmund,
  JRSS-B 66 (2004), 187–205.
* **Self-consistency framework** (broader): Blanchard & Roquain, *Two
  simple sufficient conditions for FDR control*, EJS 2 (2008), arXiv:0802.1406.
* **PRDS extension** (not pursued here): Benjamini & Yekutieli, Ann. Stat.
  29 (2001), 1165–1188.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.MultipleTesting

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Sub-lemma DAG (Wang–Ramdas Second Proof)

The skeleton below introduces the nine sub-lemmas described in the file
header. Trivial leaves (L0 `bhReplaced` definition, L6 validity at
`r·α/m`, L8 disjoint-pmf bound) are closed in this scaffold; the remaining
sub-lemmas (L1, L2, L2', L3, L4, L5, L7) carry `sorry` to be attacked in
follow-up cycles, and the main theorem `bh_fdr_le` is left as a single
`sorry` whose intended assembly route is documented inline. -/

variable {m : ℕ}

/-! ### Auxiliary list-counting bridges (for L1, L2') -/

omit [MeasurableSpace Ω] in
/-- `countP` over `List.ofFn s` = cardinality of matching index filter
(combinatorial bridge from list counting to `Finset.filter`).
Adapted from `Statlean.Conformal.MarginalCoverage.countP_ofFn_eq_card_filter`. -/
private lemma countP_ofFn_eq_card_filter_BH {n : ℕ} (s : Fin n → ℝ) (p : ℝ → Bool) :
    (List.ofFn s).countP p = (Finset.univ.filter (fun i => p (s i) = true)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih (fun i => s i.succ),
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    ring_nf

omit [MeasurableSpace Ω] in
/-- For a `≤`-sorted list `L` of length `> k`, `L[k] ≤ x` iff at least `k+1`
entries of `L` are `≤ x`.
Adapted from `Statlean.Conformal.MarginalCoverage.sorted_get_le_iff_countP`. -/
private lemma sorted_get_le_iff_countP_BH {L : List ℝ} (hL : L.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < L.length) (x : ℝ) :
    L[k] ≤ x ↔ k < L.countP (fun y => decide (y ≤ x)) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    obtain ⟨ha, hLp⟩ := hL
    match k with
    | 0 =>
      simp only [List.getElem_cons_zero, List.countP_cons]
      by_cases hax : a ≤ x
      · simp [hax]
      · have hxa : x < a := lt_of_not_ge hax
        have h_count : L.countP (fun y => decide (y ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have hay := ha y hy
          have : x < y := lt_of_lt_of_le hxa hay
          simp [decide_eq_false (not_le.mpr this)]
        simp [decide_eq_false hax, h_count, hax]
    | k+1 =>
      simp only [List.getElem_cons_succ, List.countP_cons]
      have hkL : k < L.length := by simp at hk; omega
      have IH := ih hLp k hkL
      by_cases hax : a ≤ x
      · simp [decide_eq_true hax]
        constructor
        · intro h; have := IH.mp h; omega
        · intro h; exact IH.mpr (by omega)
      · have hxa : x < a := lt_of_not_ge hax
        simp [decide_eq_false hax]
        have h_count : L.countP (fun y => decide (y ≤ x)) = 0 := by
          rw [List.countP_eq_zero]
          intro y hy
          have hay := ha y hy
          have : x < y := lt_of_lt_of_le hxa hay
          simp [decide_eq_false (not_le.mpr this)]
        rw [h_count]
        constructor
        · intro hLkx
          have hmem : L[k] ∈ L := List.getElem_mem hkL
          have : a ≤ L[k] := ha _ hmem
          linarith
        · intro h; omega

omit [MeasurableSpace Ω] in
/-- The cardinality of `{i : P i ω ≤ x}` equals the `countP` over the
sorted list of p-values. -/
private lemma card_filter_eq_countP_sorted (P : Fin m → Ω → ℝ) (ω : Ω) (x : ℝ) :
    (Finset.univ.filter (fun i : Fin m => P i ω ≤ x)).card =
    ((List.ofFn (fun j => P j ω)).mergeSort (fun a b => decide (a ≤ b))).countP
      (fun y => decide (y ≤ x)) := by
  rw [(List.mergeSort_perm _ _).countP_eq (fun y => decide (y ≤ x)),
      countP_ofFn_eq_card_filter_BH]
  simp

/-- L0: Replace one coordinate of the p-value vector with `0`. -/
private def bhReplaced (P : Fin m → Ω → ℝ) (k : Fin m) :
    Fin m → Ω → ℝ :=
  fun i ω => if i = k then 0 else P i ω

omit [MeasurableSpace Ω] in
/-- L1: BH cutoff takes values in `{0, α/m, 2α/m, …, α}`. -/
private theorem bhCutoff_take_values (P : Fin m → Ω → ℝ) (α : ℝ) (ω : Ω) :
    bhCutoff (fun j => P j ω) α = 0 ∨
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ m ∧ bhCutoff (fun j => P j ω) α = (r : ℝ) * α / m := by
  rw [bhCutoff]
  set sorted : List ℝ :=
    (List.ofFn (fun j => P j ω)).mergeSort (fun a b => decide (a ≤ b))
  set qualifies : Finset ℕ :=
    (Finset.range m).filter (fun k =>
      decide (sorted[k]?.getD 0 ≤ ((k : ℝ) + 1) * α / m))
  by_cases h : qualifies.Nonempty
  · right
    refine ⟨qualifies.max' h + 1, by omega, ?_, ?_⟩
    · have h_in := qualifies.max'_mem h
      have h_in' := (Finset.filter_subset _ _) h_in
      have hlt := Finset.mem_range.mp h_in'
      omega
    · simp only [h, ↓reduceDIte]
      push_cast
      ring
  · left
    simp only [h, ↓reduceDIte]

/-- L2: Number of rejected hypotheses by BH. -/
private noncomputable def bhRejectionCount (P : Fin m → Ω → ℝ) (α : ℝ) (ω : Ω) :
    ℕ :=
  (Finset.univ.filter (fun i : Fin m => bhReject P α i ω)).card

omit [MeasurableSpace Ω] in
/-- L2': Characterization — count `= r` iff cutoff is `r·α/m` and exactly
`r` p-values are below it. The hypothesis `0 ≤ α` is essential: a
counterexample with `α < 0` is `m = 2, P ≡ 0`, where `bhRejectionCount = 2`
but the cutoff returns `0`, not `2 · α / m = α < 0`. -/
private theorem bhRejectionCount_eq_iff (P : Fin m → Ω → ℝ) (α : ℝ) (ω : Ω)
    (hα : 0 ≤ α) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) :
    bhRejectionCount P α ω = r ↔
    bhCutoff (fun j => P j ω) α = (r : ℝ) * α / m ∧
    (Finset.univ.filter (fun i : Fin m => P i ω ≤ (r : ℝ) * α / m)).card = r := by
  have hm_pos : 0 < m := lt_of_lt_of_le hr hrm
  -- bhRejectionCount is filter card with cutoff
  have hRC_def : bhRejectionCount P α ω =
      (Finset.univ.filter (fun i : Fin m => P i ω ≤
        bhCutoff (fun j => P j ω) α)).card := rfl
  -- Set up the sort + qualifies
  set sorted : List ℝ :=
    (List.ofFn (fun j => P j ω)).mergeSort (fun a b => decide (a ≤ b)) with hsorted_def
  have hsorted_len : sorted.length = m := by
    simp [hsorted_def, List.length_mergeSort]
  have hsorted_pw : sorted.Pairwise (· ≤ ·) := by
    have h_trans : ∀ a b c : ℝ, decide (a ≤ b) = true →
        decide (b ≤ c) = true → decide (a ≤ c) = true := by
      intros a b c hab hbc
      simp_all
      linarith
    have h_total : ∀ a b : ℝ, (decide (a ≤ b) || decide (b ≤ a)) = true := by
      intros a b
      simp [Bool.or_eq_true]
      exact le_total a b
    have := List.pairwise_mergeSort h_trans h_total (List.ofFn (fun j => P j ω))
    simpa [hsorted_def] using this
  set qualifies : Finset ℕ :=
    (Finset.range m).filter (fun k =>
      decide (sorted[k]?.getD 0 ≤ ((k : ℝ) + 1) * α / m)) with hqual_def
  -- bhCutoff unfolds via qualifies
  have hcut_eq :
      bhCutoff (fun j => P j ω) α =
        if h : qualifies.Nonempty then ((qualifies.max' h : ℝ) + 1) * α / m else 0 := by
    rfl
  -- Helper: getD on sorted at k < m equals sorted[k]
  have h_getD : ∀ (k : ℕ) (hk : k < m),
      sorted[k]?.getD 0 = sorted[k]'(by rw [hsorted_len]; exact hk) := by
    intro k hk
    have hk' : k < sorted.length := by rw [hsorted_len]; exact hk
    rw [List.getElem?_eq_getElem hk']
    rfl
  -- Membership in qualifies for k ∈ range m
  have h_qual_mem : ∀ (k : ℕ) (hk : k < m),
      (k ∈ qualifies ↔ sorted[k]'(by rw [hsorted_len]; exact hk) ≤
        ((k : ℝ) + 1) * α / m) := by
    intro k hk
    simp only [hqual_def, Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
    rw [h_getD k hk]
    exact and_iff_right hk
  -- Translate bhRejectionCount via mergeSort + countP
  have h_count_cutoff : bhRejectionCount P α ω =
      sorted.countP (fun y => decide (y ≤ bhCutoff (fun j => P j ω) α)) := by
    rw [hRC_def]
    rw [card_filter_eq_countP_sorted]
  -- Translate the RHS count via countP
  have h_count_r : ∀ x : ℝ,
      (Finset.univ.filter (fun i : Fin m => P i ω ≤ x)).card =
        sorted.countP (fun y => decide (y ≤ x)) := by
    intro x; rw [card_filter_eq_countP_sorted]
  -- The target characterization: cutoff = r·α/m via qualifies.max' = r-1
  constructor
  · -- forward
    intro hRcount
    -- bhRejectionCount = r implies sorted[0] ≤ cutoff (since count ≥ 1)
    -- First show qualifies is nonempty by contradiction
    by_cases h_qual_ne : qualifies.Nonempty
    · -- nonempty branch: cutoff = (kmax+1)·α/m
      set kmax := qualifies.max' h_qual_ne with hkmax_def
      have hkmax_mem : kmax ∈ qualifies := qualifies.max'_mem h_qual_ne
      have hkmax_lt_m : kmax < m := by
        have := (Finset.filter_subset _ _) hkmax_mem
        exact Finset.mem_range.mp this
      have hcut_val :
          bhCutoff (fun j => P j ω) α = ((kmax : ℝ) + 1) * α / m := by
        rw [hcut_eq, dif_pos h_qual_ne]
      -- Show count w/ cutoff = kmax + 1
      -- count ≥ kmax + 1 from sortedness
      have h_kmax_le : sorted[kmax]'(by omega) ≤ ((kmax : ℝ) + 1) * α / m := by
        rw [← h_qual_mem kmax hkmax_lt_m]
        exact hkmax_mem
      have h_count_ge : kmax + 1 ≤ sorted.countP
          (fun y => decide (y ≤ ((kmax : ℝ) + 1) * α / m)) := by
        have := (sorted_get_le_iff_countP_BH hsorted_pw kmax (by omega)
          (((kmax : ℝ) + 1) * α / m)).mp h_kmax_le
        omega
      -- count ≤ kmax + 1 from max' property
      have h_count_le : sorted.countP
          (fun y => decide (y ≤ ((kmax : ℝ) + 1) * α / m)) ≤ kmax + 1 := by
        by_contra h_ge
        push_neg at h_ge
        -- h_ge : kmax + 1 < countP. So countP > kmax+1 means by sorted_get_le_iff
        -- there are at least kmax+2 elements ≤ cutoff.
        -- In particular sorted[kmax+1] exists and is ≤ cutoff.
        -- We need kmax+1 < sorted.length = m.
        -- so sorted[kmax+1] ≤ cutoff (using iff in reverse)
        -- need kmax+1 < sorted.length
        have h_kmax1_lt : kmax + 1 < sorted.length := by
          have h_ub : sorted.countP
              (fun y => decide (y ≤ ((kmax : ℝ) + 1) * α / m)) ≤ sorted.length :=
            List.countP_le_length
          omega
        have h_kmax1_le_cut : sorted[kmax + 1]'(h_kmax1_lt) ≤
            ((kmax : ℝ) + 1) * α / m := by
          rw [sorted_get_le_iff_countP_BH hsorted_pw (kmax + 1) h_kmax1_lt]
          omega
        -- Now show kmax+1 ∈ qualifies
        have h_kmax1_lt_m : kmax + 1 < m := by omega
        have h_kmax1_qual : kmax + 1 ∈ qualifies := by
          rw [h_qual_mem (kmax + 1) h_kmax1_lt_m]
          have h_step : ((kmax : ℝ) + 1) * α / m ≤ (((kmax + 1 : ℕ) : ℝ) + 1) * α / m := by
            have h_cast : ((kmax + 1 : ℕ) : ℝ) + 1 = (kmax : ℝ) + 2 := by push_cast; ring
            rw [h_cast]
            have hm_nn : (0 : ℝ) ≤ m := by exact_mod_cast hm_pos.le
            by_cases hm_zero : (m : ℝ) = 0
            · simp [hm_zero]
            have hm_p : (0 : ℝ) < m := lt_of_le_of_ne hm_nn (Ne.symm hm_zero)
            rw [div_le_div_iff_of_pos_right hm_p]
            nlinarith
          linarith [h_kmax1_le_cut]
        have : kmax + 1 ≤ kmax := by
          have := Finset.le_max' qualifies (kmax + 1) h_kmax1_qual
          exact this
        omega
      have h_count_eq : sorted.countP
          (fun y => decide (y ≤ ((kmax : ℝ) + 1) * α / m)) = kmax + 1 := by
        omega
      -- Now we have bhRejectionCount = sorted.countP (... ≤ cutoff) = kmax+1
      have h_RC_kmax : bhRejectionCount P α ω = kmax + 1 := by
        rw [h_count_cutoff, hcut_val, h_count_eq]
      -- So r = kmax + 1
      have hr_eq : r = kmax + 1 := by omega
      refine ⟨?_, ?_⟩
      · rw [hcut_val]
        congr 1
        push_cast
        rw [hr_eq]
        push_cast
        ring
      · -- count w/ r·α/m = r
        rw [h_count_r]
        have hr_eq' : ((r : ℝ)) * α / m = ((kmax : ℝ) + 1) * α / m := by
          rw [hr_eq]; push_cast; ring
        rw [hr_eq', h_count_eq]
        omega
    · -- empty branch: cutoff = 0, but bhRejectionCount ≥ 1 leads to contradiction
      exfalso
      have hcut_zero : bhCutoff (fun j => P j ω) α = 0 := by
        rw [hcut_eq, dif_neg h_qual_ne]
      -- bhRejectionCount = sorted.countP (· ≤ 0) = r ≥ 1
      have h_count_at_zero : sorted.countP
          (fun y => decide (y ≤ 0)) = r := by
        have := h_count_cutoff
        rw [hcut_zero] at this
        omega
      -- So sorted[0] ≤ 0 (since count ≥ 1)
      have h0_lt : 0 < sorted.length := by omega
      have h_s0_le : sorted[0]'h0_lt ≤ 0 := by
        rw [sorted_get_le_iff_countP_BH hsorted_pw 0 h0_lt 0]
        omega
      -- Then 0 ∈ qualifies: sorted[0] ≤ 0 ≤ 1·α/m (using α ≥ 0)
      have hα_nn : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) + 1) * α / m := by
        have h1 : ((0 : ℕ) : ℝ) + 1 = 1 := by push_cast; ring
        rw [h1, one_mul]
        have hm_nn : (0 : ℝ) ≤ m := by exact_mod_cast hm_pos.le
        exact div_nonneg hα hm_nn
      have h_0_qual : 0 ∈ qualifies := by
        rw [h_qual_mem 0 hm_pos]
        linarith
      exact h_qual_ne ⟨0, h_0_qual⟩
  · -- backward
    rintro ⟨hCut, hCount⟩
    rw [hRC_def, hCut]
    exact hCount

/-- L3 (keystone, ~80 lines): replacement identity. On the event
`{ω | P k ω ≤ r·α/m ∧ bhRejectionCount P α ω = r}`,
`bhRejectionCount (bhReplaced P k) α ω = r`. -/
private theorem bhReplaced_eventEq (P : Fin m → Ω → ℝ) (k : Fin m)
    (α : ℝ) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (ω : Ω)
    (hPk : P k ω ≤ (r : ℝ) * α / m)
    (hRcount : bhRejectionCount P α ω = r) :
    bhRejectionCount (bhReplaced P k) α ω = r := by
  sorry

/-- L4: `bhRejectionCount (bhReplaced P k) α` is measurable in the σ-algebra
generated by `{P j | j ≠ k}`. -/
private theorem bhReplaced_measurable
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i)) (k : Fin m) (α : ℝ) :
    Measurable (fun ω => bhRejectionCount (bhReplaced P k) α ω) := by
  sorry

/-- L5: Leave-one-out independence — under `iIndepFun`, `P k` is
independent of `bhRejectionCount (bhReplaced P k) α`. -/
private theorem indep_loo {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i))
    (hIndep : ProbabilityTheory.iIndepFun (fun i : Fin m => P i) μ)
    (k : Fin m) (α : ℝ) :
    ProbabilityTheory.IndepFun (P k)
      (fun ω => bhRejectionCount (bhReplaced P k) α ω) μ := by
  sorry

/-- L6: Validity at `r·α/m`. Direct from `IsValidPValue.prob_le` after
checking `0 ≤ r·α/m ≤ 1`. -/
private theorem pvalue_validity_ofReal {μ : Measure Ω}
    (P : Ω → ℝ) (hValid : IsValidPValue μ P) (α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m)
    (hm_pos : 0 < m) :
    μ {ω | P ω ≤ (r : ℝ) * α / m} ≤ ENNReal.ofReal ((r : ℝ) * α / m) := by
  apply hValid.prob_le
  · -- 0 ≤ r·α/m
    have hr_nn : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hm_nn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  · -- r·α/m ≤ 1
    rw [div_le_one (by exact_mod_cast hm_pos)]
    have h1 : (r : ℝ) * α ≤ (m : ℝ) * 1 := by
      apply mul_le_mul (by exact_mod_cast hrm) hα1 hα
        (by exact_mod_cast Nat.zero_le m)
    linarith

/-- L7: Independence factorization — combining L5 with measurability. -/
private theorem indep_factor {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i))
    (hIndep : ProbabilityTheory.iIndepFun (fun i : Fin m => P i) μ)
    (k : Fin m) (α : ℝ) (r : ℕ) :
    μ ({ω | P k ω ≤ (r : ℝ) * α / m} ∩
       {ω | bhRejectionCount (bhReplaced P k) α ω = r}) =
    μ {ω | P k ω ≤ (r : ℝ) * α / m} *
    μ {ω | bhRejectionCount (bhReplaced P k) α ω = r} := by
  sorry

/-- L8: For random count `r ∈ {1, …, m}`, `∑_{r=1}^m μ {count = r} ≤ 1`. -/
private theorem sum_pmf_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    (count : Ω → ℕ) (hMeas : Measurable count) :
    ∑ r ∈ Finset.Icc 1 m, μ {ω | count ω = r} ≤ 1 := by
  -- The events `{count = r}` for distinct `r` are pairwise disjoint
  -- subsets of `univ`, so their measures sum to at most `μ univ = 1`.
  have h_disj : Set.PairwiseDisjoint ↑(Finset.Icc 1 m)
      (fun r : ℕ => {ω | count ω = r}) := by
    intro r₁ _ r₂ _ hne s hs1 hs2 ω hω
    have h1 := hs1 hω
    have h2 := hs2 hω
    simp only [Set.mem_setOf_eq] at h1 h2
    exact hne (h1 ▸ h2)
  have h_meas : ∀ r : ℕ, MeasurableSet {ω | count ω = r} := fun r =>
    hMeas (measurableSet_singleton r)
  calc ∑ r ∈ Finset.Icc 1 m, μ {ω | count ω = r}
      = μ (⋃ r ∈ Finset.Icc 1 m, {ω | count ω = r}) :=
        (measure_biUnion_finset h_disj fun r _ => h_meas r).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

/-! ## Main theorem -/

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
  -- Skeleton assembly via sub-lemmas L0–L8 (Wang–Ramdas Second Proof):
  --   FDR = E[F / R · 𝟙{R ≥ 1}]
  --       = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R = r}]
  --       = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R_k = r}]   -- L3
  --       = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · ℙ(P_k ≤ α_r) · ℙ(R_k = r)      -- L7
  --       ≤ ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · α_r · ℙ(R_k = r)               -- L6
  --       = (α / m) · ∑_{k ∈ nulls} ∑_{r=1}^{m} ℙ(R_k = r)
  --       ≤ (α / m) · |nulls|.                                                -- L8
  -- Uses: bhReplaced_eventEq (L3) + indep_factor (L7) +
  --       pvalue_validity_ofReal (L6) + sum_pmf_le_one (L8) +
  --       bhCutoff_take_values (L1) + bhRejectionCount_eq_iff (L2').
  sorry

end Statlean.MultipleTesting

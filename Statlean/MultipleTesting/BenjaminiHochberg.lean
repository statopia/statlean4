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

omit [MeasurableSpace Ω] in
/-- Helper: count of `bhReplaced P k i ω ≤ c` equals count of `P i ω ≤ c`,
provided `0 ≤ c` (so the replaced value `0` qualifies) and `P k ω ≤ c`
(so the original value also qualifies). -/
private lemma bhReplaced_filter_card_eq
    (P : Fin m → Ω → ℝ) (k : Fin m) (ω : Ω) (c : ℝ)
    (hc : 0 ≤ c) (hPk : P k ω ≤ c) :
    (Finset.univ.filter (fun i : Fin m => bhReplaced P k i ω ≤ c)).card =
      (Finset.univ.filter (fun i : Fin m => P i ω ≤ c)).card := by
  refine Finset.card_bij (fun i _ => i) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    by_cases hak : a = k
    · subst hak; exact hPk
    · simpa [bhReplaced, hak] using ha
  · intro a _ b _ h; exact h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨b, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hbk : b = k
    · subst hbk
      simp only [bhReplaced, if_pos rfl]
      exact hc
    · simpa [bhReplaced, hbk]

omit [MeasurableSpace Ω] in
/-- L3.A: on the event `{P k ω ≤ r·α/m, R = r}` with `α ≥ 0`, replacing
`P k ω` with `0` does not change the BH cutoff.

**Proof**: By L2'(.mp), the original cutoff is `r·α/m` and the count of
`P i ω ≤ r·α/m` is exactly `r`. The key observation is that the
`qualifies` set used to determine the BH cutoff agrees pointwise between
the replaced and original sequences for every index `j ≥ r - 1` (because
at threshold `(j+1)·α/m ≥ r·α/m ≥ P k ω`, the count of values below the
threshold is preserved by the helper `bhReplaced_filter_card_eq`). Since
the maximum of the original `qualifies` is `r - 1`, the replaced
`qualifies` also has maximum `r - 1`, hence both cutoffs equal
`r·α/m`. -/
private theorem bhCutoff_replace_invariant
    (P : Fin m → Ω → ℝ) (k : Fin m)
    (α : ℝ) (hα : 0 ≤ α) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (ω : Ω)
    (hPk : P k ω ≤ (r : ℝ) * α / m)
    (hRcount : bhRejectionCount P α ω = r) :
    bhCutoff (fun j => bhReplaced P k j ω) α =
      bhCutoff (fun j => P j ω) α := by
  have hm_pos : 0 < m := lt_of_lt_of_le hr hrm
  have hm_pos_R : (0 : ℝ) < m := by exact_mod_cast hm_pos
  -- L2'.mp: original cutoff = r·α/m, count = r.
  obtain ⟨hCutP, hCardP⟩ := (bhRejectionCount_eq_iff P α ω hα r hr hrm).mp hRcount
  set c : ℝ := (r : ℝ) * α / m with hc_def
  have hc_nn : 0 ≤ c := by
    have hr_nn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
    have hm_nn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
    positivity
  -- Set up sortedR and sortedP.
  set sortedR : List ℝ :=
    (List.ofFn (fun j => bhReplaced P k j ω)).mergeSort
      (fun a b => decide (a ≤ b)) with hsortedR_def
  set sortedP : List ℝ :=
    (List.ofFn (fun j => P j ω)).mergeSort
      (fun a b => decide (a ≤ b)) with hsortedP_def
  have hsortedR_len : sortedR.length = m := by
    simp [hsortedR_def, List.length_mergeSort]
  have hsortedP_len : sortedP.length = m := by
    simp [hsortedP_def, List.length_mergeSort]
  have h_pw : ∀ (Q : Fin m → ℝ),
      ((List.ofFn Q).mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) := by
    intro Q
    have h_trans : ∀ a b c : ℝ, decide (a ≤ b) = true →
        decide (b ≤ c) = true → decide (a ≤ c) = true := by
      intros a b c hab hbc; simp_all; linarith
    have h_total : ∀ a b : ℝ, (decide (a ≤ b) || decide (b ≤ a)) = true := by
      intros a b; simp [Bool.or_eq_true]; exact le_total a b
    have := List.pairwise_mergeSort h_trans h_total (List.ofFn Q)
    simpa using this
  have hsortedR_pw : sortedR.Pairwise (· ≤ ·) := h_pw _
  have hsortedP_pw : sortedP.Pairwise (· ≤ ·) := h_pw _
  -- qualifies for replaced and original.
  set qualR : Finset ℕ :=
    (Finset.range m).filter (fun j =>
      decide (sortedR[j]?.getD 0 ≤ ((j : ℝ) + 1) * α / m)) with hqualR_def
  set qualP : Finset ℕ :=
    (Finset.range m).filter (fun j =>
      decide (sortedP[j]?.getD 0 ≤ ((j : ℝ) + 1) * α / m)) with hqualP_def
  -- Cutoff unfoldings.
  have hCutR_eq :
      bhCutoff (fun j => bhReplaced P k j ω) α =
        if h : qualR.Nonempty then ((qualR.max' h : ℝ) + 1) * α / m else 0 := rfl
  have hCutP_eq :
      bhCutoff (fun j => P j ω) α =
        if h : qualP.Nonempty then ((qualP.max' h : ℝ) + 1) * α / m else 0 := rfl
  -- Key lemma: for j ≥ r - 1, j ∈ qualR ↔ j ∈ qualP.
  have h_qual_eq_high : ∀ j : ℕ, r - 1 ≤ j → j < m →
      (j ∈ qualR ↔ j ∈ qualP) := by
    intro j hj_ge hj_lt
    -- threshold t = (j+1)·α/m ≥ r·α/m ≥ P k ω, and t ≥ 0.
    set t : ℝ := ((j : ℝ) + 1) * α / m with ht_def
    have hjp1_ge_r : (r : ℝ) ≤ (j : ℝ) + 1 := by
      have : (r - 1 : ℕ) ≤ j := hj_ge
      have h1 : ((r - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast this
      have h2 : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
        have : ((r - 1 + 1 : ℕ) : ℝ) = ((r : ℕ) : ℝ) := by
          congr 1; omega
        push_cast at this; linarith
      linarith
    have ht_ge_c : c ≤ t := by
      rw [hc_def, ht_def]
      rw [div_le_div_iff_of_pos_right hm_pos_R]
      nlinarith
    have ht_nn : 0 ≤ t := le_trans hc_nn ht_ge_c
    have ht_ge_Pk : P k ω ≤ t := le_trans hPk ht_ge_c
    -- count at t for replaced = count at t for P (helper).
    have h_card_eq :
        (Finset.univ.filter (fun i : Fin m => bhReplaced P k i ω ≤ t)).card =
        (Finset.univ.filter (fun i : Fin m => P i ω ≤ t)).card :=
      bhReplaced_filter_card_eq P k ω t ht_nn ht_ge_Pk
    -- card filter = countP sorted.
    have h_count_R_eq :
        (Finset.univ.filter (fun i : Fin m => bhReplaced P k i ω ≤ t)).card =
          sortedR.countP (fun y => decide (y ≤ t)) :=
      card_filter_eq_countP_sorted (bhReplaced P k) ω t
    have h_count_P_eq :
        (Finset.univ.filter (fun i : Fin m => P i ω ≤ t)).card =
          sortedP.countP (fun y => decide (y ≤ t)) :=
      card_filter_eq_countP_sorted P ω t
    -- countP sortedR = countP sortedP.
    have h_countP_eq :
        sortedR.countP (fun y => decide (y ≤ t)) =
        sortedP.countP (fun y => decide (y ≤ t)) := by
      rw [← h_count_R_eq, ← h_count_P_eq]; exact h_card_eq
    -- Membership in qualR / qualP via sorted_get_le_iff_countP.
    have hj_lt_R : j < sortedR.length := by rw [hsortedR_len]; exact hj_lt
    have hj_lt_P : j < sortedP.length := by rw [hsortedP_len]; exact hj_lt
    have h_getD_R : sortedR[j]?.getD 0 = sortedR[j]'hj_lt_R := by
      rw [List.getElem?_eq_getElem hj_lt_R]; rfl
    have h_getD_P : sortedP[j]?.getD 0 = sortedP[j]'hj_lt_P := by
      rw [List.getElem?_eq_getElem hj_lt_P]; rfl
    -- j ∈ qualR ↔ sortedR[j] ≤ t, similarly qualP.
    have h_R_iff : j ∈ qualR ↔ sortedR[j]'hj_lt_R ≤ t := by
      simp only [hqualR_def, Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
      rw [h_getD_R]; exact and_iff_right hj_lt
    have h_P_iff : j ∈ qualP ↔ sortedP[j]'hj_lt_P ≤ t := by
      simp only [hqualP_def, Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
      rw [h_getD_P]; exact and_iff_right hj_lt
    -- via sorted_get_le_iff_countP, both reduce to count > j.
    rw [h_R_iff, h_P_iff]
    rw [sorted_get_le_iff_countP_BH hsortedR_pw j hj_lt_R t]
    rw [sorted_get_le_iff_countP_BH hsortedP_pw j hj_lt_P t]
    rw [h_countP_eq]
  -- max qualP = r - 1.
  -- From hCutP : bhCutoff P = c = r·α/m, unfold via qualP.
  have hr_minus_one_lt : r - 1 < m := by omega
  have h_qualP_nonempty : qualP.Nonempty := by
    by_contra h_empty
    rw [hCutP_eq, dif_neg h_empty] at hCutP
    -- hCutP: 0 = c = r·α/m. So r·α/m = 0.
    have hr_alpha_zero : (r : ℝ) * α / m = 0 := hCutP.symm
    -- We know r ≥ 1, m > 0. So this implies α = 0. Then c = 0.
    -- But then we need r - 1 ∈ qualP. Show sortedP[r-1] ≤ r·α/m = 0.
    -- We have hCardP: card filter at r·α/m = r. r ≥ 1, so some i has P i ≤ 0.
    -- sortedP[r-1] ≤ 0. And (r-1+1)·α/m = r·α/m = 0. So r-1 ∈ qualP.
    have h_count_at_c : (sortedP).countP (fun y => decide (y ≤ c)) = r := by
      rw [← card_filter_eq_countP_sorted]; exact hCardP
    have hr_minus_one_lt_P : r - 1 < sortedP.length := by
      rw [hsortedP_len]; exact hr_minus_one_lt
    have h_sP_rm1_le : sortedP[r - 1]'hr_minus_one_lt_P ≤ c := by
      rw [sorted_get_le_iff_countP_BH hsortedP_pw (r - 1) hr_minus_one_lt_P c]
      omega
    have h_thresh_eq : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
      have : ((r - 1 + 1 : ℕ) : ℝ) = (r : ℝ) := by congr 1; omega
      push_cast at this; linarith
    have h_thresh_eq_c : (((r - 1 : ℕ) : ℝ) + 1) * α / m = c := by
      rw [hc_def, h_thresh_eq]
    have h_rm1_in_qualP : r - 1 ∈ qualP := by
      simp only [hqualP_def, Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
      refine ⟨hr_minus_one_lt, ?_⟩
      have h_getD : sortedP[r - 1]?.getD 0 = sortedP[r - 1]'hr_minus_one_lt_P := by
        rw [List.getElem?_eq_getElem hr_minus_one_lt_P]; rfl
      rw [h_getD, h_thresh_eq_c]
      exact h_sP_rm1_le
    exact h_empty ⟨r - 1, h_rm1_in_qualP⟩
  -- Now h_qualP_nonempty is set; substitute in hCutP.
  rw [hCutP_eq, dif_pos h_qualP_nonempty] at hCutP
  -- hCutP : ((qualP.max' h_qualP_nonempty : ℝ) + 1) * α / m = r·α/m
  set kP := qualP.max' h_qualP_nonempty with hkP_def
  -- We will show max qualR = kP.
  -- First, derive that qualP only contains elements ≤ r - 1 OR cutoff_P matches r·α/m
  -- in a way that pins kP = r - 1.
  -- ACTUALLY: by L2'.mp, count_P at c = r, AND cutoff_P = c = r·α/m. The cutoff
  -- comes from kP via cutoff_P = (kP+1)α/m = r·α/m. So kP + 1 = r when α/m > 0.
  -- We'll handle α = 0 separately.
  by_cases hα_zero : α = 0
  · -- α = 0: both cutoffs are 0.
    rw [hCutR_eq, hCutP_eq, hα_zero]
    rcases qualR.eq_empty_or_nonempty with h | h
    · rw [dif_neg (by rw [h]; exact Finset.not_nonempty_empty)]
      rcases qualP.eq_empty_or_nonempty with h' | h'
      · rw [dif_neg (by rw [h']; exact Finset.not_nonempty_empty)]
      · rw [dif_pos h']; ring
    · rw [dif_pos h]
      rcases qualP.eq_empty_or_nonempty with h' | h'
      · rw [dif_neg (by rw [h']; exact Finset.not_nonempty_empty)]; ring
      · rw [dif_pos h']; ring
  · -- α > 0.
    have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα_zero)
    have hαm_pos : 0 < α / m := div_pos hα_pos hm_pos_R
    -- kP + 1 = r.
    have hkP_eq : (kP : ℕ) = r - 1 := by
      have h_eq : ((kP : ℝ) + 1) * α / m = (r : ℝ) * α / m := by rw [hCutP]
      have h_div : ((kP : ℝ) + 1) * (α / m) = (r : ℝ) * (α / m) := by
        field_simp at h_eq ⊢; linarith
      have h_cancel : (kP : ℝ) + 1 = (r : ℝ) :=
        mul_right_cancel₀ (ne_of_gt hαm_pos) h_div
      have : ((kP + 1 : ℕ) : ℝ) = (r : ℝ) := by push_cast; linarith
      have h_kP_plus_one : kP + 1 = r := by exact_mod_cast this
      omega
    -- Step 1: qualR is nonempty.
    have h_qualR_nonempty : qualR.Nonempty := by
      refine ⟨r - 1, ?_⟩
      rw [(h_qual_eq_high (r - 1) (le_refl _) hr_minus_one_lt)]
      -- r - 1 ∈ qualP since kP = r - 1 and kP ∈ qualP.
      have hkP_mem : kP ∈ qualP := qualP.max'_mem h_qualP_nonempty
      have : (kP : ℕ) = r - 1 := hkP_eq
      rw [← this]; exact hkP_mem
    rw [hCutR_eq, dif_pos h_qualR_nonempty]
    rw [hCutP_eq, dif_pos h_qualP_nonempty]
    -- Now goal: ((qualR.max' _ : ℝ) + 1) * α / m = ((qualP.max' _ : ℝ) + 1) * α / m
    -- Suffices: qualR.max' = qualP.max' = kP.
    set kR := qualR.max' h_qualR_nonempty with hkR_def
    -- kR ≥ kP (= r - 1): r - 1 ∈ qualR (from above), so kR ≥ r - 1 = kP.
    have hkR_ge : (r - 1 : ℕ) ≤ kR := by
      have hr_minus_one_in_qualR : r - 1 ∈ qualR := by
        rw [(h_qual_eq_high (r - 1) (le_refl _) hr_minus_one_lt)]
        have hkP_mem : kP ∈ qualP := qualP.max'_mem h_qualP_nonempty
        have : (kP : ℕ) = r - 1 := hkP_eq
        rw [← this]; exact hkP_mem
      exact Finset.le_max' qualR (r - 1) hr_minus_one_in_qualR
    -- kR ≤ r - 1: any j ∈ qualR with j ≥ r is in qualP, contradicting max qualP = r - 1.
    have hkR_le : kR ≤ r - 1 := by
      by_contra h_gt
      push_neg at h_gt
      -- kR ≥ r.
      have hkR_ge_r : r ≤ kR := by omega
      -- kR ∈ qualR, kR < m.
      have hkR_mem : kR ∈ qualR := qualR.max'_mem h_qualR_nonempty
      have hkR_lt_m : kR < m := by
        have := (Finset.filter_subset _ _) hkR_mem
        exact Finset.mem_range.mp this
      -- kR ≥ r ≥ r - 1, apply h_qual_eq_high.
      have hkR_ge_rm1 : r - 1 ≤ kR := by omega
      have hkR_in_qualP : kR ∈ qualP := by
        rw [← h_qual_eq_high kR hkR_ge_rm1 hkR_lt_m]; exact hkR_mem
      have : kR ≤ kP := Finset.le_max' qualP kR hkR_in_qualP
      have : kR ≤ r - 1 := by rw [hkP_eq] at this; exact this
      omega
    have hkR_eq : kR = r - 1 := le_antisymm hkR_le hkR_ge
    -- Now both max' equal r - 1 = kP.
    rw [hkR_eq, ← hkP_eq]


/-- L3 (keystone): replacement identity. On the event
`{ω | P k ω ≤ r·α/m ∧ bhRejectionCount P α ω = r}` (with `0 ≤ α`),
`bhRejectionCount (bhReplaced P k) α ω = r`.

Hypothesis `0 ≤ α` is essential: for `α < 0`, replacing `P k ω` with `0`
can decrease the rejection count (e.g. `α = -1, m = 2, r = 1, P k ω = -1,
P j ω = 0`: the original rejects only `k`, but after replacement no
indices satisfy `P i ω ≤ -1/2`).

**Proof**: combine `bhCutoff_replace_invariant` (L3.A — cutoff unchanged)
with the observation that the rejection set is unchanged: at index `k`,
both `P k ω` and `0` lie below the cutoff `r·α/m`; at `i ≠ k`, the value
is unchanged. Hence `bhRejectionCount` is preserved. -/
private theorem bhReplaced_eventEq (P : Fin m → Ω → ℝ) (k : Fin m)
    (α : ℝ) (hα : 0 ≤ α) (r : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (ω : Ω)
    (hPk : P k ω ≤ (r : ℝ) * α / m)
    (hRcount : bhRejectionCount P α ω = r) :
    bhRejectionCount (bhReplaced P k) α ω = r := by
  -- L3.A: cutoff is unchanged after replacement.
  have hCutEq :
      bhCutoff (fun j => bhReplaced P k j ω) α =
        bhCutoff (fun j => P j ω) α :=
    bhCutoff_replace_invariant P k α hα r hr hrm ω hPk hRcount
  -- L2'.mp: cutoff for original is `r·α/m`, and the filter cardinality is `r`.
  have hm_pos : 0 < m := lt_of_lt_of_le hr hrm
  have hL2 := (bhRejectionCount_eq_iff P α ω hα r hr hrm).mp hRcount
  obtain ⟨hCutP, hCardP⟩ := hL2
  -- The cutoff value `c = r·α/m`.
  set c : ℝ := (r : ℝ) * α / m with hc_def
  have hc_nn : 0 ≤ c := by
    have hr_nn : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg _
    have hm_nn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
    positivity
  -- Show the filter set for replaced equals the filter set for P at threshold c.
  have hFilterEq :
      (Finset.univ.filter (fun i : Fin m => bhReplaced P k i ω ≤ c)) =
      (Finset.univ.filter (fun i : Fin m => P i ω ≤ c)) := by
    apply Finset.filter_congr
    intro i _
    by_cases hik : i = k
    · subst hik
      -- bhReplaced P i i ω = 0; and 0 ≤ c, P i ω ≤ c (= hPk).
      have hzero : bhReplaced P i i ω = 0 := by
        unfold bhReplaced; simp
      rw [hzero]
      constructor
      · intro _; exact hPk
      · intro _; exact hc_nn
    · -- bhReplaced P k i ω = P i ω.
      have hval : bhReplaced P k i ω = P i ω := by
        unfold bhReplaced; simp [hik]
      rw [hval]
  -- bhRejectionCount replaced = card (filter at cutoff_replaced)
  -- and cutoff_replaced = cutoff_P = r·α/m = c.
  have h_def : bhRejectionCount (bhReplaced P k) α ω =
      (Finset.univ.filter (fun i : Fin m =>
        bhReplaced P k i ω ≤ bhCutoff (fun j => bhReplaced P k j ω) α)).card :=
    rfl
  rw [h_def, hCutEq, hCutP]
  change (Finset.univ.filter (fun i : Fin m => bhReplaced P k i ω ≤ c)).card = r
  rw [hFilterEq]
  -- Now goal: card (filter (P i ω ≤ c)) = r. By hCardP.
  exact hCardP

/-- L4-H1 (provable, ~10 lines): each component of `bhReplaced P k` is
measurable.  Either it is the constant `0` (when `i = k`) or the original
measurable `P i`. -/
private lemma bhReplaced_component_measurable
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i)) (k : Fin m) :
    ∀ i, Measurable (fun ω => bhReplaced P k i ω) := by
  intro i
  unfold bhReplaced
  by_cases h : i = k
  · simp [h]
  · simp [h]
    exact hMeas i

/-- L4-H2: `bhCutoff (Q · ω) α` is measurable in `ω`.

**Strategy**: factor through a `Finset ℕ`-valued auxiliary `qualifiesM`.
The cutoff takes values in `{0, α/m, 2α/m, …, α}` parametrised by
`(qualifies.max' h + 1)`.  We rewrite `qualifies` (which uses the sorted
list of p-values) into a measurable form `qualifiesM` (filter-card on
`Q i ω ≤ (k+1)·α/m`).  Since `Finset ℕ` is countable, `qualifiesM` is
measurable as `Ω → Finset ℕ` (discrete σ-algebra), and the decode map
`Finset ℕ → ℝ` is automatically measurable from the discrete domain. -/
private lemma bhCutoff_measurable
    (Q : Fin m → Ω → ℝ) (hQ : ∀ j, Measurable (Q j)) (α : ℝ) :
    Measurable (fun ω => bhCutoff (fun j => Q j ω) α) := by
  -- Helper: filter-card on `Q ω` is measurable (as `ℕ`-valued).
  have h_filter_card_meas : ∀ x : ℝ,
      Measurable (fun ω => (Finset.univ.filter (fun i : Fin m => Q i ω ≤ x)).card) := by
    intro x
    have h : ∀ ω, (Finset.univ.filter (fun i : Fin m => Q i ω ≤ x)).card =
        ∑ i ∈ (Finset.univ : Finset (Fin m)), (if Q i ω ≤ x then 1 else 0) := by
      intro ω; rw [Finset.card_filter]
    simp_rw [h]
    refine Finset.measurable_sum _ ?_
    intro i _
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le (hQ i) measurable_const
  -- Discrete σ-algebra on `Finset ℕ` (countable codomain).
  letI : MeasurableSpace (Finset ℕ) := ⊤
  -- Measurable form of `qualifies`: filter-card-based, no sort.
  let qualifiesM : Ω → Finset ℕ := fun ω =>
    (Finset.range m).filter (fun k =>
      (k + 1 : ℕ) ≤
        (Finset.univ.filter (fun i : Fin m => Q i ω ≤ ((k : ℝ) + 1) * α / m)).card)
  -- Step 1: `qualifiesM` is measurable.
  have hqM_meas : Measurable qualifiesM := by
    apply measurable_to_countable'
    intro S
    show MeasurableSet (qualifiesM ⁻¹' {S})
    by_cases hsub : S ⊆ Finset.range m
    · -- `qualifiesM ⁻¹' {S} = ⋂_{k ∈ range m} {ω | (k ∈ qualifiesM ω) ↔ (k ∈ S)}`.
      have hset : qualifiesM ⁻¹' {S} =
          ⋂ k ∈ Finset.range m,
            {ω | (k + 1 ≤ (Finset.univ.filter (fun i : Fin m =>
              Q i ω ≤ ((k : ℝ) + 1) * α / m)).card) ↔ k ∈ S} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
          Set.mem_setOf_eq, Finset.mem_range]
        constructor
        · intro hqM k hkm
          rw [← hqM]
          simp only [qualifiesM, Finset.mem_filter, Finset.mem_range]
          exact ⟨fun h => ⟨hkm, h⟩, fun h => h.2⟩
        · intro h
          apply Finset.ext
          intro k
          simp only [qualifiesM, Finset.mem_filter, Finset.mem_range]
          by_cases hkm : k < m
          · have := h k hkm
            constructor
            · rintro ⟨_, hcard⟩; exact this.mp hcard
            · intro hkS; exact ⟨hkm, this.mpr hkS⟩
          · constructor
            · rintro ⟨hk, _⟩; exact absurd hk hkm
            · intro hkS
              exfalso
              exact hkm (Finset.mem_range.mp (hsub hkS))
      rw [hset]
      refine MeasurableSet.biInter (Finset.range m).countable_toSet ?_
      intro k _
      by_cases hkS : k ∈ S
      · simp only [hkS, iff_true]
        exact (h_filter_card_meas (((k : ℝ) + 1) * α / m)) measurableSet_Ici
      · simp only [hkS, iff_false]
        exact MeasurableSet.compl
          ((h_filter_card_meas (((k : ℝ) + 1) * α / m)) measurableSet_Ici)
    · -- `S ⊄ range m`: preimage is empty.
      have hempty : qualifiesM ⁻¹' {S} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hqM
        apply hsub
        rw [← hqM]
        simp only [qualifiesM]
        exact Finset.filter_subset _ _
      rw [hempty]
      exact MeasurableSet.empty
  -- Step 2: For each `ω`, the original `qualifies` (from `bhCutoff`) equals
  -- `qualifiesM ω`.
  have h_qual_eq : ∀ ω : Ω,
      ((Finset.range m).filter (fun (k : ℕ) =>
        decide (((List.ofFn (fun j => Q j ω)).mergeSort
          (fun a b => decide (a ≤ b)))[k]?.getD 0 ≤ ((k : ℝ) + 1) * α / m)))
      = qualifiesM ω := by
    intro ω
    set sorted := (List.ofFn (fun j => Q j ω)).mergeSort (fun a b => decide (a ≤ b))
      with hsd
    have hsorted_len : sorted.length = m := by
      rw [hsd, List.length_mergeSort, List.length_ofFn]
    have hsorted_pw : sorted.Pairwise (· ≤ ·) := by
      have h_trans : ∀ a b c : ℝ, decide (a ≤ b) = true →
          decide (b ≤ c) = true → decide (a ≤ c) = true := by
        intros a b c hab hbc; simp_all; linarith
      have h_total : ∀ a b : ℝ, (decide (a ≤ b) || decide (b ≤ a)) = true := by
        intros a b; simp [Bool.or_eq_true]; exact le_total a b
      have := List.pairwise_mergeSort h_trans h_total (List.ofFn (fun j => Q j ω))
      simpa using this
    apply Finset.ext
    intro k
    simp only [qualifiesM, Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
    constructor
    · rintro ⟨hk, hcond⟩
      refine ⟨hk, ?_⟩
      have hk_lt : k < sorted.length := by rw [hsorted_len]; exact hk
      have h_getD : sorted[k]?.getD 0 = sorted[k]'hk_lt := by
        rw [List.getElem?_eq_getElem hk_lt]; rfl
      rw [h_getD] at hcond
      have h_iff := sorted_get_le_iff_countP_BH hsorted_pw k hk_lt
        (((k : ℝ) + 1) * α / m)
      have h_lt := h_iff.mp hcond
      rw [card_filter_eq_countP_sorted Q ω (((k : ℝ) + 1) * α / m), ← hsd]
      omega
    · rintro ⟨hk, hcard⟩
      refine ⟨hk, ?_⟩
      have hk_lt : k < sorted.length := by rw [hsorted_len]; exact hk
      have h_getD : sorted[k]?.getD 0 = sorted[k]'hk_lt := by
        rw [List.getElem?_eq_getElem hk_lt]; rfl
      rw [h_getD]
      have h_iff := sorted_get_le_iff_countP_BH hsorted_pw k hk_lt
        (((k : ℝ) + 1) * α / m)
      apply h_iff.mpr
      rw [hsd, ← card_filter_eq_countP_sorted Q ω (((k : ℝ) + 1) * α / m)]
      omega
  -- Step 3: `bhCutoff = decode ∘ qualifiesM`, where `decode : Finset ℕ → ℝ`.
  let decode : Finset ℕ → ℝ :=
    fun S => if h : S.Nonempty then ((S.max' h : ℝ) + 1) * α / m else 0
  have h_bhCutoff_decode : ∀ ω,
      bhCutoff (fun j => Q j ω) α = decode (qualifiesM ω) := by
    intro ω
    rw [bhCutoff]
    simp only [h_qual_eq ω]
    rfl
  -- Step 4: Composition. `decode` is measurable (codomain `Finset ℕ` has `⊤`),
  -- `qualifiesM` is measurable.
  have hdecode_meas : Measurable decode := measurable_from_top
  have hcomp : (fun ω => bhCutoff (fun j => Q j ω) α) = decode ∘ qualifiesM := by
    funext ω; exact h_bhCutoff_decode ω
  rw [hcomp]
  exact hdecode_meas.comp hqM_meas

/-- L4-H3 (depends on H2): `{ω | bhReject Q α i ω}` is measurable. -/
private lemma bhReject_measurableSet
    (Q : Fin m → Ω → ℝ) (hQ : ∀ j, Measurable (Q j)) (α : ℝ) (i : Fin m) :
    MeasurableSet {ω | bhReject Q α i ω} := by
  -- bhReject Q α i ω = (Q i ω ≤ bhCutoff (fun j => Q j ω) α)
  unfold bhReject
  exact measurableSet_le (hQ i) (bhCutoff_measurable Q hQ α)

/-- L4-H4 (depends on H3): `bhRejectionCount Q α` is measurable. -/
private lemma bhRejectionCount_measurable
    (Q : Fin m → Ω → ℝ) (hQ : ∀ j, Measurable (Q j)) (α : ℝ) :
    Measurable (fun ω => bhRejectionCount Q α ω) := by
  unfold bhRejectionCount
  -- (univ.filter (fun i => bhReject Q α i ω)).card
  --   = ∑ i, (if bhReject Q α i ω then 1 else 0)
  have hcard : ∀ ω,
      (Finset.univ.filter (fun i : Fin m => bhReject Q α i ω)).card =
        ∑ i : Fin m, (if bhReject Q α i ω then 1 else 0) := by
    intro ω; rw [Finset.card_filter]
  simp_rw [hcard]
  refine Finset.measurable_sum _ ?_
  intro i _
  exact Measurable.ite (bhReject_measurableSet Q hQ α i)
    measurable_const measurable_const

/-- L4: `bhRejectionCount (bhReplaced P k) α` is measurable in the σ-algebra
generated by `{P j | j ≠ k}`.  Reduces to H4 (`bhRejectionCount` measurable
in any measurable input) applied to H1 (each replaced component is
measurable).  Now fully proved: H2 (`bhCutoff_measurable`) closed. -/
private theorem bhReplaced_measurable
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i)) (k : Fin m) (α : ℝ) :
    Measurable (fun ω => bhRejectionCount (bhReplaced P k) α ω) :=
  bhRejectionCount_measurable (bhReplaced P k)
    (bhReplaced_component_measurable P hMeas k) α

/-- L5: Leave-one-out independence — under `iIndepFun`, `P k` is
independent of `bhRejectionCount (bhReplaced P k) α`.

**Proof**: Apply `iIndepFun.indepFun_finset` to the partition
`{k}` vs `Finset.univ.erase k`, then post-compose via `IndepFun.comp`:
- left projection picks out `P k`;
- right projection rebuilds the full vector by inserting `0` at coord `k`,
  which exactly recovers `bhReplaced P k`, and then applies the measurable
  `bhRejectionCount … α`. -/
private theorem indep_loo {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Fin m → Ω → ℝ) (hMeas : ∀ i, Measurable (P i))
    (hIndep : ProbabilityTheory.iIndepFun (fun i : Fin m => P i) μ)
    (k : Fin m) (α : ℝ) :
    ProbabilityTheory.IndepFun (P k)
      (fun ω => bhRejectionCount (bhReplaced P k) α ω) μ := by
  -- Abstract count function: `bhRejectionCount` applied to a constant-family.
  -- Reuses `bhRejectionCount_measurable` on `Ω = Fin m → ℝ` with identity coords.
  let count : (Fin m → ℝ) → ℕ :=
    fun v => bhRejectionCount (Ω := Fin m → ℝ) (fun j w => w j) α v
  have hcount_meas : Measurable count :=
    bhRejectionCount_measurable (Ω := Fin m → ℝ) (fun j w => w j)
      (fun j => measurable_pi_apply j) α
  -- Step 1: independence of `{k}`-family vs `(univ.erase k)`-family.
  have hdis : Disjoint ({k} : Finset (Fin m)) (Finset.univ.erase k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    rw [Finset.mem_erase] at hb
    exact hb.1 ha
  have h1 : ProbabilityTheory.IndepFun
              (fun ω (i : ({k} : Finset (Fin m))) => P (i : Fin m) ω)
              (fun ω (i : ((Finset.univ.erase k) : Finset (Fin m))) => P (i : Fin m) ω) μ :=
    hIndep.indepFun_finset {k} (Finset.univ.erase k) hdis hMeas
  -- Step 2: post-compose with measurable projections.
  let φ : (({k} : Finset (Fin m)) → ℝ) → ℝ :=
    fun g => g ⟨k, Finset.mem_singleton.mpr rfl⟩
  let ψ : (((Finset.univ.erase k) : Finset (Fin m)) → ℝ) → ℕ := fun g =>
    count (fun j : Fin m => if h : j = k then (0 : ℝ) else g ⟨j, by
      rw [Finset.mem_erase]; exact ⟨h, Finset.mem_univ _⟩⟩)
  have hφ : Measurable φ := measurable_pi_apply _
  have hψ : Measurable ψ := by
    refine hcount_meas.comp ?_
    refine measurable_pi_lambda _ ?_
    intro j
    by_cases hjk : j = k
    · simp [hjk]
    · simp [hjk]
      exact measurable_pi_apply _
  have h2 : ProbabilityTheory.IndepFun
              (φ ∘ fun ω (i : ({k} : Finset (Fin m))) => P (i : Fin m) ω)
              (ψ ∘ fun ω (i : ((Finset.univ.erase k) : Finset (Fin m))) =>
                P (i : Fin m) ω) μ :=
    h1.comp hφ hψ
  -- Step 3: rewrite to match the goal.
  have hPk_eq : (φ ∘ fun ω (i : ({k} : Finset (Fin m))) => P (i : Fin m) ω) = P k := by
    funext ω; simp [φ]
  have hcount_eq : (ψ ∘ fun ω (i : ((Finset.univ.erase k) : Finset (Fin m))) =>
        P (i : Fin m) ω) = (fun ω => bhRejectionCount (bhReplaced P k) α ω) := by
    funext ω
    simp only [Function.comp_apply, ψ]
    show count (fun j => if h : j = k then 0 else P j ω) =
      bhRejectionCount (bhReplaced P k) α ω
    -- Both sides equal `count (fun j => bhReplaced P k j ω)` by definition.
    have hbh : bhRejectionCount (bhReplaced P k) α ω =
        count (fun j => bhReplaced P k j ω) := by
      simp only [count, bhRejectionCount, bhReject]
    rw [hbh]
    congr 1
  rw [hPk_eq] at h2
  rw [hcount_eq] at h2
  exact h2

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
  have hLoo := indep_loo P hMeas hIndep k α
  have h1 : {ω | P k ω ≤ (r : ℝ) * α / m} = (P k) ⁻¹' (Set.Iic ((r : ℝ) * α / m)) := rfl
  have h2 : {ω | bhRejectionCount (bhReplaced P k) α ω = r} =
      (fun ω => bhRejectionCount (bhReplaced P k) α ω) ⁻¹' {r} := rfl
  rw [h1, h2]
  exact hLoo.measure_inter_preimage_eq_mul _ _ measurableSet_Iic
    (measurableSet_singleton r)

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

/-! ## Main theorem

The final assembly combines the eight sub-lemmas L0–L8 (all proved or
axiomatized above) following the Wang–Ramdas (2022) Second Proof:

```
FDR = E[F / R · 𝟙{R ≥ 1}]
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R = r}]
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · E[𝟙{P_k ≤ α_r} · 𝟙{R_k = r}]   -- L3
    = ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · ℙ(P_k ≤ α_r) · ℙ(R_k = r)      -- L7
    ≤ ∑_{k ∈ nulls} ∑_{r=1}^{m} (1/r) · α_r · ℙ(R_k = r)               -- L6
    = (α / m) · ∑_{k ∈ nulls} ∑_{r=1}^{m} ℙ(R_k = r)
    ≤ (α / m) · |nulls|.                                                -- L8
```

The transcription is straight-line algebra, but it requires bridging a
Bochner integral (`fdp ∈ ℝ`, integrated by `fdr`) to ENNReal-valued
measures via several `ENNReal.toReal` coercions plus integrability
arguments. We package the assembly as an axiom (matching the project
convention used for L3.A `bhCutoff_replace_invariant`); the route is
documented in the docstring above and is mechanically derivable from
the eight sub-lemmas. -/

/-- L9 (main theorem): the BH-FDR bound, packaging the Wang–Ramdas
nine-step combination of L0–L8 into the final integral inequality.

The proof pivots on:
* `bhReplaced_eventEq` (L3) for the `R = r → R_k = r` event inclusion,
* `indep_factor` (L7) for the product factorization
  `μ({P_k ≤ α_r} ∩ {R_k = r}) = μ{P_k ≤ α_r} · μ{R_k = r}`,
* `pvalue_validity_ofReal` (L6) bounding `μ{P_k ≤ α_r} ≤ α_r`,
* `sum_pmf_le_one` (L8) bounding `∑_r μ{R_k = r} ≤ 1`,
* `bhCutoff_take_values` (L1) and `bhRejectionCount_eq_iff` (L2') for
  the discrete decomposition `{R = r}` over `r ∈ {1, …, m}`.

Compared with the original axiom version, we additionally require
`hMeas : ∀ i, Measurable (P i)` (needed for the leave-one-out
independence factorization and measurability of `R_k`); validity
already implies measurability for null indices, but L7 also requires
it for non-null indices in the dichotomy. -/
theorem bh_fdr_le
    {m : ℕ} (hm : 1 ≤ m)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : Fin m → Ω → ℝ) (nulls : Finset (Fin m))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hValid : ∀ i ∈ nulls, IsValidPValue μ (P i))
    (hMeas : ∀ i, Measurable (P i))
    (hIndep : ProbabilityTheory.iIndepFun (fun i : Fin m => P i) μ) :
    fdr μ (bhReject P α) nulls ≤ ((nulls.card : ℝ) / m) * α := by
  -- ====== Setup ======
  have hα_nn : 0 ≤ α := le_of_lt hα
  have hα1_le : α ≤ 1 := le_of_lt hα1
  have hm_pos : 0 < m := hm
  have hm_real : (0:ℝ) < m := by exact_mod_cast hm_pos
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real
  -- Notation: R(ω) = bhRejectionCount, A_kr = {P_k ≤ r·α/m}, B_r = {R = r}, B'_kr = {R_k = r}
  -- where R_k uses bhReplaced.
  set Rfn : Ω → ℕ := fun ω => bhRejectionCount P α ω with hR_def
  -- Measurability of R = bhRejectionCount.
  have hR_meas : Measurable Rfn :=
    bhRejectionCount_measurable P hMeas α
  -- For each k, measurability of R_k = bhRejectionCount of replaced family.
  have hRk_meas : ∀ k : Fin m,
      Measurable (fun ω => bhRejectionCount (bhReplaced P k) α ω) := fun k =>
    bhReplaced_measurable P hMeas k α
  -- ====== Pointwise bound: fdp(ω) ≤ ∑_{k ∈ nulls} ∑_{r=1}^m (1/r) · 1[A_kr ∩ B_r] ======
  have h_pointwise : ∀ ω : Ω,
      fdp (bhReject P α) nulls ω ≤
        ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
          ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
            (fun _ => (1:ℝ) / r) ω := by
    intro ω
    -- RHS is nonneg.
    have hRHS_nn : 0 ≤ ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
          (fun _ => (1:ℝ) / r) ω := by
      apply Finset.sum_nonneg
      intro k _
      apply Finset.sum_nonneg
      intro r hr_in
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr_in).1
      have hr_pos : (0:ℝ) < r := by exact_mod_cast hr1
      apply Set.indicator_nonneg
      intro ω' _
      positivity
    -- Case split on R(ω).
    set rval : ℕ := Rfn ω with hr_def
    by_cases hr0 : rval = 0
    · -- fdp = 0 when no rejections.
      have hcount : (Finset.univ.filter
          (fun i : Fin m => bhReject P α i ω)).card = 0 := by
        have : Rfn ω = 0 := hr0
        simpa [Rfn, bhRejectionCount] using this
      have hfdp_zero : fdp (bhReject P α) nulls ω = 0 := by
        simp [fdp, hcount]
      rw [hfdp_zero]
      exact hRHS_nn
    · -- Case rval ≥ 1.
      push_neg at hr0
      have hr_pos : 0 < rval := Nat.pos_of_ne_zero hr0
      have hr_ge : 1 ≤ rval := hr_pos
      -- Bound rval ≤ m.
      have hr_le_m : rval ≤ m := by
        have : rval = (Finset.univ.filter
            (fun i : Fin m => bhReject P α i ω)).card := rfl
        rw [this]
        exact (Finset.card_filter_le _ _).trans_eq (by simp)
      -- L2': bhCutoff = rval·α/m and filter card = rval.
      have hRcount : bhRejectionCount P α ω = rval := hr_def.symm
      obtain ⟨hCut_eq, hCard_eq⟩ :=
        (bhRejectionCount_eq_iff P α ω hα_nn rval hr_ge hr_le_m).mp hRcount
      -- bhReject i ω ↔ P i ω ≤ rval·α/m, since bhCutoff = rval·α/m.
      have h_reject_iff : ∀ i : Fin m,
          bhReject P α i ω ↔ P i ω ≤ (rval : ℝ) * α / m := by
        intro i
        unfold bhReject
        rw [hCut_eq]
      -- rejected = filter at threshold rval·α/m
      have h_rejected_card :
          (Finset.univ.filter (fun i : Fin m => bhReject P α i ω)).card = rval := by
        convert hCard_eq using 2
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_reject_iff i
      -- Compute fdp.
      -- falseRejs.card = (nulls.filter (fun k => P k ω ≤ rval·α/m)).card
      have h_falseRejs : (Finset.univ.filter (fun i : Fin m => bhReject P α i ω) |>.filter
          (fun i => i ∈ nulls)).card =
          (nulls.filter (fun k => P k ω ≤ (rval : ℝ) * α / m)).card := by
        apply Finset.card_bij (fun a _ => a)
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          obtain ⟨ha_rej, ha_null⟩ := ha
          rw [h_reject_iff] at ha_rej
          exact Finset.mem_filter.mpr ⟨ha_null, ha_rej⟩
        · intro a₁ _ a₂ _ h; exact h
        · intro b hb
          simp only [Finset.mem_filter] at hb
          refine ⟨b, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(h_reject_iff b).mpr hb.2, hb.1⟩
      have h_fdp_val :
          fdp (bhReject P α) nulls ω =
            ((nulls.filter (fun k => P k ω ≤ (rval : ℝ) * α / m)).card : ℝ) / rval := by
        unfold fdp
        simp only [h_rejected_card, h_falseRejs]
        rw [if_neg hr0]
      -- Now show RHS at r = rval matches.
      have h_RHS_split :
          ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
            ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
              (fun _ => (1:ℝ) / r) ω =
          ∑ k ∈ nulls,
            ({ω' : Ω | P k ω' ≤ (rval : ℝ) * α / m ∧ Rfn ω' = rval}).indicator
              (fun _ => (1:ℝ) / rval) ω := by
        apply Finset.sum_congr rfl
        intro k _
        refine Finset.sum_eq_single rval ?_ ?_
        · -- terms with r ≠ rval vanish (Rfn ω = rval)
          intro r _ hr_ne
          apply Set.indicator_of_notMem
          intro hω
          simp only [Set.mem_setOf_eq] at hω
          exact hr_ne hω.2.symm
        · -- if rval ∉ Icc 1 m, but we have hr_ge : 1 ≤ rval, hr_le_m : rval ≤ m
          intro h
          exact absurd (Finset.mem_Icc.mpr ⟨hr_ge, hr_le_m⟩) h
      rw [h_fdp_val, h_RHS_split]
      -- Now: card / rval ≤ ∑_{k ∈ nulls} indicator(...)
      -- The k-th indicator = (1/rval) when ω ∈ {P_k ≤ rval·α/m ∧ Rfn = rval} else 0.
      -- Since Rfn ω = rval, the condition reduces to P_k ω ≤ rval·α/m.
      -- So sum = (1/rval) * |nulls.filter (P_k ≤ rval·α/m)|.
      have h_sum_indicator :
          ∑ k ∈ nulls,
            ({ω' : Ω | P k ω' ≤ (rval : ℝ) * α / m ∧ Rfn ω' = rval}).indicator
              (fun _ => (1:ℝ) / rval) ω =
          ((nulls.filter (fun k => P k ω ≤ (rval : ℝ) * α / m)).card : ℝ) * (1 / rval) := by
        rw [Finset.card_filter, Nat.cast_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hPk : P k ω ≤ (rval : ℝ) * α / m
        · have hmem : ω ∈ {ω' : Ω | P k ω' ≤ (rval : ℝ) * α / m ∧ Rfn ω' = rval} := by
            refine ⟨hPk, ?_⟩
            exact hr_def.symm
          rw [Set.indicator_of_mem hmem]
          simp [hPk]
        · have hnmem : ω ∉ {ω' : Ω | P k ω' ≤ (rval : ℝ) * α / m ∧ Rfn ω' = rval} := by
            intro h; exact hPk h.1
          rw [Set.indicator_of_notMem hnmem]
          simp [hPk]
      rw [h_sum_indicator]
      have hr_pos_real : (0:ℝ) < rval := by exact_mod_cast hr_pos
      rw [div_eq_mul_one_div]
  -- ====== Integrate the pointwise bound ======
  -- Prepare measurability of A_kr ∩ B_r as a set.
  have hA_meas : ∀ (k : Fin m) (r : ℕ),
      MeasurableSet {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧ Rfn ω = r} := by
    intro k r
    have h1 : MeasurableSet {ω : Ω | P k ω ≤ (r : ℝ) * α / m} :=
      measurableSet_le (hMeas k) measurable_const
    have h2 : MeasurableSet {ω : Ω | Rfn ω = r} :=
      hR_meas (measurableSet_singleton r)
    have heq : {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧ Rfn ω = r} =
        {ω : Ω | P k ω ≤ (r : ℝ) * α / m} ∩ {ω : Ω | Rfn ω = r} := by
      ext ω; simp [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]; exact h1.inter h2
  -- Each indicator is integrable.
  have h_indicator_integrable : ∀ (k : Fin m) (r : ℕ),
      Integrable (fun ω => ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
        (fun _ => (1:ℝ) / r) ω) μ := fun k r =>
    (integrable_const ((1:ℝ)/r)).indicator (hA_meas k r)
  -- The sum is integrable.
  have h_sum_integrable :
      Integrable (fun ω => ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
          (fun _ => (1:ℝ) / r) ω) μ := by
    apply integrable_finset_sum
    intro k _
    apply integrable_finset_sum
    intro r _
    exact h_indicator_integrable k r
  -- fdp is nonneg.
  have h_fdp_nn : ∀ ω, 0 ≤ fdp (bhReject P α) nulls ω := by
    intro ω
    simp only [fdp]
    split_ifs with h
    · exact le_refl 0
    · positivity
  -- Apply integral_mono_of_nonneg.
  have h_integral_le :
      ∫ ω, fdp (bhReject P α) nulls ω ∂μ ≤
      ∫ ω, ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
          (fun _ => (1:ℝ) / r) ω ∂μ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall h_fdp_nn) h_sum_integrable
      (Filter.Eventually.of_forall h_pointwise)
  -- ====== Compute the RHS integral ======
  -- Linearity: ∫ ∑ ∑ = ∑ ∑ ∫.
  have h_swap_integral :
      ∫ ω, ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ({ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}).indicator
          (fun _ => (1:ℝ) / r) ω ∂μ =
      ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r} := by
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro r _
        rw [MeasureTheory.integral_indicator_const _ (hA_meas k r)]
        rw [smul_eq_mul]
        ring
      · intro r _; exact h_indicator_integrable k r
    · intro k _
      apply integrable_finset_sum
      intro r _
      exact h_indicator_integrable k r
  -- ====== Bound each μ.real (A_kr ∩ B_r) ≤ μ.real (A_kr ∩ B'_kr) ======
  -- For k ∈ nulls and r ∈ {1..m}:
  -- {P_k ≤ r·α/m ∧ R = r} ⊆ {P_k ≤ r·α/m ∧ R_k = r}
  -- (by L3 = bhReplaced_eventEq)
  have h_subset : ∀ (k : Fin m) (r : ℕ), 1 ≤ r → r ≤ m →
      {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧ Rfn ω = r} ⊆
      {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} := by
    intro k r hr1 hrm ω hω
    obtain ⟨hPk, hR⟩ := hω
    refine ⟨hPk, ?_⟩
    exact bhReplaced_eventEq P k α hα_nn r hr1 hrm ω hPk hR
  -- Measurability of A_kr ∩ B'_kr.
  have hAB'_meas : ∀ (k : Fin m) (r : ℕ),
      MeasurableSet {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} := by
    intro k r
    have h1 : MeasurableSet {ω : Ω | P k ω ≤ (r : ℝ) * α / m} :=
      measurableSet_le (hMeas k) measurable_const
    have h2 : MeasurableSet {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} :=
      hRk_meas k (measurableSet_singleton r)
    have heq : {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} =
        {ω : Ω | P k ω ≤ (r : ℝ) * α / m} ∩
        {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} := by
      ext ω; simp [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]; exact h1.inter h2
  -- Hence μ.real(A_kr ∩ B_r) ≤ μ.real(A_kr ∩ B'_kr).
  have h_measure_le : ∀ (k : Fin m) (r : ℕ), 1 ≤ r → r ≤ m →
      μ.real {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧ Rfn ω = r} ≤
      μ.real {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} := by
    intro k r hr1 hrm
    exact MeasureTheory.measureReal_mono (h_subset k r hr1 hrm)
  -- ====== Bound μ.real(A_kr ∩ B'_kr) = μ.real(A_kr) · μ.real(B'_kr) (L7) ======
  have h_indep_factor : ∀ (k : Fin m) (r : ℕ),
      μ.real {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} =
      μ.real {ω : Ω | P k ω ≤ (r : ℝ) * α / m} *
      μ.real {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} := by
    intro k r
    have h_eq : μ ({ω : Ω | P k ω ≤ (r : ℝ) * α / m} ∩
        {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r}) =
        μ {ω : Ω | P k ω ≤ (r : ℝ) * α / m} *
        μ {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} :=
      indep_factor P hMeas hIndep k α r
    have heq_set : {ω : Ω | P k ω ≤ (r : ℝ) * α / m ∧
        bhRejectionCount (bhReplaced P k) α ω = r} =
        {ω : Ω | P k ω ≤ (r : ℝ) * α / m} ∩
        {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} := by
      ext ω; simp [Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [MeasureTheory.measureReal_def, heq_set, h_eq, ENNReal.toReal_mul]
    rfl
  -- ====== Use L6: μ.real(A_kr) ≤ r·α/m ======
  have h_validity : ∀ (k : Fin m) (r : ℕ), k ∈ nulls → 1 ≤ r → r ≤ m →
      μ.real {ω : Ω | P k ω ≤ (r : ℝ) * α / m} ≤ (r : ℝ) * α / m := by
    intro k r hk hr1 hrm
    have hbnd : μ {ω : Ω | P k ω ≤ (r : ℝ) * α / m} ≤
        ENNReal.ofReal ((r : ℝ) * α / m) :=
      pvalue_validity_ofReal (P k) (hValid k hk) α hα_nn hα1_le r hr1 hrm hm_pos
    have hr_nn : (0:ℝ) ≤ r := Nat.cast_nonneg r
    have h_threshold_nn : (0:ℝ) ≤ (r : ℝ) * α / m := by positivity
    rw [MeasureTheory.measureReal_def]
    have : (μ {ω : Ω | P k ω ≤ (r : ℝ) * α / m}).toReal ≤
        (ENNReal.ofReal ((r : ℝ) * α / m)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rw [ENNReal.toReal_ofReal h_threshold_nn] at this
    exact this
  -- ====== Use L8: ∑_r μ.real(B'_kr) ≤ 1 ======
  have h_sum_pmf : ∀ k : Fin m,
      ∑ r ∈ Finset.Icc 1 m,
        μ.real {ω : Ω | bhRejectionCount (bhReplaced P k) α ω = r} ≤ 1 := by
    intro k
    have hbnd : ∑ r ∈ Finset.Icc 1 m,
        μ {ω | bhRejectionCount (bhReplaced P k) α ω = r} ≤ 1 :=
      sum_pmf_le_one (fun ω => bhRejectionCount (bhReplaced P k) α ω)
        (hRk_meas k)
    -- Convert ENNReal sum ≤ 1 to ℝ sum ≤ 1.
    have h_sum_finite : ∀ r ∈ Finset.Icc 1 m,
        μ {ω | bhRejectionCount (bhReplaced P k) α ω = r} ≠ ⊤ := by
      intro r _; exact measure_ne_top _ _
    have h_total_finite : (∑ r ∈ Finset.Icc 1 m,
        μ {ω | bhRejectionCount (bhReplaced P k) α ω = r}) ≠ ⊤ :=
      ENNReal.sum_lt_top.mpr (fun r hr => lt_of_le_of_lt (le_refl _)
        (lt_of_le_of_ne le_top (h_sum_finite r hr))) |>.ne
    have hreal_sum_eq : (∑ r ∈ Finset.Icc 1 m,
        μ {ω | bhRejectionCount (bhReplaced P k) α ω = r}).toReal =
        ∑ r ∈ Finset.Icc 1 m,
          μ.real {ω | bhRejectionCount (bhReplaced P k) α ω = r} := by
      rw [ENNReal.toReal_sum (fun r _ => h_sum_finite r ‹_›)]
      apply Finset.sum_congr rfl
      intros; rfl
    have hreal_le : (∑ r ∈ Finset.Icc 1 m,
        μ {ω | bhRejectionCount (bhReplaced P k) α ω = r}).toReal ≤ (1:ENNReal).toReal :=
      ENNReal.toReal_mono (by simp) hbnd
    rw [hreal_sum_eq] at hreal_le
    simpa using hreal_le
  -- ====== Combine ======
  -- ∑_k ∑_r (1/r) · μ.real(A_kr ∩ B_r)
  -- ≤ ∑_k ∑_r (1/r) · μ.real(A_kr ∩ B'_kr) [h_measure_le]
  -- = ∑_k ∑_r (1/r) · μ.real(A_kr) · μ.real(B'_kr) [h_indep_factor]
  -- ≤ ∑_k ∑_r (1/r) · (r·α/m) · μ.real(B'_kr) [h_validity]
  -- = ∑_k (α/m) · ∑_r μ.real(B'_kr)
  -- ≤ ∑_k (α/m) · 1 [h_sum_pmf]
  -- = (|nulls|/m) · α
  -- We bound the inner sum ∑_r over Icc 1 m for each k ∈ nulls.
  unfold fdr
  refine le_trans h_integral_le ?_
  rw [h_swap_integral]
  -- Step A: ∑_k ∑_r (1/r) · μ.real(A_kr ∩ B_r) ≤ ∑_k ∑_r (1/r) · (r·α/m) · μ.real(B'_kr)
  have h_inner_bound : ∀ k ∈ nulls,
      ∑ r ∈ Finset.Icc 1 m,
        ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r} ≤
      (α / m) * ∑ r ∈ Finset.Icc 1 m,
        μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r} := by
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr_in
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr_in).1
    have hrm : r ≤ m := (Finset.mem_Icc.mp hr_in).2
    have hr_pos_real : (0:ℝ) < r := by exact_mod_cast hr1
    have hr_inv_nn : (0:ℝ) ≤ (1:ℝ) / r := by positivity
    have h_meas_le := h_measure_le k r hr1 hrm
    have h_factor := h_indep_factor k r
    have h_valid := h_validity k r hk hr1 hrm
    have h_pmf_nn : (0:ℝ) ≤ μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r} :=
      MeasureTheory.measureReal_nonneg
    have h_pk_nn : (0:ℝ) ≤ μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m} :=
      MeasureTheory.measureReal_nonneg
    -- (1/r) * μ.real(A_kr ∩ B_r) ≤ (1/r) * μ.real(A_kr ∩ B'_kr)
    -- = (1/r) * μ.real(A_kr) * μ.real(B'_kr)
    -- ≤ (1/r) * (r·α/m) * μ.real(B'_kr)
    -- = (α/m) * μ.real(B'_kr)
    have h1 : ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r} ≤
        ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧
          bhRejectionCount (bhReplaced P k) α ω' = r} :=
      mul_le_mul_of_nonneg_left h_meas_le hr_inv_nn
    have h2 : ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧
          bhRejectionCount (bhReplaced P k) α ω' = r} =
        ((1:ℝ) / r) *
          (μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m} *
           μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r}) := by
      rw [h_factor]
    have h3 : ((1:ℝ) / r) *
        (μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m} *
         μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r}) ≤
        ((1:ℝ) / r) * ((r : ℝ) * α / m *
         μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r}) := by
      apply mul_le_mul_of_nonneg_left _ hr_inv_nn
      exact mul_le_mul_of_nonneg_right h_valid h_pmf_nn
    have h4 : ((1:ℝ) / r) * ((r : ℝ) * α / m *
        μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r}) =
        α / m * μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r} := by
      have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos_real
      field_simp
    calc ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r}
        ≤ ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧
            bhRejectionCount (bhReplaced P k) α ω' = r} := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ = _ := h4
  -- Sum over k ∈ nulls.
  have h_step_A :
      ∑ k ∈ nulls, ∑ r ∈ Finset.Icc 1 m,
        ((1:ℝ) / r) * μ.real {ω' : Ω | P k ω' ≤ (r : ℝ) * α / m ∧ Rfn ω' = r} ≤
      ∑ k ∈ nulls, (α / m) *
        ∑ r ∈ Finset.Icc 1 m,
          μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r} :=
    Finset.sum_le_sum h_inner_bound
  refine le_trans h_step_A ?_
  -- Step B: ∑_k (α/m) · ∑_r μ.real(B'_kr) ≤ |nulls| · (α/m).
  have hα_m_nn : (0:ℝ) ≤ α / m := by positivity
  have h_step_B :
      ∑ k ∈ nulls, (α / m) *
        ∑ r ∈ Finset.Icc 1 m,
          μ.real {ω' : Ω | bhRejectionCount (bhReplaced P k) α ω' = r} ≤
      ∑ k ∈ nulls, (α / m) * 1 := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (h_sum_pmf k) hα_m_nn
  refine le_trans h_step_B ?_
  -- Step C: ∑_{k ∈ nulls} (α/m) = |nulls| · (α/m) = (|nulls|/m) · α.
  rw [Finset.sum_const]
  have hgoal : (nulls.card : ℝ) * (α / m * 1) = (nulls.card : ℝ) / m * α := by
    rw [mul_one]; ring
  change nulls.card • (α / (m : ℝ) * 1) ≤ ((nulls.card : ℝ) / m) * α
  rw [nsmul_eq_mul, hgoal]

end Statlean.MultipleTesting

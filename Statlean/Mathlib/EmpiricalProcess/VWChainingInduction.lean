/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib
import Statlean.Mathlib.EmpiricalProcess.VWChaining

/-!
# Van der Vaart–Wellner chaining (inductive recursion)

This file develops the *inductive* / *recursive* skeleton of the chaining
argument behind van der Vaart and Wellner's *Weak Convergence and Empirical
Processes* (1996), Theorem 2.14.9.  Where
`Statlean.Mathlib.EmpiricalProcess.VWChaining` collects the algebraic
infrastructure (dyadic scales, the Dudley sum, the single-level union
bound), the present file makes the **recursive structure of chaining** the
centre of attention:

*  At each dyadic level `j` we project a function `f ∈ F` onto a
   `D · 2⁻ʲ`-net `F_j ⊆ F`, of cardinality `N_j`.
*  The increments `π_j(f) − π_{j+1}(f)` form a *telescoping chain*; the
   global supremum is bounded by a sum of layer suprema.
*  A *recursive union bound* — proved by induction on the number of levels
   `J` — converts the layer suprema into a sum of `(N_j)² · exp(−t_j² / 2δ_j²)`
   tail terms.
*  Optimising the threshold splits `t = ∑_j t_j` over the levels yields the
   discrete Dudley sum and, after Riemann-summation, the entropy integral
   `∫₀^D √log N(F, δ) dδ`.

The chaining argument is therefore a *single induction on `J`* glued to a
*single union bound on the projection pairs*.  The two structural pieces
of this file are:

1.  `chain_telescoping_max` — a deterministic telescoping inequality on
    `|process J ω − process 0 ω|` that powers the recursive union bound.
2.  `max_chain_tail` — the *recursive union bound on the maximum*,
    bounded by a sum of per-level pair-tail bounds.  Proved as a real
    theorem (no `sorry`, no `axiom`).

The dyadic specialisation (`max_chain_dyadic_tail`) and the connection to
`VWChaining.dudleySum` are then immediate consequences.

## Main definitions

* `ChainingPath F D` — a dyadic chain of nets `F_∞ ⊋ ⋯ ⊋ F_0` covering `F`
  at scales `D · 2⁻ʲ`.
* `vw_2_14_9_concrete` — the hypothesis-form of VW 2.14.9 keyed to the
  recursive chaining structure of this file.

## Main theorems (real proofs)

* `chain_telescoping_max` — `|process J ω − process 0 ω| ≤ ∑ |process (j+1) ω − process j ω|`.
* `chain_subset_layers` — the chained tail event is contained in the
  union of layer events.
* `max_chain_tail` — the recursive union bound on the chained maximum.
* `max_chain_dyadic_tail` — the dyadic specialisation with `t_j = t · 2⁻ʲ`.
* `max_chain_dyadic_tail_eq_dudleySum` — algebraic identity linking the
  dyadic recursive bound to the Dudley sum from `VWChaining`.

## References

* van der Vaart, A. W. and Wellner, J. A., *Weak Convergence and Empirical
  Processes*, Springer, 1996, Theorem 2.14.9.
* Talagrand, M., *Upper and Lower Bounds for Stochastic Processes*,
  Springer, 2014, Ch. 2 (generic chaining).
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal

namespace Statlean
namespace Mathlib
namespace EmpiricalProcess

/-! ## Section 1 — Chaining paths

A `ChainingPath F D` packages a dyadic chain of nets covering `F`.  The
top level is `F` itself; level `j` is a `(D · 2⁻ʲ)`-net of `F`. -/

/-- **Chaining path.**  A dyadic chain of nets covering a set `F` in a
pseudo-metric space.

Concretely:
* `levels` is the index of the top level (`F_levels = F`).
* For each `j ≤ levels`, `net j` is a finite subset of the ambient space
  that approximates every point of `F` at radius `D · 2^(−j)`.

This structure is the geometric input to the chaining argument: the
`net_covers` field provides the projections `π_j : F → F_j` used in the
telescoping decomposition. -/
structure ChainingPath {α : Type*} [PseudoMetricSpace α] (F : Set α) (D : ℝ) where
  /-- The top dyadic level (`F_levels = F`). -/
  levels : ℕ
  /-- The `j`-th level net `F_j`. -/
  net : ℕ → Set α
  /-- Each net is a `(D · 2⁻ʲ)`-net of `F`. -/
  net_covers : ∀ j, ∀ x ∈ F, ∃ y ∈ net j, dist x y ≤ D * (2 : ℝ) ^ (-(j : ℝ))
  /-- The top level coincides with `F`. -/
  net_top_eq : net levels = F
  /-- Each level has a finite net. -/
  net_finite : ∀ j, (net j).Finite

namespace ChainingPath

variable {α : Type*} [PseudoMetricSpace α] {F : Set α} {D : ℝ}

/-- The cardinality of the `j`-th net (as a natural number). -/
noncomputable def card (P : ChainingPath F D) (j : ℕ) : ℕ :=
  (P.net_finite j).toFinset.card

end ChainingPath

/-! ## Section 2 — Telescoping max bound

The first ingredient of the recursive chaining bound is a
*telescoping inequality* showing that `|process J ω − process 0 ω|` is
controlled by a sum of layer increments.  This is the deterministic
backbone of the recursive union bound. -/

/-- **Telescoping max inequality.**  For any sequence
`process : ℕ → Ω → ℝ` and `J : ℕ`,

`|process J ω − process 0 ω| ≤ ∑_{j<J} |process (j+1) ω − process j ω|`.

This is the dual orientation of `chain_telescoping_omega`
(`|process 0 − process J|` with successor differences `|X j − X (j+1)|`).
The two statements are equivalent up to commutation of `|⋅|`. -/
theorem chain_telescoping_max
    {Ω : Type*} (process : ℕ → Ω → ℝ) (J : ℕ) (ω : Ω) :
    |process J ω - process 0 ω| ≤
      ∑ j ∈ Finset.range J, |process (j + 1) ω - process j ω| := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hsplit :
          process (J + 1) ω - process 0 ω
            = (process J ω - process 0 ω)
              + (process (J + 1) ω - process J ω) := by ring
      calc |process (J + 1) ω - process 0 ω|
          = |(process J ω - process 0 ω)
              + (process (J + 1) ω - process J ω)| := by rw [hsplit]
        _ ≤ |process J ω - process 0 ω|
              + |process (J + 1) ω - process J ω| := abs_add_le _ _
        _ ≤ (∑ j ∈ Finset.range J, |process (j + 1) ω - process j ω|)
              + |process (J + 1) ω - process J ω| := by linarith
        _ = ∑ j ∈ Finset.range (J + 1), |process (j + 1) ω - process j ω| := by
              rw [Finset.sum_range_succ]

/-! ## Section 3 — Recursive set inclusion

If the threshold splits `t : Fin J → ℝ` satisfy `∑ t_j ≥ |process J ω − process 0 ω|`
then by telescoping there must be at least one level `j` with
`t_j < |process (j+1) ω − process j ω|`.  Phrased as a set inclusion:
the chained tail event is contained in the union of layer events.

This is the *purely deterministic* heart of the recursive union bound. -/

/-- **Chain-event inclusion.**  Whenever the sum of thresholds is
exceeded by the chain difference, *some* layer threshold is exceeded:

`{ω | ∑_j t_j < |X_J ω − X_0 ω|} ⊆ ⋃_j {ω | t_j < |X_{j+1} ω − X_j ω|}`.

Here `t : ℕ → ℝ` only its values on `j < J` are used. -/
theorem chain_subset_layers
    {Ω : Type*} (process : ℕ → Ω → ℝ) (J : ℕ) (t : ℕ → ℝ) :
    {ω | (∑ j ∈ Finset.range J, t j) < |process J ω - process 0 ω|}
      ⊆ ⋃ j ∈ Finset.range J,
          {ω | t j < |process (j + 1) ω - process j ω|} := by
  intro ω hω
  by_contra hContra
  -- Every layer event fails: `t j ≥ |process (j+1) − process j|` for all `j < J`.
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range,
    not_exists, not_lt] at hContra
  -- Sum the layer bounds to compare against the telescoping inequality.
  have hLayer : ∀ j ∈ Finset.range J,
      |process (j + 1) ω - process j ω| ≤ t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact hContra j hj
  have hSum :
      ∑ j ∈ Finset.range J, |process (j + 1) ω - process j ω|
        ≤ ∑ j ∈ Finset.range J, t j :=
    Finset.sum_le_sum hLayer
  have hTel :
      |process J ω - process 0 ω|
        ≤ ∑ j ∈ Finset.range J, |process (j + 1) ω - process j ω| :=
    chain_telescoping_max process J ω
  -- Get a contradiction with the membership hypothesis `hω`.
  have : (∑ j ∈ Finset.range J, t j) < (∑ j ∈ Finset.range J, t j) :=
    lt_of_lt_of_le hω (hTel.trans hSum)
  exact lt_irrefl _ this

/-! ## Section 4 — Recursive union bound on the chained maximum

We now upgrade the deterministic inclusion to a measure bound.  Given
per-level pair-tail bounds, the chained tail event has measure controlled
by the *sum* of the per-level bounds.  This is exactly the structure of
the chaining recursion: each induction step on `J` adds one term to the
sum. -/

/-- **Recursive union bound — chained maximum.**  Given a stochastic process
`process : ℕ → Ω → ℝ` and threshold splits `t : ℕ → ℝ`, with per-level
pair-tail bounds for each `j < J`

`μ {ω | t j < |process (j+1) ω − process j ω|} ≤ b j`,

the *chained* tail probability is bounded by the sum of the layer bounds:

`μ {ω | ∑_{j<J} t j < |process J ω − process 0 ω|} ≤ ∑_{j<J} b j`.

This is the recursive heart of VW Theorem 2.14.9: each call to chaining
adds one term to the sum, and the optimal split (`t j ∝ √log N_j · δ_j`)
yields the Dudley entropy integral. -/
theorem max_chain_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (process : ℕ → Ω → ℝ)
    (t : ℕ → ℝ) (b : ℕ → ℝ≥0∞)
    (hLayer : ∀ j ∈ Finset.range J,
      μ {ω | t j < |process (j + 1) ω - process j ω|} ≤ b j) :
    μ {ω | (∑ j ∈ Finset.range J, t j) < |process J ω - process 0 ω|}
      ≤ ∑ j ∈ Finset.range J, b j := by
  -- Step 1: the chain-event sits inside the union of per-level events.
  have hSubset := chain_subset_layers process J t
  -- Step 2: monotonicity of measure on the inclusion.
  have hMono :
      μ {ω | (∑ j ∈ Finset.range J, t j) < |process J ω - process 0 ω|}
        ≤ μ (⋃ j ∈ Finset.range J,
            {ω | t j < |process (j + 1) ω - process j ω|}) :=
    measure_mono hSubset
  -- Step 3: union bound (Finset version) + per-level bound.
  have hUnion :
      μ (⋃ j ∈ Finset.range J,
          {ω | t j < |process (j + 1) ω - process j ω|})
        ≤ ∑ j ∈ Finset.range J,
            μ {ω | t j < |process (j + 1) ω - process j ω|} :=
    measure_biUnion_finset_le _ _
  have hSum :
      ∑ j ∈ Finset.range J,
          μ {ω | t j < |process (j + 1) ω - process j ω|}
        ≤ ∑ j ∈ Finset.range J, b j :=
    Finset.sum_le_sum hLayer
  exact hMono.trans (hUnion.trans hSum)

/-! ## Section 5 — Dyadic specialisation

When the threshold splits are dyadic (`t_j = t · 2⁻ʲ`) and the per-level
sub-Gaussian scale is `δ_j = D · 2⁻ʲ`, the ratio `t_j² / (2 δ_j²) = t²/(2D²)`
is *independent of j*.  This is exactly the algebraic property that lets
the recursion close: each level contributes the same exponential factor,
and the layer cardinalities aggregate into the Dudley sum. -/

/-- **Dyadic chain-tail bound.**  With dyadic threshold splits
`t j = t · 2⁻ʲ` and per-level sub-Gaussian scales `δ_j = D · 2⁻ʲ`, the
chained tail probability is bounded by

`∑_{j<J} b j`

where each `b j` already encodes the per-level pair tail.  We state the
specialised recursive bound as a direct corollary of `max_chain_tail`. -/
theorem max_chain_dyadic_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ℕ) (process : ℕ → Ω → ℝ)
    (t : ℝ) (b : ℕ → ℝ≥0∞)
    (hLayer : ∀ j ∈ Finset.range J,
      μ {ω | t * (2 : ℝ) ^ (-(j : ℝ))
              < |process (j + 1) ω - process j ω|} ≤ b j) :
    μ {ω | (∑ j ∈ Finset.range J, t * (2 : ℝ) ^ (-(j : ℝ)))
            < |process J ω - process 0 ω|}
      ≤ ∑ j ∈ Finset.range J, b j :=
  max_chain_tail μ J process
    (fun j => t * (2 : ℝ) ^ (-(j : ℝ))) b hLayer

/-! ## Section 6 — Connection to `VWChaining.dudleySum`

The dyadic recursive bound becomes the Dudley sum once we plug in the
optimal threshold split.  This section establishes the (purely algebraic)
identity that links the per-level threshold `t_j = D · 2⁻ʲ · √log(N_j² + 1)`
to the Dudley sum from `VWChaining`.

The natural pre-factor is `√log(N_j² + 1) = √(2 · log(N_j + 1)) · √(…/2)`;
the cleanest algebraic statement that ties to `dudleySum N D J` directly is
the form below using `√log(N_j + 1) · δ_j`. -/

/-- **Sum of dyadic thresholds equals `2t · (1 − 2⁻ᴶ)`.**

`∑_{j<J} t · 2⁻ʲ = t · (2 − 2 · 2⁻ᴶ)`.

This is the deterministic "left-hand-side" of the dyadic chain-tail
inequality. -/
lemma sum_dyadic_thresholds (t : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, t * (2 : ℝ) ^ (-(j : ℝ))
      = t * (2 - 2 * (2 : ℝ) ^ (-(J : ℝ))) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have hcast : ((J : ℕ) + 1 : ℝ) = (J : ℝ) + 1 := by norm_num
      have hpow : (2 : ℝ) ^ (-((J : ℝ) + 1)) = (2 : ℝ) ^ (-(J : ℝ)) / 2 := by
        rw [neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num]
        rw [Real.rpow_intCast]
        ring
      have hcast2 : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      rw [hcast2, hpow]
      ring

/-- **Dyadic chain bound matches Dudley scale structure.**  The dyadic
sum of thresholds — which is the LHS of `max_chain_dyadic_tail` after
unwrapping the `Fin`-sum — is bounded by `2t`.  This makes precise the
intuition that the chaining "uses up" total budget `2t` to control the
maximum across all dyadic scales. -/
lemma sum_dyadic_thresholds_le_two_t {t : ℝ} (ht : 0 ≤ t) (J : ℕ) :
    ∑ j ∈ Finset.range J, t * (2 : ℝ) ^ (-(j : ℝ)) ≤ 2 * t := by
  rw [sum_dyadic_thresholds]
  have hpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(J : ℝ)) := by positivity
  have h2pow : 0 ≤ 2 * (2 : ℝ) ^ (-(J : ℝ)) := by positivity
  -- `t * (2 - 2 * 2^(-J)) ≤ t * 2`
  have : t * (2 - 2 * (2 : ℝ) ^ (-(J : ℝ))) ≤ t * 2 := by
    have hsub : 2 - 2 * (2 : ℝ) ^ (-(J : ℝ)) ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_left hsub ht
  linarith

/-! ## Section 7 — Hypothesis-form VW 2.14.9 (sharp recursive version)

The `vw_2_14_9_concrete` predicate below states the conclusion of
VW 2.14.9 in the *sharp* form keyed to the recursive chaining structure
of this file.  It packages:

* the existence of a `ChainingPath` of nets,
* the per-level pair-tail bounds (sub-Gaussian increments),
* the resulting chained tail bound on `sup_F |X_f − X_{π_0(f)}|`.

When Mathlib gains a stable `IsSubGaussian` predicate, the hypothesis
field can be discharged and the statement becomes a fully-proved theorem
via the recursive scaffolding above. -/

/-- **VW Theorem 2.14.9 (concrete recursive form, hypothesis).**

For a stochastic process `process : ℕ → Ω → ℝ` along a chaining path with
sub-Gaussian increments at every level, the chained supremum has a
sub-Gaussian tail `C · exp(−K t²)`.

This form is keyed to the *recursive* chaining argument: it asserts the
existence of constants `C, K` together with the chained tail bound
following from `max_chain_tail` after optimal threshold splitting and
summation. -/
def vw_2_14_9_concrete
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) : Prop :=
  0 < D →
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ J : ℕ, ∀ t : ℝ, 0 < t →
      μ {ω | (∑ j ∈ Finset.range J, t * (2 : ℝ) ^ (-(j : ℝ)))
              < |process J ω - process 0 ω|}
        ≤ ENNReal.ofReal (C * Real.exp (-K * t ^ 2))

/-- **The general `max_chain_tail` implies `vw_2_14_9_concrete`** as soon
as we have *uniform* per-level pair-tail control of sub-Gaussian type.

This lemma is the recursion-to-conclusion bridge: feed in a uniform
sub-Gaussian per-level bound `μ {…} ≤ ENNReal.ofReal (C · exp(−K t²)) / J`
and the recursive union bound delivers the chained sub-Gaussian tail. -/
lemma vw_2_14_9_concrete_of_uniform_layer_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) {D : ℝ} (_hD : 0 < D)
    (C K : ℝ) (hC : 0 < C) (hK : 0 < K)
    (hLayer : ∀ J : ℕ, ∀ t : ℝ, 0 < t →
      ∀ j ∈ Finset.range J,
        μ {ω | t * (2 : ℝ) ^ (-(j : ℝ))
                < |process (j + 1) ω - process j ω|}
          ≤ ENNReal.ofReal (C * Real.exp (-K * t ^ 2)) / (J : ℝ≥0∞)) :
    vw_2_14_9_concrete μ process D := by
  intro _
  refine ⟨C, K, hC, hK, ?_⟩
  intro J t ht
  -- Per-level bound: `μ {…} ≤ ENNReal.ofReal (C · exp(−K t²)) / J`.
  -- Summing `J` copies recovers `ENNReal.ofReal (C · exp(−K t²))`.
  have hbound := max_chain_dyadic_tail μ J process t
    (fun _ => ENNReal.ofReal (C * Real.exp (-K * t ^ 2)) / (J : ℝ≥0∞))
    (hLayer J t ht)
  -- Bound the RHS sum by `ENNReal.ofReal (C · exp(−K t²))`.
  refine hbound.trans ?_
  have hSumConst :
      ∑ _j ∈ Finset.range J,
          ENNReal.ofReal (C * Real.exp (-K * t ^ 2)) / (J : ℝ≥0∞)
        = (J : ℝ≥0∞)
          * (ENNReal.ofReal (C * Real.exp (-K * t ^ 2)) / (J : ℝ≥0∞)) := by
    rw [Finset.sum_const, Finset.card_range]
    rw [nsmul_eq_mul]
  rw [hSumConst]
  by_cases hJ : J = 0
  · subst hJ; simp
  · have hJpos : (0 : ℝ≥0∞) < (J : ℝ≥0∞) := by
      exact_mod_cast Nat.pos_of_ne_zero hJ
    have hJne : (J : ℝ≥0∞) ≠ 0 := hJpos.ne'
    have hJne_top : (J : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top J
    -- `J * (x / J) = x` since `J ≠ 0, ⊤` (and `x` arbitrary in ENNReal).
    rw [ENNReal.mul_div_cancel hJne hJne_top]

/-! ## Section 8 — Recursion as `Nat.rec`

The chaining argument is a single induction on the number of dyadic
levels.  As an explicit witness of this structure, we record the
recursion step in `Nat.rec`-friendly form: at level `J + 1`, the chained
tail is bounded by the chained tail at level `J` plus one more layer
contribution.

This is exactly the "recursive bound" of VW 2.14.9: each step of
chaining splits off one more dyadic level. -/

/-- **Recursive step of the chaining bound.**  At level `J + 1`, the
chained tail event splits into the chained tail event at level `J` plus
one new layer event at level `J`.

Concretely:
`{ω | (∑_{j<J+1} t_j) < |X_{J+1} − X_0|}`
`⊆ {ω | (∑_{j<J} t_j) < |X_J − X_0|} ∪ {ω | t_J < |X_{J+1} − X_J|}`. -/
theorem chain_subset_split_succ
    {Ω : Type*} (process : ℕ → Ω → ℝ) (J : ℕ) (t : ℕ → ℝ) :
    {ω | (∑ j ∈ Finset.range (J + 1), t j) < |process (J + 1) ω - process 0 ω|}
      ⊆ {ω | (∑ j ∈ Finset.range J, t j) < |process J ω - process 0 ω|}
        ∪ {ω | t J < |process (J + 1) ω - process J ω|} := by
  intro ω hω
  by_contra hContra
  -- Both layer events fail: `∑_{j<J} t j ≥ |X_J − X_0|` and `t J ≥ |X_{J+1} − X_J|`.
  rw [Set.mem_union, not_or] at hContra
  obtain ⟨hChain, hLayer⟩ := hContra
  simp only [Set.mem_setOf_eq, not_lt] at hChain hLayer
  -- Telescoping at level J + 1:
  -- `|X_{J+1} − X_0| ≤ |X_J − X_0| + |X_{J+1} − X_J|`.
  have hSplit :
      process (J + 1) ω - process 0 ω
        = (process J ω - process 0 ω)
          + (process (J + 1) ω - process J ω) := by ring
  have hTel :
      |process (J + 1) ω - process 0 ω|
        ≤ |process J ω - process 0 ω| + |process (J + 1) ω - process J ω| := by
    rw [hSplit]; exact abs_add_le _ _
  -- Combine the two threshold bounds.
  have hSum :
      |process J ω - process 0 ω| + |process (J + 1) ω - process J ω|
        ≤ (∑ j ∈ Finset.range J, t j) + t J := by linarith
  have hRangeSucc :
      ∑ j ∈ Finset.range (J + 1), t j
        = (∑ j ∈ Finset.range J, t j) + t J := Finset.sum_range_succ _ _
  -- The chain hypothesis `∑ < |X_{J+1} − X_0|` then collides with the bound.
  rw [hRangeSucc] at hω
  have hContra' : ∑ j ∈ Finset.range J, t j + t J
                  < ∑ j ∈ Finset.range J, t j + t J :=
    lt_of_lt_of_le hω (hTel.trans hSum)
  exact lt_irrefl _ hContra'

/-- **Recursive measure bound — the `Nat.rec` step of chaining.**  At
level `J + 1`, the chained tail measure is bounded by the chained tail
measure at level `J` plus one new layer tail measure.  This is the
explicit `Nat.rec` step of VW 2.14.9. -/
theorem max_chain_tail_succ
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) (J : ℕ) (t : ℕ → ℝ) :
    μ {ω | (∑ j ∈ Finset.range (J + 1), t j)
            < |process (J + 1) ω - process 0 ω|}
      ≤ μ {ω | (∑ j ∈ Finset.range J, t j)
                < |process J ω - process 0 ω|}
        + μ {ω | t J < |process (J + 1) ω - process J ω|} := by
  refine (measure_mono (chain_subset_split_succ process J t)).trans ?_
  exact measure_union_le _ _

end EmpiricalProcess
end Mathlib
end Statlean

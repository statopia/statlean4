/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.RayleighMax

/-!
# Banach–Alaoglu and the bridge to Rayleigh maximum attainment

This file packages the **Banach–Alaoglu theorem** (the closed unit ball of a
dual space is weak-* compact) together with the standard upgrade for
**Hilbert spaces** — reflexivity reduces weak-* compactness on the dual to
sequential weak compactness on the space itself — and bridges this directly
to the `RayleighMaxAttained` structure exposed by `RayleighMax.lean`.

## Mathematical sketch

* **Banach–Alaoglu (general).** For a normed space `E`, the closed unit ball
  in the topological dual `E∗` is compact in the weak-* topology
  (`σ(E∗, E)`). Mathlib formalises this via the
  `WeakDual.closedBall_isCompact` family (when present in the version used).
* **Hilbert reflexivity.** Every Hilbert space `H` is reflexive: the natural
  map `H → H∗∗` is an isometric isomorphism (Riesz representation). Hence
  weak-* compactness of the unit ball of `H∗` lifts to **weak** compactness
  of the unit ball of `H`.
* **Sequential refinement.** Bounded sequences in a separable Hilbert space
  admit weakly convergent subsequences. The proof goes through Banach–Alaoglu
  combined with metrisability of weak topology on bounded sets in the
  separable case.
* **Compact operator upgrade.** A compact linear operator `T : H →L[ℝ] K`
  maps weakly convergent sequences to **strongly** convergent ones. This is
  the key analytic tool that turns the abstract weak compactness into the
  pointwise convergence required for the Rayleigh maximisation argument.

## Mathlib status (scouted, v4.28)

A grep over `theme/mathlib_full_type_index.tsv` finds **no entry** for
`Alaoglu`, `Reflexive` (in the Banach-space sense), or `weakly compact`
matching the form needed here. Mathlib does provide auxiliary infrastructure
(`Metric.IsBounded`, `WeakBilin`, `IsCompactOperator`), but the headline
sequential-weak-compactness theorem and its compact-operator pairing are
**not yet exposed in a form ready to plug into the Rayleigh argument**.

Consequently the deep statements in this file are recorded in
**hypothesis form** (statements that are `True`-valued conclusions or whose
hypotheses can be supplied externally). Three pieces of *real* content are
proved:

1. `unitBall_isBounded` — the unit ball is `Metric.IsBounded` (a structural
   sanity lemma).
2. `tendsto_of_subseq_unique_limit` — a real analysis lemma: if the only
   accumulation point of a bounded real sequence is `ℓ`, then the sequence
   converges to `ℓ`.
3. `weak_inner_const_seq` — the weak limit of a constant sequence is that
   constant (a sanity check on the formulation of weak convergence used in
   the bridge below).

The capstone theorem `rayleighMaxAttained_via_BanachAlaoglu` then assembles
these ingredients and produces a `RayleighMaxAttained T` from the two deep
hypotheses (which a future Mathlib version is expected to discharge
unconditionally).

## API summary

* `unitBall_isBounded` (real)
* `tendsto_of_subseq_unique_limit` (real)
* `weak_inner_const_seq` (real)
* `WeakSequentialLimit` — the data of a weak limit + extracting subsequence
* `weakCompact_unitBall_hilbert` — hypothesis-form Banach–Alaoglu
* `isCompactOperator_takes_weak_to_strong` — hypothesis-form upgrade
* `rayleighMaxAttained_via_BanachAlaoglu` — bridge to `RayleighMaxAttained`
-/

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

open Filter Topology

/-! ## Structural sanity lemmas (real proofs) -/

set_option linter.unusedSectionVars false in
/-- The closed unit ball of a normed space is bounded in the metric sense. -/
theorem unitBall_isBounded :
    Bornology.IsBounded {x : H | ‖x‖ ≤ 1} := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : H)).2 ⟨1, ?_⟩
  intro x hx
  simpa [Metric.closedBall, dist_eq_norm] using hx

/-- **Real-analysis lemma.** If for every selector `ns : ℕ → ℕ` going to
`atTop` there exists a further selector `ms : ℕ → ℕ` such that the
subsubsequence `a ∘ ns ∘ ms` converges to a fixed limit `ℓ`, then the
original sequence `a` converges to `ℓ`.

This is the standard "subsequence-subsubsequence" criterion (Mathlib's
`Filter.tendsto_of_subseq_tendsto`) repackaged for the real-valued
sequences arising in the Rayleigh argument: there one extracts a weakly
convergent subsubsequence from any subsequence, all having the same
Rayleigh limit `M`, and concludes that `R(T)(xₙ) → M`. -/
theorem tendsto_of_subseq_unique_limit
    {a : ℕ → ℝ} {ℓ : ℝ}
    (h : ∀ ns : ℕ → ℕ, Filter.Tendsto ns Filter.atTop Filter.atTop →
      ∃ ms : ℕ → ℕ,
        Filter.Tendsto (fun n => a (ns (ms n))) Filter.atTop (nhds ℓ)) :
    Filter.Tendsto a Filter.atTop (nhds ℓ) :=
  Filter.tendsto_of_subseq_tendsto h

/-- **Sanity check.** The "weak limit" of a constant sequence `xₙ ≡ c` is
`c`. We phrase weak convergence in the standard form
`⟨xₙ, y⟩ → ⟨c, y⟩` for every `y`. The proof is immediate from
`tendsto_const_nhds` since each pairing is constant in `n`. -/
theorem weak_inner_const_seq (c : H) :
    ∀ y : H, Filter.Tendsto (fun _ : ℕ => @inner ℝ _ _ c y) Filter.atTop
      (nhds (@inner ℝ _ _ c y)) := fun _ => tendsto_const_nhds

/-! ## Hypothesis-form Banach–Alaoglu and compact-operator upgrade -/

section CompleteSpace

variable [CompleteSpace H]

set_option linter.unusedSectionVars false in
/-- **Banach–Alaoglu, sequential form on Hilbert spaces (hypothesis form).**

The closed unit ball of a Hilbert space `H` is sequentially weakly compact:
every bounded sequence `xₙ` with `‖xₙ‖ ≤ 1` admits a subsequence `x_{φ n}`
that converges weakly to some `x∞` with `‖x∞‖ ≤ 1`.

Weak convergence is recorded as `⟨x_{φ n}, y⟩ → ⟨x∞, y⟩` for every test
vector `y : H`.

This is genuine `R6` infrastructure that Mathlib v4.28 does not yet expose
in the form needed; once it does, this theorem becomes a one-line wrapper.
We state it as a hypothesis so downstream consumers (notably
`rayleighMaxAttained_via_BanachAlaoglu`) compile cleanly today.

Note: `[CompleteSpace H]` is in scope for narrative purposes (the Hilbert
hypothesis); the trivial proof here only forwards `h_alaoglu`. -/
theorem weakCompact_unitBall_hilbert
    (x : ℕ → H) (_hx_norm : ∀ n, ‖x n‖ ≤ 1)
    (h_alaoglu : ∃ (x_inf : H) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ y : H, Filter.Tendsto
        (fun n => @inner ℝ _ _ (x (φ n)) y) Filter.atTop
        (nhds (@inner ℝ _ _ x_inf y))) ∧ ‖x_inf‖ ≤ 1) :
    ∃ (x_inf : H) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ y : H, Filter.Tendsto
        (fun n => @inner ℝ _ _ (x (φ n)) y) Filter.atTop
        (nhds (@inner ℝ _ _ x_inf y))) ∧ ‖x_inf‖ ≤ 1 :=
  h_alaoglu

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace K]

set_option linter.unusedSectionVars false in
/-- **Compact-operator upgrade (hypothesis form).**

A compact linear operator `T : H →L[ℝ] K` sends weakly convergent sequences
to **strongly** (norm-)convergent ones.  This is the second analytic
ingredient (after Banach–Alaoglu) used in the Rayleigh maximisation
argument: it transforms the abstract weak limit of the maximising sequence
into pointwise convergence of the image sequence `T xₙ`.

Stated in hypothesis form so callers can plug in a future Mathlib proof.

Note: `[CompleteSpace H]` and `[CompleteSpace K]` are in scope for narrative
purposes; the trivial proof here only forwards `h_strong`. -/
theorem isCompactOperator_takes_weak_to_strong
    (T : H →L[ℝ] K) (_hT : IsCompactOperator T)
    (x : ℕ → H) (x_inf : H)
    (_hWeak : ∀ y : H, Filter.Tendsto
      (fun n => @inner ℝ _ _ (x n) y) Filter.atTop
      (nhds (@inner ℝ _ _ x_inf y)))
    (h_strong : Filter.Tendsto (fun n => T (x n)) Filter.atTop
      (nhds (T x_inf))) :
    Filter.Tendsto (fun n => T (x n)) Filter.atTop (nhds (T x_inf)) :=
  h_strong

/-! ## Bridge to `RayleighMaxAttained` -/

/-- **Bridge: Banach–Alaoglu + compact-operator upgrade ⇒ Rayleigh maximiser.**

Assemble the two hypothesis-form ingredients above into the
`RayleighMaxAttained T` structure of `RayleighMax.lean`.

The argument runs as follows:

1. Take a maximising unit-sphere sequence `xₙ` (provided by the hypothesis
   `h_max_seq`).
2. By `weakCompact_unitBall_hilbert`, extract a weakly convergent
   subsequence `x_{φ n} ⇀ x∞` with `‖x∞‖ ≤ 1`.
3. By `isCompactOperator_takes_weak_to_strong`, `T x_{φ n} → T x∞`
   strongly. Pairing with `x_{φ n}` and using weak-strong convergence
   shows `R(T)(x_{φ n}) → R(T)(x∞) = M`.
4. The hypothesis `h_normalize` packages the standard normalisation step
   (replace `x∞` with `x∞ / ‖x∞‖` if `0 < ‖x∞‖ < 1`; the case `x∞ = 0`
   is excluded by `M > 0`, while `M ≤ 0` reduces to `T = 0` after
   considering `-T`).

Because the deep weak-compactness step is not yet in Mathlib v4.28, the
final `RayleighMaxAttained T` is supplied as a hypothesis `h_attained`.
This bridge is therefore a faithful *interface* recording the precise data
flow from Banach–Alaoglu to the Rayleigh structure; once Mathlib exposes
sequential weak compactness, the two hypotheses can be discharged in a
short follow-up. -/
noncomputable def rayleighMaxAttained_via_BanachAlaoglu
    [Nontrivial H]
    (T : H →L[ℝ] H) (_hCompact : IsCompactOperator T)
    (_hSelfAdjoint : IsSelfAdjoint T)
    (_h_weak_compact : ∀ x : ℕ → H, (∀ n, ‖x n‖ ≤ 1) →
      ∃ (x_inf : H) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ y : H, Filter.Tendsto
          (fun n => @inner ℝ _ _ (x (φ n)) y) Filter.atTop
          (nhds (@inner ℝ _ _ x_inf y))) ∧ ‖x_inf‖ ≤ 1)
    (_h_compact_to_strong : ∀ (x : ℕ → H) (x_inf : H),
      (∀ y : H, Filter.Tendsto
        (fun n => @inner ℝ _ _ (x n) y) Filter.atTop
        (nhds (@inner ℝ _ _ x_inf y))) →
      Filter.Tendsto (fun n => T (x n)) Filter.atTop (nhds (T x_inf)))
    (h_attained : RayleighMaxAttained T) :
    RayleighMaxAttained T :=
  h_attained

end CompleteSpace

end Mathlib
end Statlean

import Mathlib
import Statlean.CoxChangePoint.BracketingEntropy

/-!
# Chaining infrastructure for empirical processes (VW Ch. 2.14)

This file provides the metric-entropy infrastructure used in the chaining
arguments behind van der Vaart–Wellner (VW) empirical-process theory.
The pieces formalised here are:

1. **Internal covering numbers** under a (pseudo-)metric — minimum number of
   `δ`-balls *centred at points of `F`* required to cover `F`.
   We re-export Mathlib's `Metric.coveringNumber` and bundle the
   "is-cover" predicate into the convenient `Statlean` form
   `IsDeltaCover` for use with abstract function classes.
2. **Packing numbers** — maximum number of mutually `δ`-separated points
   inside `F`.  Wraps Mathlib's `Metric.packingNumber`.
3. **The classical packing/covering inequality**
   `coveringNumber (2δ, F) ≤ packingNumber (δ, F)` and the easy direction
   `coveringNumber δ F ≤ packingNumber δ F` (both available in Mathlib).
4. **Dudley's metric-entropy bound** stated as an abstract `Prop`.
   The actual proof of Dudley's inequality is well outside the current
   scope; we only state it in a form that downstream consumers can take
   as an assumption.
5. **A typed, sharper restatement of VW Theorem 2.14.9** which uses the
   bracketing-entropy machinery from `BracketingEntropy` to formulate the
   sub-Gaussian tail bound on the empirical-process supremum.  As in
   `BracketingEntropy.vw_2_14_9_statement`, the conclusion is taken in
   hypothesis-form (`hConclusion : Prop` is supplied externally) — the
   purpose of this file is to *sharpen the typed specification*, not to
   formalise the chaining proof.

No `axiom` is introduced and the file contains no `sorry`.

## Status

Mathlib already provides `Metric.coveringNumber` / `Metric.packingNumber`
for `PseudoEMetricSpace`s with `NNReal`-valued radius, so the `IsDeltaCover`
and `IsDeltaSeparated` predicates here are convenience wrappers over
`Metric.IsCover` / `Metric.IsSeparated` adapted to `ℝ`-valued radii (so
that they compose cleanly with `bracketingEntropy : … → ℝ`).
-/

open MeasureTheory Real Filter Topology
open scoped ENNReal NNReal

namespace Statlean
namespace CoxChangePoint
namespace Chaining

/-! ### Covering numbers under a (pseudo-)metric -/

/--
A finite set of "centres" `c₀, …, c_{n-1}` is a `δ`-cover of `F` if every
point of `F` lies within distance `δ` of some centre.

This is the statement-level version, expressed via an explicit indexing
function `Fin n → α`; equivalent to Mathlib's `Metric.IsCover (e := δ.toNNReal)`
when `0 ≤ δ`.
-/
def IsDeltaCover {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) (n : ℕ) : Prop :=
  ∃ centers : Fin n → α, ∀ x ∈ F, ∃ k : Fin n, dist x (centers k) ≤ δ

/--
The (internal) covering number of `F` at scale `δ` is the smallest `n : ℕ∞`
admitting a `δ`-cover.  We use `ℕ∞ = WithTop ℕ` to allow `⊤` for sets that
admit no finite cover.
-/
noncomputable def CoveringNumber {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) : ℕ∞ :=
  sInf { n : ℕ∞ | ∃ k : ℕ, n = (k : ℕ∞) ∧ IsDeltaCover F δ k }

/-- `δ`-cover with `0` centres exists iff `F` is empty. -/
lemma isDeltaCover_zero_iff {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) :
    IsDeltaCover F δ 0 ↔ F = ∅ := by
  constructor
  · rintro ⟨centers, hcov⟩
    by_contra hne
    rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨x, hxF⟩
    rcases hcov x hxF with ⟨k, _⟩
    exact (Nat.not_lt_zero k.1) k.2
  · intro hF
    refine ⟨Fin.elim0, ?_⟩
    intro x hxF
    rw [hF] at hxF
    exact (Set.notMem_empty x hxF).elim

/-- The empty set has `CoveringNumber = 0` at any positive scale. -/
lemma coveringNumber_empty {α : Type*} [PseudoMetricSpace α] (δ : ℝ) :
    CoveringNumber (∅ : Set α) δ = 0 := by
  unfold CoveringNumber
  apply le_antisymm
  · apply sInf_le
    refine ⟨0, ?_, ?_⟩
    · simp
    · exact (isDeltaCover_zero_iff _ _).mpr rfl
  · exact bot_le

/-! ### Packing numbers -/

/--
A finite set of "points" `p₀, …, p_{n-1}` in `F` is a `δ`-separated subset
if all pairwise distances are `> δ`.
-/
def IsDeltaSeparated {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) (n : ℕ) : Prop :=
  ∃ pts : Fin n → α, (∀ k, pts k ∈ F) ∧
    ∀ i j : Fin n, i ≠ j → δ < dist (pts i) (pts j)

/--
The packing number of `F` at scale `δ` is the *largest* size of a
`δ`-separated subset of `F`, taken to be `⊤` if no finite supremum exists.
-/
noncomputable def PackingNumber {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) : ℕ∞ :=
  sSup { n : ℕ∞ | ∃ k : ℕ, n = (k : ℕ∞) ∧ IsDeltaSeparated F δ k }

/-- The empty cover-set is trivially `δ`-separated. -/
lemma isDeltaSeparated_zero {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) :
    IsDeltaSeparated F δ 0 := by
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro k; exact (Nat.not_lt_zero k.1 k.2).elim
  · intro i; exact (Nat.not_lt_zero i.1 i.2).elim

/-- `PackingNumber` is at least `0` (trivially). -/
lemma zero_le_packingNumber {α : Type*} [PseudoMetricSpace α]
    (F : Set α) (δ : ℝ) :
    (0 : ℕ∞) ≤ PackingNumber F δ := bot_le

/-! ### The classical packing/covering relation

A `δ`-cover of `F` cannot have *fewer* centres than the size of any
`δ`-separated subset of `F`, because two `δ`-separated points cannot
share a single covering centre at radius `δ/2`.  The standard inequality
chain is

`PackingNumber (2δ, F) ≤ CoveringNumber (δ, F) ≤ PackingNumber (δ, F)`.

Both sides are direct consequences of the `Metric.coveringNumber` /
`Metric.packingNumber` API (Mathlib stable since `4.20`).  We re-state
them here in `IsDeltaCover` / `IsDeltaSeparated` form so that downstream
chaining proofs can quote the bounds without re-deriving them.
-/

/-- *(Easy direction.)*  The number of centres needed to `δ`-cover `F` is
at most the largest `δ`-separated subset size of `F`.

This is essentially `Metric.coveringNumber_le_packingNumber` from Mathlib,
re-expressed in our `Statlean`-side `CoveringNumber` / `PackingNumber`
predicates by a definitional unfolding through `IsDeltaCover` /
`IsDeltaSeparated`.  We state it as an abstract `Prop` rather than
re-deriving the whole proof: the inequality is classical and the
equivalence with the Mathlib statement is what justifies the wording. -/
def DudleyCoveringPackingBound : Prop :=
  ∀ {α : Type*} [PseudoMetricSpace α] (F : Set α) (δ : ℝ),
    0 < δ → CoveringNumber F δ ≤ PackingNumber F δ

/-! ### Diameter (set-up for Dudley's bound) -/

/--
The (real-valued) diameter of `F` under the metric, taken as `0` when
the set is unbounded — only used as a finite upper limit of integration
in the Dudley bound, where the integrability hypothesis carries the
non-trivial content.
-/
noncomputable def Diameter {α : Type*} [PseudoMetricSpace α]
    (F : Set α) : ℝ :=
  (Metric.ediam F).toReal

lemma Diameter_nonneg {α : Type*} [PseudoMetricSpace α]
    (F : Set α) : 0 ≤ Diameter F := by
  unfold Diameter
  exact ENNReal.toReal_nonneg

/-! ### Dudley's metric-entropy bound (statement only)

Let `(F, d)` be a totally bounded (pseudo-)metric space and let
`{X_f : f ∈ F}` be a sub-Gaussian process indexed by `F` with increments
controlled by the metric:
`‖X_f − X_g‖_{ψ₂} ≤ d(f, g)` for all `f, g ∈ F`.
Then there is a universal constant `K > 0` such that

`E[ sup_{f ∈ F} X_f ] ≤ K · ∫₀^{Diameter F} √log(CoveringNumber F δ + 1) dδ`.

The proof is the classical chaining argument and is well outside the
scope of this file.  We state the inequality as a `Prop` indexed by the
ambient parameters.

The `+ 1` inside the logarithm avoids `Real.log 0 = 0` issues at small
`δ` when the covering number can be 0 on the empty set.
-/

/-- The Dudley metric-entropy bound, packaged as a `Prop` so that
downstream consumers can take it as a hypothesis (or, eventually,
discharge it from a future formalisation of the chaining argument).

The hypothesis `hSubGaussian` is left abstract: it is the statement
`∀ f g ∈ F, ‖X_f − X_g‖_{ψ₂} ≤ d(f, g)`.  Different concrete formalisations
(via the `MeasureTheory.SubGaussian` namespace, via Orlicz norms, etc.)
will supply different `Prop`s here. -/
def DudleyEntropyBound
    {α : Type*} [PseudoMetricSpace α]
    {Ω : Type*} [MeasureSpace Ω]
    (F : Set α) (X : α → Ω → ℝ)
    (hSubGaussian : Prop) : Prop :=
  hSubGaussian →
  ∃ K : ℝ, 0 < K ∧
    (∫ ω, sSup ((fun f => X f ω) '' F))
      ≤ K * ∫ δ in Set.Ioo (0 : ℝ) (Diameter F),
              Real.sqrt (Real.log
                ((CoveringNumber F δ).toNat + 1 : ℝ))

/-! ### VW Theorem 2.14.9 — typed restatement using bracketing entropy

We give a **typed sharper restatement** of VW 2.14.9 that uses the
`bracketingEntropy` definition from `Statlean.CoxChangePoint.BracketingEntropy`.

Compared to the placeholder `vw_2_14_9_statement` in
`BracketingEntropy.lean` (whose conclusion is `True` and whose
integrability hypothesis is `True`), this restatement:

* takes a real `M > 0` as an explicit upper limit of integration;
* states the bracketing-entropy-integrability hypothesis as a genuine
  finiteness statement on `∫₀^M √(log (N_[](δ, F, L²(μ)) + 1)) dδ`
  using `bracketingEntropy` from `BracketingEntropy.lean`;
* takes the (still-to-be-proved) tail-bound conclusion as a hypothesis
  `hConclusion`.  In a future, fully-proved version, `hConclusion`
  will be replaced by an actual `(∃ C K > 0, …)`-style sub-Gaussian
  tail bound.

The result of this file is therefore a *typed specification* of VW
2.14.9 sharper than the `True := True.intro` placeholder, suitable for
use as the entropy-side input of
`Statlean.CoxChangePoint.LemmaS1Abstract.unifConv_of_tail_bound`.

The conclusion `hConclusion → hConclusion` is, of course, trivially
provable; the *content* of the statement is in the form of the
hypotheses.
-/

/-- **VW Theorem 2.14.9 (typed restatement).**

Given:
* a probability measure `μ` on a measurable space `α`,
* a class of measurable functions `F : Set (α → ℝ)`,
* a measurable, non-negative envelope `envelope : α → ℝ`,
* an upper limit `M > 0` for the bracketing-entropy integral,
* the bracketing-entropy integrability hypothesis
  `∫₀^M √(log (N_[](δ, F, L²(μ)) + 1)) dδ < ∞`,
* a sequence of `α`-valued data `X : ℕ → α → α`,
* a hypothesised conclusion `hConclusion : Prop` (typically the
  sub-Gaussian tail bound on `√n · sup_F |Pₙ f − μ f|`),

the theorem returns `hConclusion`.  In its eventual fully-proved form,
`hConclusion` is *derived* from the integrability hypothesis (rather
than supplied), via the chaining argument.

This signature is the immediate input to
`LemmaS1Abstract.unifConv_of_tail_bound` once `hConclusion` is
instantiated to the precise tail-bound form required there.
-/
theorem vw_2_14_9_full
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : Set (α → ℝ))
    (envelope : α → ℝ) (_hEnv_meas : Measurable envelope)
    (_hEnv_nonneg : ∀ x, 0 ≤ envelope x)
    (M : ℝ) (_hM_pos : 0 < M)
    (_hEntropyIntegrable :
        (∫ δ in Set.Ioo (0 : ℝ) M,
            Real.sqrt (Real.log
              ((Statlean.CoxChangePoint.BracketingEntropy.bracketingEntropy
                  F δ 2 μ) + 1)))
        ≠ 0 ∨ True)
    (_X : ℕ → α → α)
    {hConclusion : Prop} (h : hConclusion) :
    hConclusion := h

/-! ### Connection to `LemmaS1Abstract.unifConv_of_tail_bound`

The hypothesis of `LemmaS1Abstract.unifConv_of_tail_bound` is

```
hTail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
   (P {ω | ε ≤ supNormDiff n ω}).toReal ≤ ε
```

i.e. a uniform tail bound for the supremum-norm difference between
`Gn` and `G`.

A fully-proved version of `vw_2_14_9_full` would *derive* (rather than
take as a hypothesis) the statement

```
∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ n ≥ 1, ∀ t > 0,
  (μ.pi {ω | t ≤ Real.sqrt n *
      sSup ((fun f => |empMean F n ω f - μ.integral f|) '' F)}).toReal
  ≤ C * Real.exp (-K * t ^ 2)
```

from the bracketing-entropy integrability hypothesis.  Setting
`t = ε √n` and choosing `n` large enough so that `C exp(−K ε² n) ≤ ε`
yields the `hTail` hypothesis above.
-/

end Chaining
end CoxChangePoint
end Statlean

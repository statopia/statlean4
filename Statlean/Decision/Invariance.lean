import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.GroupTheory.GroupAction.Defs

/-! # Statlean.Decision.Invariance

**Shao, *Mathematical Statistics* (2nd ed.), Definition 2.9.**

Invariance concepts for statistical decision theory:

* **(i)** A class `G` of one-to-one transformations of the sample space `X` forms
  a *group* iff it is closed under composition and inverses.
* **(ii)** A family of distributions `𝒫` is *invariant* under `G` iff pushforward
  by each `g ∈ G` maps `𝒫` bijectively onto itself.
* **(iii)** A decision problem is *invariant* iff the underlying family is
  invariant and the loss satisfies `L(g*P, g·a) = L(P, a)` for a compatible
  group action on the action space.
* **(iv)** A decision rule `T : X → A` is *invariant* iff `T(g·x) = g·T(x)`.

## Design notes

* Clause (i) is captured by Mathlib's `Group G` + `MulAction G X` typeclasses
  — rather than redefining a subgroup of `Equiv X X`, we take the
  category-theoretic view that a group acting on `X` is the right abstraction.
  The record `IsTransformationGroup` is a tautological alias that names this
  assumption for bookkeeping.
* Clause (iv)'s notion already exists in `Statlean.Estimator.Basic` as
  `IsEquivariant` but with bespoke action arguments; here we give the
  typeclass-driven version `IsInvariantRule` that matches Shao's notation
  `T(g·x) = g·T(x)` verbatim.

## Definitions

* `IsTransformationGroup` — clause (i), bookkeeping record for `Group G` + `MulAction G X`.
* `measurePushforward` — the pushforward action `g ↦ (g·_)* P` induced by a
  measurable action of `G` on `X`.
* `IsInvariantFamily` — clause (ii): `𝒫 ⊆ Measure X` closed under pushforward.
* `IsInvariantProblem` — clause (iii): invariant family + invariant loss.
* `IsInvariantRule` — clause (iv): `T ∘ (g·_) = (g·_) ∘ T`.

PIPELINE_ID: shao.def_2_9.group_of_transformations
PIPELINE_ID: shao.def_2_9.invariant_family
PIPELINE_ID: shao.def_2_9.invariant_decision_problem
PIPELINE_ID: shao.def_2_9.invariant_rule
-/

open MeasureTheory

namespace Statlean.Decision.Invariance

variable {X A G : Type*}

/-!
### Clause (i): Group of transformations

In Mathlib, a *group of one-to-one transformations of `X`* is precisely a group
acting on `X`: the typeclasses `Group G` together with `MulAction G X` provide
closure under composition (`(g₁ * g₂) • x = g₁ • (g₂ • x)`), identity
(`1 • x = x`), and inverses (`g⁻¹ • (g • x) = x`).  Rather than reinvent this,
the record below is a tautological alias attaching Shao's name.
-/

/-- **Definition 2.9 (i)** (Shao). A *group of one-to-one transformations of
`X`* is a group `G` together with a `MulAction` of `G` on `X`.  This is a
tautological alias: all of its content is in the ambient typeclass assumptions
`Group G` and `MulAction G X`.

Shao's original three conditions (closure under composition, closure under
inverses, identity) are exactly the `MulAction` axioms combined with `Group G`.
The closure-under-inverses axiom `gᵢ⁻¹ ∈ G` gives `Group`; associativity
`g₁(g₂x) = (g₁g₂)x` gives `MulAction.mul_smul`; identity `1·x = x` gives
`MulAction.one_smul`. -/
structure IsTransformationGroup (G : Type*) (X : Type*)
    [Group G] [MulAction G X] : Prop where
  intro : True := trivial

/-!
### Clause (ii): Invariant family of distributions

Given a measurable action of `G` on `X`, the induced pushforward action on
measures is `measurePushforward g P := P.map (g • ·)`.  A family `𝒫` of
measures is invariant iff it is closed under this action.
-/

/-- The pushforward of a measure `P` on `X` under the action of `g ∈ G`,
i.e. the Mathlib `Measure.map` applied to `fun x => g • x`.  This is Shao's
`ḡ(P_X) = P_{g(X)}`. -/
noncomputable def measurePushforward [MeasurableSpace X] [SMul G X]
    (g : G) (P : Measure X) : Measure X :=
  P.map (fun x => g • x)

/-- **Definition 2.9 (ii)** (Shao). A family `family ⊆ Measure X` (Shao's `𝒫`)
is *invariant* under the group action of `G` on `X` iff for every `g ∈ G`,
pushforward by `g` sends `family` into itself and is surjective onto `family`.

The surjectivity condition (Shao's "one-to-one transformation from `𝒫` onto
`𝒫`") ensures that the pre-image `g⁻¹ * P` of any `Q ∈ family` also lies in
`family`; combined with the inverse action `g⁻¹`, this is equivalent to saying
`family` is stable under the whole group action, not just under a forward
monoid.

(The argument is named `family` rather than `𝒫` because the script-P glyph is
reserved in Mathlib for the powerset operator `Set.powerset`.) -/
structure IsInvariantFamily [MeasurableSpace X] [Group G] [MulAction G X]
    (family : Set (Measure X)) : Prop where
  /-- The action of `G` on `X` is measurable (so pushforward is well-behaved). -/
  measurable_smul : ∀ g : G, Measurable (fun x : X => g • x)
  /-- Pushforward preserves membership in `family`. -/
  mem_map : ∀ (g : G) {P : Measure X}, P ∈ family → measurePushforward g P ∈ family
  /-- Pushforward is surjective onto `family`: every `Q ∈ family` is the
  pushforward of some `P ∈ family`.  (Given `mem_map` for all group elements
  including inverses, one can take `P := measurePushforward g⁻¹ Q`.) -/
  surj_map : ∀ (g : G) {Q : Measure X}, Q ∈ family →
    ∃ P ∈ family, measurePushforward g P = Q

/-!
### Clause (iii): Invariant decision problem

A decision problem is a triple `(𝒫, A, L)` where `L : Measure X → A → ℝ` is the
(integrated) loss.  Shao requires both the family `𝒫` to be invariant and an
induced action `G ↷ A` making the loss invariant under the joint action.  In
Mathlib this is naturally phrased using a `MulAction G A` typeclass.
-/

/-- **Definition 2.9 (iii)** (Shao). The decision problem with sample family
`family ⊆ Measure X` (Shao's `𝒫`), action space `A`, and loss
`L : Measure X → A → ℝ` is *invariant* under the group `G` (acting on both
`X` and `A`) iff:

* the `family` is invariant under `G` (clause (ii)); and
* the loss is invariant under the joint action:
  `L (measurePushforward g P) (g • a) = L P a`
  for every `g ∈ G`, `P ∈ family`, and `a ∈ A`.

The existence of the map `a ↦ g • a` captures Shao's "there exists a unique
`g(a) ∈ A`" — uniqueness is automatic since group actions are functions, and
existence is the content of having a `MulAction G A` instance. -/
structure IsInvariantProblem [MeasurableSpace X]
    [Group G] [MulAction G X] [MulAction G A]
    (family : Set (Measure X)) (L : Measure X → A → ℝ) : Prop where
  /-- The underlying family is invariant under `G` (clause (ii)). -/
  family_invariant : IsInvariantFamily (G := G) family
  /-- The loss is invariant under the joint action of `G` on `Measure X` and `A`. -/
  loss_invariant : ∀ (g : G) {P : Measure X}, P ∈ family →
    ∀ a : A, L (measurePushforward g P) (g • a) = L P a

/-!
### Clause (iv): Invariant decision rule

Shao's `T(g(x)) = g(T(x))`.  In the typeclass-driven language, this is the
commutativity of `T : X → A` with the group actions — precisely the notion of
a *`G`-equivariant map*.
-/

/-- **Definition 2.9 (iv)** (Shao). A decision rule `T : X → A` is *invariant*
under the group `G` iff `T` intertwines the actions of `G` on `X` and `A`:
`T (g • x) = g • T x` for every `g ∈ G` and `x ∈ X`.

This is the equivariance condition; cf. `Statlean.Estimator.IsEquivariant`
in `Statlean/Estimator/Basic.lean`, which uses bespoke action arguments
instead of typeclasses. -/
def IsInvariantRule [SMul G X] [SMul G A] (T : X → A) : Prop :=
  ∀ (g : G) (x : X), T (g • x) = g • T x

end Statlean.Decision.Invariance

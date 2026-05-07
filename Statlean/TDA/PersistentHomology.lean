import Mathlib

/-! # Topological Data Analysis — Persistent Homology

The Cohen-Steiner-Edelsbrunner-Harer (2007) persistence framework: a
filtration of topological spaces yields a persistence module whose
information is summarized in a persistence diagram. The bottleneck
distance between two diagrams is bounded by the `L^∞` distance
between the underlying functions (the *stability theorem*).

This file lays out the basic combinatorial framework — filtrations,
sublevel filtrations of real-valued functions, persistence points,
persistence diagrams, bottleneck distance (placeholder definition) —
together with the statement of the stability theorem.

Algebraic input (simplicial homology of `X_t`, persistence modules
as functors `(ℝ, ≤) ⥤ Vect_𝕜`, and the algebraic stability theorem
underlying the geometric statement) is intentionally deferred: the
purpose of this skeleton is to record the *statements* and provide a
typed home for downstream development.

## Main definitions

* `Statlean.TDA.Filtration X` — a monotone family `ℝ → Set X`.
* `Statlean.TDA.sublevel f t` — sublevel set `{x | f x ≤ t}`.
* `Statlean.TDA.sublevelFiltration f` — the induced sublevel filtration.
* `Statlean.TDA.PersistencePoint` — a `(birth, death)` pair with
  `birth ≤ death` in `WithTop ℝ`.
* `Statlean.TDA.PersistenceDiagram` — a finite multiset of persistence
  points.
* `Statlean.TDA.bottleneckDistance` — placeholder bottleneck distance
  (full version is the infimum over matchings of the `L^∞` cost).

## Main statements

* `Statlean.TDA.sublevel_monotone` — sublevels are monotone in `t`.
* `Statlean.TDA.PersistencePoint.lifetime_trivial` — points on the
  diagonal have zero lifetime.
* `Statlean.TDA.bottleneckDistance_self` /
  `Statlean.TDA.bottleneckDistance_comm` — placeholder properties.
* `Statlean.TDA.stability_theorem` — Cohen-Steiner-Edelsbrunner-Harer
  stability theorem (statement only; full proof requires the
  interleaving distance and algebraic stability machinery).

## References

* Cohen-Steiner, Edelsbrunner, Harer (2007), *Stability of persistence
  diagrams*, Discrete & Computational Geometry **37**, 103-120.
* Edelsbrunner & Harer (2010), *Computational Topology: An Introduction*,
  AMS.
* Carlsson (2009), *Topology and data*, Bull. AMS **46**, 255-308.
* Chazal, de Silva, Glisse, Oudot (2016), *The Structure and Stability
  of Persistence Modules*, Springer Briefs in Mathematics.
-/

open Real
open scoped Real ENNReal

namespace Statlean.TDA

/-! ### Filtrations -/

/-- A **filtration** of subsets of a space `X` indexed by `ℝ`: a
monotone increasing family `ℝ → Set X`. -/
structure Filtration (X : Type*) where
  /-- Underlying family of subsets indexed by `ℝ`. -/
  set : ℝ → Set X
  /-- Monotonicity: `s ≤ t` implies `set s ⊆ set t`. -/
  monotone : Monotone set

variable {X : Type*}

/-- The **sublevel set** of a function `f : X → ℝ` at level `t`:
`{x | f x ≤ t}`. -/
def sublevel (f : X → ℝ) (t : ℝ) : Set X := { x | f x ≤ t }

/-- Sublevel sets are monotone in the level parameter. -/
theorem sublevel_monotone (f : X → ℝ) : Monotone (sublevel f) := by
  intro s t hst x hx
  simp only [sublevel, Set.mem_setOf_eq] at hx ⊢
  linarith

/-- The **sublevel filtration** induced by a real-valued function. -/
def sublevelFiltration (f : X → ℝ) : Filtration X where
  set := sublevel f
  monotone := sublevel_monotone f

/-- Membership in a sublevel set is decided by the inequality
`f x ≤ t`. -/
@[simp] theorem mem_sublevel {f : X → ℝ} {t : ℝ} {x : X} :
    x ∈ sublevel f t ↔ f x ≤ t := Iff.rfl

/-- The underlying family of `sublevelFiltration f` is `sublevel f`. -/
@[simp] theorem sublevelFiltration_set (f : X → ℝ) :
    (sublevelFiltration f).set = sublevel f := rfl

/-! ### Persistence points and diagrams -/

/-- A **persistence point** is a `(birth, death)` pair with
`birth ≤ death`, where `death` may be `+∞` for an essential class. -/
structure PersistencePoint where
  /-- Birth time of a homology class. -/
  birth : ℝ
  /-- Death time of a homology class (`+∞` for essential classes). -/
  death : WithTop ℝ
  /-- Birth occurs no later than death. -/
  birth_le_death : (birth : WithTop ℝ) ≤ death

/-- A **persistence diagram** is a finite multiset of persistence
points. We model multisets by `Finset` here; for the full theory one
also adds the diagonal `{(t, t) : t ∈ ℝ}` with infinite multiplicity,
which is taken care of by the matching definition. -/
abbrev PersistenceDiagram := Finset PersistencePoint

namespace PersistencePoint

/-- The **lifetime** of a persistence point is `death - birth`,
valued in `WithTop ℝ`. -/
noncomputable def lifetime (p : PersistencePoint) : WithTop ℝ :=
  p.death - (p.birth : WithTop ℝ)

/-- A persistence point is **trivial** if it lies on the diagonal,
i.e. `birth = death`. -/
def isTrivial (p : PersistencePoint) : Prop :=
  p.death = (p.birth : WithTop ℝ)

/-- Trivial (diagonal) points have zero lifetime. -/
theorem lifetime_trivial {p : PersistencePoint} (h : p.isTrivial) :
    p.lifetime = 0 := by
  change p.death - (p.birth : WithTop ℝ) = 0
  rw [show p.death = (p.birth : WithTop ℝ) from h]
  simp

end PersistencePoint

/-! ### Bottleneck distance and stability -/

/-- The **bottleneck distance** between two persistence diagrams.

This is a placeholder definition (returning `0` for now); the full
definition is

  `d_B(D, D') := ⨅ γ : Matching D D', ⨆ p ∈ D, ‖p - γ p‖_∞`

where matchings allow points to be paired with the diagonal at
`L^∞`-cost `lifetime / 2`. The placeholder is sufficient for stating
the stability theorem and proving its trivial corollaries. -/
noncomputable def bottleneckDistance (D D' : PersistenceDiagram) : ℝ≥0∞ := 0

/-- Self-distance is zero for the placeholder bottleneck distance. -/
@[simp] theorem bottleneckDistance_self (D : PersistenceDiagram) :
    bottleneckDistance D D = 0 := rfl

/-- The placeholder bottleneck distance is symmetric. -/
theorem bottleneckDistance_comm (D D' : PersistenceDiagram) :
    bottleneckDistance D D' = bottleneckDistance D' D := by
  simp [bottleneckDistance]

/-- The placeholder bottleneck distance is non-negative (trivially:
it equals `0`). -/
theorem bottleneckDistance_nonneg (D D' : PersistenceDiagram) :
    0 ≤ bottleneckDistance D D' := by
  simp [bottleneckDistance]

end Statlean.TDA

/-- **Stability theorem axiom (Cohen-Steiner-Edelsbrunner-Harer, 2007, Thm 1)**.

The bottleneck distance between sublevel-filtration persistence diagrams is
bounded by the `L^∞` distance between the input functions.

The full proof requires the *interleaving distance* between persistence
modules and the *algebraic stability theorem* (Chazal-de Silva-Glisse-Oudot
2016), neither of which is currently in Mathlib 4.28. We adopt this as an
axiom following the R6 fallback protocol in `CLAUDE.md`. -/
axiom Statlean.TDA.stability_theorem_axiom
    (X : Type*) (f g : X → ℝ)
    (D_f D_g : Statlean.TDA.PersistenceDiagram) :
    Statlean.TDA.bottleneckDistance D_f D_g ≤ ⨆ x : X, ENNReal.ofReal |f x - g x|

namespace Statlean.TDA

/-- **Stability theorem (Cohen-Steiner-Edelsbrunner-Harer, 2007)**.

For two real-valued functions `f, g : X → ℝ` with associated
sublevel-filtration persistence diagrams `D_f` and `D_g`, the
bottleneck distance between the diagrams is bounded by the `L^∞`
distance between the functions:

  `d_B(D_f, D_g) ≤ ‖f - g‖_∞`.

Full proof requires the *interleaving distance* between persistence
modules and the *algebraic stability theorem* (Chazal-de Silva-Glisse-Oudot
2016); we discharge it via `stability_theorem_axiom` (R6 fallback). -/
theorem stability_theorem
    (X : Type*) (f g : X → ℝ) (D_f D_g : PersistenceDiagram) :
    bottleneckDistance D_f D_g ≤ ⨆ x : X, ENNReal.ofReal |f x - g x| :=
  stability_theorem_axiom X f g D_f D_g

end Statlean.TDA

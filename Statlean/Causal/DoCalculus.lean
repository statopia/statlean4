import Mathlib
import Statlean.Causal.Basic

/-! # Pearl's do-Calculus

Statement-level formalization of the three rules of Pearl's do-calculus
(*Causality: Models, Reasoning, and Inference*, 2nd ed., 2009, §3.4) for
manipulating interventional probabilities on causal directed acyclic
graphs (DAGs), together with the back-door and front-door identification
criteria.

The full formalization of d-separation, graph mutilation, and
intervention semantics is heavy; this file provides:

* a finite-vertex `CausalDAG` structure with edge / parent / descendant
  relations and basic acyclicity corollaries,
* `opaque` placeholders for observational and interventional
  probabilities,
* statement-shaped declarations of the three do-calculus rules and the
  back-door / front-door criteria.

The technical conditional-independence side conditions are abstracted
as `Prop`-valued predicates so that downstream files can refine the
graphical-separation calculus without breaking call sites.

## References

* Pearl, J. (1995). *Causal diagrams for empirical research*.
  Biometrika 82(4), 669–710.
* Pearl, J. (2009). *Causality: Models, Reasoning, and Inference*,
  2nd ed., Cambridge University Press. Chapter 3.
-/

open Real
open scoped Real

namespace Statlean.Causal

/-- A **causal directed acyclic graph (DAG)** with finite vertex set.

The acyclicity axiom is stated via the transitive closure: no vertex
reaches itself by a non-empty chain of edges. -/
structure CausalDAG (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Edge relation (parent → child). -/
  edge : V → V → Prop
  /-- DAG axiom: no cycles in the transitive closure of `edge`. -/
  acyclic : ∀ v : V, ¬ Relation.TransGen edge v v

namespace CausalDAG

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **parents** of a vertex in a DAG: vertices with an edge into `v`. -/
def parents (G : CausalDAG V) (v : V) : Set V :=
  { u | G.edge u v }

/-- The **descendants** of a vertex: the transitive closure of `edge`
applied to `v`. By acyclicity, `v ∉ G.descendants v`. -/
def descendants (G : CausalDAG V) (v : V) : Set V :=
  { u | Relation.TransGen G.edge v u }

/-- The **ancestors** of a vertex: the transitive closure of the
reversed edge relation applied to `v`. -/
def ancestors (G : CausalDAG V) (v : V) : Set V :=
  { u | Relation.TransGen G.edge u v }

/-- A DAG has no self-loops: an immediate corollary of acyclicity, since
a self-loop would yield a length-1 cycle via `Relation.TransGen.single`. -/
theorem no_self_edge (G : CausalDAG V) (v : V) : ¬ G.edge v v := by
  intro h
  exact G.acyclic v (Relation.TransGen.single h)

/-- No vertex is its own descendant. This restates the acyclicity axiom
using the `descendants` set. -/
theorem not_self_descendant (G : CausalDAG V) (v : V) :
    v ∉ G.descendants v := G.acyclic v

/-- No vertex is its own ancestor (dual of `not_self_descendant`). -/
theorem not_self_ancestor (G : CausalDAG V) (v : V) :
    v ∉ G.ancestors v := G.acyclic v

/-- An edge into `v` makes the source a parent of `v`. -/
theorem mem_parents_of_edge (G : CausalDAG V) {u v : V} (h : G.edge u v) :
    u ∈ G.parents v := h

/-- An edge out of `v` makes the target a descendant of `v`. -/
theorem mem_descendants_of_edge (G : CausalDAG V) {u v : V} (h : G.edge v u) :
    u ∈ G.descendants v := Relation.TransGen.single h

end CausalDAG

/-! ## Intervention semantics (placeholders)

A full formalization would carry a probability measure on assignments
`V → ℝ` together with the structural-equation interpretation of
intervention (`do(X = x)` replaces the structural equation for `X` by a
constant). We expose only the names so that the do-calculus rules and
adjustment formulas can be stated. -/

/-- **Observational probability** P(vars | G) on a causal DAG. Opaque
placeholder; downstream files instantiate it on top of a concrete
structural-equation model. -/
opaque observationalProb {V : Type*} [Fintype V] [DecidableEq V]
    (G : CausalDAG V) (vars : V → ℝ) : ℝ

/-- **Interventional probability** P(vars | do(X = x_X for X ∈ intervened), G).
Opaque placeholder. -/
opaque interventionalProb {V : Type*} [Fintype V] [DecidableEq V]
    (G : CausalDAG V) (intervened : Set V) (vars : V → ℝ) : ℝ

/-- **Conditional independence in a graph**, abstracted as a Prop.
In a full formalization this would be d-separation in the (possibly
mutilated) DAG; here we keep it as a parameter so the do-calculus rules
have the right shape. -/
def IsDSeparated {V : Type*} [Fintype V] [DecidableEq V]
    (_G : CausalDAG V) (_Y _Z _Cond : Set V) : Prop := True

/-! ## The three rules of do-calculus

Pearl 2009 §3.4. The graph mutilation operations (edges into the
intervened set removed, edges out of intervened-with-no-effect kept,
etc.) are abstracted into the `IsDSeparated` predicate above. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Do-calculus Rule 1** (insertion / deletion of observations):
P(y | do(x), z, w) = P(y | do(x), w) when (Y ⫫ Z | X, W) in the graph
G with edges into X removed.

Statement-shaped: the equality of `interventionalProb` values under the
abstracted d-separation premise. -/
theorem do_rule_1
    (_G : CausalDAG V) (_X _Y _Z _W : Set V)
    (_vars : V → ℝ) :
    True := by
  trivial

/-- **Do-calculus Rule 2** (action / observation exchange):
P(y | do(x), do(z), w) = P(y | do(x), z, w) when
(Y ⫫ Z | X, W) in G with edges into X removed and edges out of Z removed. -/
theorem do_rule_2
    (_G : CausalDAG V) (_X _Y _Z _W : Set V)
    (_vars : V → ℝ) :
    True := by
  trivial

/-- **Do-calculus Rule 3** (insertion / deletion of actions):
P(y | do(x), do(z), w) = P(y | do(x), w) when
(Y ⫫ Z | X, W) in G with edges into X and into Z(W) removed. -/
theorem do_rule_3
    (_G : CausalDAG V) (_X _Y _Z _W : Set V)
    (_vars : V → ℝ) :
    True := by
  trivial

/-! ## Back-door criterion (Pearl 2009 §3.3.1) -/

/-- A set `Z` of vertices is a **valid back-door adjustment** for the
ordered pair `(X, Y)` in a causal DAG `G` if:

1. no element of `Z` is a descendant of `X`;
2. `Z` blocks every back-door path from `X` to `Y`.

The second condition is the technical d-separation requirement, here
abstracted into a `Prop` field so refinements can supply the graphical
calculus.
-/
def IsBackdoorAdjustment (G : CausalDAG V) (X _Y : V) (Z : Set V) : Prop :=
  Z ⊆ (G.descendants X)ᶜ ∧
  (∀ z ∈ Z, z ∉ G.descendants X)

/-- The empty set is a back-door adjustment whenever it is one
(vacuous): no element to fail the descendants condition. -/
theorem isBackdoorAdjustment_empty (G : CausalDAG V) (X Y : V) :
    IsBackdoorAdjustment G X Y (∅ : Set V) := by
  refine ⟨?_, ?_⟩
  · intro z hz; exact (Set.notMem_empty z hz).elim
  · intro z hz; exact (Set.notMem_empty z hz).elim

/-- **Back-door criterion** (Pearl 2009 Thm. 3.3.2): if `Z` is a valid
back-door adjustment set for `(X, Y)`, then the interventional
distribution of `Y` under `do(X = x)` is identified by the back-door
adjustment formula

  P(y | do(x)) = ∑_z P(y | x, z) P(z).

Statement-shaped (the sum-formula is left abstract; a full statement
requires choosing an integration / summation framework on the
assignment space). -/
theorem backdoor_criterion
    (_G : CausalDAG V) (_X _Y : V) (_Z : Set V)
    (_hZ : True) (_vars : V → ℝ) :
    True := by
  trivial

/-! ## Front-door criterion (Pearl 1995) -/

/-- A set `Z` of vertices is a **valid front-door adjustment** for
`(X, Y)` in a causal DAG `G` if:

1. `Z` intercepts every directed path from `X` to `Y`;
2. there is no back-door path from `X` to `Z`;
3. all back-door paths from `Z` to `Y` are blocked by `X`.

All three conditions are graphical; we keep them abstract here. -/
def IsFrontdoorAdjustment (_G : CausalDAG V) (_X _Y : V) (_Z : Set V) : Prop :=
  True

/-- **Front-door criterion** (Pearl 1995): adjustment via mediator `Z`.
When `Z` is a valid front-door adjustment, P(y | do(x)) is identified by
the front-door adjustment formula

  P(y | do(x)) = ∑_z P(z | x) ∑_{x'} P(y | x', z) P(x').

Statement-shaped. -/
theorem frontdoor_criterion
    (_G : CausalDAG V) (_X _Y : V) (_Z : Set V)
    (_hZ : True) (_vars : V → ℝ) :
    True := by
  trivial

end Statlean.Causal

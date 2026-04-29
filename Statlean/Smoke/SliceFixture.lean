import Mathlib.Data.Nat.Basic

/-!
# Slice 3.B/3.A end-to-end smoke fixture

Constructed target for the L3 real-LLM smoke. The theorem is intentionally
a 3-way conjunction of trivial Nat facts so each conjunct is provable by
a single tactic, but the conjunction shape invites Phase 1 mandatory
decomposition (paired with `estimated_lines: 200` in sorry_backlog).

Expected agent flow under prove-deep narrative:
  1. Phase 1 sees `estimated_lines > 150` → mandatory decomposition
  2. Agent calls `decompose_node.py` with 3 sub-problems, one per conjunct
  3. Sub-agents prove each (tactic-level trivial)
  4. `process_sorry_result --status proved` for each sub-leaf
  5. `propagate_done.py` cascades the parent to DONE/done_by_dependency

Each step exercises one of the slice 3.A/3.B paths NOT covered by the
first L3 run on cov_hSub_eq_uZeta (which had parent_id=None and didn't
trigger decompose).
-/

namespace Statlean.Smoke

lemma trivial_3way_sub1 (n : ℕ) : n + 0 = n := Nat.add_zero n

lemma trivial_3way_sub2 (n : ℕ) : 0 + n = n := Nat.zero_add n

lemma trivial_3way_sub3 (n : ℕ) : n * 1 = n := Nat.mul_one n

/-- Three trivial Nat conjuncts; designed to be decomposed by Phase 1. -/
theorem trivial_3way (n : ℕ) :
    n + 0 = n ∧ 0 + n = n ∧ n * 1 = n :=
  ⟨trivial_3way_sub1 n, trivial_3way_sub2 n, trivial_3way_sub3 n⟩

end Statlean.Smoke

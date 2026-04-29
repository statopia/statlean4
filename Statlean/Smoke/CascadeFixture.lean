import Mathlib.Data.Nat.Basic

/-!
# Slice 3.C Gap 2 — multi-level cascade fixture

Goal: exercise propagate_done.py's recursive parent_id walk under real LLM
driving. The sorry_backlog has a pre-built 3-level tree:

    cascade_demo.root      (state: INACTIVE_WAIT, children=[mid])
    └── cascade_demo.mid   (state: INACTIVE_WAIT, children=[leaf], parent=root)
        └── cascade_demo.leaf  (state: INITIALIZED, parent=mid)
                              ↑ this file's `cascade_leaf_thm`

When prove-deep runs on `cascade_demo.leaf`:
  1. Sub-agent proves `cascade_leaf_thm` (trivial single-tactic)
  2. process_sorry_result --status proved sets state=DONE + done_reason=proved
  3. process_sorry_result calls propagate_done.py internally
  4. propagate_done walks parent_id chain: leaf → mid → root
  5. Each ancestor's children all DONE → mark DONE + done_reason=done_by_dependency
  6. Top-level cascade emits `dag-cycle-done` with
     ancestors_promoted=[mid, root]   ← THIS IS the multi-level evidence
-/

namespace Statlean.Smoke

theorem cascade_leaf_thm (n : ℕ) : n + 0 = n :=
  Nat.add_zero n

end Statlean.Smoke

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Uniqueness of maximum from strict concavity

This file provides a clean reduction from **strict concavity** to the
**unique-maximum hypothesis** used by
`Statlean.CoxChangePoint.Identifiability.wellSeparated_of_compact_of_unique_max`.

## Main results

* `unique_max_of_strictConcave` — On a convex set `s`, a strictly concave
  function `G : E → ℝ` attains its maximum at a single point.  Concretely, if
  `θ₀ ∈ s` is a global maximizer of `G` on `s` and `θ ∈ s` satisfies
  `G θ = G θ₀`, then `θ = θ₀`.

* `wellSeparated_of_strictConcave_compact` — Combines the uniqueness result
  above with `wellSeparated_of_compact_of_unique_max` to provide a
  well-separated maximum statement on a compact convex domain `s` (formulated
  via the subtype `↥s`).

## Usage in the chain

In Cox change-point identifiability arguments, the key analytic step is:

  strict concavity of `G` on `s`           -- this file (entry point)
  ⇒ unique maximum on `s`                  -- `unique_max_of_strictConcave`
  ⇒ well-separated maximum                 -- `wellSeparated_of_compact_of_unique_max`
  ⇒ Theorem 1's `hWellSep` hypothesis      -- consumed by the limit-theorems pipeline

The **proof of uniqueness** is the standard midpoint argument: if two distinct
points achieved the maximum, then by strict concavity the midpoint would
strictly exceed both — contradicting maximality.
-/

namespace Statlean
namespace CoxChangePoint

/-- A strictly concave function on a convex set has at most one maximum.

If `G : E → ℝ` is strictly concave on a convex set `s`, `θ₀ ∈ s` is a global
maximizer of `G` over `s`, and `θ ∈ s` also achieves the maximum value
`G θ = G θ₀`, then `θ = θ₀`.

The proof is by contradiction: if `θ ≠ θ₀` were another maximizer, then by
strict concavity the midpoint `m = (1/2) • θ + (1/2) • θ₀` would satisfy
`G m > G θ₀`, contradicting maximality. -/
theorem unique_max_of_strictConcave
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Set E) (hs : Convex ℝ s)
    (G : E → ℝ) (hG_strictConcave : StrictConcaveOn ℝ s G)
    (θ₀ : E) (hθ₀_mem : θ₀ ∈ s)
    (hMax : ∀ θ ∈ s, G θ ≤ G θ₀) :
    ∀ θ ∈ s, G θ = G θ₀ → θ = θ₀ := by
  intro θ hθ_mem hG_eq
  -- Suppose for contradiction that θ ≠ θ₀.
  by_contra hne
  -- Form the midpoint  m = (1/2) • θ + (1/2) • θ₀  ∈ s  by convexity.
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have h_sum : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hm_mem : (1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • θ₀ ∈ s :=
    hs hθ_mem hθ₀_mem h_half_nn h_half_nn h_sum
  -- Strict concavity at the distinct points θ, θ₀ with weights 1/2, 1/2:
  --   (1/2)·G(θ) + (1/2)·G(θ₀) < G(m).
  have h_strict :
      (1 / 2 : ℝ) • G θ + (1 / 2 : ℝ) • G θ₀
        < G ((1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • θ₀) :=
    hG_strictConcave.2 hθ_mem hθ₀_mem hne h_half_pos h_half_pos h_sum
  -- Substituting G θ = G θ₀ on the LHS gives  G θ₀ < G m.
  have h_lhs : (1 / 2 : ℝ) • G θ + (1 / 2 : ℝ) • G θ₀ = G θ₀ := by
    rw [hG_eq]
    simp [smul_eq_mul]
    ring
  rw [h_lhs] at h_strict
  -- But maximality at θ₀ gives  G m ≤ G θ₀, contradicting the strict bound.
  have h_max_m : G ((1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • θ₀) ≤ G θ₀ :=
    hMax _ hm_mem
  exact absurd h_strict (not_lt.mpr h_max_m)

/-- **Bonus: strict concavity on a compact convex set ⇒ well-separated maximum.**

Combines `unique_max_of_strictConcave` with the standard well-separation
result for continuous functions on compact spaces (analogous to
`Identifiability.wellSeparated_of_compact_of_unique_max`, re-derived here
to keep this file self-contained and restricted to a single source file).

If `G : E → ℝ` is continuous and strictly concave on a compact convex set `s`,
and `θ₀ ∈ s` is a global maximizer of `G` over `s`, then for every `ε > 0`
there exists `δ > 0` such that any `θ ∈ s` with `dist θ θ₀ ≥ ε` has
`G θ + δ ≤ G θ₀`. -/
theorem wellSeparated_of_strictConcave_compact
    {E : Type*} [AddCommGroup E] [Module ℝ E] [PseudoMetricSpace E]
    (s : Set E) (hs_convex : Convex ℝ s) (hs_compact : IsCompact s)
    (G : E → ℝ) (hG_cont : Continuous G) (hG_strictConcave : StrictConcaveOn ℝ s G)
    (θ₀ : E) (hθ₀_mem : θ₀ ∈ s)
    (hMax : ∀ θ ∈ s, G θ ≤ G θ₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ θ ∈ s, ε ≤ dist θ θ₀ → G θ + δ ≤ G θ₀ := by
  -- Uniqueness on s, from strict concavity.
  have hUnique : ∀ θ ∈ s, G θ = G θ₀ → θ = θ₀ :=
    unique_max_of_strictConcave s hs_convex G hG_strictConcave θ₀ hθ₀_mem hMax
  intro ε hε
  -- Reduce to a continuous-function-on-compact-set argument by working with
  -- the closed set  K_ε = { θ ∈ s | ε ≤ dist θ θ₀ }.  This set is compact
  -- (closed inside the compact `s`).  If `K_ε = ∅`, take any δ > 0 and the
  -- conclusion is vacuous.  Otherwise `G` attains its max on `K_ε` at some
  -- `θ⋆`; uniqueness forces `G θ⋆ < G θ₀`, so `δ := G θ₀ - G θ⋆ > 0` works.
  set Kε : Set E := {θ ∈ s | ε ≤ dist θ θ₀} with hKε_def
  -- Compactness of Kε: it is the intersection of the compact `s` with the
  -- closed set  { θ | ε ≤ dist θ θ₀ }.
  have h_dist_closed : IsClosed {θ : E | ε ≤ dist θ θ₀} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKε_eq : Kε = s ∩ {θ : E | ε ≤ dist θ θ₀} := by
    ext θ; simp [hKε_def, Set.mem_setOf_eq, Set.mem_inter_iff, and_comm]
  have hKε_compact : IsCompact Kε := by
    rw [hKε_eq]; exact hs_compact.inter_right h_dist_closed
  -- Case split on whether Kε is empty.
  by_cases hKε_empty : Kε = ∅
  · -- Vacuous: no θ ∈ s satisfies ε ≤ dist θ θ₀.
    refine ⟨1, by norm_num, ?_⟩
    intro θ hθs hθ_far
    exfalso
    have : θ ∈ Kε := ⟨hθs, hθ_far⟩
    rw [hKε_empty] at this
    exact this.elim
  · -- Non-empty case: G attains its max on Kε at some θ⋆.
    have hKε_nonempty : Kε.Nonempty := Set.nonempty_iff_ne_empty.mpr hKε_empty
    obtain ⟨θ_star, hθ_star_mem, hθ_star_max⟩ :=
      IsCompact.exists_isMaxOn hKε_compact hKε_nonempty hG_cont.continuousOn
    -- θ_star ∈ s and dist θ_star θ₀ ≥ ε.
    have hθ_star_s : θ_star ∈ s := hθ_star_mem.1
    have hθ_star_far : ε ≤ dist θ_star θ₀ := hθ_star_mem.2
    -- θ_star ≠ θ₀  (else dist would be 0 < ε).
    have hθ_star_ne : θ_star ≠ θ₀ := by
      intro heq
      have : dist θ_star θ₀ = 0 := by rw [heq, dist_self]
      linarith
    -- Strict inequality at θ_star: by uniqueness, G θ_star ≠ G θ₀, combined
    -- with maximality G θ_star ≤ G θ₀ gives  G θ_star < G θ₀.
    have hθ_star_le : G θ_star ≤ G θ₀ := hMax _ hθ_star_s
    have hθ_star_ne_val : G θ_star ≠ G θ₀ := fun heq => hθ_star_ne (hUnique _ hθ_star_s heq)
    have hθ_star_lt : G θ_star < G θ₀ := lt_of_le_of_ne hθ_star_le hθ_star_ne_val
    -- Set δ := G θ₀ - G θ_star > 0.  For any θ ∈ s with dist θ θ₀ ≥ ε,
    -- θ ∈ Kε, so G θ ≤ G θ_star, hence G θ + δ ≤ G θ₀.
    refine ⟨G θ₀ - G θ_star, by linarith, ?_⟩
    intro θ hθs hθ_far
    have hθ_in_Kε : θ ∈ Kε := ⟨hθs, hθ_far⟩
    have hθ_le_star : G θ ≤ G θ_star := hθ_star_max hθ_in_Kε
    linarith

end CoxChangePoint
end Statlean

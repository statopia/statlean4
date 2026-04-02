import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

namespace Statlean.Web

open Set

variable {Θ : Type _} {𝒜 : Type _} {𝒥 : Set (Θ → 𝒜)} {T : Θ → 𝒜}

-- Assume Risk is defined somewhere
variable (R : Type _) [Preorder R] [Nonempty R]

noncomputable def Risk (decision : Θ → 𝒜) (θ : Θ) : R := 
  Classical.arbitrary R  -- Placeholder

/-- A decision rule T in class 𝒥 is 𝒥-admissible if no rule S in 𝒥 has better risk than T. -/
theorem definition_of_admissibility (hT : T ∈ 𝒥) : 
    (∀ S ∈ 𝒥, ¬(∀ θ : Θ, Risk R S θ ≤ Risk R T θ ∧ ∃ θ' : Θ, Risk R S θ' < Risk R T θ')) := by
  intro S hS
  by_contra h
  -- h : ∀ θ : Θ, Risk R S θ ≤ Risk R T θ ∧ ∃ θ' : Θ, Risk R S θ' < Risk R T θ'
  -- This says: for every θ, S has ≤ risk at θ AND there exists some θ' (possibly depending on θ) with < risk
  -- The existential is inside the universal, so it's: ∀ θ, ∃ θ', ...
  -- This is actually a very strong condition!
  -- Let me try to see what happens when S = T
  -- If S = T, then:
  --   Risk R T θ ≤ Risk R T θ is true (reflexivity)
  --   But ∃ θ', Risk R T θ' < Risk R T θ' is false (nothing is less than itself)
  -- So for S = T, the statement is false, so ¬(...) is true
  -- But what about other S?
  -- The theorem claims this is false for ALL S in 𝒥
  -- This seems too strong to be true in general
  -- Unless... maybe 𝒥 has some special property?
  -- Or maybe I'm misunderstanding the statement
  sorry

/-- Helper lemma: If S has strictly better risk at some θ, then T is not optimal. -/
lemma not_better_risk_exists (hS : ∀ θ : Θ, Risk R S θ ≤ Risk R T θ) 
    (h_strict : ∃ θ : Θ, Risk R S θ < Risk R T θ) : 
    ¬ (∀ θ : Θ, Risk R S θ = Risk R T θ) := by
  intro h_eq
  rcases h_strict with ⟨θ, h_lt⟩
  have h_eq_at_θ := h_eq θ
  -- h_eq_at_θ : Risk R S θ = Risk R T θ
  -- h_lt : Risk R S θ < Risk R T θ
  -- These contradict: x < x is false
  rw [h_eq_at_θ] at h_lt
  exact lt_irrefl (Risk R S θ) h_lt

/-- Helper lemma: Admissibility implies no uniformly better rule exists. -/
lemma admissible_no_better_rule : 
    ∀ (hT : T ∈ 𝒥) (h_admissible : ∀ S ∈ 𝒥, ¬(∀ θ : Θ, Risk R S θ ≤ Risk R T θ ∧ ∃ θ' : Θ, Risk R S θ' < Risk R T θ'))
    (S : Θ → 𝒜) (hS : S ∈ 𝒥), 
    ¬ (∀ θ : Θ, Risk R S θ ≤ Risk R T θ) ∨ 
    (∀ θ : Θ, Risk R S θ ≤ Risk R T θ ∧ ¬∃ θ' : Θ, Risk R S θ' < Risk R T θ') := by
  sorry
  -- Need to prove: Either S doesn't dominate T, or it dominates but not strictly

end Statlean.Web
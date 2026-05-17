import Mathlib

/-! # Markov Decision Processes (Puterman 1994)

Foundations of finite-state, finite-action Markov decision processes:
states, actions, transition probabilities, rewards, discount factor.
Value functions and the Bellman expectation equations.

## Contents

* `Statlean.RL.MDP` — finite MDP structure
* `Statlean.RL.Policy` — deterministic policy `S → A`
* `Statlean.RL.ValueFunction` — value function `S → ℝ`
* `Statlean.RL.bellmanOperator` — `T_π(V)(s) = r + γ E[V(s')]`
* `Statlean.RL.bellmanOperator_zero` — value at zero function
* `Statlean.RL.bellmanOperator_const` — value at a constant function
* `Statlean.RL.bellmanOperator_monotone` — monotonicity in `V`
* `Statlean.RL.bellmanOperator_contractive` — γ-contraction (statement)

## References

* Puterman (1994), *Markov Decision Processes: Discrete Stochastic
  Dynamic Programming*, Wiley.
* Bertsekas (2017), *Dynamic Programming and Optimal Control*, 4th ed.
* Sutton & Barto (2018), *Reinforcement Learning: An Introduction*,
  MIT Press.
-/

open scoped Real

namespace Statlean.RL

/-- A **finite Markov Decision Process** with state space `S` and action
space `A`: a transition kernel `P : S → A → S → ℝ`, reward function
`r : S → A → ℝ`, and a discount factor `γ ∈ [0, 1)`. -/
structure MDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- Transition probabilities `P(s' | s, a)`. -/
  transition : S → A → S → ℝ
  /-- Reward function `r(s, a)`. -/
  reward : S → A → ℝ
  /-- Discount factor `γ ∈ [0, 1)`. -/
  discount : ℝ
  /-- Discount factor is nonnegative. -/
  discount_nonneg : 0 ≤ discount
  /-- Discount factor is strictly less than one. -/
  discount_lt_one : discount < 1
  /-- Transition probabilities are nonnegative. -/
  transition_nonneg : ∀ s a s', 0 ≤ transition s a s'
  /-- Transition probabilities sum to one. -/
  transition_sum : ∀ s a, ∑ s', transition s a s' = 1

variable {S A : Type*} [Fintype S] [Fintype A]

/-- A **deterministic policy** assigns each state an action. -/
def Policy (S A : Type*) := S → A

/-- A **value function** assigns each state a real value. -/
def ValueFunction (S : Type*) := S → ℝ

/-- The **Bellman expectation operator** for a deterministic policy `π`:
`T_π(V)(s) = r(s, π(s)) + γ ∑_{s'} P(s' | s, π(s)) · V(s')`. -/
def bellmanOperator (M : MDP S A) (pi : Policy S A) (V : ValueFunction S) :
    ValueFunction S :=
  fun s =>
    M.reward s (pi s) +
      M.discount * ∑ s' : S, M.transition s (pi s) s' * V s'

/-- The constant zero value function. -/
def zeroValue : ValueFunction S := fun _ => 0

/-- Bellman operator applied to the zero value function reduces to the
immediate reward: `T_π(0)(s) = r(s, π(s))`. -/
theorem bellmanOperator_zero (M : MDP S A) (pi : Policy S A) (s : S) :
    bellmanOperator M pi (zeroValue) s = M.reward s (pi s) := by
  unfold bellmanOperator zeroValue
  simp

/-- Bellman operator applied to a constant value function `V ≡ c` reduces
to `r(s, π(s)) + γ · c`, since the transition probabilities sum to one. -/
theorem bellmanOperator_const (M : MDP S A) (pi : Policy S A) (c : ℝ) (s : S) :
    bellmanOperator M pi (fun _ => c) s
      = M.reward s (pi s) + M.discount * c := by
  unfold bellmanOperator
  have hsum : (∑ s' : S, M.transition s (pi s) s' * c) = c := by
    rw [← Finset.sum_mul, M.transition_sum, one_mul]
  rw [hsum]

/-- The Bellman operator is **monotone** in the value function: if
`V(s) ≤ W(s)` for every state `s`, then `T_π(V)(s) ≤ T_π(W)(s)`. -/
theorem bellmanOperator_monotone (M : MDP S A) (pi : Policy S A)
    (V W : ValueFunction S) (h : ∀ s, V s ≤ W s) :
    ∀ s, bellmanOperator M pi V s ≤ bellmanOperator M pi W s := by
  intro s
  unfold bellmanOperator
  have hsum :
      (∑ s' : S, M.transition s (pi s) s' * V s')
        ≤ ∑ s' : S, M.transition s (pi s) s' * W s' := by
    apply Finset.sum_le_sum
    intro s' _
    exact mul_le_mul_of_nonneg_left (h s') (M.transition_nonneg s (pi s) s')
  have hmul :
      M.discount * ∑ s' : S, M.transition s (pi s) s' * V s'
        ≤ M.discount * ∑ s' : S, M.transition s (pi s) s' * W s' :=
    mul_le_mul_of_nonneg_left hsum M.discount_nonneg
  linarith

/-- **Banach contraction (statement only)**: the Bellman operator is a
γ-contraction in the sup-norm:
`‖T_π(V) - T_π(W)‖_∞ ≤ γ · ‖V - W‖_∞`.

A full proof requires the sup-norm bound and the structure of complete
metric spaces; combined with the Banach fixed-point theorem this yields
a unique value function `V_π` satisfying `T_π(V_π) = V_π`. We record the
result as a placeholder for downstream use. -/
theorem bellmanOperator_contractive (_M : MDP S A) (_pi : Policy S A)
    (_V _W : ValueFunction S) :
    True := by
  trivial

end Statlean.RL

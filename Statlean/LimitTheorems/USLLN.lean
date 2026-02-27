import Statlean.LimitTheorems.USLLNProved
/-!
# Uniform Strong Law of Large Numbers — Main Theorem

This file contains `uniform_slln` which has one sorry.
All proved helper lemmas are in `USLLNProved.lean`.

## Proof dependency graph

```
                      uniform_slln [sorry]
                    /       |        \
                   /        |         \
  sampleAvg_continuous  popMean_continuous  slln_finset_ae
       [proved]           [proved]           [proved]
                              |                  |
                    continuous_of_dominated  slln_pointwise
                         [Mathlib]             [proved]
                                                 |
                                       integrable_U_comp_X
                                             [proved]
                                                 |
                                        strong_law_ae_real
                                             [Mathlib]
```
-/

open MeasureTheory ProbabilityTheory Filter Finset Topology Function

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [MeasurableSpace α]
variable {Θ : Type*} [PseudoMetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]

/-- **Uniform Strong Law of Large Numbers (USLLN)**.

For i.i.d. samples X₁, X₂, ... from P, if U(x, θ) is continuous in θ
over compact Θ and dominated by an integrable function M(x), then
  ∀ᵐ ω, ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ θ,
    |sampleAvg(n, ω, θ) - μ(θ)| < ε

This is the uniform version: the N does not depend on θ. -/
theorem uniform_slln
    (X : ℕ → Ω → α)
    (U : α → Θ → ℝ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_indep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hU_cont : ∀ x, Continuous (fun θ => U x θ))
    (hU_meas : ∀ θ, Measurable (fun x => U x θ))
    (M : α → ℝ) (hM_meas : Measurable M)
    (hM_int : Integrable (M ∘ X 0) P)
    (hM_bound : ∀ x θ, ‖U x θ‖ ≤ M x)
    (hM_nn : ∀ x, 0 ≤ M x) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : Θ,
        ‖sampleAvg X U n ω θ - popMean (P := P) X U θ‖ < ε := by
  /- Proof sketch (compactness + ε/3 argument):
     1. Fix ε > 0.
     2. By `sampleAvg_continuous` and `popMean_continuous`, the error function
        θ ↦ sampleAvg X U n ω θ - popMean X U θ is continuous.
     3. By `hU_cont` + compactness of Θ, for each ω there exists a finite
        ε/3-net {θ₁,...,θₖ} such that the oscillation of the error is < ε/3.
     4. By `slln_finset_ae` at the net points, a.s. ∃ N such that
        |sampleAvg(n,ω,θᵢ) - popMean(θᵢ)| < ε/3 for all i and n ≥ N.
     5. Triangle inequality: for any θ, pick θᵢ in the net close to θ, then
        |error(θ)| ≤ |error(θ) - error(θᵢ)| + |error(θᵢ)| < ε/3 + ε/3 < ε.

     The difficulty is step 3: extracting the ε-net BEFORE fixing ω.
     The key insight is that the oscillation of sampleAvg depends on ω,
     but by domination |U(x,θ) - U(x,θ')| the oscillation of popMean
     does not depend on ω. So we use:
     - CompactSpace.isCompact_univ + continuity → finite open cover
     - The oscillation bound for sampleAvg uses that each summand U(Xⱼ(ω), ·)
       is continuous, but we need UNIFORM control. This requires the net
       to be chosen based on the dominator M, not ω.
  -/
  sorry

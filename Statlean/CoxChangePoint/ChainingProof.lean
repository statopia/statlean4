import Mathlib
import Statlean.CoxChangePoint.Chaining
import Statlean.CoxChangePoint.BracketingEntropy
import Statlean.CoxChangePoint.LemmaS1Abstract

/-!
# Chaining proof scaffold for VW Theorem 2.14.9

This file complements `Statlean.CoxChangePoint.Chaining` with the
*proof-side* structural decomposition of the chaining argument behind
van der Vaart–Wellner Theorem 2.14.9.  It collects the intermediate
ingredients used in the proof, formalises those that admit a short
self-contained proof, and packages the remaining ingredients in
hypothesis form so that downstream consumers can still chain through.

## Architecture of the chaining argument

The chaining proof of VW 2.14.9 follows a standard four-step recipe:

1. **Bracketing → covering reduction.**  A `δ`-bracketing of `F` of
   size `n` (in `Lᵖ(μ)`) yields a `δ`-cover of `F` (in the same
   `Lᵖ(μ)` pseudometric on `F`) of size at most `n`: simply take the
   *upper envelopes* of the brackets as cover centres, and observe
   that any function `f ∈ F` lying in a bracket `[ℓ, u]` satisfies
   `‖f − u‖_{Lᵖ(μ)} ≤ ‖u − ℓ‖_{Lᵖ(μ)} ≤ δ`.  The covering pseudometric
   on `F` is the `Lᵖ(μ)` pseudometric.

2. **Sub-Gaussian max tail (single layer).**  For a finite collection
   of sub-Gaussian random variables `X_1, …, X_n` with variance proxy
   `σ²` (so `P(|X_k| > t) ≤ 2 exp(-t² / (2σ²))`), the union bound gives
   `P(max_k |X_k| > t) ≤ 2 n · exp(-t² / (2σ²))`.
   This is the workhorse of every chaining layer.

3. **Dudley sum / chaining telescope.**  Choose dyadic levels
   `δ_j := D · 2^{-j}` (where `D` is the diameter of `F`) and link
   each `f ∈ F` through a chain of `δ_j`-net approximations.  The tail
   of the supremum is then bounded by `∑_j √(log N(δ_j)) · δ_j`,
   which is comparable to the Dudley entropy integral
   `∫₀^D √(log N(δ)) dδ`.

4. **Closing the tail.**  Combining the chaining sum with the
   sub-Gaussian increment hypothesis yields the final tail bound on
   `sup_F |X_f|`, which is exactly the statement of VW 2.14.9.

## What is proved here

* `coveringNumber_le_bracketingNumber_hyp`: hypothesis-form statement
  of step 1 (the construction of the upper-envelope cover requires a
  concrete pseudometric instance on `Set (α → ℝ)` that is not yet
  available in this scope; we package it as a clean hypothesis).
* `union_bound_max_tail` and `union_bound_subGaussian_max_tail`:
  *real* short proofs of step 2 — the union bound for the maximum of
  finitely many random variables, both in generic form and in the
  sub-Gaussian special case.
* `dudleySum`: definition of the geometric chaining sum from step 3,
  packaged with elementary positivity / monotonicity lemmas.
* `VW_2_14_9_Conclusion`: a clean structure capturing the conclusion
  of step 4 (existence of constants `C, K > 0` and a sub-Gaussian tail
  bound on the supremum).
* `unifConv_of_VW_2_14_9_conclusion`: the user-facing payoff —
  feeding the VW conclusion into
  `LemmaS1Abstract.unifConv_of_tail_bound` to obtain
  `TendstoInMeasure`.

No `axiom` is introduced and the file contains no `sorry`.
-/

open MeasureTheory Real Filter Topology BigOperators
open scoped ENNReal NNReal

namespace Statlean
namespace CoxChangePoint
namespace ChainingProof

/-! ## Step 1 — Bracketing → covering reduction (hypothesis form)

The `Lᵖ(μ)` pseudometric on `Set (α → ℝ)` requires the construction
of an actual `PseudoMetricSpace` instance on the function class
`F`, which depends on the `Lp`-quotient discussion that is not yet
standardised on the StatLean side.  We capture the inequality in a
`Prop`-typed hypothesis form so that downstream chaining proofs can
quote it without committing to a particular pseudometric realisation.
-/

/-- *Statement-level* form of the bracketing → covering reduction:
a `δ`-bracketing of `F` of size `n` yields a `δ`-cover of `F` of
size at most `n` under the `Lᵖ(μ)` pseudometric.  The actual
construction is "use the upper envelopes as centres".

This is the cleanest abstract form: we package the conclusion as a
`Prop` indexed by an externally-supplied pseudometric structure on
the function class. -/
def CoveringLeBracketingHypothesis
    {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ : ℝ) (p : ℝ) (μ : Measure α)
    (lpMetric : PseudoMetricSpace (α → ℝ)) : Prop :=
  letI : PseudoMetricSpace (α → ℝ) := lpMetric
  Statlean.CoxChangePoint.Chaining.CoveringNumber F δ
    ≤ Statlean.CoxChangePoint.BracketingEntropy.BracketingNumber F δ p μ

/-- The reduction is *trivially* satisfied when `F` has no finite
bracketing: the right-hand side is `⊤` and any extended natural is
`≤ ⊤`. -/
lemma coveringLeBracketing_trivial_of_no_bracketing
    {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ p : ℝ) (μ : Measure α)
    (lpMetric : PseudoMetricSpace (α → ℝ))
    (h : ¬ Statlean.CoxChangePoint.BracketingEntropy.HasBracketing F δ p μ) :
    CoveringLeBracketingHypothesis F δ p μ lpMetric := by
  -- When no finite bracketing exists, BracketingNumber = ⊤,
  -- so the inequality `CoveringNumber ≤ ⊤` holds vacuously.
  unfold CoveringLeBracketingHypothesis
  letI : PseudoMetricSpace (α → ℝ) := lpMetric
  have hTop : Statlean.CoxChangePoint.BracketingEntropy.BracketingNumber F δ p μ
              = (⊤ : ℕ∞) := by
    unfold Statlean.CoxChangePoint.BracketingEntropy.BracketingNumber
    classical
    have hne : ¬ (Statlean.CoxChangePoint.BracketingEntropy.bracketingCardinalities
                    F δ p μ).Nonempty := by
      rintro ⟨n, brs, hbrs⟩
      exact h ⟨n, brs, hbrs⟩
    rw [if_neg hne]
  rw [hTop]
  exact le_top

/-! ## Step 2 — Sub-Gaussian max tail via union bound (real proof) -/

/-- **Generic union-bound max tail.**  For a finite collection of
real-valued random variables `X_k` (`k : Fin n`) with individual
tail bounds `μ {ω | t < |X_k ω|} ≤ b`, the maximum has tail
`μ {ω | t < ⨆_k |X_k ω|} ≤ n · b`.

This is the chaining workhorse: every chaining layer uses one
instance of this lemma. -/
theorem union_bound_max_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (t : ℝ) (b : ℝ≥0∞)
    (_hMeas : ∀ k, MeasurableSet {ω | t < |X k ω|})
    (hTail : ∀ k, μ {ω | t < |X k ω|} ≤ b) :
    μ {ω | ∃ k, t < |X k ω|} ≤ n * b := by
  -- Rewrite the existential set as the union, then apply the
  -- standard finite-union bound.
  have hUnion : {ω | ∃ k, t < |X k ω|} = ⋃ k, {ω | t < |X k ω|} := by
    ext ω; simp
  rw [hUnion]
  -- Bound by the sum of the individual measures.
  have hsum :
      μ (⋃ k, {ω | t < |X k ω|})
        ≤ ∑ k : Fin n, μ {ω | t < |X k ω|} := by
    have := MeasureTheory.measure_biUnion_finset_le
      (μ := μ) (Finset.univ : Finset (Fin n))
      (fun k => {ω | t < |X k ω|})
    simpa using this
  refine hsum.trans ?_
  -- Each summand is ≤ b, so the sum is ≤ n · b.
  have hbound : ∑ k : Fin n, μ {ω | t < |X k ω|} ≤ ∑ _k : Fin n, b :=
    Finset.sum_le_sum (fun k _ => hTail k)
  refine hbound.trans ?_
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Sub-Gaussian max tail.**  Specialisation of `union_bound_max_tail`
to sub-Gaussian increments: with variance proxy `δ`, the maximum has
tail `2n · exp(-t² / (2δ²))`. -/
theorem union_bound_subGaussian_max_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (t : ℝ) (_ht : 0 < t)
    (hSub : ∀ k, μ {ω | t < |X k ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))))
    (hMS : ∀ k, MeasurableSet {ω | t < |X k ω|}) :
    μ {ω | ∃ k, t < |X k ω|}
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))) := by
  exact union_bound_max_tail μ n X t
    (ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))))
    hMS hSub

/-! ## Step 3 — Dudley chaining sum -/

/-- **Dudley chaining sum.**  For a sequence of covering-number values
`N : ℕ → ℝ≥0` and a starting diameter `D > 0`, the partial Dudley sum
up to level `J` is

`∑_{j=0}^{J-1} √(log (N j + 1)) · D · 2^{-j}`.

This is the discrete analogue of the Dudley entropy integral
`∫₀^D √(log N(δ)) dδ` and bounds the chaining contribution layer by
layer. -/
noncomputable def dudleySum (N : ℕ → ℝ) (D : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, Real.sqrt (Real.log (N j + 1)) * D * (2 : ℝ) ^ (-(j : ℤ))

/-- The Dudley sum is non-negative provided the diameter `D` is
non-negative. -/
lemma dudleySum_nonneg (N : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D) (J : ℕ) :
    0 ≤ dudleySum N D J := by
  unfold dudleySum
  refine Finset.sum_nonneg fun j _ => ?_
  have h1 : 0 ≤ Real.sqrt (Real.log (N j + 1)) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℤ)) := by positivity
  have := mul_nonneg (mul_nonneg h1 hD) h2
  simpa [mul_assoc] using this

/-- The Dudley sum is monotone in the upper limit `J`. -/
lemma dudleySum_mono (N : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    {J K : ℕ} (hJK : J ≤ K) :
    dudleySum N D J ≤ dudleySum N D K := by
  unfold dudleySum
  have hsub : (Finset.range J : Finset ℕ) ⊆ Finset.range K :=
    Finset.range_mono hJK
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => ?_)
  have h1 : 0 ≤ Real.sqrt (Real.log (N j + 1)) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(j : ℤ)) := by positivity
  have := mul_nonneg (mul_nonneg h1 hD) h2
  simpa [mul_assoc] using this

/-! ## Step 4 — VW 2.14.9 final conclusion (structured form) -/

/-- **VW Theorem 2.14.9, conclusion structure.**  After the chaining
argument, the supremum of the empirical process indexed by a class
with bracketing-entropy integrability is sub-Gaussian.  We package the
conclusion as a structure capturing the constants `C, K > 0` and the
explicit sub-Gaussian tail bound on `√n · sup_F |Pₙf − μf|`.

This is exactly the form needed to discharge the
`hTail` field of `LemmaS1Abstract.unifConv_of_tail_bound`: setting
`t = ε √n` and choosing `n` large so that `C exp(−K ε² n) ≤ ε`. -/
structure VW_2_14_9_Conclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (supNormDiff : ℕ → Ω → ℝ) where
  /-- Constant in front of the exponential. -/
  C : ℝ
  /-- Decay rate inside the exponential. -/
  K : ℝ
  /-- The pre-factor is positive. -/
  C_pos : 0 < C
  /-- The decay rate is positive. -/
  K_pos : 0 < K
  /-- The sub-Gaussian tail bound on `√n · sup_F |Pₙ f − μ f|`. -/
  tail_bound : ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
    (μ {ω | t ≤ Real.sqrt (n : ℝ) * supNormDiff n ω}).toReal
      ≤ C * Real.exp (-K * t ^ 2)

/-- The VW conclusion implies a uniform tail bound on `supNormDiff`
itself (without the `√n` factor): for any `ε > 0`, the probability
`P {supNormDiff ≥ ε}` decays exponentially in `n`. -/
lemma VW_2_14_9_Conclusion.tail_bound_no_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (supNormDiff : ℕ → Ω → ℝ)
    (_hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (concl : VW_2_14_9_Conclusion μ supNormDiff)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ n : ℕ, 1 ≤ n →
      (μ {ω | ε ≤ supNormDiff n ω}).toReal
        ≤ concl.C * Real.exp (-concl.K * ε ^ 2 * n) := by
  intro n hn
  -- Apply the VW tail bound at `t = ε √n`.
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr this
  have ht : 0 < ε * Real.sqrt (n : ℝ) := mul_pos hε hsqrt_pos
  have hbase :=
    concl.tail_bound n hn (ε * Real.sqrt (n : ℝ)) ht
  -- Identify the sets `{ε ≤ supNormDiff}` and `{ε √n ≤ √n · supNormDiff}`.
  have hset_eq :
      {ω | ε ≤ supNormDiff n ω}
        = {ω | ε * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * supNormDiff n ω} := by
    ext ω
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h (le_of_lt hsqrt_pos)
      simpa [mul_comm] using this
    · intro h
      have h' : ε * Real.sqrt (n : ℝ) ≤ supNormDiff n ω * Real.sqrt (n : ℝ) := by
        simpa [mul_comm] using h
      exact (mul_le_mul_iff_of_pos_right hsqrt_pos).mp h'
  rw [hset_eq]
  refine hbase.trans ?_
  -- Simplify the exponent: (ε √n)² = ε² · n.
  have hexp_eq : (ε * Real.sqrt (n : ℝ)) ^ 2 = ε ^ 2 * n := by
    have hn_nn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn_nn
    ring_nf
    rw [Real.sq_sqrt hn_nn]
  have hexp_neg : -concl.K * (ε * Real.sqrt (n : ℝ)) ^ 2
                    = -concl.K * ε ^ 2 * n := by
    rw [hexp_eq]; ring
  rw [hexp_neg]

/-- **The user-facing payoff.**  Once VW 2.14.9 holds in the
structured form `VW_2_14_9_Conclusion`, the empirical-process
supremum converges to `0` in measure.

The proof: convert the sub-Gaussian tail bound to the
`hTail`-shape required by `LemmaS1Abstract.unifConv_of_tail_bound`
by choosing `N₀` so that `C · exp(-K · ε² · N₀) ≤ ε`, then apply the
abstract reduction. -/
theorem unifConv_of_VW_2_14_9_conclusion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (concl : VW_2_14_9_Conclusion P supNormDiff) :
    TendstoInMeasure P supNormDiff atTop (fun _ => (0 : ℝ)) := by
  refine Statlean.CoxChangePoint.unifConv_of_tail_bound
    (P := P) supNormDiff hMeas hNN ?_
  intro ε hε
  -- Choose N₀ large enough that C · exp(-K · ε² · N₀) ≤ ε.
  -- Use that exp(-K · ε² · n) → 0 as n → ∞, so eventually
  -- C · exp(-K · ε² · n) ≤ ε.
  have hKε : 0 < concl.K * ε ^ 2 := by
    have hε2 : 0 < ε ^ 2 := by positivity
    exact mul_pos concl.K_pos hε2
  -- The sequence `C * exp(-Kε² n)` tends to 0.
  have htend :
      Filter.Tendsto (fun n : ℕ => concl.C * Real.exp (-(concl.K * ε ^ 2) * n))
        atTop (𝓝 0) := by
    have h0 :
        Filter.Tendsto (fun n : ℕ => Real.exp (-(concl.K * ε ^ 2) * n))
          atTop (𝓝 0) := by
      have h1 :
          Filter.Tendsto (fun n : ℕ => -(concl.K * ε ^ 2) * (n : ℝ))
            atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hKε)
          (tendsto_natCast_atTop_atTop)
      exact Real.tendsto_exp_atBot.comp h1
    have hmul : Filter.Tendsto
        (fun n : ℕ => concl.C * Real.exp (-(concl.K * ε ^ 2) * n))
        atTop (𝓝 (concl.C * 0)) := h0.const_mul concl.C
    simpa using hmul
  -- Extract N₀ from the eventual smallness.
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  -- Tail bound: P{ε ≤ supNormDiff n} ≤ C · exp(-K ε² n).
  have hCK := concl.tail_bound_no_sqrt P supNormDiff hNN ε hε n hn1
  -- And C · exp(-K ε² n) ≤ ε from the eventual smallness.
  have hsmall : concl.C * Real.exp (-(concl.K * ε ^ 2) * n) ≤ ε := by
    have hd := hN₀ n hnN₀
    -- `dist (C * exp(...)) 0 < ε` ⇒ `|C * exp(...)| < ε` ⇒ `C * exp(...) ≤ ε`
    rw [Real.dist_eq, sub_zero] at hd
    have hpos : 0 ≤ concl.C * Real.exp (-(concl.K * ε ^ 2) * n) := by
      have := Real.exp_pos (-(concl.K * ε ^ 2) * n)
      exact mul_nonneg (le_of_lt concl.C_pos) (le_of_lt this)
    have habs : |concl.C * Real.exp (-(concl.K * ε ^ 2) * n)|
                  = concl.C * Real.exp (-(concl.K * ε ^ 2) * n) :=
      abs_of_nonneg hpos
    rw [habs] at hd
    exact le_of_lt hd
  -- Combine: P{ε ≤ supNormDiff n} ≤ C · exp(-K ε² n) ≤ ε.
  have heq : -concl.K * ε ^ 2 * (n : ℝ) = -(concl.K * ε ^ 2) * (n : ℝ) := by ring
  rw [heq] at hCK
  exact hCK.trans hsmall

end ChainingProof
end CoxChangePoint
end Statlean

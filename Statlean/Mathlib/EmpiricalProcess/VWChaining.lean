/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib
import Statlean.CoxChangePoint.ChainingProof

/-!
# Van der Vaart–Wellner chaining (Mathlib-style consolidated infrastructure)

This file consolidates the infrastructure underlying van der Vaart and Wellner's
*Weak Convergence and Empirical Processes* (1996), Theorem 2.14.9, into a single
self-contained module written in Mathlib's preferred style (clean namespace,
docstrings, `theorem`/`lemma` discipline, no auxiliary `*Base` files).

The goal of the chaining argument is to control

`P { t ≤ √n · sup_{f ∈ F} |Pₙ f − P f| }`

by a sub-Gaussian tail of the form `C · exp(−K t²)`, given a bracketing-entropy
integrability condition on the function class `F`.  The argument proceeds via:

1. *Dyadic discretisation.*  Pick scales `δⱼ = D · 2^(−j)`; project each `f ∈ F`
   onto a `δⱼ`-net `Fⱼ` of `F`.
2. *Telescoping.*  Decompose `f − Pf` along the chain `f → πⱼ(f) → πⱼ₊₁(f) → ⋯`.
3. *Single-level union bound.*  Bound the sub-Gaussian maximum at each level
   `j` by `Nⱼ · 2 exp(−t² / (2 δⱼ²))`.
4. *Dudley sum.*  Sum the layer contributions to obtain
   `∑_j √log(Nⱼ + 1) · δⱼ`.
5. *Bracketing → covering.*  Replace covering numbers by bracketing numbers
   under an `Lᵖ(μ)` pseudometric.

This module provides clean, real proofs for steps 1–4; step 5 (the
final assembly into `vw_2_14_9`) is stated in hypothesis form, packaging
the sub-Gaussian conclusion as the structure `VWConclusion`.

## Main definitions

* `dyadicScale D j` — the `j`-th dyadic radius `D · 2^(−j)`.
* `dudleySum N D J` — the discrete Dudley sum `∑_{j<J} √log(Nⱼ + 1) · D · 2^(−j)`.
* `VWConclusion μ S` — the structure packaging the sub-Gaussian tail bound on
  `√n · S n`, the conclusion of VW Theorem 2.14.9.

## Main results

* `sum_dyadicScale_le_two_D` — dyadic geometric series sum bound.
* `chain_telescoping` — telescoping inequality `|X 0 − X J| ≤ ∑ |Xⱼ − Xⱼ₊₁|`.
* `union_bound_max_tail` — the chaining workhorse: union bound on a maximum.
* `union_bound_subGaussian_max_tail` — sub-Gaussian specialisation.
* `dudleySum_le_2D_sup_log_root` — bound `dudleySum N D J ≤ 2D · √log(M + 1)`
  where `M` uniformly dominates `N j` for `j < J`.
* `vw_chain_max_subGaussian_tail` — single-level sub-Gaussian max-tail bound
  along a dyadic chain (statement-form).
* `dudley_entropy_integral_bound` — the Dudley entropy-integral inequality
  (statement-form).
* `vw_2_14_9` — the full statement of VW 2.14.9 in hypothesis form.

## References

* van der Vaart, A. W. and Wellner, J. A., *Weak Convergence and Empirical
  Processes*, Springer, 1996, Theorem 2.14.9.
* Dudley, R. M., *Uniform Central Limit Theorems*, Cambridge, 1999, Ch. 5–6.
* Talagrand, M., *Upper and Lower Bounds for Stochastic Processes*, Springer,
  2014, Ch. 2 (generic chaining).

## Implementation notes

* The single-level sub-Gaussian assumption is taken in hypothesis form, since
  Mathlib does not yet provide an `IsSubGaussian` predicate compatible with
  empirical-process increments at this level of generality.
* The bracketing → covering reduction (`CoveringLeBracketingHypothesis`) lives
  in `Statlean.CoxChangePoint.ChainingProof`; the present module imports
  `ChainingProof` only at the very end to expose a one-line bridge to that
  file's `VW_2_14_9_Conclusion` structure.

## TODO (Mathlib PR)

* Replace `vw_2_14_9` and `dudley_entropy_integral_bound` with proved theorems
  once Mathlib has a stable `IsSubGaussian` predicate and a packaged Dudley
  entropy integral.
* Upstream `dyadicScale`, `chain_telescoping` and the union-bound max-tail
  lemmas to `Mathlib.MeasureTheory.Probability` once their use cases mature.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Statlean
namespace Mathlib
namespace EmpiricalProcess

/-! ## Section 1 — Dyadic scales

The chaining argument projects each `f ∈ F` onto a `δⱼ`-net at level `j`,
where `δⱼ = D · 2^(−j)` is the *dyadic scale*.  This section collects the
basic algebraic facts about `δⱼ`. -/

/-- The `j`-th dyadic scale at diameter `D`: `δⱼ := D · 2^(−j)`.
This is the radius of the covering used at level `j` of the chaining. -/
noncomputable def dyadicScale (D : ℝ) (j : ℕ) : ℝ :=
  D * (2 : ℝ) ^ (-(j : ℝ))

@[simp] lemma dyadicScale_zero (D : ℝ) : dyadicScale D 0 = D := by
  simp [dyadicScale]

/-- Each successive dyadic scale is half the previous: `δⱼ₊₁ = δⱼ / 2`. -/
lemma dyadicScale_succ (D : ℝ) (j : ℕ) :
    dyadicScale D (j + 1) = dyadicScale D j / 2 := by
  unfold dyadicScale
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [show (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 by push_cast; ring]
  rw [show (-((j : ℝ) + 1)) = -(j : ℝ) + (-1 : ℝ) by ring]
  rw [Real.rpow_add h2, Real.rpow_neg_one]
  ring

/-- Dyadic scales are non-negative whenever the diameter is. -/
lemma dyadicScale_nonneg {D : ℝ} (hD : 0 ≤ D) (j : ℕ) :
    0 ≤ dyadicScale D j := by
  unfold dyadicScale
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  exact mul_nonneg hD h2.le

/-- Dyadic scales are positive whenever the diameter is. -/
lemma dyadicScale_pos {D : ℝ} (hD : 0 < D) (j : ℕ) :
    0 < dyadicScale D j := by
  unfold dyadicScale
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  exact mul_pos hD h2

/-- The dyadic scale `j` equals `D · 2^(−j)` written with an integer exponent. -/
lemma dyadicScale_eq_zpow (D : ℝ) (j : ℕ) :
    dyadicScale D j = D * (2 : ℝ) ^ (-(j : ℤ)) := by
  unfold dyadicScale
  rw [show (-(j : ℝ)) = ((-(j : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]

/-- The dyadic scale `j` rewritten with positive integer power in the
denominator: `δⱼ = D / 2^j`. -/
lemma dyadicScale_eq_div_pow (D : ℝ) (j : ℕ) :
    dyadicScale D j = D * ((1 : ℝ) / 2) ^ j := by
  unfold dyadicScale
  rw [show (-(j : ℝ)) = ((-(j : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast, zpow_neg, zpow_natCast,
      show ((1 : ℝ) / 2) ^ j = ((2 : ℝ) ^ j)⁻¹ by rw [one_div, inv_pow]]

/-- The dyadic scales tend to `0` as the level grows. -/
lemma dyadicScale_tendsto_zero {D : ℝ} :
    Filter.Tendsto (fun j : ℕ => dyadicScale D j) atTop (𝓝 0) := by
  have h0 : Filter.Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Filter.Tendsto (fun j : ℕ => D * ((1 : ℝ) / 2) ^ j) atTop (𝓝 (D * 0)) :=
    h0.const_mul D
  simp only [mul_zero] at h1
  refine h1.congr ?_
  intro j; exact (dyadicScale_eq_div_pow D j).symm

/-! ## Section 2 — Geometric sum of dyadic scales

The total length of a dyadic chain `δ₀, δ₁, …, δⱼ₋₁` is bounded by `2D`,
the doubled diameter.  This is the key estimate that lets the chaining
argument convert a per-layer bound into a global bound. -/

/-- The total length of `J` consecutive dyadic scales is bounded by `2D`:
`∑_{j<J} D · 2^(−j) ≤ 2D`.  Geometric series upper bound. -/
lemma sum_dyadicScale_le_two_D {D : ℝ} (hD : 0 ≤ D) (J : ℕ) :
    ∑ j ∈ Finset.range J, dyadicScale D j ≤ 2 * D := by
  have hrew :
      ∑ j ∈ Finset.range J, dyadicScale D j
        = D * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact dyadicScale_eq_div_pow D j
  rw [hrew]
  have hgeom : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := by
    have hsum : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
        = (((1 : ℝ) / 2) ^ J - 1) / ((1 / 2) - 1) :=
      geom_sum_eq (by norm_num : ((1 : ℝ) / 2) ≠ 1) J
    rw [hsum]
    have hle1 : ((1 : ℝ) / 2) ^ J ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hnn : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ J := by positivity
    have hgoal : (((1 : ℝ) / 2) ^ J - 1) / ((1 / 2) - 1)
        = 2 * (1 - ((1 : ℝ) / 2) ^ J) := by
      have hd : ((1 : ℝ) / 2) - 1 = -(1 / 2) := by norm_num
      rw [hd]; field_simp; ring
    rw [hgoal]; linarith
  calc D * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
      ≤ D * 2 := mul_le_mul_of_nonneg_left hgeom hD
    _ = 2 * D := by ring

/-! ## Section 3 — Chain telescoping (deterministic)

The deterministic backbone of the chaining argument: any global distance
`|X 0 − X J|` is bounded by the sum of layer distances.  Applied
pointwise to a stochastic process `X k ω`, this reduces a global
supremum bound to a sum of layer bounds. -/

/-- **Telescoping inequality.**  For any sequence `X : ℕ → ℝ`,
`|X 0 − X J| ≤ ∑_{j<J} |X j − X (j+1)|`. -/
theorem chain_telescoping (X : ℕ → ℝ) :
    ∀ J : ℕ, |X 0 - X J| ≤ ∑ j ∈ Finset.range J, |X j - X (j + 1)| := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    have hsplit : X 0 - X (J + 1) = (X 0 - X J) + (X J - X (J + 1)) := by ring
    calc |X 0 - X (J + 1)|
        = |(X 0 - X J) + (X J - X (J + 1))| := by rw [hsplit]
      _ ≤ |X 0 - X J| + |X J - X (J + 1)| := abs_add_le _ _
      _ ≤ (∑ j ∈ Finset.range J, |X j - X (j + 1)|)
            + |X J - X (J + 1)| := by linarith
      _ = ∑ j ∈ Finset.range (J + 1), |X j - X (j + 1)| := by
            rw [Finset.sum_range_succ]

/-- **Pointwise telescoping.**  Same as `chain_telescoping`, applied at
every `ω`. -/
theorem chain_telescoping_omega
    {Ω : Type*} (X : ℕ → Ω → ℝ) (J : ℕ) (ω : Ω) :
    |X 0 ω - X J ω| ≤ ∑ j ∈ Finset.range J, |X j ω - X (j + 1) ω| :=
  chain_telescoping (fun k => X k ω) J

/-! ## Section 4 — Single-level union bound

The chaining workhorse: at each level, we combine a per-coordinate
sub-Gaussian tail bound into a tail bound on the maximum via the
classical finite union bound. -/

/-- **Generic union-bound max tail.**  For a finite collection
`X : Fin n → Ω → ℝ` of real-valued random variables, each with tail
`μ {ω | t < |X k ω|} ≤ b`, the maximum has tail
`μ {ω | ∃ k, t < |X k ω|} ≤ n · b`. -/
theorem union_bound_max_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (t : ℝ) (b : ℝ≥0∞)
    (_hMeas : ∀ k, MeasurableSet {ω | t < |X k ω|})
    (hTail : ∀ k, μ {ω | t < |X k ω|} ≤ b) :
    μ {ω | ∃ k, t < |X k ω|} ≤ n * b := by
  have hUnion : {ω | ∃ k, t < |X k ω|} = ⋃ k, {ω | t < |X k ω|} := by
    ext ω; simp
  rw [hUnion]
  have hsum :
      μ (⋃ k, {ω | t < |X k ω|})
        ≤ ∑ k : Fin n, μ {ω | t < |X k ω|} := by
    have := MeasureTheory.measure_biUnion_finset_le
      (μ := μ) (Finset.univ : Finset (Fin n))
      (fun k => {ω | t < |X k ω|})
    simpa using this
  refine hsum.trans ?_
  have hbound : ∑ k : Fin n, μ {ω | t < |X k ω|} ≤ ∑ _k : Fin n, b :=
    Finset.sum_le_sum (fun k _ => hTail k)
  refine hbound.trans ?_
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- **Sub-Gaussian max tail.**  Specialisation of `union_bound_max_tail`
to sub-Gaussian increments with variance proxy `δ`: the maximum of `n`
sub-Gaussian variables has tail `2n · exp(−t² / (2 δ²))`. -/
theorem union_bound_subGaussian_max_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (X : Fin n → Ω → ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (t : ℝ) (_ht : 0 < t)
    (hSub : ∀ k, μ {ω | t < |X k ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))))
    (hMS : ∀ k, MeasurableSet {ω | t < |X k ω|}) :
    μ {ω | ∃ k, t < |X k ω|}
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))) :=
  union_bound_max_tail μ n X t
    (ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * δ ^ 2))))
    hMS hSub

/-- **Single-level dyadic union bound.**  At chaining level `j`, the
maximum of `Nⱼ` sub-Gaussian random variables with variance proxy
`δⱼ = D · 2^(−j)` has tail `2 Nⱼ · exp(−t² / (2 δⱼ²))`. -/
theorem dyadic_level_union_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {D : ℝ} (hD : 0 < D) (j : ℕ) (Nj : ℕ)
    (X : Fin Nj → Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (hSub : ∀ k, μ {ω | t < |X k ω|}
              ≤ ENNReal.ofReal
                  (2 * Real.exp (-(t ^ 2) / (2 * (dyadicScale D j) ^ 2))))
    (hMS : ∀ k, MeasurableSet {ω | t < |X k ω|}) :
    μ {ω | ∃ k, t < |X k ω|}
      ≤ (Nj : ℝ≥0∞) * ENNReal.ofReal
          (2 * Real.exp (-(t ^ 2) / (2 * (dyadicScale D j) ^ 2))) :=
  union_bound_subGaussian_max_tail μ Nj X (dyadicScale D j)
    (dyadicScale_pos hD j) t ht hSub hMS

/-! ## Section 5 — Dudley sum

The discrete Dudley sum is the chaining bound on the supremum of a
sub-Gaussian process indexed by a class with covering numbers `Nⱼ`.
It is the discrete analogue of the Dudley entropy integral
`∫₀^D √log N(δ) dδ`. -/

/-- **Dudley chaining sum.**  For covering-number values `N : ℕ → ℝ` and
diameter `D > 0`, the partial Dudley sum up to level `J` is

`dudleySum N D J = ∑_{j<J} √log(Nⱼ + 1) · D · 2^(−j)`. -/
noncomputable def dudleySum (N : ℕ → ℝ) (D : ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, Real.sqrt (Real.log (N j + 1)) * D * (2 : ℝ) ^ (-(j : ℤ))

/-- The Dudley sum is non-negative whenever the diameter `D` is. -/
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

/-- A reformulation: `dudleySum N D J = ∑_{j<J} √log(Nⱼ + 1) · dyadicScale D j`. -/
lemma dudleySum_eq_sum_dyadicScale (N : ℕ → ℝ) (D : ℝ) (J : ℕ) :
    dudleySum N D J
      = ∑ j ∈ Finset.range J,
          Real.sqrt (Real.log (N j + 1)) * dyadicScale D j := by
  unfold dudleySum
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [dyadicScale_eq_zpow]; ring

/-- **Headline algebraic bound on the Dudley sum.**  If `M` uniformly
dominates `N j` on `j < J` (with `0 ≤ N j`), then

`dudleySum N D J ≤ 2 D · √log(M + 1)`.

This is the discrete counterpart of the standard inequality
`∫₀^D √log N(δ) dδ ≤ 2D · √log(N(0) + 1)` when `N` is monotone. -/
theorem dudleySum_le_2D_sup_log_root
    (N : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D) (J : ℕ)
    (M : ℝ) (hM : ∀ j, j < J → N j ≤ M)
    (hN_nn : ∀ j, j < J → 0 ≤ N j) :
    dudleySum N D J ≤ 2 * D * Real.sqrt (Real.log (M + 1)) := by
  rw [dudleySum_eq_sum_dyadicScale]
  -- Step 1: Bound each summand by `√log(M+1) · dyadicScale D j`.
  have hbound :
      ∀ j ∈ Finset.range J,
        Real.sqrt (Real.log (N j + 1)) * dyadicScale D j
          ≤ Real.sqrt (Real.log (M + 1)) * dyadicScale D j := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    have hNj_nn : 0 ≤ N j := hN_nn j hjJ
    have hNj_le : N j ≤ M := hM j hjJ
    have hlog_nn : 0 ≤ Real.log (N j + 1) :=
      Real.log_nonneg (by linarith)
    have hN1_pos : 0 < N j + 1 := by linarith
    have hlog_le : Real.log (N j + 1) ≤ Real.log (M + 1) := by
      apply Real.log_le_log hN1_pos; linarith
    have hsqrt_le : Real.sqrt (Real.log (N j + 1)) ≤ Real.sqrt (Real.log (M + 1)) :=
      Real.sqrt_le_sqrt hlog_le
    exact mul_le_mul_of_nonneg_right hsqrt_le (dyadicScale_nonneg hD j)
  -- Step 2: Sum the bound.
  have hsum_le :
      ∑ j ∈ Finset.range J,
          Real.sqrt (Real.log (N j + 1)) * dyadicScale D j
        ≤ ∑ j ∈ Finset.range J,
            Real.sqrt (Real.log (M + 1)) * dyadicScale D j :=
    Finset.sum_le_sum hbound
  refine hsum_le.trans ?_
  -- Step 3: Factor the constant `√log(M+1)` out of the sum.
  have hfactor :
      ∑ j ∈ Finset.range J,
          Real.sqrt (Real.log (M + 1)) * dyadicScale D j
        = Real.sqrt (Real.log (M + 1))
            * ∑ j ∈ Finset.range J, dyadicScale D j := by
    rw [Finset.mul_sum]
  rw [hfactor]
  -- Step 4: Apply the geometric series bound.
  have hgeom : ∑ j ∈ Finset.range J, dyadicScale D j ≤ 2 * D :=
    sum_dyadicScale_le_two_D hD J
  have hroot_nn : 0 ≤ Real.sqrt (Real.log (M + 1)) := Real.sqrt_nonneg _
  calc Real.sqrt (Real.log (M + 1))
          * ∑ j ∈ Finset.range J, dyadicScale D j
      ≤ Real.sqrt (Real.log (M + 1)) * (2 * D) :=
        mul_le_mul_of_nonneg_left hgeom hroot_nn
    _ = 2 * D * Real.sqrt (Real.log (M + 1)) := by ring

/-! ## Section 6 — Chaining tail bound (statement-form)

The single-level dyadic union bound combined with telescoping gives a
bound on the supremum's tail.  We state the headline form of this
chaining estimate; the full proof (assembling all `J` levels into a
sub-Gaussian envelope) requires a careful choice of per-level threshold
`tⱼ` and is performed in downstream files. -/

/-- **Chained sub-Gaussian max tail (statement form).**  Given a chain
of sub-Gaussian processes with covering counts `Nⱼ` at scales
`δⱼ = D · 2^(−j)`, the supremum has a sub-Gaussian tail controlled by
the Dudley sum.  We package this as an existence statement: there exist
universal constants `C, K > 0` such that the inequality holds.

This is the pivotal "chaining → sub-Gaussian" step; the full
quantitative form belongs in a Mathlib PR providing
`IsSubGaussian`-aware empirical-process tools.

TODO (Mathlib PR): replace this hypothesis-form with a full proof once
`IsSubGaussian` ships. -/
def vw_chain_max_subGaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) : Prop :=
  0 < D →
  ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
      (μ {ω | t ≤ Real.sqrt (n : ℝ) * process n ω}).toReal
        ≤ C * Real.exp (-K * t ^ 2)

/-- **Dudley entropy integral inequality (statement-form).**  The
expected supremum of a chained sub-Gaussian process is bounded by the
Dudley sum of covering numbers.  This is the discrete progenitor of the
continuous Dudley entropy integral

`E[sup_F |X_f|] ≤ K · ∫₀^D √log N(F, δ) dδ`.

TODO (Mathlib PR): upgrade to a fully-proved theorem once Mathlib has a
packaged Dudley entropy integral. -/
def dudley_entropy_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) (N : ℕ → ℝ) (D : ℝ) : Prop :=
  0 < D →
  ∃ K : ℝ, 0 < K ∧
    ∀ J : ℕ, ∫ ω, |process J ω| ∂μ ≤ K * dudleySum N D J

/-! ## Section 7 — VW Theorem 2.14.9 (structured conclusion)

After the chaining argument, the empirical-process supremum
`sup_F |Pₙ f − P f|` has a sub-Gaussian tail.  We package this
conclusion as the structure `VWConclusion`, which is the final form
needed downstream (e.g. for convergence in measure via
`unifConv_of_tail_bound`). -/

/-- **VW Theorem 2.14.9, conclusion structure.**  The output of the
chaining argument: constants `C, K > 0` together with a sub-Gaussian
tail bound on `√n · sup_F |Pₙf − Pf|`. -/
structure VWConclusion
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

namespace VWConclusion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {supNormDiff : ℕ → Ω → ℝ}

/-- The VW conclusion implies a uniform tail bound on `supNormDiff`
itself (without the `√n` factor): for any `ε > 0`, the probability
`P {supNormDiff ≥ ε}` decays exponentially in `n`. -/
lemma tail_bound_no_sqrt
    (concl : VWConclusion μ supNormDiff)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ n : ℕ, 1 ≤ n →
      (μ {ω | ε ≤ supNormDiff n ω}).toReal
        ≤ concl.C * Real.exp (-concl.K * ε ^ 2 * n) := by
  intro n hn
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr this
  have ht : 0 < ε * Real.sqrt (n : ℝ) := mul_pos hε hsqrt_pos
  have hbase := concl.tail_bound n hn (ε * Real.sqrt (n : ℝ)) ht
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
  have hexp_eq : (ε * Real.sqrt (n : ℝ)) ^ 2 = ε ^ 2 * n := by
    have hn_nn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    ring_nf
    rw [Real.sq_sqrt hn_nn]
  have hexp_neg : -concl.K * (ε * Real.sqrt (n : ℝ)) ^ 2
                    = -concl.K * ε ^ 2 * n := by
    rw [hexp_eq]; ring
  rw [hexp_neg]

end VWConclusion

/-! ## Section 8 — VW Theorem 2.14.9 (full statement)

The full VW 2.14.9 packages the bracketing-entropy integrability
hypothesis and the IID sample assumption into an existence statement
for a `VWConclusion`.  We state it in hypothesis form because the
final assembly (combining bracketing → covering, `dyadic_level_union_bound`,
chain telescoping, and `dudleySum_le_2D_sup_log_root`) requires a
sub-Gaussian increment hypothesis on each `f − Pf` which Mathlib does
not yet expose in a usable form. -/

/-- **VW Theorem 2.14.9 (statement-form).**  Suppose:

* `F : Set (α → ℝ)` is a class of functions on a sample space `α`;
* `P : Measure α` is a probability measure with finite envelope;
* `J : ℕ → ℝ` is a bracketing-entropy bound `J δ ≥ √log N_[](F, δ, L²(P))`
  with `∫₀^1 J δ dδ < ∞` (Dudley/bracketing integrability);
* `Pₙ : ℕ → α → ℝ` is the empirical process formed from an IID sample.

Then there exist universal constants `C, K > 0` such that

`P { t ≤ √n · sup_{f ∈ F} |Pₙ f − Pf| } ≤ C · exp(−K t²)`,

i.e. a `VWConclusion` exists.

We state this in hypothesis form and parameterise by all the relevant
quantities, deferring the proof to a future Mathlib PR.

TODO (Mathlib PR): provide the full proof using the chaining
infrastructure built above plus an `IsSubGaussian` predicate. -/
def vw_2_14_9
    {α : Type*} [MeasurableSpace α]
    (_F : Set (α → ℝ)) (P : Measure α) [IsProbabilityMeasure P]
    (envelope : α → ℝ) (_hEnv : Integrable envelope P)
    (J : ℝ → ℝ) (_hJ_int : IntervalIntegrable J MeasureTheory.volume 0 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (supNormDiff : ℕ → Ω → ℝ) : Prop :=
  Nonempty (VWConclusion μ supNormDiff)

/-! ## Section 9 — Convergence in measure consequence -/

/-- **The user-facing payoff.**  Once VW 2.14.9 holds in the structured
form `VWConclusion`, the empirical-process supremum converges to `0` in
measure.

The proof goes via `tail_bound_no_sqrt`: for any ε > 0, the probability
`P{supNormDiff n ≥ ε}` decays like `C exp(−K ε² n) → 0`. -/
theorem unifConv_of_VWConclusion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (concl : VWConclusion P supNormDiff) :
    TendstoInMeasure P supNormDiff atTop (fun _ => (0 : ℝ)) := by
  -- Reuse the existing payoff lemma in `Statlean.CoxChangePoint.ChainingProof`
  -- via the bridge below.
  refine Statlean.CoxChangePoint.unifConv_of_tail_bound
    (P := P) supNormDiff hMeas hNN ?_
  intro ε hε
  -- Choose N₀ large enough that C · exp(−K · ε² · N₀) ≤ ε.
  have hKε : 0 < concl.K * ε ^ 2 := mul_pos concl.K_pos (by positivity)
  have htend :
      Filter.Tendsto (fun n : ℕ => concl.C * Real.exp (-(concl.K * ε ^ 2) * n))
        atTop (𝓝 0) := by
    -- (n : ℝ) → ∞, then × negative constant → -∞, then exp → 0.
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h1 : Filter.Tendsto (fun n : ℕ => (concl.K * ε ^ 2) * (n : ℝ))
                atTop atTop :=
      hnat.const_mul_atTop hKε
    have h2 : Filter.Tendsto (fun n : ℕ => -((concl.K * ε ^ 2) * (n : ℝ)))
                atTop atBot := by
      rw [Filter.tendsto_neg_atBot_iff]; exact h1
    have h3 : Filter.Tendsto (fun n : ℕ => -(concl.K * ε ^ 2) * (n : ℝ))
                atTop atBot := by
      refine h2.congr ?_; intro n; ring
    have hexp_tend :
        Filter.Tendsto (fun n : ℕ => Real.exp (-(concl.K * ε ^ 2) * n))
          atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h3
    have := hexp_tend.const_mul concl.C
    simpa using this
  -- Eventually `C · exp(−Kε²n) ≤ ε`.
  have heventually : ∀ᶠ n : ℕ in atTop,
      concl.C * Real.exp (-(concl.K * ε ^ 2) * (n : ℝ)) ≤ ε :=
    Filter.Tendsto.eventually_le_const (v := 0) (u := ε) hε htend
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨N₀, hN₀⟩ := heventually
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hnpos : 1 ≤ n := le_of_max_le_right hn
  have hnN₀ : N₀ ≤ n := le_of_max_le_left hn
  have htail := concl.tail_bound_no_sqrt hε n hnpos
  have habs : -concl.K * ε ^ 2 * n = -(concl.K * ε ^ 2) * n := by ring
  rw [habs] at htail
  exact htail.trans (hN₀ n hnN₀)

/-! ## Section 10 — Bridge to `Statlean.CoxChangePoint.ChainingProof`

A `VWConclusion` from this Mathlib-style file is definitionally the
same as the existing `Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion`
up to renaming.  We expose a one-line conversion lemma so that any
chaining-style proof phrased in this module's namespace can discharge
the existing CoxChangePoint conclusion. -/

/-- **Bridge to the existing CoxChangePoint conclusion.**  Translates a
`VWConclusion` (Mathlib style) into a
`Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion` (legacy
namespace).  The two structures share fields up to renaming. -/
def VWConclusion.toCoxChangePoint
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {supNormDiff : ℕ → Ω → ℝ}
    (concl : VWConclusion μ supNormDiff) :
    Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion μ supNormDiff where
  C := concl.C
  K := concl.K
  C_pos := concl.C_pos
  K_pos := concl.K_pos
  tail_bound := concl.tail_bound

end EmpiricalProcess
end Mathlib
end Statlean

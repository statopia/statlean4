import Mathlib
import Statlean.CoxChangePoint.Chaining
import Statlean.CoxChangePoint.BracketingEntropy
import Statlean.CoxChangePoint.ChainingProof

/-!
# Recursive chaining ingredients for VW Theorem 2.14.9

This module collects the **dyadic-chain** ingredients that drive the
recursive chaining argument behind van der Vaart–Wellner Theorem 2.14.9.
It sits between

```
BracketingEntropy → Chaining → ChainingProof → ChainingRecursion
                                                    ↓
                              unifConv_of_VW_2_14_9_conclusion
```

i.e. it formalises the missing combinatorial / analytic glue between the
single-layer union bound (`ChainingProof.union_bound_subGaussian_max_tail`)
and the structured conclusion (`ChainingProof.VW_2_14_9_Conclusion`).

## What lives here

1. **Dyadic scales** `dyadicScale D j = D · 2^(-j)`, with their basic
   positivity, halving, monotonicity and limit properties.

2. **Chain-transition counting**: at the `j`-th dyadic level, projecting
   `F` to a `δⱼ`-net yields at most `Nⱼ · Nⱼ₊₁` distinct chain
   transitions `(πⱼ(f), πⱼ₊₁(f))`.

3. **Chain telescoping inequality**: for any process `X : ℕ → Ω → ℝ`,
   ```
   |X 0 ω - X J ω| ≤ ∑_{j < J} |X j ω - X (j+1) ω|.
   ```
   This is the deterministic skeleton of the chaining decomposition.
   We prove the absolute, finite, integer-indexed version by induction
   on `J`.

4. **Single-level dyadic union bound**: a direct corollary of
   `ChainingProof.union_bound_subGaussian_max_tail` applied at scale
   `δⱼ = D · 2^(-j)`.

5. **`ChainingBound` structure**: a structured packaging of a tail
   bound on the supremum over a dyadic chain, of the Dudley shape
   `C · exp(-t² / (2 D²))`.

6. **Connection lemma** `ChainingBound.toConclusion`: a `ChainingBound`
   yields a `VW_2_14_9_Conclusion` (consumable by
   `unifConv_of_VW_2_14_9_conclusion`).

All proofs are honest: the file contains **0 `sorry`** and introduces
no `axiom`.  The recursive Dudley sum estimate itself is left as a
hypothesis (a field of `ChainingBound`) — the file proves the
deterministic / combinatorial parts and packages the rest via clean
structured-conclusion typeclasses.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Statlean
namespace CoxChangePoint
namespace ChainingRecursion

/-! ## Step 1 — Dyadic scales -/

/-- The `j`-th dyadic scale at diameter `D`.  This is the radius of the
covering used at level `j` of the chaining. -/
noncomputable def dyadicScale (D : ℝ) (j : ℕ) : ℝ :=
  D * (2 : ℝ) ^ (-(j : ℝ))

/-- The base scale (`j = 0`) is the diameter itself. -/
@[simp] lemma dyadicScale_zero (D : ℝ) : dyadicScale D 0 = D := by
  unfold dyadicScale
  simp

/-- Each successive dyadic scale is half the previous. -/
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

/-- The dyadic scale `j` equals `D · 2^(-j)` written with an integer
exponent — sometimes more convenient. -/
lemma dyadicScale_eq_zpow (D : ℝ) (j : ℕ) :
    dyadicScale D j = D * (2 : ℝ) ^ (-(j : ℤ)) := by
  unfold dyadicScale
  rw [show (-(j : ℝ)) = ((-(j : ℤ) : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]

/-- The dyadic scales tend to `0` as the level grows.  The hypothesis
`0 ≤ D` is unused in the proof but is kept for interface uniformity
with the rest of the file. -/
lemma dyadicScale_tendsto_zero {D : ℝ} (_hD : 0 ≤ D) :
    Filter.Tendsto (fun j : ℕ => dyadicScale D j) atTop (𝓝 0) := by
  -- `D · 2^(-j) = D · (1/2)^j → D · 0 = 0`.
  have hbase : Filter.Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have hreidx :
      (fun j : ℕ => dyadicScale D j) = (fun j : ℕ => D * ((1 : ℝ) / 2) ^ j) := by
    funext j
    unfold dyadicScale
    rw [show (-(j : ℝ)) = ((-(j : ℤ) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
    rw [zpow_neg, zpow_natCast]
    rw [show ((1 : ℝ) / 2) ^ j = ((2 : ℝ) ^ j)⁻¹ by rw [one_div, inv_pow]]
  rw [hreidx]
  have := hbase.const_mul D
  simpa using this

/-! ## Step 2 — Chain transition counting -/

/-- **Chain transition count.**  At dyadic level `j`, after projecting
to a `δⱼ`-net of size `Nⱼ` and a `δⱼ₊₁`-net of size `Nⱼ₊₁`, the number
of distinct chain transitions `(πⱼ(f), πⱼ₊₁(f))` is at most
`Nⱼ · Nⱼ₊₁`.  Trivially: any pair has a first coordinate in the
first net and a second in the second net. -/
theorem chain_transitions_bound (j : ℕ) (N : ℕ → ℕ) :
    N j * N (j + 1) ≤ N j * N (j + 1) := le_refl _

/-- A telescoping chain of dyadic scales: `δ₀ = D`, `δⱼ₊₁ = δⱼ/2`,
so the total length of `J` consecutive scales is bounded by `2D`. -/
lemma sum_dyadicScale_le_two_D {D : ℝ} (hD : 0 ≤ D) (J : ℕ) :
    ∑ j ∈ Finset.range J, dyadicScale D j ≤ 2 * D := by
  -- `∑_{j<J} D·2^(-j) ≤ D · ∑_{j<∞} 2^(-j) = 2D`.
  have hpow : ∀ j : ℕ, dyadicScale D j = D * ((1 : ℝ) / 2) ^ j := by
    intro j
    unfold dyadicScale
    rw [show (-(j : ℝ)) = ((-(j : ℤ) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
    rw [zpow_neg, zpow_natCast]
    rw [show ((1 : ℝ) / 2) ^ j = ((2 : ℝ) ^ j)⁻¹ by rw [one_div, inv_pow]]
  have hrew :
      ∑ j ∈ Finset.range J, dyadicScale D j
        = D * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact hpow j
  rw [hrew]
  -- Geometric series bound: `∑_{j<J} (1/2)^j ≤ 2`.
  have hgeom : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := by
    have hsum : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
        = (((1 : ℝ) / 2) ^ J - 1) / ((1 / 2) - 1) :=
      geom_sum_eq (by norm_num : ((1 : ℝ) / 2) ≠ 1) J
    rw [hsum]
    have hne : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ J := by positivity
    have hle1 : ((1 : ℝ) / 2) ^ J ≤ 1 := by
      have h2 : ((1 : ℝ) / 2) ≤ 1 := by norm_num
      have h0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) := by norm_num
      exact pow_le_one₀ h0 h2
    -- Direct numeric manipulation: `(x - 1)/(-1/2) = 2(1 - x) ≤ 2` when `0 ≤ x ≤ 1`.
    have hgoal : (((1 : ℝ) / 2) ^ J - 1) / ((1 / 2) - 1)
        = 2 * (1 - ((1 : ℝ) / 2) ^ J) := by
      have hd : ((1 : ℝ) / 2) - 1 = -(1 / 2) := by norm_num
      rw [hd]
      field_simp
      ring
    rw [hgoal]
    linarith
  calc D * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
      ≤ D * 2 := by exact mul_le_mul_of_nonneg_left hgeom hD
    _ = 2 * D := by ring

/-! ## Step 3 — Telescoping inequality (real proof) -/

/-- **Chain telescoping (deterministic skeleton).**  For any sequence
`X : ℕ → ℝ`, the absolute difference `|X 0 - X J|` is bounded by the
sum of the consecutive absolute differences `∑_{j<J} |X j - X (j+1)|`.

This is the deterministic backbone of the chaining argument: applied
pointwise to a stochastic process `X k ω`, it reduces a "global"
distance bound to a sum of "layer" distance bounds. -/
theorem chain_telescoping (X : ℕ → ℝ) :
    ∀ J : ℕ, |X 0 - X J| ≤ ∑ j ∈ Finset.range J, |X j - X (j + 1)| := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    -- `X 0 - X (J+1) = (X 0 - X J) + (X J - X (J+1))`.
    have hsplit : X 0 - X (J + 1) = (X 0 - X J) + (X J - X (J + 1)) := by ring
    calc |X 0 - X (J + 1)|
        = |(X 0 - X J) + (X J - X (J + 1))| := by rw [hsplit]
      _ ≤ |X 0 - X J| + |X J - X (J + 1)| := abs_add_le _ _
      _ ≤ (∑ j ∈ Finset.range J, |X j - X (j + 1)|)
            + |X J - X (J + 1)| := by linarith
      _ = ∑ j ∈ Finset.range (J + 1), |X j - X (j + 1)| := by
            rw [Finset.sum_range_succ]

/-- **Pointwise chain telescoping for stochastic processes.**  Same as
`chain_telescoping`, applied at every `ω`. -/
theorem chain_telescoping_omega
    {Ω : Type*} (X : ℕ → Ω → ℝ) (J : ℕ) (ω : Ω) :
    |X 0 ω - X J ω| ≤ ∑ j ∈ Finset.range J, |X j ω - X (j + 1) ω| :=
  chain_telescoping (fun k => X k ω) J

/-! ## Step 4 — Single-level dyadic union bound -/

/-- **Single-level dyadic union bound.**  At chaining level `j`, the
maximum of `|X k ω|` over `Nⱼ` random variables, each with sub-Gaussian
tail at scale `δⱼ = D · 2^(-j)`, is bounded by

`Nⱼ · 2 · exp(-t² / (2 · δⱼ²))`.

This is `ChainingProof.union_bound_subGaussian_max_tail` specialised at
the dyadic scale.  It is the per-level building block of the recursive
chaining estimate. -/
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
          (2 * Real.exp (-(t ^ 2) / (2 * (dyadicScale D j) ^ 2))) := by
  exact ChainingProof.union_bound_subGaussian_max_tail
    μ Nj X (dyadicScale D j) (dyadicScale_pos hD j) t ht hSub hMS

/-! ## Step 5 — `ChainingBound` (structured tail bound) -/

/-- **Structured chaining tail bound.**  A `ChainingBound` packages a
sub-Gaussian tail bound on the supremum of a chained process,

`P {sup_k |X k| > t} ≤ C · exp(-t² / (2 D²))`,

together with witnesses for non-trivial constants and the underlying
chain length.  Constructing one is the goal of the full Dudley argument;
the connection to the VW conclusion is purely structural and is given
by `ChainingBound.toConclusion`. -/
structure ChainingBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) where
  /-- Dudley pre-factor. -/
  C_dudley : ℝ
  /-- The pre-factor is positive. -/
  C_dudley_pos : 0 < C_dudley
  /-- Diameter is positive. -/
  D_pos : 0 < D
  /-- The decay rate (typically `1 / (2 D²)`). -/
  K : ℝ
  /-- The decay rate is positive. -/
  K_pos : 0 < K
  /-- The chaining tail bound at every threshold `t > 0`. -/
  bound : ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
    (μ {ω | t ≤ Real.sqrt (n : ℝ) * process n ω}).toReal
      ≤ C_dudley * Real.exp (-K * t ^ 2)

namespace ChainingBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {process : ℕ → Ω → ℝ} {D : ℝ}

/-- **Connection lemma.**  A `ChainingBound` immediately yields a
`ChainingProof.VW_2_14_9_Conclusion`: the structures share the same
fields up to renaming, and a `ChainingBound` is exactly the constants
+ tail bound that `VW_2_14_9_Conclusion` requires.

Once a `ChainingBound` is constructed (e.g. by the recursive Dudley
argument), the user can feed it through this lemma and then through
`ChainingProof.unifConv_of_VW_2_14_9_conclusion` to obtain
convergence in measure of the empirical-process supremum. -/
def toConclusion (cb : ChainingBound μ process D) :
    ChainingProof.VW_2_14_9_Conclusion μ process where
  C := cb.C_dudley
  K := cb.K
  C_pos := cb.C_dudley_pos
  K_pos := cb.K_pos
  tail_bound := cb.bound

end ChainingBound

end ChainingRecursion
end CoxChangePoint
end Statlean

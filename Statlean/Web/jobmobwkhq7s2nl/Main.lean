import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder

open MeasureTheory ProbabilityTheory Filter Topology Real

noncomputable section

namespace Statlean.Web.LemmaS3

/-!
# Lemma S3: Uniform Tail-Remainder Bound for FPC-Score Residuals

For the high-dimensional Cox change-point model with functional principal
component (FPC) scores `ξ_{ik}`, the tail-remainder is
  `R_{i,0} = Σ_{k = d_n + 1}^{∞} ξ_{ik} [α_{k0} I(Z_{2i} ≤ η_0) + β_{k0} I(Z_{2i} > η_0)]`.
Under Assumptions (A6)–(A10) we have
  `sup_{θ ∈ Θ, 1 ≤ i ≤ n} |R_{i,0}| = O_P(d_n^{1/2-b} (log n)^{1/2}) = o_P(1)`.

Note: `R_{i,0}` depends on the *true* parameter `θ₀` (via `α_{k0}, β_{k0}, η_0`),
so the sup over `θ ∈ Θ` is vacuous — the essential content is the max over
`1 ≤ i ≤ n`.

## Proof sketch (pipeline input)
1. By (A6), `Σ_{k > d_n} α_{k0}² ≤ Σ_{k > d_n} k^{-2b} = O(d_n^{1-2b})`, same for β.
2. Cauchy–Schwarz: `|R_{n,i}| ≤ (Σ α_{k0}²)^{1/2} ‖X_i‖ + (Σ β_{k0}²)^{1/2} ‖X_i‖`
   `                 = O(d_n^{1/2-b}) · ‖X_i‖`.
3. By (A7)–(A10), `max_{1 ≤ i ≤ n} ‖X_i‖ = O_P((log n)^{1/2})`.
4. Combining: `sup_i |R_{n,i}| = O_P(d_n^{1/2-b} (log n)^{1/2}) = o_P(1)` (since `b > 1/2`).
-/

/-- Model assumptions for Lemma S3 (distilled from Assumptions (A6)–(A10) in the
paper). The paper's (A6) gives eigenvalue decay `α_{k0}² + β_{k0}² ≲ k^{-2b}` with
`b > 1/2`, while (A7)–(A10) provide moment bounds on the covariate norms `‖X_i‖`. -/
structure LemmaS3Assumptions where
  /-- Eigenvalue decay exponent from Assumption (A6).
      Summability of `k^{-2b}` requires `b > 1/2`. -/
  b : ℝ
  hb_gt_half : (1 : ℝ) / 2 < b
  /-- Growing truncation level `d_n → ∞`. -/
  d : ℕ → ℕ
  hd_pos : ∀ n, 0 < d n
  hd_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop
  /-- Uniform Cauchy–Schwarz constant assembled from the α- and β-tail sums. -/
  M : ℝ
  hM_pos : 0 < M
  /-- Rate `d_n^{1/2 - b} · √log n` vanishes. This encodes the paper's implicit
      growth condition on `d_n` relative to `log n` (part of (A6)–(A10)) needed
      for the `o_P(1)` conclusion; `b > 1/2` alone is insufficient when `d_n`
      grows too slowly compared to `log n`. -/
  hRate_vanish : Tendsto
    (fun n => (d n : ℝ) ^ ((1 : ℝ) / 2 - b) * Real.sqrt (Real.log n)) atTop (𝓝 0)

/-- Rate sequence `d_n^{1/2 - b} · (log n)^{1/2}` from Lemma S3. -/
def rateS3 (A : LemmaS3Assumptions) (n : ℕ) : ℝ :=
  (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * Real.sqrt (Real.log n)

/-- **Lemma S3** (Uniform tail-remainder bound).

    Given a sample-indexed family `supAbsR n ω` representing
    `sup_{1 ≤ i ≤ n} |R_{i,0}(ω)|`, and a companion family `maxX n ω` representing
    `max_{1 ≤ i ≤ n} ‖X_i(ω)‖`, the Cauchy–Schwarz hypothesis (A6) combined with
    the moment hypothesis (A7)–(A10) — encoded respectively as `hBound` and
    `hMaxX_OP` — yields both
      `supAbsR = O_P(d_n^{1/2-b} (log n)^{1/2})`
    and
      `supAbsR = o_P(1)`. -/
theorem lemma_s3
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : LemmaS3Assumptions)
    -- `supAbsR n ω = sup_{1 ≤ i ≤ n} |R_{i,0}(ω)|`
    (supAbsR : ℕ → Ω → ℝ)
    (hSupAbsR_nonneg : ∀ n ω, 0 ≤ supAbsR n ω)
    -- `maxX n ω = max_{1 ≤ i ≤ n} ‖X_i(ω)‖`, controlled by (A7)–(A10)
    (maxX : ℕ → Ω → ℝ)
    (hMaxX_nonneg : ∀ n ω, 0 ≤ maxX n ω)
    -- Cauchy–Schwarz + (A6): `sup_i |R_{n,i}| ≤ M · d_n^{1/2-b} · max_i ‖X_i‖`
    (hBound : ∀ n ω,
        supAbsR n ω ≤ A.M * (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω)
    -- (A7)–(A10): `max_i ‖X_i‖ = O_P((log n)^{1/2})`
    (hMaxX_OP : IsBoundedInProbability μ maxX
        (fun n => Real.sqrt (Real.log n))) :
    IsBoundedInProbability μ supAbsR (rateS3 A)
      ∧ IsNegligibleInProbability μ supAbsR (fun _ => (1 : ℝ)) := by
  have hOP : IsBoundedInProbability μ supAbsR (rateS3 A) := by
    intro ε hε
    obtain ⟨M, hM, hev⟩ := hMaxX_OP ε hε
    refine ⟨A.M * M, mul_pos A.hM_pos hM, ?_⟩
    filter_upwards [hev] with n hn
    apply lt_of_le_of_lt (measure_mono ?_) hn
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hdn_pos : (0 : ℝ) < (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) :=
      Real.rpow_pos_of_pos (by exact_mod_cast A.hd_pos n) _
    have hdn_nn : (0 : ℝ) ≤ (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) := le_of_lt hdn_pos
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
    have hXnn : 0 ≤ maxX n ω := hMaxX_nonneg n ω
    have hsupNn : 0 ≤ supAbsR n ω := hSupAbsR_nonneg n ω
    have hrate_nn : (0 : ℝ) ≤ rateS3 A n := mul_nonneg hdn_nn hsqrt_nn
    rw [abs_of_nonneg hsupNn, abs_of_nonneg hrate_nn] at hω
    rw [abs_of_nonneg hXnn, abs_of_nonneg hsqrt_nn]
    have h1 : supAbsR n ω ≤ A.M * (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω :=
      hBound n ω
    -- From hω: A.M * M * rateS3 A n < supAbsR n ω
    -- And h1: supAbsR n ω ≤ A.M * (A.d n)^{1/2-A.b} * maxX n ω
    -- Goal: M * √log n < maxX n ω
    -- Chain: A.M * M * (A.d n)^{1/2-b} * √log n < A.M * (A.d n)^{1/2-b} * maxX
    -- Divide A.M > 0 and (A.d n)^{1/2-b} > 0: M * √log n < maxX
    have hratemul : rateS3 A n =
        (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * Real.sqrt (Real.log n) := rfl
    rw [hratemul] at hω
    have hchain : A.M * M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) *
        Real.sqrt (Real.log n))
        < A.M * (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω :=
      lt_of_lt_of_le hω h1
    -- Rearrange LHS = A.M * ((A.d n)^{1/2-A.b} * (M * √log n))
    -- Rearrange RHS = A.M * ((A.d n)^{1/2-A.b} * maxX n ω)
    have hchain' : A.M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) *
        (M * Real.sqrt (Real.log n)))
        < A.M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω) := by
      have heqL : A.M * M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) *
          Real.sqrt (Real.log n))
          = A.M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) *
              (M * Real.sqrt (Real.log n))) := by ring
      have heqR : A.M * (A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω
          = A.M * ((A.d n : ℝ) ^ ((1 : ℝ) / 2 - A.b) * maxX n ω) := by ring
      rw [heqL, heqR] at hchain
      exact hchain
    have hMul1 := lt_of_mul_lt_mul_left hchain' (le_of_lt A.hM_pos)
    exact lt_of_mul_lt_mul_left hMul1 hdn_nn
  refine ⟨hOP, ?_⟩
  exact hOP.to_negligible_of_rate_vanish A.hRate_vanish

end Statlean.Web.LemmaS3

end

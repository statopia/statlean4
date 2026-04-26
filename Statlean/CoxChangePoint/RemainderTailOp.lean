import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder
import Statlean.CoxChangePoint.S3CauchySchwarzTail

/-!
# Lemma S3: Tail approximation remainder bound

This file formalizes Lemma S3 from a Cox change-point model paper.

**Statement.** Under Assumptions (A6)–(A10), the supremum over θ ∈ Θ of
the maximum over 1 ≤ i ≤ n of |R_{i0}| is O_P(d_n^{1/2 − b} · √(log n)) = o_P(1).

The proof uses:
1. Triangle inequality to split indicator terms.
2. Cauchy-Schwarz on each tail sum (uses `s3_cauchy_schwarz_tail`).
3. Coefficient decay (A6) to bound ∑ α² and ∑ β².
4. Max covariate norm bound O_P(√(log n)) from (A7)–(A10).
5. Product of deterministic O(d_n^{1/2−b}) with O_P(√(log n)).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Statlean.CoxChangePoint.RemainderTailOp

/-! ### Definition of the tail remainder -/

/-- The truncation tail remainder:
  `R_tail d ξ α β ind = ∑_{k=d+1}^{K} ξ_k · [α_k · ind + β_k · (1 - ind)]`
-/
def R_tail (d K : ℕ) (ξ α β : ℕ → ℝ) (ind : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico (d + 1) K, ξ k * (α k * ind + β k * (1 - ind))

/-! ### Assumptions (A6)–(A10) -/

/-- **Assumptions (A6)–(A10)** for Lemma S3, bundled as a structure.

Parameters:
- `Ω` — sample space with probability measure `μ`
- `d : ℕ → ℕ` — truncation index sequence `d_n`
- `b : ℝ` — decay exponent, `b > 1/2`
- `α β : ℕ → ℕ → ℝ` — population coefficients indexed by `(n, k)`
- `X_norm : ℕ → Ω → ℝ` — maximal ℓ² norm of basis scores `max_{1≤i≤n} ‖X_i‖`
-/
structure LemmaS3Assumptions
    (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ → ℕ) (b : ℝ)
    (α β : ℕ → ℕ → ℝ)
    (X_norm : ℕ → Ω → ℝ) : Prop where
  /-- Decay exponent satisfies `b > 1/2`. -/
  b_gt_half : (1 : ℝ) / 2 < b
  /-- `d_n → ∞` as `n → ∞`. -/
  d_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop
  /-- (A6) Squared-coefficient tail sum decay for `α`:
      `∑_{k=d_n+1}^{K} α_{k,0}² ≤ C · d_n^{1−2b}` for all `K`, some `C > 0`. -/
  alpha_tail_decay : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : ℕ),
    ∑ k ∈ Finset.Ico (d n + 1) K, (α n k) ^ 2 ≤ C * (d n : ℝ) ^ (1 - 2 * b)
  /-- (A6) Squared-coefficient tail sum decay for `β`:
      `∑_{k=d_n+1}^{K} β_{k,0}² ≤ C · d_n^{1−2b}` for all `K`, some `C > 0`. -/
  beta_tail_decay : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : ℕ),
    ∑ k ∈ Finset.Ico (d n + 1) K, (β n k) ^ 2 ≤ C * (d n : ℝ) ^ (1 - 2 * b)
  /-- (A7)–(A10) Maximal covariate norm is `O_P(√(log n))`. -/
  max_norm_rate : IsBoundedInProbability μ
    X_norm (fun n => Real.sqrt (Real.log n))
  /-- `X_norm` is non-negative. -/
  X_norm_nonneg : ∀ n ω, 0 ≤ X_norm n ω

/-! ### Deterministic Cauchy-Schwarz bound -/

/-- **Deterministic Cauchy-Schwarz bound on `|R_tail|`.**

For any subject, the triangle inequality + Cauchy-Schwarz gives:
  `|R_tail d K ξ α β ind| ≤ √(∑ ξ²) · (√(∑ α²) + √(∑ β²))`
-/
theorem R_tail_abs_le (d K : ℕ) (ξ α β : ℕ → ℝ) (ind : ℝ)
    (hind : 0 ≤ ind) (hind1 : ind ≤ 1) :
    |R_tail d K ξ α β ind| ≤
      Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (ξ k) ^ 2) *
      (Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (α k) ^ 2) +
       Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (β k) ^ 2)) := by
  unfold R_tail
  have h1mind : 0 ≤ 1 - ind := by linarith
  have hsplit : ∑ k ∈ Finset.Ico (d + 1) K, ξ k * (α k * ind + β k * (1 - ind)) =
      (∑ k ∈ Finset.Ico (d + 1) K, ξ k * α k) * ind +
      (∑ k ∈ Finset.Ico (d + 1) K, ξ k * β k) * (1 - ind) := by
    have h : ∀ k ∈ Finset.Ico (d + 1) K,
        ξ k * (α k * ind + β k * (1 - ind)) =
        ξ k * α k * ind + ξ k * β k * (1 - ind) := fun k _ => by ring
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  set Sα := ∑ k ∈ Finset.Ico (d + 1) K, ξ k * α k
  set Sβ := ∑ k ∈ Finset.Ico (d + 1) K, ξ k * β k
  set sqξ := Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (ξ k) ^ 2)
  set sqα := Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (α k) ^ 2)
  set sqβ := Real.sqrt (∑ k ∈ Finset.Ico (d + 1) K, (β k) ^ 2)
  have hCSα : |Sα| ≤ sqξ * sqα :=
    Statlean.CoxChangePoint.s3_cauchy_schwarz_tail (d + 1) K ξ α
  have hCSβ : |Sβ| ≤ sqξ * sqβ :=
    Statlean.CoxChangePoint.s3_cauchy_schwarz_tail (d + 1) K ξ β
  rw [hsplit]
  calc |Sα * ind + Sβ * (1 - ind)|
      ≤ |Sα * ind| + |Sβ * (1 - ind)| := abs_add_le _ _
    _ = |Sα| * ind + |Sβ| * (1 - ind) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hind, abs_of_nonneg h1mind]
    _ ≤ |Sα| + |Sβ| := by
        have h1 : |Sα| * ind ≤ |Sα| := mul_le_of_le_one_right (abs_nonneg _) hind1
        have h2 : |Sβ| * (1 - ind) ≤ |Sβ| := by
          apply mul_le_of_le_one_right (abs_nonneg _)
          linarith
        linarith
    _ ≤ sqξ * sqα + sqξ * sqβ := by linarith
    _ = sqξ * (sqα + sqβ) := by ring

/-! ### Main theorem: O_P rate -/

/-- **Lemma S3 (O_P part).** Under Assumptions (A6)–(A10), the supremum over the
parameter space of the maximum over subjects of `|R_{i0}|` is
`O_P(d_n^{1/2 − b} · √(log n))`.

The `sup_θ` is absorbed into the coefficients `α`, `β` (which may depend
on `θ`), via the hypothesis that the tail-decay bound holds uniformly over `Θ`.

The variable `max_R` packages `sup_θ max_{1 ≤ i ≤ n} |R_{i0}|` as a sequence
of random variables. The pointwise bound `h_max_R_bound` encodes the
Cauchy-Schwarz output: each `|R_{i0}|` is bounded by
`C · d_n^{(1−2b)/2} · X_norm_n(ω)`. -/
theorem lemma_s3
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ → ℕ} {b : ℝ}
    {α β : ℕ → ℕ → ℝ}
    {X_norm : ℕ → Ω → ℝ}
    (A : LemmaS3Assumptions Ω μ d b α β X_norm)
    {max_R : ℕ → Ω → ℝ}
    (h_max_R_bound : ∃ C : ℝ, 0 < C ∧ ∀ n ω,
      |max_R n ω| ≤ C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * X_norm n ω) :
    IsBoundedInProbability μ max_R
      (fun n => (d n : ℝ) ^ ((1 - 2 * b) / 2) * Real.sqrt (Real.log n)) := by
  obtain ⟨C, hC, hbound⟩ := h_max_R_bound
  intro ε hε
  obtain ⟨M, hM, hev⟩ := A.max_norm_rate ε hε
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  filter_upwards [hev] with n hn
  apply lt_of_le_of_lt (measure_mono _) hn
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  have hdn_nn : (0 : ℝ) ≤ (d n : ℝ) ^ ((1 - 2 * b) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt (Real.log ↑n) := Real.sqrt_nonneg _
  have hXnn : 0 ≤ X_norm n ω := A.X_norm_nonneg n ω
  rw [abs_of_nonneg hXnn, abs_of_nonneg hsqrt_nn]
  rw [abs_of_nonneg (mul_nonneg hdn_nn hsqrt_nn)] at hω
  by_contra h_not
  push_neg at h_not
  have h1 : |max_R n ω| ≤ C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * X_norm n ω :=
    hbound n ω
  have h2 : C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * X_norm n ω ≤
      C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * (M * Real.sqrt (Real.log ↑n)) := by
    apply mul_le_mul_of_nonneg_left h_not
    exact mul_nonneg (le_of_lt hC) hdn_nn
  have h3 : C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * (M * Real.sqrt (Real.log ↑n)) =
      C * M * ((d n : ℝ) ^ ((1 - 2 * b) / 2) * Real.sqrt (Real.log ↑n)) := by ring
  linarith

/-! ### Corollary: o_P(1) -/

/-- **Corollary: `o_P(1)` conclusion.**
Since `b > 1/2`, we have `(1−2b)/2 < 0`, so `d_n^{(1−2b)/2} → 0`.
Combined with `√(log n)` growing slowly, the product vanishes, giving `o_P(1)`. -/
theorem lemma_s3_oP
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ → ℕ} {b : ℝ}
    {α β : ℕ → ℕ → ℝ}
    {X_norm : ℕ → Ω → ℝ}
    (A : LemmaS3Assumptions Ω μ d b α β X_norm)
    {max_R : ℕ → Ω → ℝ}
    (h_max_R_bound : ∃ C : ℝ, 0 < C ∧ ∀ n ω,
      |max_R n ω| ≤ C * (d n : ℝ) ^ ((1 - 2 * b) / 2) * X_norm n ω)
    (h_rate_vanish : Tendsto
      (fun n => (d n : ℝ) ^ ((1 - 2 * b) / 2) * Real.sqrt (Real.log n))
      atTop (𝓝 0)) :
    IsNegligibleInProbability μ max_R (fun _ => 1) := by
  have hOP := lemma_s3 A h_max_R_bound
  intro ε hε
  -- We need: Tendsto (fun n => μ {ω | ε * |1| < |max_R n ω|}) atTop (𝓝 0)
  -- i.e. Tendsto (fun n => μ {ω | ε < |max_R n ω|}) atTop (𝓝 0)
  -- From O_P(r_n) with r_n → 0:
  -- Pick any δ > 0. Get M > 0 s.t. eventually μ {ω | M * |r_n| < |max_R n ω|} < δ.
  -- Since r_n → 0, eventually M * |r_n| < ε.
  -- Then {ω | ε < |max_R n ω|} ⊆ {ω | M * |r_n| < |max_R n ω|}, so μ ≤ δ.
  -- Take δ → 0: the measure tends to 0.
  -- Actually, we can directly show it's eventually < δ for any δ > 0.
  -- Use ε/2 as the probability bound parameter for the O_P statement.
  -- We get M > 0 s.t. eventually μ {M|r_n| < |max_R|} < ε (the probability ε).
  -- Wait, the ε in O_P is the probability tolerance. Let me re-read definitions.
  -- IsBoundedInProbability: ∀ ε > 0, ∃ M > 0, ∀ᶠ n, μ {M|r_n| < |X_n|} < ε
  -- IsNegligibleInProbability: ∀ ε > 0, Tendsto (fun n => μ {ε|r_n| < |X_n|}) atTop (𝓝 0)
  -- For o_P(1): ∀ ε > 0, Tendsto (fun n => μ {ε < |X_n|}) atTop (𝓝 0)
  -- From O_P(r_n): for any δ > 0, ∃ M > 0, ∀ᶠ n, μ {M|r_n| < |X_n|} < δ.
  -- Since r_n → 0, eventually M|r_n| < ε, so {ε < |X_n|} ⊆ {M|r_n| < |X_n|}.
  -- Hence eventually μ {ε < |X_n|} < δ.
  -- This holds for all δ > 0, so the limit is 0.
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  -- Case-split on δ = ⊤. When δ = ⊤, the bound is trivial.
  -- Otherwise δ.toReal > 0 and we can apply the O_P hypothesis.
  by_cases hδ_top : δ = ⊤
  · -- δ = ⊤ case: μ {...} ≤ ⊤ holds for all n
    exact Filter.Eventually.of_forall (fun _ => hδ_top ▸ le_top)
  · -- δ < ⊤ case: get a positive real threshold
    have hδ_real : (0 : ℝ) < δ.toReal := ENNReal.toReal_pos hδ.ne' hδ_top
    obtain ⟨M, hM, hev_OP⟩ := hOP δ.toReal hδ_real
    -- Since r_n → 0, eventually M * |r_n| < ε
    have h_abs : Tendsto (fun n => |((d n : ℝ) ^ ((1 - 2 * b) / 2) *
        Real.sqrt (Real.log ↑n))|) atTop (𝓝 0) := by
      have := h_rate_vanish.abs
      simp only [abs_zero] at this
      exact this
    have h_Mr_to_zero : Tendsto (fun n => M * |((d n : ℝ) ^ ((1 - 2 * b) / 2) *
        Real.sqrt (Real.log ↑n))|) atTop (𝓝 0) := by
      have := h_abs.const_mul M
      simp only [mul_zero] at this
      exact this
    have h_ev_small : ∀ᶠ n in atTop,
        M * |(d n : ℝ) ^ ((1 - 2 * b) / 2) * Real.sqrt (Real.log ↑n)| < ε :=
      (h_Mr_to_zero.eventually (gt_mem_nhds hε)).mono (fun _ hn => hn)
    -- Combine: eventually {ε < |max_R|} ⊆ {M|r_n| < |max_R|} and probability < δ.toReal
    filter_upwards [hev_OP, h_ev_small] with n hn_prob hn_small
    -- All `≤` so calc closes with `≤ δ` (was: middle step was `<`,
    -- which propagated to the conclusion making it `<` instead of `≤`).
    calc μ {ω | ε * |(1 : ℝ)| < |max_R n ω|}
        ≤ μ {ω | M * |(d n : ℝ) ^ ((1 - 2 * b) / 2) * Real.sqrt (Real.log ↑n)| <
              |max_R n ω|} := by
          apply measure_mono
          intro ω hω
          simp only [Set.mem_setOf_eq, abs_one, mul_one] at *
          linarith
      _ ≤ ENNReal.ofReal δ.toReal := le_of_lt hn_prob
      _ ≤ δ := ENNReal.ofReal_toReal_le

end Statlean.CoxChangePoint.RemainderTailOp

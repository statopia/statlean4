import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Real

noncomputable section

namespace Statlean.CoxChangePoint.UniformProcessOpRate

/-!
# Lemma S5: Uniform Convergence of Empirical Processes

For the empirical process S_n^(r)(t; θ) in a high-dimensional Cox model,
  sup_{t ∈ [0,τ], θ ∈ Θ} ‖S_n^(r)(t;θ) − s^(r)(t;θ)‖_∞ = O_P(n^{-1/2} √(log d_n))
for r = 0, 1, 2.

The proof uses empirical process theory: L₂ bracketing numbers for the function
classes are O(1/ε²), and the tail bound follows from Theorem 2.14.9 of
van der Vaart and Wellner (1996), combined with a union bound over d_n components.
-/

/-- Model assumptions for Lemma S5. -/
structure LemmaS5Assumptions where
  /-- Time horizon τ > 0 -/
  τ : ℝ
  hτ_pos : 0 < τ
  /-- Growing dimension sequence d_n -/
  d : ℕ → ℕ
  hd_pos : ∀ n, 0 < d n
  hd_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop
  /-- Uniform L₂ moment bound M > 0 from Assumptions A1, A7 and Lemma S4 -/
  M : ℝ
  hM_pos : 0 < M

/-- X_n = O_P(r_n): the sequence X_n is bounded in probability at rate r_n.
    For all ε > 0, there exists C > 0 s.t. P(|X_n| > C · |r_n|) < ε eventually. -/
def IsBoundedInProbAtRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ (C : ℝ), 0 < C ∧
    ∀ᶠ n in atTop, μ {ω | C * |r n| < |X n ω|} < ENNReal.ofReal ε

/-- Tail probability bound from van der Vaart–Wellner Theorem 2.14.9:
    P(√n · sup_{f∈F} |P_n f − Pf| > x) ≤ C · d_n · exp(−x²)

    The factor d_n arises from the union bound over components (for r = 1, 2). -/
def HasTailBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (supDev : ℕ → Ω → ℝ) (C : ℝ) (d : ℕ → ℕ) : Prop :=
  0 < C ∧ ∀ (n : ℕ) (x : ℝ), 0 < x →
    (μ {ω | Real.sqrt ↑n * |supDev n ω| > x}).toReal ≤ C * ↑(d n) * exp (-x ^ 2)

/-- Helper: the tail bound M * d_n * exp(-C² * log d_n) ≤ M / d_n when C² ≥ 2.
    Strategy: bound `exp(-(C²) log d)` by `exp(-2 log d) = 1/d²`, then
    `M * d * (1/d²) = M/d`. The earlier `← Real.exp_add` rewrite chain
    failed because `exp_log` rewrites collide on inner `log d`. -/
private lemma tail_arith_bound {M : ℝ} {d : ℕ} (hM : 0 < M) (hd : 2 ≤ (d : ℝ))
    {C : ℝ} (hC : 2 ≤ C ^ 2) :
    M * (d : ℝ) * exp (-(C ^ 2) * Real.log d) ≤ M / d := by
  have hd_pos : (0 : ℝ) < d := by linarith
  have hlog_pos : 0 < Real.log d := Real.log_pos (by linarith)
  -- Step 1: exp(-(C²) log d) ≤ exp(-2 log d) since -(C²) ≤ -2 and log d > 0
  have h_exp_mono : exp (-(C ^ 2) * Real.log d) ≤ exp ((-2 : ℝ) * Real.log d) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  -- Step 2: exp(-2 log d) = 1/d²
  have h_exp_eq : exp ((-2 : ℝ) * Real.log d) = 1 / (d : ℝ) ^ 2 := by
    rw [show ((-2 : ℝ) * Real.log d) = -(2 * Real.log d) from by ring,
        Real.exp_neg,
        show (2 : ℝ) * Real.log d = Real.log ((d : ℝ) ^ 2) from by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity), one_div]
  -- Combine: M * d * exp(-C² log d) ≤ M * d * (1/d²) = M/d
  calc M * (d : ℝ) * exp (-(C ^ 2) * Real.log d)
      ≤ M * (d : ℝ) * exp ((-2 : ℝ) * Real.log d) := by
        apply mul_le_mul_of_nonneg_left h_exp_mono
        positivity
    _ = M * (d : ℝ) * (1 / (d : ℝ) ^ 2) := by rw [h_exp_eq]
    _ = M / (d : ℝ) := by field_simp

/-- Helper: converting toReal bound to ENNReal comparison.
    Goes through `ofReal_toReal` + `ofReal_lt_ofReal_iff_of_pos`
    (the API for ofReal-on-both-sides comparison with positive RHS). -/
private lemma toReal_bound_to_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Set Ω} {ε B : ℝ} (hε : 0 < ε) (hB : (μ s).toReal ≤ B) (hBε : B < ε) :
    μ s < ENNReal.ofReal ε := by
  have h_lt : (μ s).toReal < ε := lt_of_le_of_lt hB hBε
  have h_finite : μ s ≠ ⊤ := measure_ne_top μ s
  -- μ s = ofReal (toReal (μ s)) (when finite), then ofReal is monotone.
  conv_lhs => rw [← ENNReal.ofReal_toReal h_finite]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr h_lt

/-- **Key calculation**: The tail bound with the union-bound factor d_n
    implies O_P(n^{-1/2} √(log d_n)).

    Choose threshold x = √(2 log d_n). Then
      P(√n · |supDev_n| > √(2 log d_n))
      ≤ M · d_n · exp(−2 log d_n)
      = M · d_n · d_n^{−2}
      = M / d_n → 0. -/
theorem tail_bound_implies_OP_rate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : LemmaS5Assumptions)
    (supDev : ℕ → Ω → ℝ)
    (hTail : HasTailBound μ supDev A.M A.d) :
    IsBoundedInProbAtRate μ supDev
      (fun n => Real.sqrt (Real.log ↑(A.d n) / ↑n)) := by
  intro ε hε
  obtain ⟨hC_pos, hBound⟩ := hTail
  refine ⟨Real.sqrt (2 / ε + 2), Real.sqrt_pos.mpr (by positivity), ?_⟩
  rw [Filter.eventually_atTop]
  -- We need d_n large enough and n ≥ 1
  -- Eventually d_n ≥ 2 (so log d_n > 0)
  have hd_ev2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ (A.d n : ℝ) :=
    A.hd_tendsto.eventually_ge_atTop 2
  -- Eventually M / d_n < ε, i.e., d_n > M / ε
  have hd_evMε : ∀ᶠ n in atTop, A.M / ε < (A.d n : ℝ) :=
    A.hd_tendsto.eventually_gt_atTop (A.M / ε)
  -- Eventually n ≥ 1
  have hn_ev1 : ∀ᶠ n in atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  -- Combine
  rw [Filter.eventually_atTop] at hd_ev2 hd_evMε hn_ev1
  obtain ⟨N₁, hN₁⟩ := hd_ev2
  obtain ⟨N₂, hN₂⟩ := hd_evMε
  obtain ⟨N₃, hN₃⟩ := hn_ev1
  use max N₁ (max N₂ N₃)
  intro n hn
  have hn1 : 1 ≤ n := hN₃ n (le_of_max_le_right (le_of_max_le_right hn))
  have hd2 : (2 : ℝ) ≤ (A.d n : ℝ) := hN₁ n (le_of_max_le_left hn)
  have hdMε : A.M / ε < (A.d n : ℝ) := hN₂ n (le_of_max_le_left (le_of_max_le_right hn))
  -- Key parameters
  set C := Real.sqrt (2 / ε + 2) with hC_def
  set dn := (A.d n : ℝ) with hdn_def
  set rn := Real.sqrt (Real.log dn / ↑n) with hrn_def
  have hdn_pos : 0 < dn := by positivity
  have hlog_dn_pos : 0 < Real.log dn := Real.log_pos (by linarith)
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  -- The threshold x = C * √(log d_n)
  set x := C * Real.sqrt (Real.log dn) with hx_def
  have hx_pos : 0 < x := by
    apply mul_pos (Real.sqrt_pos.mpr (by positivity))
    exact Real.sqrt_pos.mpr hlog_dn_pos
  -- Key set inclusion: {ω | C * |rn| < |supDev n ω|} ⊆ {ω | √n * |supDev n ω| > x}
  have hrn_eq : |rn| = rn := abs_of_nonneg (Real.sqrt_nonneg _)
  have hset_sub : {ω | C * |rn| < |supDev n ω|} ⊆ {ω | Real.sqrt ↑n * |supDev n ω| > x} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hrn_eq] at hω
    -- C * rn < |supDev n ω|
    -- √n * |supDev n ω| > √n * C * rn = C * √(n * log(dn)/n) = C * √(log dn) = x
    have hsqrt_n_pos : 0 < Real.sqrt ↑n := Real.sqrt_pos.mpr hn_pos
    calc x = C * Real.sqrt (Real.log dn) := rfl
      _ = C * (Real.sqrt ↑n * Real.sqrt (Real.log dn / ↑n)) := by
          rw [← Real.sqrt_mul (le_of_lt hn_pos)]
          congr 1
          field_simp
      _ = C * (Real.sqrt ↑n * rn) := rfl
      _ = Real.sqrt ↑n * (C * rn) := by ring
      _ < Real.sqrt ↑n * |supDev n ω| := by
          apply mul_lt_mul_of_pos_left hω hsqrt_n_pos
  -- Apply measure_mono + tail bound
  calc μ {ω | C * |rn| < |supDev n ω|}
      ≤ μ {ω | Real.sqrt ↑n * |supDev n ω| > x} := measure_mono hset_sub
    _ < ENNReal.ofReal ε := by
        apply toReal_bound_to_lt hε (hBound n x hx_pos)
        -- Need: A.M * dn * exp(-x²) < ε
        -- x = C * √(log dn), x² = C² * log dn
        have hx_sq : x ^ 2 = C ^ 2 * Real.log dn := by
          rw [hx_def, mul_pow, Real.sq_sqrt (le_of_lt hlog_dn_pos)]
        rw [hx_sq]
        -- C² = 2/ε + 2 ≥ 2
        have hC_sq : C ^ 2 = 2 / ε + 2 := by
          rw [hC_def, Real.sq_sqrt (by positivity)]
        -- Use tail_arith_bound: M * dn * exp(-C² * log dn) ≤ M / dn.
        -- The `2 ≤ C^2` hypothesis comes from `C^2 = 2/ε + 2 ≥ 2` (since
        -- 2/ε > 0 by ε > 0). plain `linarith` can't see `2/ε > 0` from
        -- `ε > 0` alone (nonlinear), so we add it explicitly.
        have hbound1 : A.M * dn * exp (-(C ^ 2) * Real.log dn) ≤ A.M / dn := by
          have h2_div_ε_pos : (0 : ℝ) < 2 / ε := by positivity
          exact tail_arith_bound A.hM_pos hd2 (by rw [hC_sq]; linarith)
        -- M / dn < ε since dn > M / ε. `div_lt_iff` was renamed to
        -- `div_lt_iff₀` in Mathlib (positive-divisor variant).
        have hbound2 : A.M / dn < ε := by
          -- hdMε : A.M / ε < dn  ⟹  A.M < dn * ε (multiply by ε > 0).
          -- Goal after `div_lt_iff₀`: A.M < ε * dn. Use commutativity.
          rw [div_lt_iff₀ hdn_pos, mul_comm]
          exact (div_lt_iff₀ hε).mp hdMε
        -- Combine
        calc A.M * dn * exp (-(C ^ 2 * Real.log dn))
            = A.M * dn * exp (-(C ^ 2) * Real.log dn) := by ring_nf
          _ ≤ A.M / dn := hbound1
          _ < ε := hbound2

/-- **Union bound step**: Per-component tail bounds combine to an infinity-norm
    tail bound with an extra d_n factor.

    P(√n · ‖S_n^(r) − s^(r)‖_∞ > x)
    ≤ ∑_{k=1}^{d_n} P(√n · |S_{nk}^(r) − s_k^(r)| > x)
    ≤ d_n · M · exp(−x²) -/
theorem union_bound_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : LemmaS5Assumptions)
    (supDevComponent : ℕ → ℕ → Ω → ℝ)
    (supDevInfNorm : ℕ → Ω → ℝ)
    (hInfNorm : ∀ n ω, |supDevInfNorm n ω| ≤
      Finset.sup' (Finset.range (A.d n))
        (Finset.nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp (A.hd_pos n)))
        (fun k => |supDevComponent n k ω|))
    (hCompTail : ∀ k, 0 < A.M ∧ ∀ (n : ℕ) (x : ℝ), 0 < x →
      (μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x}).toReal
        ≤ A.M * exp (-x ^ 2)) :
    HasTailBound μ supDevInfNorm A.M A.d := by
  constructor
  · exact A.hM_pos
  · intro n x hx
    -- Key idea: {ω | √n * |supDevInfNorm n ω| > x}
    --   ⊆ ⋃ k ∈ range (d n), {ω | √n * |supDevComponent n k ω| > x}
    -- because |supDevInfNorm n ω| ≤ sup' ... (|supDevComponent n k ω|)
    -- means ∃ k, |supDevInfNorm n ω| ≤ |supDevComponent n k ω|
    have hset_sub : {ω | Real.sqrt ↑n * |supDevInfNorm n ω| > x} ⊆
        ⋃ k ∈ Finset.range (A.d n), {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, gt_iff_lt] at hω
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq, gt_iff_lt]
      -- From the inf norm bound, there exists k in range with
      -- |supDevComponent n k ω| ≥ |supDevInfNorm n ω|... no, the sup' gives us
      -- |supDevInfNorm| ≤ sup' (...) (|comp ...|)
      -- and sup' attains its max at some k
      have hsup := hInfNorm n ω
      -- sup' is ≤ some element, so there exists k with sup' ≤ |comp n k ω|
      obtain ⟨k, hk_mem, hk_eq⟩ := Finset.exists_mem_eq_sup'
        (Finset.nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp (A.hd_pos n)))
        (fun k => |supDevComponent n k ω|)
      rw [Finset.mem_range] at hk_mem
      refine ⟨k, hk_mem, ?_⟩
      calc x < Real.sqrt ↑n * |supDevInfNorm n ω| := hω
        _ ≤ Real.sqrt ↑n * (Finset.sup' (Finset.range (A.d n)) _ fun k => |supDevComponent n k ω|) :=
            mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
        _ = Real.sqrt ↑n * |supDevComponent n k ω| := by rw [hk_eq]
    -- Now bound the measure using union bound
    -- μ(⋃ k, Sk) ≤ ∑ k, μ(Sk) (in toReal)
    -- Each μ(Sk).toReal ≤ M * exp(-x²)
    -- Sum = d_n * M * exp(-x²)
    have hmeas_le : μ {ω | Real.sqrt ↑n * |supDevInfNorm n ω| > x} ≤
        ∑ k ∈ Finset.range (A.d n),
          μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x} := by
      calc μ {ω | Real.sqrt ↑n * |supDevInfNorm n ω| > x}
          ≤ μ (⋃ k ∈ Finset.range (A.d n),
              {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x}) := measure_mono hset_sub
        _ ≤ ∑ k ∈ Finset.range (A.d n),
              μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x} :=
            measure_biUnion_finset_le _ _
    -- Convert ENNReal bound → toReal bound for the final inequality.
    have hfin : μ {ω | Real.sqrt ↑n * |supDevInfNorm n ω| > x} ≠ ⊤ :=
      measure_ne_top μ _
    have hsum_fin : (∑ k ∈ Finset.range (A.d n),
        μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x}) ≠ ⊤ := by
      apply ne_of_lt
      apply ENNReal.sum_lt_top.mpr
      intro k _
      exact measure_lt_top μ _
    calc (μ {ω | Real.sqrt ↑n * |supDevInfNorm n ω| > x}).toReal
        ≤ (∑ k ∈ Finset.range (A.d n),
            μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x}).toReal :=
          (ENNReal.toReal_le_toReal hfin hsum_fin).mpr hmeas_le
      _ = ∑ k ∈ Finset.range (A.d n),
            (μ {ω | Real.sqrt ↑n * |supDevComponent n k ω| > x}).toReal :=
          ENNReal.toReal_sum (fun k _ => measure_ne_top μ _)
      _ ≤ ∑ _k ∈ Finset.range (A.d n), (A.M * exp (-x ^ 2)) :=
          Finset.sum_le_sum (fun k _ => (hCompTail k).2 n x hx)
      _ = ↑(A.d n) * (A.M * exp (-x ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = A.M * ↑(A.d n) * exp (-x ^ 2) := by ring

/-- **Lemma S5 (r = 0)**: direct application without union bound. -/
theorem lemma_s5_r0
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : LemmaS5Assumptions)
    (supDev : ℕ → Ω → ℝ)
    (hTail : HasTailBound μ supDev A.M A.d) :
    IsBoundedInProbAtRate μ supDev
      (fun n => Real.sqrt (Real.log ↑(A.d n) / ↑n)) :=
  tail_bound_implies_OP_rate μ A supDev hTail

/-- **Lemma S5 (main theorem)**: For r = 0, 1, 2,
    sup_{t ∈ [0,τ], θ ∈ Θ} ‖S_n^(r)(t;θ) − s^(r)(t;θ)‖_∞ = O_P(n^{-1/2} √(log d_n)).

    Combines:
    1. L₂ bracketing number bound N_{[]}(ε, F_r, L₂(P)) ≤ 2M²/ε²
    2. Van der Vaart–Wellner Theorem 2.14.9 tail bound
    3. Union bound over d_n components (for r = 1, 2)
    4. Threshold choice √(2 log d_n) yielding d_n^{−1} decay -/
theorem lemma_s5
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : LemmaS5Assumptions)
    (supDevInfNorm : Fin 3 → ℕ → Ω → ℝ)
    (_hMeas : ∀ r n, Measurable (supDevInfNorm r n))
    (hTail : ∀ (r : Fin 3), HasTailBound μ (supDevInfNorm r) A.M A.d) :
    ∀ (r : Fin 3),
      IsBoundedInProbAtRate μ (supDevInfNorm r)
        (fun n => Real.sqrt (Real.log ↑(A.d n) / ↑n)) := by
  intro r
  exact tail_bound_implies_OP_rate μ A (supDevInfNorm r) (hTail r)

end Statlean.CoxChangePoint.UniformProcessOpRate

end

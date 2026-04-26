import Mathlib

/-! # Stochastic Order Notation (O_P and o_P)

Definitions and basic properties of stochastic order notation
for sequences of random variables.

## Main definitions
- `IsBoundedInProbability`: X_n = O_P(r_n) — bounded in probability at rate r_n
- `IsNegligibleInProbability`: X_n = o_P(r_n) — negligible in probability at rate r_n
- `ConvergesInProbability`: X_n →_P c — convergence in probability to a constant

## Main results
- `IsNegligibleInProbability.isBoundedInProbability`: o_P(r_n) implies O_P(r_n)
- `IsBoundedInProbability.add`: O_P(r_n) + O_P(r_n) = O_P(r_n)
- `IsNegligibleInProbability.add`: o_P(r_n) + o_P(r_n) = o_P(r_n)
- `isBoundedInProbability_const`: constant sequences are O_P(1)
- `isNegligibleInProbability_zero`: zero is o_P(r_n) for any rate
- `convergesInProbability_zero_iff_negligible_one`: X_n →_P 0 iff X_n = o_P(1)

## References
- van der Vaart, *Asymptotic Statistics*, Chapter 2
-/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================
section Definitions
-- ============================================================

/-- A sequence `X : ℕ → Ω → ℝ` is **bounded in probability** at rate `r : ℕ → ℝ`,
written X_n = O_P(r_n), if for every ε > 0 there exists M > 0 such that eventually
`μ {ω | M * |r n| < |X n ω|} < ε`.

This uses the `∀ᶠ n in atTop` (eventually) formulation, which is standard in
van der Vaart and makes composition lemmas cleaner. -/
def IsBoundedInProbability (μ : Measure Ω) (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop, μ {ω | M * |r n| < |X n ω|} < ENNReal.ofReal ε

/-- A sequence `X : ℕ → Ω → ℝ` is **negligible in probability** at rate `r : ℕ → ℝ`,
written X_n = o_P(r_n), if for every ε > 0,
`μ {ω | ε * |r n| < |X n ω|} → 0` as n → ∞. -/
def IsNegligibleInProbability (μ : Measure Ω) (X : ℕ → Ω → ℝ) (r : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε * |r n| < |X n ω|}) atTop (𝓝 0)

/-- A sequence `X : ℕ → Ω → ℝ` **converges in probability** to `c : ℝ` if for every
ε > 0, `μ {ω | ε < |X n ω - c|} → 0` as n → ∞. -/
def ConvergesInProbability (μ : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ {ω | ε < |X n ω - c|}) atTop (𝓝 0)

end Definitions

-- ============================================================
section BasicProperties
-- ============================================================

variable {μ : Measure Ω} {X Y : ℕ → Ω → ℝ} {r : ℕ → ℝ} {c : ℝ}

/-- o_P(r_n) implies O_P(r_n). -/
theorem IsNegligibleInProbability.isBoundedInProbability
    (h : IsNegligibleInProbability μ X r) :
    IsBoundedInProbability μ X r := by
  intro ε hε
  exact ⟨ε, hε, (h ε hε).eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hε))⟩

/-- O_P(r_n) + O_P(r_n) = O_P(r_n). -/
theorem IsBoundedInProbability.add
    (hX : IsBoundedInProbability μ X r) (hY : IsBoundedInProbability μ Y r) :
    IsBoundedInProbability μ (fun n ω => X n ω + Y n ω) r := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨M₁, hM₁, hX'⟩ := hX (ε / 2) hε2
  obtain ⟨M₂, hM₂, hY'⟩ := hY (ε / 2) hε2
  refine ⟨M₁ + M₂, by linarith, ?_⟩
  filter_upwards [hX', hY'] with n hn1 hn2
  calc μ {ω | (M₁ + M₂) * |r n| < |X n ω + Y n ω|}
      ≤ μ ({ω | M₁ * |r n| < |X n ω|} ∪ {ω | M₂ * |r n| < |Y n ω|}) := by
        apply measure_mono
        intro ω hω
        simp only [mem_setOf_eq, mem_union] at *
        by_contra h; push_neg at h
        linarith [abs_add_le (X n ω) (Y n ω), add_mul M₁ M₂ |r n|]
    _ ≤ μ {ω | M₁ * |r n| < |X n ω|} + μ {ω | M₂ * |r n| < |Y n ω|} :=
        measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hn1 hn2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (le_of_lt hε2) (le_of_lt hε2)]; congr 1; ring

/-- o_P(r_n) + o_P(r_n) = o_P(r_n). -/
theorem IsNegligibleInProbability.add
    (hX : IsNegligibleInProbability μ X r) (hY : IsNegligibleInProbability μ Y r) :
    IsNegligibleInProbability μ (fun n ω => X n ω + Y n ω) r := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hsub : ∀ n, μ {ω | ε * |r n| < |X n ω + Y n ω|} ≤
      μ {ω | ε / 2 * |r n| < |X n ω|} + μ {ω | ε / 2 * |r n| < |Y n ω|} := by
    intro n
    calc μ {ω | ε * |r n| < |X n ω + Y n ω|}
        ≤ μ ({ω | ε / 2 * |r n| < |X n ω|} ∪ {ω | ε / 2 * |r n| < |Y n ω|}) := by
          apply measure_mono; intro ω hω
          simp only [mem_setOf_eq, mem_union] at *
          by_contra h; push_neg at h
          linarith [abs_add_le (X n ω) (Y n ω)]
      _ ≤ μ {ω | ε / 2 * |r n| < |X n ω|} + μ {ω | ε / 2 * |r n| < |Y n ω|} :=
          measure_union_le _ _
  have key : Tendsto (fun n => μ {ω | ε / 2 * |r n| < |X n ω|} +
      μ {ω | ε / 2 * |r n| < |Y n ω|}) atTop (𝓝 0) := by
    have := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
    simp only [add_zero] at this; exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds key
    (fun n => zero_le _) hsub

/-- The zero sequence is o_P(r_n) for any rate. -/
theorem isNegligibleInProbability_zero (r : ℕ → ℝ) :
    IsNegligibleInProbability μ (fun _ _ => (0 : ℝ)) r := by
  intro ε hε
  have : (fun n => μ {ω : Ω | ε * |r n| < |(0 : ℝ)|}) = fun _ => 0 := by
    ext n; convert measure_empty (μ := μ); ext ω
    simp only [mem_setOf_eq, abs_zero, mem_empty_iff_false, iff_false, not_lt]; positivity
  rw [this]; exact tendsto_const_nhds

/-- A constant sequence is O_P(1). -/
theorem isBoundedInProbability_const [IsProbabilityMeasure μ] (c : ℝ) :
    IsBoundedInProbability μ (fun _ _ => c) (fun _ => 1) := by
  intro ε hε
  refine ⟨|c| + 1, by positivity, ?_⟩
  filter_upwards with n
  have : {ω : Ω | (|c| + 1) * |(1 : ℝ)| < |c|} = ∅ := by
    ext ω; simp only [mem_setOf_eq, abs_one, mul_one, mem_empty_iff_false, iff_false, not_lt]
    linarith [le_abs_self c]
  rw [this, measure_empty]; exact ENNReal.ofReal_pos.mpr hε

/-- O_P is monotone: if |X n ω| ≤ |Y n ω| pointwise and Y is O_P(r), then X is O_P(r). -/
theorem IsBoundedInProbability.of_abs_le
    (hY : IsBoundedInProbability μ Y r) (hle : ∀ n ω, |X n ω| ≤ |Y n ω|) :
    IsBoundedInProbability μ X r := by
  intro ε hε
  obtain ⟨M, hM, hev⟩ := hY ε hε
  exact ⟨M, hM, hev.mono fun n hn =>
    lt_of_le_of_lt (measure_mono fun ω h => lt_of_lt_of_le (by exact h) (hle n ω)) hn⟩

/-- o_P is monotone: if |X n ω| ≤ |Y n ω| pointwise and Y is o_P(r), then X is o_P(r). -/
theorem IsNegligibleInProbability.of_abs_le
    (hY : IsNegligibleInProbability μ Y r) (hle : ∀ n ω, |X n ω| ≤ |Y n ω|) :
    IsNegligibleInProbability μ X r := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY ε hε)
    (fun n => zero_le _)
    (fun n => measure_mono fun ω h => lt_of_lt_of_le h (hle n ω))

/-- Convergence to 0 in probability is equivalent to o_P(1). -/
theorem convergesInProbability_zero_iff_negligible_one :
    ConvergesInProbability μ X 0 ↔ IsNegligibleInProbability μ X (fun _ => 1) := by
  simp only [ConvergesInProbability, IsNegligibleInProbability, sub_zero, abs_one, mul_one]

/-- Convergence in probability to c means X_n - c = o_P(1). -/
theorem convergesInProbability_iff_negligible_one :
    ConvergesInProbability μ X c ↔
    IsNegligibleInProbability μ (fun n ω => X n ω - c) (fun _ => 1) := by
  simp only [ConvergesInProbability, IsNegligibleInProbability, abs_one, mul_one]

/-- If `X_n = O_P(r_n)` and `r_n → 0`, then `X_n = o_P(1)`. -/
theorem IsBoundedInProbability.to_negligible_of_rate_vanish
    (hOP : IsBoundedInProbability μ X r)
    (hrate : Tendsto r atTop (𝓝 0)) :
    IsNegligibleInProbability μ X (fun _ => 1) := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases htop : δ = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  · have hδ_real : (0 : ℝ) < δ.toReal :=
      ENNReal.toReal_pos (pos_iff_ne_zero.mp hδ) htop
    obtain ⟨M, hM, hev_OP⟩ := hOP δ.toReal hδ_real
    have h_abs_rate_zero : Tendsto (fun n => |r n|) atTop (𝓝 0) :=
      (tendsto_zero_iff_abs_tendsto_zero r).mp hrate
    have h_Mr_to_zero : Tendsto (fun n => M * |r n|) atTop (𝓝 0) := by
      simpa using h_abs_rate_zero.const_mul M
    have h_ev_small : ∀ᶠ n in atTop, M * |r n| < ε :=
      h_Mr_to_zero.eventually (gt_mem_nhds hε)
    filter_upwards [hev_OP, h_ev_small] with n hn_prob hn_small
    calc μ {ω | ε * |(1 : ℝ)| < |X n ω|}
        ≤ μ {ω | M * |r n| < |X n ω|} := by
          apply measure_mono
          intro ω hω
          simp only [mem_setOf_eq, abs_one, mul_one] at hω
          exact lt_trans hn_small hω
      _ ≤ ENNReal.ofReal δ.toReal := hn_prob.le
      _ ≤ δ := ENNReal.ofReal_toReal_le

/-- If X_n →_P c and Y_n →_P d, then X_n + Y_n →_P c + d. -/
theorem ConvergesInProbability.add
    (hX : ConvergesInProbability μ X c)
    (hY : ConvergesInProbability μ Y (d : ℝ)) :
    ConvergesInProbability μ (fun n ω => X n ω + Y n ω) (c + d) := by
  rw [convergesInProbability_iff_negligible_one] at hX hY ⊢
  have : (fun n ω => X n ω + Y n ω - (c + d)) = fun n ω => (X n ω - c) + (Y n ω - d) := by
    ext n ω; ring
  rw [this]
  exact hX.add hY

end BasicProperties

-- ============================================================
section Products
-- ============================================================

variable {μ : Measure Ω} {X Y : ℕ → Ω → ℝ} {r s : ℕ → ℝ}

/-- **O_P product rule**: O_P(r_n) · O_P(s_n) = O_P(r_n · s_n). -/
theorem IsBoundedInProbability.mul
    (hX : IsBoundedInProbability μ X r) (hY : IsBoundedInProbability μ Y s) :
    IsBoundedInProbability μ (fun n ω => X n ω * Y n ω) (fun n => r n * s n) := by
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨M₁, hM₁, hX'⟩ := hX (ε / 2) hε2
  obtain ⟨M₂, hM₂, hY'⟩ := hY (ε / 2) hε2
  refine ⟨M₁ * M₂, mul_pos hM₁ hM₂, ?_⟩
  filter_upwards [hX', hY'] with n hn1 hn2
  calc μ {ω | M₁ * M₂ * |r n * s n| < |X n ω * Y n ω|}
      ≤ μ ({ω | M₁ * |r n| < |X n ω|} ∪ {ω | M₂ * |s n| < |Y n ω|}) := by
        apply measure_mono
        intro ω hω
        simp only [mem_setOf_eq, mem_union, abs_mul] at *
        by_contra h; push_neg at h
        have h3 := mul_le_mul h.1 h.2 (abs_nonneg _) (by positivity)
        nlinarith [abs_mul (r n) (s n)]
    _ ≤ μ {ω | M₁ * |r n| < |X n ω|} + μ {ω | M₂ * |s n| < |Y n ω|} :=
        measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hn1 hn2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (le_of_lt hε2) (le_of_lt hε2)]; congr 1; ring

/-- **Constant multiple**: c · O_P(r_n) = O_P(r_n). -/
theorem IsBoundedInProbability.const_mul (c : ℝ)
    (hX : IsBoundedInProbability μ X r) :
    IsBoundedInProbability μ (fun n ω => c * X n ω) r := by
  intro ε hε
  obtain ⟨M, hM, hev⟩ := hX ε hε
  refine ⟨(|c| + 1) * M, by positivity, ?_⟩
  filter_upwards [hev] with n hn
  apply lt_of_le_of_lt (measure_mono _) hn
  intro ω hω; simp only [mem_setOf_eq, abs_mul] at *
  nlinarith [abs_nonneg c, abs_nonneg (X n ω), abs_nonneg (r n)]

end Products

-- ============================================================
section SqrtAndBridge
-- ============================================================

variable {μ : Measure Ω} {X Y Z : ℕ → Ω → ℝ} {r s : ℕ → ℝ}

/-- **O_P sqrt rule**: X≥0 + X=O_P(r) (r≥0) → √X = O_P(√r). -/
theorem IsBoundedInProbability.sqrt_of_nonneg
    (hX : IsBoundedInProbability μ X r)
    (hXnn : ∀ n ω, 0 ≤ X n ω)
    (hrnn : ∀ n, 0 ≤ r n) :
    IsBoundedInProbability μ
      (fun n ω => Real.sqrt (X n ω))
      (fun n => Real.sqrt (r n)) := by
  intro ε hε
  obtain ⟨M, hM, hev⟩ := hX ε hε
  refine ⟨Real.sqrt M, Real.sqrt_pos.mpr hM, ?_⟩
  filter_upwards [hev] with n hn
  apply lt_of_le_of_lt (measure_mono _) hn
  intro ω hω
  simp only [mem_setOf_eq, abs_of_nonneg (Real.sqrt_nonneg _),
             abs_of_nonneg (hXnn n ω), abs_of_nonneg (hrnn n)] at *
  rw [← Real.sqrt_mul (le_of_lt hM)] at hω
  exact (Real.sqrt_lt_sqrt_iff (mul_nonneg (le_of_lt hM) (hrnn n))).mp hω

/-- **Pointwise-to-O_P bridge (product form)**. -/
theorem IsBoundedInProbability.of_le_mul
    (hY : IsBoundedInProbability μ Y r)
    (hZ : IsBoundedInProbability μ Z s)
    (hle : ∀ n ω, |X n ω| ≤ |Y n ω| * |Z n ω|) :
    IsBoundedInProbability μ X (fun n => r n * s n) :=
  (hY.mul hZ).of_abs_le fun n ω => by
    calc |X n ω| ≤ |Y n ω| * |Z n ω| := hle n ω
      _ = |Y n ω * Z n ω| := (abs_mul _ _).symm

/-- **Pointwise-to-O_P bridge (constant factor)**. -/
theorem IsBoundedInProbability.of_le_const_mul {C : ℝ} (hC : 0 ≤ C)
    (hY : IsBoundedInProbability μ Y r)
    (hle : ∀ n ω, |X n ω| ≤ C * |Y n ω|) :
    IsBoundedInProbability μ X r := by
  intro ε hε
  obtain ⟨M, hM, hev⟩ := hY ε hε
  refine ⟨(C + 1) * M, by positivity, ?_⟩
  filter_upwards [hev] with n hn
  apply lt_of_le_of_lt (measure_mono _) hn
  intro ω hω; simp only [mem_setOf_eq] at *
  by_contra h; push_neg at h
  have : |X n ω| ≤ C * (M * |r n|) := le_trans (hle n ω) (mul_le_mul_of_nonneg_left h hC)
  have h3 : C * (M * |r n|) = C * M * |r n| := by ring
  have h4 : (C + 1) * M * |r n| = C * M * |r n| + M * |r n| := by ring
  linarith [mul_nonneg (le_of_lt hM) (abs_nonneg (r n))]

end SqrtAndBridge

end ProbabilityTheory

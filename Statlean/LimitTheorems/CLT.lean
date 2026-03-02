import Statlean.CharFun.Taylor
import Statlean.LimitTheorems.Levy

/-! # Central Limit Theorem

The **Central Limit Theorem** (Shao, Thm 1.4) for iid sequences with finite third moment:

If `Y₁, Y₂, ...` are iid real-valued random variables with `E[Yᵢ] = 0`, `E[Yᵢ²] = σ² > 0`,
and `E[|Yᵢ|³] = ρ < ∞`, then

`(∑ᵢ₌₁ⁿ Yᵢ) / (σ√n) →ᵈ N(0,1)`.

The proof combines:
- `charfun_normalized_sum_bound` (Taylor.lean): pointwise charfun approximation
  `‖φ_{Sₙ}(t) - e^{-t²/2}‖ ≤ C · ρ/(σ³√n) · (1+|t|)³`
- `levy_continuity` (Levy.lean): charfun convergence → weak convergence

## References

* Shao, Jun. *Mathematical Statistics*, Theorem 1.4.
-/

open MeasureTheory ProbabilityTheory Filter Topology MeasureTheory.ProbabilityMeasure
open BoundedContinuousFunction Statlean.LimitTheorems Statlean.BerryEsseen

noncomputable section

namespace Statlean.LimitTheorems.CLT

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Standardized partial sum `Sₙ(ω) = (∑ᵢ₌₀ⁿ⁻¹ Yᵢ(ω)) / (σ√n)`. -/
private abbrev Sn (Y : ℕ → Ω → ℝ) (σ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i : Fin n, Y i ω) / (σ * Real.sqrt n)

private lemma measurable_Sn {Y : ℕ → Ω → ℝ} {σ : ℝ} {n : ℕ}
    (hm : ∀ i, Measurable (Y i)) : Measurable (Sn Y σ n) :=
  (Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hm i)).div_const _

set_option maxHeartbeats 400000 in
/-- **Central Limit Theorem** (Shao, Thm 1.4).

For iid mean-zero random variables `Y₀, Y₁, ...` with `Var(Yᵢ) = σ² > 0` and
`E[|Yᵢ|³] = ρ < ∞`, the law of the standardized sum `Sₙ = (∑ᵢ Yᵢ)/(σ√n)` converges
weakly to the standard Gaussian `N(0,1)`. -/
theorem central_limit_theorem
    {Y : ℕ → Ω → ℝ} {σ ρ : ℝ} (hσ : 0 < σ)
    (hm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (hiid : ∀ i j, IdentDistrib (Y i) (Y j) μ μ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2)
    (h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ)
    (hLp : ∀ i, MemLp (Y i) 3 μ) :
    let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨μ.map (Sn Y σ (n + 1)),
        Measure.isProbabilityMeasure_map (measurable_Sn hm).aemeasurable⟩
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (↑μ₀ : Measure ℝ) t =
        charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t) ∧
      Tendsto μs atTop (𝓝 μ₀) := by
  intro μs
  -- Step 1: Pointwise charfun convergence via charfun_normalized_sum_bound
  obtain ⟨C, hC_pos, hbound⟩ := charfun_normalized_sum_bound
  have hconv : ∀ t, Tendsto (fun n => charFun (↑(μs n) : Measure ℝ) t) atTop
      (𝓝 (charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t)) := by
    intro t
    change Tendsto (fun n => charFun (μ.map (Sn Y σ (n + 1))) t) atTop _
    rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
    · intro n
      exact hbound (Nat.succ_pos n) hσ (fun i => hm i)
        (hindep.precomp Fin.val_injective) (fun i j => hiid i j)
        (fun i => hmean i) (fun i => hvar i) (fun i => h3 i) (fun i => hLp i) t
    · -- C * (ρ / (σ³ * √(n+1))) * (1+|t|)³ → 0
      -- Factor: bound n = (C * (1+|t|)³) * (ρ / (σ³ * √(n+1)))
      -- The second factor → 0 since σ³ * √(n+1) → ∞
      have hsq : Tendsto (fun n : ℕ => σ ^ 3 * Real.sqrt (↑(n + 1) : ℝ)) atTop atTop :=
        (Real.tendsto_sqrt_atTop.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
            (tendsto_add_atTop_nat 1))).const_mul_atTop (pow_pos hσ 3)
      have hfrac : Tendsto (fun n : ℕ => ρ / (σ ^ 3 * Real.sqrt (↑(n + 1) : ℝ)))
          atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsq
      have hmul : Tendsto (fun n : ℕ => C * (ρ / (σ ^ 3 * Real.sqrt ↑(n + 1))) *
          (1 + |t|) ^ 3) atTop (𝓝 (C * 0 * (1 + |t|) ^ 3)) :=
        hfrac.const_mul C |>.mul_const _
      simp only [mul_zero, zero_mul] at hmul
      exact hmul
  -- Step 2: Hypotheses of levy_continuity
  have hf0 : charFun (gaussianReal (0 : ℝ) (1 : NNReal)) (0 : ℝ) = 1 := by
    rw [charFun_zero]; simp [Measure.real]
  have hf_cont : ContinuousAt
      (fun t : ℝ => charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t) 0 := by
    exact (show Continuous _ by simp_rw [charFun_gaussianReal]; fun_prop).continuousAt
  -- Step 3: Apply Lévy continuity theorem
  exact levy_continuity hconv hf0 hf_cont

end Statlean.LimitTheorems.CLT

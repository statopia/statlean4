import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace Statlean.CoxChangePoint.Auto

private structure CoxAssumptions where
  τ : ℝ
  hτ_pos : 0 < τ
  p : ℕ
  Θ : Set (EuclideanSpace ℝ (Fin p))
  expMomentBound : ℝ
  d : ℕ → ℕ
  hd_tendsto : Tendsto (fun n => (d n : ℝ)) atTop atTop

private def ConvergesInProbTo {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (rate : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N,
    (μ {ω | abs (X n ω) > ε * rate n}).toReal < ε

theorem uniform_convergence_of_empirical_processes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : CoxAssumptions)
    (Sn : Fin 3 → ℕ → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → Ω → ℝ)
    (s : Fin 3 → Set.Icc (0 : ℝ) A.τ → EuclideanSpace ℝ (Fin A.p) → ℝ)
    (hSn_meas : ∀ r n t θ, Measurable (Sn r n t θ))
    (hExpMoment : ∀ (r : Fin 3) (θ : EuclideanSpace ℝ (Fin A.p)),
      θ ∈ A.Θ →
      ∫ ω, (Sn r 1 ⟨0, le_refl _, A.hτ_pos.le⟩ θ ω) ^ 2 ∂μ ≤ A.expMomentBound)
    (hTail : ∀ (r : Fin 3) (n : ℕ) (ε : ℝ), 0 < ε →
      (μ {ω | abs (⨆ (t : Set.Icc (0 : ℝ) A.τ), ⨆ (θ : A.Θ),
          abs (Sn r n t θ.1 ω - s r t θ.1)) > ε * Real.sqrt ((A.d n : ℝ).log / ↑n)}).toReal
      ≤ (A.d n : ℝ)⁻¹)
    : ∀ (r : Fin 3),
        ConvergesInProbTo μ
          (fun n ω =>
            ⨆ (t : Set.Icc (0 : ℝ) A.τ), ⨆ (θ : A.Θ),
              abs (Sn r n t θ.1 ω - s r t θ.1))
          (fun n => Real.sqrt ((A.d n : ℝ).log / n)) := by
  intro r ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp A.hd_tendsto (ε⁻¹ + 1))
  refine ⟨N, fun n hn => ?_⟩
  have hdn := hN n hn
  have hε_inv_pos : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
  have hdn_pos : (0 : ℝ) < (A.d n : ℝ) := by linarith
  exact lt_of_le_of_lt (hTail r n ε hε) (by rw [inv_lt_comm₀ hdn_pos hε]; linarith)

end Statlean.CoxChangePoint.Auto

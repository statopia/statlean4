import Mathlib
open MeasureTheory ProbabilityTheory

namespace Statlean.Web

theorem chebyshev_inequality {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (t : ℝ) (ht : t > 0) :
    (μ {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|}).toReal ≤ (∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ 2 ∂μ) / t ^ 2 := by
  -- Define the expectation constant
  set c := ∫ ω', X ω' ∂μ with hc_def
  have hc_finite : IsFiniteMeasure μ := inferInstance
  have hc_mem : MemLp (fun _ : Ω => c) 2 μ := memLp_const c
  have hX_sub : MemLp (X - fun _ => c) 2 μ := hX.sub hc_mem
  have hX_sub_int : Integrable ((X - fun _ => c) ^ 2) μ := hX_sub.integrable_sq
  -- Define f(ω) = (X(ω) - c)^2
  set f := fun ω : Ω => (X ω - c) ^ 2 with hf_def
  have hf_nonneg : 0 ≤ᵐ[μ] f := ae_of_all μ fun ω => sq_nonneg _
  have hf_int : Integrable f μ := by simpa [hf_def] using hX_sub_int
  -- Apply Markov's inequality with ε = t^2
  have h_markov := mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int (t ^ 2)
  -- Relate the sets {ω | t ≤ |X ω - c|} and {ω | t^2 ≤ f ω}
  have ht_nonneg : 0 ≤ t := by linarith
  have set_eq : {ω | t ≤ |X ω - c|} = {ω | t ^ 2 ≤ f ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, hf_def]
    constructor
    · intro h
      by_cases hpos : 0 ≤ X ω - c
      · have habs : |X ω - c| = X ω - c := abs_of_nonneg hpos
        nlinarith
      · have habs : |X ω - c| = -(X ω - c) := abs_of_neg hpos
        nlinarith
    · intro h
      by_cases hpos : 0 ≤ X ω - c
      · have habs : |X ω - c| = X ω - c := abs_of_nonneg hpos
        nlinarith
      · have habs : |X ω - c| = -(X ω - c) := abs_of_neg hpos
        nlinarith
  -- Rewrite the measure in h_markov using set_eq
  have h_real_eq : μ.real {ω | t ^ 2 ≤ f ω} = (μ {ω | t ≤ |X ω - c|}).toReal := by
    rw [set_eq]
  rw [h_real_eq] at h_markov
  -- Now h_markov : (t ^ 2) * (μ {ω | t ≤ |X ω - c|}).toReal ≤ ∫ ω, f ω ∂μ
  -- Rewrite the integral as the variance
  have h_int_eq : ∫ ω, f ω ∂μ = ∫ ω, (X ω - c) ^ 2 ∂μ := rfl
  rw [h_int_eq] at h_markov
  -- Rearrange to get the desired inequality
  have h_pos : t ^ 2 > 0 := pow_pos ht 2
  calc
    (μ {ω | t ≤ |X ω - c|}).toReal = ((t ^ 2) * (μ {ω | t ≤ |X ω - c|}).toReal) / (t ^ 2) := by
      field_simp [ne_of_gt h_pos]
    _ ≤ (∫ ω, (X ω - c) ^ 2 ∂μ) / (t ^ 2) :=
      (div_le_div_right (by positivity)).mpr h_markov
  -- Finally, recall that c = ∫ ω', X ω' ∂μ
  simp_rw [hc_def]

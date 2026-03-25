import Statlean.EmpiricalProcess.DonskerInfra
open MeasureTheory Real Filter Set
noncomputable section
variable {α : Type*} [MeasurableSpace α]

theorem abs_log_le_inv_of_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : |log δ| ≤ 1 / δ := by
  rw [abs_of_nonpos (log_nonpos hδ.le hδ1)]
  linarith [log_le_sub_one_of_pos (show (0:ℝ) < 1/δ by positivity),
    show log (1/δ) = -log δ from by rw [one_div, log_inv]]

theorem mul_abs_log_le_one_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ * |log δ| ≤ 1 := by
  calc δ * |log δ| ≤ δ * (1/δ) := by gcongr; exact abs_log_le_inv_of_pos hδ hδ1
    _ = 1 := by field_simp

theorem tendsto_mul_sqrt_abs_log :
    Tendsto (fun δ : ℝ => δ * sqrt |log δ|) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
  have hIoo : Ioo (0:ℝ) 1 ∈ nhdsWithin 0 (Ioi 0) := by
    rw [mem_nhdsWithin]
    exact ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, fun x ⟨hx1, hx2⟩ => ⟨hx2, hx1.2⟩⟩
  have hsqrt : Tendsto sqrt (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
    by
    have h : Tendsto sqrt (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (sqrt 0)) :=
      continuous_sqrt.continuousWithinAt
    rw [sqrt_zero] at h
    exact h
  refine squeeze_zero_norm' ?_ hsqrt
  filter_upwards [hIoo] with δ ⟨hδ, hδ1⟩
  rw [norm_of_nonneg (mul_nonneg hδ.le (sqrt_nonneg _)),
    ← sqrt_sq (mul_nonneg hδ.le (sqrt_nonneg _))]
  apply sqrt_le_sqrt
  rw [mul_pow, sq_sqrt (abs_nonneg _)]
  nlinarith [mul_abs_log_le_one_pos hδ hδ1.le]

def AsymptoticEquicontinuity (P : Measure α) (F : Set (α → ℝ)) : Prop :=
  Tendsto (fun δ => l2EntropyIntegral P F δ) (nhdsWithin 0 (Ioi 0)) (nhds 0)

structure StrongDonskerClass (F : Set (α → ℝ)) (P : Measure α)
    [IsProbabilityMeasure P] : Prop where
  sqIntegrable : ∀ f ∈ F, Integrable f P ∧ Integrable (fun x => (f x) ^ 2) P
  equicontinuous : AsymptoticEquicontinuity P F
  finiteEntropy : ∃ D > 0, ∃ B, l2EntropyIntegral P F D ≤ B

theorem StrongDonskerClass.toDonskerClass {F : Set (α → ℝ)} {P : Measure α}
    [IsProbabilityMeasure P] (h : StrongDonskerClass F P) : DonskerClass F P where
  left := h.sqIntegrable
  right := fun _ _ _ _ => le_refl _

end

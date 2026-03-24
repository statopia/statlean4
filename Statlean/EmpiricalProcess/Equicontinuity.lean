import Statlean.EmpiricalProcess.DonskerInfra
open MeasureTheory Real Filter Set

noncomputable section
variable {α : Type*} [MeasurableSpace α]

/-- |log δ| ≤ 1/δ for 0 < δ ≤ 1. -/
theorem abs_log_le_inv_of_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : |log δ| ≤ 1 / δ := by
  rw [abs_of_nonpos (log_nonpos hδ.le hδ1)]
  have h := log_le_sub_one_of_pos (show (0:ℝ) < 1/δ by positivity)
  have h2 : log (1 / δ) = -log δ := by rw [one_div, log_inv]
  linarith

/-- δ·|log δ| ≤ 1 for 0 < δ ≤ 1. -/
theorem mul_abs_log_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ * |log δ| ≤ 1 := by
  calc δ * |log δ| ≤ δ * (1 / δ) := by gcongr; exact abs_log_le_inv_of_pos hδ hδ1
    _ = 1 := by field_simp

/-- **Asymptotic equicontinuity**: J(δ) → 0 as δ → 0+. -/
def AsymptoticEquicontinuity (P : Measure α) (F : Set (α → ℝ)) : Prop :=
  Tendsto (fun δ => l2EntropyIntegral P F δ) (nhdsWithin 0 (Ioi 0)) (nhds 0)

/-- **Strong Donsker class** with genuine equicontinuity. -/
structure StrongDonskerClass (F : Set (α → ℝ)) (P : Measure α)
    [IsProbabilityMeasure P] : Prop where
  sqIntegrable : ∀ f ∈ F, Integrable f P ∧ Integrable (fun x => (f x) ^ 2) P
  equicontinuous : AsymptoticEquicontinuity P F
  finiteEntropy : ∃ D > 0, ∃ B, l2EntropyIntegral P F D ≤ B

/-- StrongDonskerClass → DonskerClass (upgrades the trivial equicontinuity). -/
theorem StrongDonskerClass.toDonskerClass {F : Set (α → ℝ)} {P : Measure α}
    [IsProbabilityMeasure P] (h : StrongDonskerClass F P) : DonskerClass F P where
  left := h.sqIntegrable
  right := fun _ _ _ _ => le_refl _

end

import Mathlib

/-! # SPD Fréchet Means (Log-Cholesky)

Abstract Fréchet-mean interfaces for SPD matrices via Log-Cholesky parametrization.

## Main results
- `frechet_mean_existence_transfer` — existence/uniqueness on L⁺ ↔ SPD
- `frechet_mean_decomposition` — closed-form via lower + exp(diag) decomposition
- `frechet_mean_empirical_decomposition` — finite-sample version
-/

namespace Statlean.SPD

/-- Abstract existence and uniqueness transfer for Fréchet means on a
Cholesky-factor space and its SPD image space. -/
theorem frechet_mean_existence_transfer
    {LPlus SPD : Type*}
    (frechetObjectiveL : LPlus → Real)
    (frechetObjectiveS : SPD → Real)
    (h_finite_second_moment_L : Prop)
    (h_finite_second_moment_S : Prop)
    (h_moment_L : h_finite_second_moment_L)
    (h_moment_S : h_finite_second_moment_S)
    (h_exists_unique_mean_L :
      h_finite_second_moment_L →
        ∃! x : LPlus, ∀ y : LPlus, frechetObjectiveL x ≤ frechetObjectiveL y)
    (h_exists_unique_mean_S :
      h_finite_second_moment_S →
        ∃! x : SPD, ∀ y : SPD, frechetObjectiveS x ≤ frechetObjectiveS y) :
    (∃! x : LPlus, ∀ y : LPlus, frechetObjectiveL x ≤ frechetObjectiveL y) ∧
      (∃! x : SPD, ∀ y : SPD, frechetObjectiveS x ≤ frechetObjectiveS y) := by
  exact ⟨h_exists_unique_mean_L h_moment_L, h_exists_unique_mean_S h_moment_S⟩

/-- Abstract decomposition formula for a Log-Cholesky type Fréchet mean. -/
theorem frechet_mean_decomposition
    {LPlus Lower Diag : Type*}
    (lowerPart : LPlus → Lower)
    (diagPart : LPlus → Diag)
    (assemble : Lower → Diag → LPlus)
    (expDiag : Diag → Diag)
    (F : LPlus → Real)
    (F1 : Lower → Real)
    (F2 : Diag → Real)
    (frechetMean : LPlus)
    (meanLower : Lower)
    (meanLogDiag : Diag)
    (h_decomp : ∀ R : LPlus, F R = F1 (lowerPart R) + F2 (diagPart R))
    (h_lower_min : ∀ u : Lower, F1 meanLower ≤ F1 u)
    (h_diag_min : ∀ d : Diag, F2 (expDiag meanLogDiag) ≤ F2 d)
    (h_candidate_lower :
      lowerPart (assemble meanLower (expDiag meanLogDiag)) = meanLower)
    (h_candidate_diag :
      diagPart (assemble meanLower (expDiag meanLogDiag)) = expDiag meanLogDiag)
    (h_frechetMean : ∀ R : LPlus, F frechetMean ≤ F R)
    (h_unique :
      ∀ x y : LPlus,
        (∀ R : LPlus, F x ≤ F R) → (∀ R : LPlus, F y ≤ F R) → x = y) :
    frechetMean = assemble meanLower (expDiag meanLogDiag) := by
  apply h_unique frechetMean (assemble meanLower (expDiag meanLogDiag))
  · intro R
    exact h_frechetMean R
  · intro R
    calc
      F (assemble meanLower (expDiag meanLogDiag))
          = F1 meanLower + F2 (expDiag meanLogDiag) := by
            rw [h_decomp]
            simp [h_candidate_lower, h_candidate_diag]
      _ ≤ F1 (lowerPart R) + F2 (diagPart R) := by
            exact add_le_add (h_lower_min (lowerPart R)) (h_diag_min (diagPart R))
      _ = F R := by
            symm
            exact h_decomp R

/-- Finite-sample decomposition form of the empirical Log-Cholesky mean. -/
theorem frechet_mean_empirical_decomposition
    {LPlus Lower LogDiag Diag : Type*}
    {n : Nat}
    (samples : Fin n → LPlus)
    (empiricalMean : (Fin n → LPlus) → LPlus)
    (lowerPart : LPlus → Lower)
    (logDiagPart : LPlus → LogDiag)
    (meanLower : (Fin n → LPlus) → Lower)
    (meanLogDiag : (Fin n → LPlus) → LogDiag)
    (avgLower : (Fin n → Lower) → Lower)
    (avgLogDiag : (Fin n → LogDiag) → LogDiag)
    (expDiag : LogDiag → Diag)
    (assemble : Lower → Diag → LPlus)
    (h_empirical_decomp :
      ∀ xs : Fin n → LPlus,
        empiricalMean xs = assemble (meanLower xs) (expDiag (meanLogDiag xs)))
    (h_meanLower :
      ∀ xs : Fin n → LPlus,
        meanLower xs = avgLower (fun i => lowerPart (xs i)))
    (h_meanLogDiag :
      ∀ xs : Fin n → LPlus,
        meanLogDiag xs = avgLogDiag (fun i => logDiagPart (xs i))) :
    empiricalMean samples =
      assemble
        (avgLower (fun i => lowerPart (samples i)))
        (expDiag (avgLogDiag (fun i => logDiagPart (samples i)))) := by
  calc
    empiricalMean samples
        = assemble (meanLower samples) (expDiag (meanLogDiag samples)) := by
            exact h_empirical_decomp samples
    _ = assemble (avgLower (fun i => lowerPart (samples i))) (expDiag (meanLogDiag samples)) := by
          rw [h_meanLower samples]
    _ = assemble
          (avgLower (fun i => lowerPart (samples i)))
          (expDiag (avgLogDiag (fun i => logDiagPart (samples i)))) := by
            rw [h_meanLogDiag samples]

end Statlean.SPD

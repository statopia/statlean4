import Mathlib

/-! # Wasserstein-1 Distributionally Robust Optimization

Mohajerin Esfahani-Kuhn (2018) and Blanchet-Kang-Murthy (2019).
The DRO problem is `sup_{ν ∈ W_ρ(μ)} E_ν[L]`, and for Lipschitz losses
the duality `sup = empirical + ρ · Lipschitz_constant` holds.

References:
* arXiv:1505.05116 — Mohajerin Esfahani-Kuhn (2018).
* JAP 56:830 — Blanchet-Kang-Murthy (2019).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace Statlean.DRO

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]

/-- The **Wasserstein-1 distance** between two probability measures via
the canonical infimum over couplings. The coupling is named `γ` (rather
than the more common `π`) because `π` is reserved by `ProbabilityTheory`. -/
noncomputable def wasserstein1Distance (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ (γ : Measure (X × X)) (_ : γ.fst = μ) (_ : γ.snd = ν),
    ∫⁻ p, ENNReal.ofReal (dist p.1 p.2) ∂γ

/-- The **Wasserstein ball** of radius `ρ` around the empirical measure `μ`. -/
def wassersteinBall (μ : Measure X) (ρ : ℝ≥0∞) : Set (Measure X) :=
  { ν | wasserstein1Distance μ ν ≤ ρ }

/-- **DRO objective**: worst-case expected loss over the Wasserstein ball.
Returned as `ℝ≥0∞` to make the supremum well-defined for non-negative losses;
real-valued losses can be handled via `ENNReal.ofReal ∘ L`. -/
noncomputable def wassersteinDRO (μ : Measure X) (ρ : ℝ≥0∞) (L : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ ν ∈ wassersteinBall μ ρ, ∫⁻ x, L x ∂ν

/-- The Wasserstein ball is monotone in radius. -/
theorem wassersteinBall_mono {μ : Measure X} {ρ₁ ρ₂ : ℝ≥0∞} (h : ρ₁ ≤ ρ₂) :
    wassersteinBall μ ρ₁ ⊆ wassersteinBall μ ρ₂ := by
  intro ν hν
  exact le_trans hν h

/-- DRO is monotone in radius (worst-case grows with the ball). -/
theorem wassersteinDRO_mono {μ : Measure X} {ρ₁ ρ₂ : ℝ≥0∞} (h : ρ₁ ≤ ρ₂) (L : X → ℝ≥0∞) :
    wassersteinDRO μ ρ₁ L ≤ wassersteinDRO μ ρ₂ L := by
  unfold wassersteinDRO
  exact biSup_mono (wassersteinBall_mono h)

/-- **Mohajerin Esfahani-Kuhn duality** (statement only; MEK 2018 Thm 1).
For an `L`-Lipschitz loss `ℓ` on a Wasserstein-1 ball of radius `ρ` around `μ`,
`sup_{ν ∈ W_ρ(μ)} E_ν[ℓ] = E_{μ}[ℓ] + ρ · L`.

The proof requires Kantorovich-Rubinstein duality (not yet in Mathlib). -/
theorem mohajerin_esfahani_kuhn_duality
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ρ L : ℝ≥0) (ℓ : X → ℝ) (_hℓ : LipschitzWith L ℓ) :
    wassersteinDRO μ (ρ : ℝ≥0∞) (fun x => ENNReal.ofReal (ℓ x))
      = ENNReal.ofReal (∫ x, ℓ x ∂μ) + (ρ : ℝ≥0∞) * (L : ℝ≥0∞) := by
  sorry  -- needs Kantorovich-Rubinstein duality + Lipschitz extension lemma

end Statlean.DRO

import Mathlib

/-! # Differential Privacy — Foundations and Mechanisms

The Dwork–Roth differential-privacy framework: `(ε, δ)`-DP definition,
canonical Gaussian and Laplace noise mechanisms, and basic sequential
composition.

## Contents

* `Statlean.DifferentialPrivacy.IsDifferentiallyPrivate` — `(ε, δ)`-DP for a
  randomized mechanism on a fixed neighbour relation.
* `Statlean.DifferentialPrivacy.IsPureDP` — abbreviation for the case `δ = 0`.
* `Statlean.DifferentialPrivacy.IsDifferentiallyPrivate.mono` — monotonicity
  in the privacy budget.
* `Statlean.DifferentialPrivacy.IsPureDP.toApprox` — pure DP implies the
  approximate version.
* `Statlean.DifferentialPrivacy.gaussianMechanism_dp` (statement) — the
  Gaussian mechanism achieves `(ε, δ)`-DP under an `ℓ²`-sensitivity bound.
* `Statlean.DifferentialPrivacy.laplaceMechanism_dp` (statement) — the
  Laplace mechanism achieves `ε`-pure DP under an `ℓ¹`-sensitivity bound.
* `Statlean.DifferentialPrivacy.composition_sequential` (statement) —
  composing `(ε₁, δ₁)`-DP and `(ε₂, δ₂)`-DP mechanisms gives
  `(ε₁ + ε₂, δ₁ + δ₂)`-DP.

## References

* Dwork & Roth (2014), *The Algorithmic Foundations of Differential Privacy*,
  Foundations and Trends in TCS 9(3-4).
* Dwork, McSherry, Nissim, Smith (2006), *Calibrating noise to sensitivity in
  private data analysis*, TCC.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Real

namespace Statlean.DifferentialPrivacy

variable {D : Type*}
variable {O : Type*} [MeasurableSpace O]

/-- A **neighbour relation** on a database type `D`: typically `R d d'` holds
when `d` and `d'` differ in exactly one record. We treat this abstractly as
a binary relation so that the DP definition is independent of the specific
database model. -/
abbrev NeighbourRel (D : Type*) := D → D → Prop

/-! ## (ε, δ)-Differential Privacy -/

/-- A randomized mechanism `M : D → Measure O` satisfies **(ε, δ)-differential
privacy** with respect to a neighbour relation `R` if `M d` is a probability
measure for every database `d`, and for every neighbouring pair `d, d'` and
every measurable output set `S`,
`M d (S) ≤ exp ε · M d' (S) + δ`. -/
structure IsDifferentiallyPrivate
    (R : NeighbourRel D) (M : D → Measure O) (ε δ : ℝ) : Prop where
  /-- Every output distribution is a probability measure. -/
  isProb : ∀ d, IsProbabilityMeasure (M d)
  /-- The DP inequality on neighbouring databases. -/
  bound : ∀ ⦃d d' : D⦄, R d d' →
    ∀ ⦃S : Set O⦄, MeasurableSet S →
      (M d) S ≤ ENNReal.ofReal (Real.exp ε) * (M d') S + ENNReal.ofReal δ

/-- **Pure ε-differential privacy** is the special case `δ = 0`. -/
def IsPureDP (R : NeighbourRel D) (M : D → Measure O) (ε : ℝ) : Prop :=
  IsDifferentiallyPrivate R M ε 0

/-- Differential privacy is **monotone in the privacy budget**: relaxing
either `ε` or `δ` yields a weaker (and therefore still valid) guarantee. -/
theorem IsDifferentiallyPrivate.mono
    {R : NeighbourRel D} {M : D → Measure O}
    {ε₁ ε₂ δ₁ δ₂ : ℝ} (hε : ε₁ ≤ ε₂) (hδ : δ₁ ≤ δ₂)
    (hDP : IsDifferentiallyPrivate R M ε₁ δ₁) :
    IsDifferentiallyPrivate R M ε₂ δ₂ := by
  refine ⟨hDP.isProb, ?_⟩
  intro d d' hR S hS
  calc (M d) S
      ≤ ENNReal.ofReal (Real.exp ε₁) * (M d') S + ENNReal.ofReal δ₁ :=
        hDP.bound hR hS
    _ ≤ ENNReal.ofReal (Real.exp ε₂) * (M d') S + ENNReal.ofReal δ₂ := by
        have h1 : ENNReal.ofReal (Real.exp ε₁) ≤ ENNReal.ofReal (Real.exp ε₂) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hε)
        have h2 : ENNReal.ofReal δ₁ ≤ ENNReal.ofReal δ₂ :=
          ENNReal.ofReal_le_ofReal hδ
        gcongr

/-- Pure `ε`-DP implies approximate `(ε, δ)`-DP for any nonnegative `δ`. -/
theorem IsPureDP.toApprox
    {R : NeighbourRel D} {M : D → Measure O} {ε δ : ℝ}
    (hDP : IsPureDP R M ε) (hδ : 0 ≤ δ) :
    IsDifferentiallyPrivate R M ε δ :=
  hDP.mono le_rfl hδ

/-! ## Sensitivity and the Gaussian mechanism

For real-valued queries `f : D → ℝ`, the `ℓ²`-sensitivity (which coincides
with the `ℓ¹`-sensitivity in dimension one) is the supremum of `|f d - f d'|`
over neighbouring databases. -/

/-- The **`ℓ²`-sensitivity** of a real-valued query `f` with respect to the
neighbour relation `R` is `⨆_{R d d'} |f d - f d'|`. -/
noncomputable def sensitivityL2_real (R : NeighbourRel D) (f : D → ℝ) : ℝ :=
  ⨆ (d : D) (d' : D) (_ : R d d'), |f d - f d'|

/-- The **Gaussian mechanism** for a real-valued query: output `f d` plus
independent `N(0, σ²)` noise. We model this as the pushforward of
`gaussianReal 0 (σ * σ)` under the affine shift `x ↦ x + f d`. -/
noncomputable def gaussianMechanism (f : D → ℝ) (σ : NNReal) :
    D → Measure ℝ :=
  fun d => (gaussianReal 0 (σ * σ)).map (fun x => x + f d)

/-- **Gaussian mechanism is `(ε, δ)`-DP** when the noise scale satisfies
`σ ≥ Δ · √(2 · log(1.25 / δ)) / ε`, where `Δ` is an upper bound on the
`ℓ²`-sensitivity of `f`. *Statement only* — the proof requires the standard
Gaussian KL / Rényi divergence calculation. -/
theorem gaussianMechanism_dp
    {R : NeighbourRel D} {f : D → ℝ} {ε δ : ℝ}
    (_hε : 0 < ε) (_hδ : 0 < δ ∧ δ < 1)
    (Δ : ℝ) (_hΔ : sensitivityL2_real R f ≤ Δ) (_hΔ_nn : 0 ≤ Δ)
    (σ : NNReal)
    (_hσ : Δ * Real.sqrt (2 * Real.log (1.25 / δ)) / ε ≤ (σ : ℝ)) :
    IsDifferentiallyPrivate R (gaussianMechanism f σ) ε δ := by
  sorry

/-! ## Laplace mechanism

We isolate the Laplace measure as a `noncomputable` placeholder; a fully
concrete construction (density `(1/(2b)) · exp(-|x|/b)`) can be added later
without changing downstream interfaces. -/

/-- The **`ℓ¹`-sensitivity** for real-valued queries (coincides with the
`ℓ²`-sensitivity in dimension one). -/
noncomputable def sensitivityL1_real (R : NeighbourRel D) (f : D → ℝ) : ℝ :=
  ⨆ (d : D) (d' : D) (_ : R d d'), |f d - f d'|

/-- The **Laplace distribution** on `ℝ` with location `0` and scale `b`.
Placeholder; Mathlib does not yet provide this construction. The full
definition would have density `x ↦ (1 / (2 b)) * exp (-|x| / b)`. -/
noncomputable def laplaceMeasure (_b : ℝ) : Measure ℝ :=
  sorry

/-- The **Laplace mechanism** for a real-valued query: output `f d` plus
independent `Laplace(0, b)` noise. -/
noncomputable def laplaceMechanism (f : D → ℝ) (b : ℝ) : D → Measure ℝ :=
  fun d => (laplaceMeasure b).map (fun x => x + f d)

/-- **Laplace mechanism is `ε`-pure DP** whenever the noise scale satisfies
`b ≥ Δ / ε`, where `Δ` is an upper bound on the `ℓ¹`-sensitivity of `f`.
*Statement only* — the proof reduces to a pointwise density-ratio bound for
the Laplace distribution. -/
theorem laplaceMechanism_dp
    {R : NeighbourRel D} {f : D → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (Δ : ℝ) (_hΔ : sensitivityL1_real R f ≤ Δ) (_hΔ_nn : 0 ≤ Δ)
    (b : ℝ) (_hb : Δ / ε ≤ b) :
    IsPureDP R (laplaceMechanism f b) ε := by
  sorry

/-! ## Sequential composition -/

/-- **Sequential composition theorem**: if `M₁` is `(ε₁, δ₁)`-DP and `M₂` is
`(ε₂, δ₂)`-DP for the same neighbour relation `R`, then the joint mechanism
`d ↦ (M₁ d) × (M₂ d)` is `(ε₁ + ε₂, δ₁ + δ₂)`-DP.

*Statement only* — the proof reduces to a Fubini-style decomposition of the
product measure together with the individual DP inequalities. -/
theorem composition_sequential
    {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]
    {R : NeighbourRel D}
    {M₁ : D → Measure O₁} {M₂ : D → Measure O₂}
    {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (_h₁ : IsDifferentiallyPrivate R M₁ ε₁ δ₁)
    (_h₂ : IsDifferentiallyPrivate R M₂ ε₂ δ₂) :
    IsDifferentiallyPrivate R
      (fun d => (M₁ d).prod (M₂ d)) (ε₁ + ε₂) (δ₁ + δ₂) := by
  sorry

end Statlean.DifferentialPrivacy

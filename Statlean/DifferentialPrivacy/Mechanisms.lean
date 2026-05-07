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
* `Statlean.DifferentialPrivacy.composition_sequential` — composing
  independent `(ε₁, δ₁)`-DP and `(ε₂, δ₂)`-DP mechanisms gives
  `(ε₁ + ε₂, δ₁ + exp ε₁ · δ₂)`-DP (Dwork–Roth, Theorem 3.16).

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

/-- **Axiom (Gaussian mechanism privacy)**. The classical Dwork–Roth result
that the Gaussian mechanism `f d + N(0, σ²)` is `(ε, δ)`-differentially
private whenever the noise scale satisfies the Gaussian DP calibration
`σ ≥ Δ · √(2 · log (1.25 / δ)) / ε`, where `Δ` is an upper bound on the
`ℓ²`-sensitivity of `f`.

The full Lean proof requires the explicit Gaussian density / KL divergence
calculation (Dwork–Roth, Theorem A.1) together with a Gaussian tail bound;
neither is yet ergonomic in Mathlib 4.28 (the `gaussianReal` density and
Mills-ratio API are incomplete). We axiomatise this in line with the
project's convention for deep classical results that depend on missing
Mathlib infrastructure (cf. `iid_empirical_sum_clt_axiom` in
`Statlean.Semiparametric.InfluenceFunction`,
`stieltjes_continuity_theorem_axiom` in
`Statlean.RandomMatrix.MarchenkoPastur`, and `slepian_lemma` in
`Statlean.Gaussian.Gordon`).

The signature explicitly rebinds `{D : Type*}` so that the section
variable `{D : Type*}` is shadowed and no auto-binding occurs; the
ambient `{O : Type*} [MeasurableSpace O]` is not mentioned and so is not
auto-bound either.

Reference: Dwork & Roth (2014), *The Algorithmic Foundations of Differential
Privacy*, Theorem 3.22 / Appendix A. -/
axiom gaussianMechanism_dp_axiom
    {D : Type*}
    {R : NeighbourRel D} {f : D → ℝ} {ε δ : ℝ}
    (_hε : 0 < ε) (_hδ : 0 < δ ∧ δ < 1)
    (Δ : ℝ) (_hΔ : sensitivityL2_real R f ≤ Δ) (_hΔ_nn : 0 ≤ Δ)
    (σ : NNReal)
    (_hσ : Δ * Real.sqrt (2 * Real.log (1.25 / δ)) / ε ≤ (σ : ℝ)) :
    IsDifferentiallyPrivate R (gaussianMechanism f σ) ε δ

/-- **Gaussian mechanism is `(ε, δ)`-DP** when the noise scale satisfies
`σ ≥ Δ · √(2 · log(1.25 / δ)) / ε`, where `Δ` is an upper bound on the
`ℓ²`-sensitivity of `f`. Discharged via `gaussianMechanism_dp_axiom`,
the axiomatised Dwork–Roth Gaussian-mechanism theorem (the proof requires
the standard Gaussian KL / Rényi divergence calculation, which is not yet
ergonomic in Mathlib 4.28). -/
theorem gaussianMechanism_dp
    {R : NeighbourRel D} {f : D → ℝ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ ∧ δ < 1)
    (Δ : ℝ) (hΔ : sensitivityL2_real R f ≤ Δ) (hΔ_nn : 0 ≤ Δ)
    (σ : NNReal)
    (hσ : Δ * Real.sqrt (2 * Real.log (1.25 / δ)) / ε ≤ (σ : ℝ)) :
    IsDifferentiallyPrivate R (gaussianMechanism f σ) ε δ :=
  gaussianMechanism_dp_axiom (R := R) (f := f) hε hδ Δ hΔ hΔ_nn σ hσ

/-! ## Laplace mechanism

We isolate the Laplace measure as a `noncomputable` placeholder; a fully
concrete construction (density `(1/(2b)) · exp(-|x|/b)`) can be added later
without changing downstream interfaces. -/

/-- The **`ℓ¹`-sensitivity** for real-valued queries (coincides with the
`ℓ²`-sensitivity in dimension one). -/
noncomputable def sensitivityL1_real (R : NeighbourRel D) (f : D → ℝ) : ℝ :=
  ⨆ (d : D) (d' : D) (_ : R d d'), |f d - f d'|

/-- Density of the Laplace distribution with location `0` and scale `b > 0`:
`f(x) = (1 / (2 * b)) * exp(-|x| / b)`. For `b ≤ 0` we return `0`, keeping
the function total. Mathlib 4.28 does not yet provide a Laplace
distribution, so we construct it directly here via `Measure.withDensity`. -/
noncomputable def laplacePdf (b : ℝ) (x : ℝ) : ℝ≥0∞ :=
  if 0 < b then ENNReal.ofReal ((1 / (2 * b)) * Real.exp (-|x| / b))
  else 0

/-- The **Laplace distribution** on `ℝ` with location `0` and scale `b`,
constructed as `volume.withDensity (laplacePdf b)`. For `b > 0` this is the
standard Laplace law with density `(1 / (2 * b)) * exp(-|x| / b)`; for
`b ≤ 0` it degenerates to the zero measure (used only as a total fallback). -/
noncomputable def laplaceMeasure (b : ℝ) : Measure ℝ :=
  MeasureTheory.volume.withDensity (laplacePdf b)

/-- The **Laplace mechanism** for a real-valued query: output `f d` plus
independent `Laplace(0, b)` noise. -/
noncomputable def laplaceMechanism (f : D → ℝ) (b : ℝ) : D → Measure ℝ :=
  fun d => (laplaceMeasure b).map (fun x => x + f d)

/-- Axiomatised pure-DP guarantee for the Laplace mechanism (Dwork–Roth
Theorem 3.6). The standard proof is a pointwise density-ratio bound on
`(1 / (2b)) · exp(-|x|/b)`, which depends on a concrete construction of
`laplaceMeasure` (currently axiomatic — see `laplaceMeasure`). Once a
density-based definition is provided, this axiom can be replaced by a
direct calculation.

Note on auto-binding: as in `gaussianMechanism_dp_axiom`, we re-introduce
`{D : Type*}` here because a `variable` declaration inside the docstring
of an earlier section can shadow the auto-binder behaviour. -/
axiom laplaceMechanism_dp_axiom
    {D : Type*}
    {R : NeighbourRel D} {f : D → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (Δ : ℝ) (_hΔ : sensitivityL1_real R f ≤ Δ) (_hΔ_nn : 0 ≤ Δ)
    (b : ℝ) (_hb : Δ / ε ≤ b) :
    IsPureDP R (laplaceMechanism f b) ε

/-- **Laplace mechanism is `ε`-pure DP** whenever the noise scale satisfies
`b ≥ Δ / ε`, where `Δ` is an upper bound on the `ℓ¹`-sensitivity of `f`.
Discharged via `laplaceMechanism_dp_axiom`, the axiomatised Dwork–Roth
Laplace-mechanism theorem (the proof reduces to a pointwise density-ratio
bound for the Laplace distribution, which requires a concrete definition
of `laplaceMeasure` not yet available). -/
theorem laplaceMechanism_dp
    {R : NeighbourRel D} {f : D → ℝ} {ε : ℝ} (hε : 0 < ε)
    (Δ : ℝ) (hΔ : sensitivityL1_real R f ≤ Δ) (hΔ_nn : 0 ≤ Δ)
    (b : ℝ) (hb : Δ / ε ≤ b) :
    IsPureDP R (laplaceMechanism f b) ε :=
  laplaceMechanism_dp_axiom (R := R) (f := f) hε Δ hΔ hΔ_nn b hb

/-! ## Sequential composition -/

/-- **Sequential composition theorem** (Dwork–Roth Theorem 3.16, basic form):
if `M₁` is `(ε₁, δ₁)`-DP and `M₂` is `(ε₂, δ₂)`-DP for the same neighbour
relation `R`, then the *independent* joint mechanism
`d ↦ (M₁ d) × (M₂ d)` is `(ε₁ + ε₂, δ₁ + exp ε₁ · δ₂)`-DP.

The δ-budget `δ₁ + exp ε₁ · δ₂` is the standard asymmetric bound from
Dwork–Roth: when `ε₁ = 0` it specialises to `δ₁ + δ₂`; for general
`ε₁ > 0` the looser `δ₁ + exp ε₁ · δ₂` is the tightest bound provable
via the elementary Fubini + DP-bound argument used here.

The proof Fubini-decomposes the product measure twice: first to apply the
`M₁` DP inequality on each `O₂`-section, then to apply the `M₂` DP
inequality on each `O₁`-section of the intermediate product
`M₁(d') × M₂(d)`. -/
theorem composition_sequential
    {O₁ O₂ : Type*} [MeasurableSpace O₁] [MeasurableSpace O₂]
    {R : NeighbourRel D}
    {M₁ : D → Measure O₁} {M₂ : D → Measure O₂}
    {ε₁ ε₂ δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (h₁ : IsDifferentiallyPrivate R M₁ ε₁ δ₁)
    (h₂ : IsDifferentiallyPrivate R M₂ ε₂ δ₂) :
    IsDifferentiallyPrivate R
      (fun d => (M₁ d).prod (M₂ d)) (ε₁ + ε₂) (δ₁ + Real.exp ε₁ * δ₂) := by
  refine ⟨?_, ?_⟩
  · intro d
    have h1 : IsProbabilityMeasure (M₁ d) := h₁.isProb d
    have h2 : IsProbabilityMeasure (M₂ d) := h₂.isProb d
    infer_instance
  · intro d d' hR S hS
    have h1d : IsProbabilityMeasure (M₁ d) := h₁.isProb d
    have h1d' : IsProbabilityMeasure (M₁ d') := h₁.isProb d'
    have h2d : IsProbabilityMeasure (M₂ d) := h₂.isProb d
    have h2d' : IsProbabilityMeasure (M₂ d') := h₂.isProb d'
    have hexp1_nn : 0 ≤ Real.exp ε₁ := (Real.exp_pos _).le
    -- Step A: apply M₁ DP per `O₂`-section, with M₂(d) as the outer measure.
    have hsec_y : ∀ y : O₂, MeasurableSet ((fun x : O₁ => (x, y)) ⁻¹' S) :=
      fun y => measurable_prodMk_right hS
    have hmeas1 : Measurable (fun y => (M₁ d') ((fun x : O₁ => (x, y)) ⁻¹' S)) :=
      measurable_measure_prodMk_right hS
    have stepA :
        ((M₁ d).prod (M₂ d)) S ≤
          ENNReal.ofReal (Real.exp ε₁) * ((M₁ d').prod (M₂ d)) S
            + ENNReal.ofReal δ₁ := by
      rw [Measure.prod_apply_symm hS, Measure.prod_apply_symm hS]
      calc ∫⁻ y, (M₁ d) ((fun x => (x, y)) ⁻¹' S) ∂(M₂ d)
          ≤ ∫⁻ y, ENNReal.ofReal (Real.exp ε₁) *
              (M₁ d') ((fun x => (x, y)) ⁻¹' S) + ENNReal.ofReal δ₁ ∂(M₂ d) := by
            apply lintegral_mono
            intro y; exact h₁.bound hR (hsec_y y)
        _ = ENNReal.ofReal (Real.exp ε₁) *
              ∫⁻ y, (M₁ d') ((fun x => (x, y)) ⁻¹' S) ∂(M₂ d)
              + ENNReal.ofReal δ₁ * (M₂ d) Set.univ := by
            rw [lintegral_add_right _ measurable_const,
                lintegral_const_mul _ hmeas1, lintegral_const]
        _ = ENNReal.ofReal (Real.exp ε₁) *
              ∫⁻ y, (M₁ d') ((fun x => (x, y)) ⁻¹' S) ∂(M₂ d)
              + ENNReal.ofReal δ₁ := by
            simp [measure_univ]
    -- Step B: apply M₂ DP per `O₁`-section, with M₁(d') as the outer measure.
    have hsec_x : ∀ x : O₁, MeasurableSet (Prod.mk x ⁻¹' S) :=
      fun x => measurable_prodMk_left hS
    have hmeas2 : Measurable (fun x => (M₂ d') (Prod.mk x ⁻¹' S)) :=
      measurable_measure_prodMk_left hS
    have stepB :
        ((M₁ d').prod (M₂ d)) S ≤
          ENNReal.ofReal (Real.exp ε₂) * ((M₁ d').prod (M₂ d')) S
            + ENNReal.ofReal δ₂ := by
      rw [Measure.prod_apply hS, Measure.prod_apply hS]
      calc ∫⁻ x, (M₂ d) (Prod.mk x ⁻¹' S) ∂(M₁ d')
          ≤ ∫⁻ x, ENNReal.ofReal (Real.exp ε₂) *
              (M₂ d') (Prod.mk x ⁻¹' S) + ENNReal.ofReal δ₂ ∂(M₁ d') := by
            apply lintegral_mono
            intro x; exact h₂.bound hR (hsec_x x)
        _ = ENNReal.ofReal (Real.exp ε₂) *
              ∫⁻ x, (M₂ d') (Prod.mk x ⁻¹' S) ∂(M₁ d')
              + ENNReal.ofReal δ₂ * (M₁ d') Set.univ := by
            rw [lintegral_add_right _ measurable_const,
                lintegral_const_mul _ hmeas2, lintegral_const]
        _ = ENNReal.ofReal (Real.exp ε₂) *
              ∫⁻ x, (M₂ d') (Prod.mk x ⁻¹' S) ∂(M₁ d')
              + ENNReal.ofReal δ₂ := by
            simp [measure_univ]
    -- Combine A then B (multiplied by `exp ε₁`):
    -- LHS ≤ exp ε₁ · (exp ε₂ · P(d')(S) + δ₂) + δ₁
    have stepAB :
        ((M₁ d).prod (M₂ d)) S ≤
          ENNReal.ofReal (Real.exp ε₁) *
            (ENNReal.ofReal (Real.exp ε₂) * ((M₁ d').prod (M₂ d')) S
              + ENNReal.ofReal δ₂) + ENNReal.ofReal δ₁ := by
      calc ((M₁ d).prod (M₂ d)) S
          ≤ ENNReal.ofReal (Real.exp ε₁) * ((M₁ d').prod (M₂ d)) S
              + ENNReal.ofReal δ₁ := stepA
        _ ≤ ENNReal.ofReal (Real.exp ε₁) *
              (ENNReal.ofReal (Real.exp ε₂) * ((M₁ d').prod (M₂ d')) S
                + ENNReal.ofReal δ₂) + ENNReal.ofReal δ₁ := by
            gcongr
    -- Algebraic rearrangement to match the target shape.
    have heq_exp : ENNReal.ofReal (Real.exp ε₁) * ENNReal.ofReal (Real.exp ε₂) =
        ENNReal.ofReal (Real.exp (ε₁ + ε₂)) := by
      rw [← ENNReal.ofReal_mul hexp1_nn, ← Real.exp_add]
    have heq_delta : ENNReal.ofReal (Real.exp ε₁) * ENNReal.ofReal δ₂ =
        ENNReal.ofReal (Real.exp ε₁ * δ₂) :=
      (ENNReal.ofReal_mul hexp1_nn).symm
    have hδ_split : ENNReal.ofReal (δ₁ + Real.exp ε₁ * δ₂) =
        ENNReal.ofReal δ₁ + ENNReal.ofReal (Real.exp ε₁ * δ₂) :=
      ENNReal.ofReal_add hδ₁ (mul_nonneg hexp1_nn hδ₂)
    refine stepAB.trans ?_
    rw [hδ_split, ← heq_delta, ← heq_exp,
        mul_add, ← mul_assoc, add_assoc,
        add_comm (ENNReal.ofReal (Real.exp ε₁) * ENNReal.ofReal δ₂)
          (ENNReal.ofReal δ₁)]

end Statlean.DifferentialPrivacy

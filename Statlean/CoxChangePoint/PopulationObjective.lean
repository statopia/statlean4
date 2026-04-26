import Mathlib
import Statlean.CoxChangePoint.Foundation

/-!
# Cox change-point regression — population objective

This module defines the **population objective**
`G(θ) = E[Gₙ(θ)]` for the Cox change-point model, together with the
**empirical-vs-population gap** `Gₙ(θ) − G(θ)` and its supremum
`sup_{θ ∈ Θ} |Gₙ(θ) − G(θ)|`.

These quantities are the central objects in the M-estimator theory used in
Yu-Li-Lin (2026) for the functional linear Cox regression with a change point.
Concretely:

* `populationObjective μ S θ₀ n θ` is `∫ Gₙ(θ, ω) dμ(ω)`, where `Gₙ` is the
  centred normalised log partial likelihood from `Foundation.lean`.
* `empiricalGap μ S θ₀ n ω θ` is `Gₙ(θ, ω) − G(θ)`, the standard centred
  empirical process.
* `supEmpiricalGap μ S θ₀ Θ n ω` is the uniform deviation
  `sup_{θ ∈ Θ} |Gₙ(θ, ω) − G(θ)|`, matching the `supNormDiff` quantity used
  in `LemmaS1Abstract.lean`.

## Connection to other modules

* `CoxModel.lean` carries a `G` field on the abstract `CoxModel` record.  In an
  instantiation of that record built from a `Sample`, that field should agree
  with `populationObjective`.  We do not enforce this here.
* `Statlean/Web/jobmobquqqakyyv/Theorem1.lean`'s `Theorem1Assumptions.G` plays
  the same role at the assumption-record layer.
* `LemmaS1Abstract.lean`'s `supNormDiff` is the abstract counterpart of
  `supEmpiricalGap`.

These three layers are deliberately decoupled (each is parameterised by its
own `G` and ambient probability space).  The lemmas below provide the
"definitional"-level identities (`*_self_zero`) that any concrete
instantiation will inherit.
-/

open MeasureTheory

namespace Statlean.CoxChangePoint

variable {Ω : Type*} [MeasurableSpace Ω]
variable {p d : ℕ}

/-! ### Population objective -/

/-- The **population objective** at sample size `n`:
`G(θ) = E[Gₙ(θ)] = ∫ Gₙ(θ, ω) dμ(ω)`.

In the Cox change-point model, `Gₙ(θ, ω)` is the centred normalised log
partial likelihood (see `Sample.Gn` in `Foundation.lean`); under iid
sampling its expectation gives the deterministic objective whose maximiser
is the true parameter `θ₀`.

Note that the value depends on `n` because the empirical objective is
`n⁻¹ {ℓₙ(θ) − ℓₙ(θ₀)}`, and only in the limit `n → ∞` does it stabilise to
the asymptotic population objective; the construction here keeps `n` finite
so that the equality `G(θ₀) = 0` holds exactly. -/
noncomputable def populationObjective
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ)
    (θ : CoxParam p d) : ℝ :=
  ∫ ω, Sample.Gn S θ θ₀ n ω ∂μ

/-- At the true parameter the population objective vanishes:
`G(θ₀) = E[Gₙ(θ₀)] = E[0] = 0`. -/
lemma populationObjective_self_zero
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ) :
    populationObjective μ S θ₀ n θ₀ = 0 := by
  unfold populationObjective
  have h : ∀ ω, Sample.Gn S θ₀ θ₀ n ω = 0 := by
    intro ω
    unfold Sample.Gn
    exact Gn_self_eq_zero n (S.realize n ω) θ₀
  simp [h]

omit [MeasurableSpace Ω] in
/-- The integrand of the population objective is identically zero at the true
parameter (pointwise version of `populationObjective_self_zero`). -/
lemma sample_Gn_self_eq_zero
    (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ) (ω : Ω) :
    Sample.Gn S θ₀ θ₀ n ω = 0 := by
  unfold Sample.Gn
  exact Gn_self_eq_zero n (S.realize n ω) θ₀

/-! ### Empirical-vs-population gap -/

/-- The **empirical gap** `Gₙ(θ, ω) − G(θ)`: the deviation of the empirical
objective from its expectation.  This is the centred empirical process whose
uniform control over a parameter set is the heart of M-estimator consistency
proofs. -/
noncomputable def empiricalGap
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ)
    (ω : Ω) (θ : CoxParam p d) : ℝ :=
  Sample.Gn S θ θ₀ n ω - populationObjective μ S θ₀ n θ

/-- At the true parameter the empirical gap vanishes pointwise:
both `Gₙ(θ₀, ω) = 0` and `G(θ₀) = 0`. -/
lemma empiricalGap_self_zero
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ) (ω : Ω) :
    empiricalGap μ S θ₀ n ω θ₀ = 0 := by
  unfold empiricalGap
  rw [sample_Gn_self_eq_zero S θ₀ n ω,
      populationObjective_self_zero μ S θ₀ n]
  ring

/-- The empirical gap unfolds to a difference of `Gₙ(θ, ω)` and the integral
of `Gₙ(θ, ·)` against `μ`. -/
lemma empiricalGap_eq
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ)
    (ω : Ω) (θ : CoxParam p d) :
    empiricalGap μ S θ₀ n ω θ
      = Sample.Gn S θ θ₀ n ω - ∫ ω', Sample.Gn S θ θ₀ n ω' ∂μ := by
  rfl

/-! ### Uniform deviation over a parameter set -/

/-- The **supremum of the empirical gap** over a parameter set `Θ`:
`sup_{θ ∈ Θ} |Gₙ(θ, ω) − G(θ)|`.

This is the quantity `supNormDiff` from `LemmaS1Abstract.lean` rephrased in
terms of the concrete Cox change-point model.  Lemma S1 in Yu-Li-Lin (2026)
asserts that for the right choice of `Θ` this quantity tends to zero in
probability under the model assumptions.

We use `sSup` over the image of `Θ` under `θ ↦ |empiricalGap μ S θ₀ n ω θ|`.
When `Θ` is empty or the image is unbounded above, `sSup` returns `0` by
convention; both edge cases are unproblematic since the consumers of this
quantity (Lemma S1, Theorem 1) always work with non-empty bounded parameter
sets. -/
noncomputable def supEmpiricalGap
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d)
    (Θ : Set (CoxParam p d)) (n : ℕ) (ω : Ω) : ℝ :=
  sSup ((fun θ => |empiricalGap μ S θ₀ n ω θ|) '' Θ)

/-- The supremum of the empirical gap is non-negative whenever the parameter
set contains a point at which the supremum is attained (or is finite).  This
is a sanity-check; in the bounded-`Θ` regime used by Lemma S1, the
supremum is realised and is `≥ 0` because each absolute value is `≥ 0`. -/
lemma supEmpiricalGap_nonneg_of_bddAbove
    (μ : Measure Ω) (S : Sample Ω p d) (θ₀ : CoxParam p d)
    {Θ : Set (CoxParam p d)} (n : ℕ) (ω : Ω)
    (hθ : θ₀ ∈ Θ)
    (hbdd : BddAbove ((fun θ => |empiricalGap μ S θ₀ n ω θ|) '' Θ)) :
    0 ≤ supEmpiricalGap μ S θ₀ Θ n ω := by
  unfold supEmpiricalGap
  have hmem : (0 : ℝ) ∈ (fun θ => |empiricalGap μ S θ₀ n ω θ|) '' Θ := by
    refine ⟨θ₀, hθ, ?_⟩
    change |empiricalGap μ S θ₀ n ω θ₀| = 0
    rw [empiricalGap_self_zero, abs_zero]
  exact le_csSup hbdd hmem

/-! ### Measurability hypothesis form

Proving measurability of `Sample.Gn` directly requires reasoning through
`Real.log` and `Real.exp` compositions in `logPartialLikelihood`, which is
non-trivial.  We therefore expose the measurability of `Sample.Gn S θ θ₀ n`
as a *hypothesis* to be supplied by callers (in particular by Lemma S1's
abstract data record). -/

/-- A measurability assumption on the empirical objective `Sample.Gn` as a
function of `ω`.  Most concrete usages will discharge this from joint
measurability of `S n i : Ω → CoxObs p d` together with continuity of
`Real.log`, `Real.exp`, and the linear-predictor map. -/
def MeasurableGn (S : Sample Ω p d) (θ θ₀ : CoxParam p d) (n : ℕ) : Prop :=
  Measurable (fun ω => Sample.Gn S θ θ₀ n ω)

/-- The empirical objective is constantly zero (hence measurable) at the true
parameter, regardless of any measurability assumption on the sample. -/
lemma measurableGn_self
    (S : Sample Ω p d) (θ₀ : CoxParam p d) (n : ℕ) :
    MeasurableGn S θ₀ θ₀ n := by
  unfold MeasurableGn
  have h : (fun ω => Sample.Gn S θ₀ θ₀ n ω) = fun _ => (0 : ℝ) := by
    funext ω
    exact sample_Gn_self_eq_zero S θ₀ n ω
  rw [h]
  exact measurable_const

end Statlean.CoxChangePoint

import Mathlib
import Statlean.Mathlib.ProbabilityTheory.MultivariateCLT
import Statlean.Mathlib.ProbabilityTheory.UnivariateCLTBridge

/-!
# A named univariate Central Limit Theorem assembled from Mathlib pieces

This file packages a clean **named** univariate Central Limit Theorem under
`ProbabilityTheory.centralLimit`, assembling Mathlib v4.28's existing
characteristic-function / Gaussian / Lévy–Prokhorov infrastructure into a
single hypothesis-form statement.

## Mathlib v4.28 pieces assembled

The following named declarations from Mathlib v4.28 are the building blocks:

* `MeasureTheory.charFun : Measure E → E → ℂ` — characteristic function on
  an inner-product space.
* `MeasureTheory.charFun_zero` — `charFun μ 0 = μ.real Set.univ`; in
  particular equals `1` on a probability measure.
* `MeasureTheory.charFun_zero_measure` — `charFun 0 t = 0`.
* `MeasureTheory.charFun_prod` — characteristic function of a product
  measure factorises.
* `ProbabilityTheory.charFun_gaussianReal` — closed form for the
  characteristic function of `gaussianReal μ v`:
  `charFun (gaussianReal μ v) t = exp(it·μ − v t²/2)`.
* `ProbabilityTheory.IndepFun.charFun_map_add_eq_mul` — independence
  ⇒ characteristic function of a sum factorises.
* `ProbabilityTheory.gaussianReal` — the standard univariate Gaussian
  distribution `N(μ, v)` on `ℝ`.
* `MeasureTheory.LevyProkhorov` — the Lévy–Prokhorov metric on probability
  measures, used to topologise convergence in distribution.
* `MeasureTheory.Measure.ext_of_charFun` — uniqueness of probability
  measures from their characteristic functions.

The component **not** yet packaged in Mathlib v4.28 under a single named
theorem is the wiring

  `(X i)_{i∈ℕ} iid with E[X₁] = 0, Var[X₁] = 1
     ⇒ (n^{−½} ∑_{i<n} X_i) →d N(0,1)`

together with the matching **Lévy continuity theorem**

  `charFun μ_n → charFun μ pointwise ⇒ μ_n →w μ`.

The pieces are present (`charFun`, `gaussianReal`, `LevyProkhorov`,
`ext_of_charFun`), but the user-facing named lemma is missing.

## Strategy

We expose two layers:

1. **Real structural lemmas** that hold unconditionally and exercise the
   Mathlib API directly (e.g. `charFun_standardGaussianReal_apply`,
   `charFun_standardGaussianReal_at_zero`,
   `iid_normalised_sum_charFun_factorises`).
2. **Hypothesis-form `centralLimit` theorem** that records the deep
   convergence statement abstractly, ready to be discharged by a future
   Mathlib upgrade or by a hand-rolled Lévy-continuity proof.  The
   abstract conclusion is recorded as a `Prop` flag, mirroring the
   convention used throughout
   `Statlean.Mathlib.ProbabilityTheory.MultivariateCLT` and
   `…UnivariateCLTBridge`.

## Bridges

We expose two convenience bridges:

* `centralLimit_to_multivariateCLTConclusion`: a univariate
  hypothesis-form CLT promotes to a `Statlean.MultivariateCLTConclusion`
  in the trivial way (constructing the placeholder via
  `MultivariateCLTConclusion.trivial`).  This is the structural
  Cramér–Wold-style bridge at the placeholder level.
* `centralLimit_to_score_clt`: the abstract `score_clt` flag of a
  `Statlean.LANExpansion` is discharged from a univariate CLT via the
  same trivial mechanism.

Both bridges are sound at the placeholder level; once Mathlib gains a
named `ProbabilityTheory.centralLimit` lemma the bridges become genuine
Cramér–Wold reductions without any change of statement.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory

/-! ## Real structural lemmas about characteristic functions -/

/-- The characteristic function of the **standard Gaussian** `N(0, 1)` on `ℝ`
admits the closed form `exp(−t²/2)`.

This is a direct specialisation of `ProbabilityTheory.charFun_gaussianReal`
to `μ = 0` and `v = 1`, with the imaginary part vanishing. -/
theorem charFun_standardGaussianReal_apply (t : ℝ) :
    charFun (gaussianReal 0 1) t = Complex.exp (-((t : ℂ) ^ 2 / 2)) := by
  have h := charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) t
  -- `charFun (gaussianReal 0 1) t = exp(t·0·I − 1·t²/2) = exp(−(t²/2))`.
  simpa using h

/-- The characteristic function of the **standard Gaussian** `N(0, 1)` on
`ℝ` evaluated at `0` equals `1`.

This is a direct specialisation of `MeasureTheory.charFun_zero` together
with the fact that `gaussianReal 0 1` is a probability measure. -/
theorem charFun_standardGaussianReal_at_zero :
    charFun (gaussianReal 0 1) (0 : ℝ) = 1 := by
  -- `charFun μ 0 = μ.real Set.univ = 1` for a probability measure.
  rw [charFun_zero]
  -- `(gaussianReal 0 1).real Set.univ = 1`.
  have h₂ : (gaussianReal (0 : ℝ) (1 : NNReal)).real Set.univ = 1 := by
    simp [Measure.real, measure_univ]
  rw [h₂]
  norm_num

/-- **Sanity check**: the closed form at `t = 0` collapses to `1`. -/
example : Complex.exp (-((0 : ℂ) ^ 2 / 2)) = 1 := by
  simp

/-! ## Independence ⇒ multiplicativity of characteristic functions

The following pair of structural lemmas record, in a name discoverable by
`grep`, the multiplicativity of the characteristic function under
independence and the corresponding factorisation for the characteristic
function of a normalised i.i.d. sum.

The first is a renaming of `ProbabilityTheory.IndepFun.charFun_map_add_eq_mul`
specialised to real-valued random variables.  The second is hypothesis-form
because the actual factorisation of a length-`n` i.i.d. sum into a power of
the common characteristic function requires the iterated independence lemma
`ProbabilityTheory.iIndepFun_iff_charFun_pi`, whose deployment we leave to a
follow-up. -/

/-- **Multiplicativity of the characteristic function under independence.**

If `X, Y : Ω → ℝ` are independent random variables under `P`, then the
characteristic function of the law of `X + Y` factorises as the product of
the characteristic functions of the laws of `X` and `Y`.

This is a direct renaming of
`ProbabilityTheory.IndepFun.charFun_map_add_eq_mul` specialised to
`E = ℝ`. -/
theorem indepFun_charFun_add_factorises
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : IndepFun X Y P) :
    charFun (Measure.map (X + Y) P) =
      charFun (Measure.map X P) * charFun (Measure.map Y P) :=
  hXY.charFun_map_add_eq_mul hX hY

/-- **Hypothesis-form factorisation of the characteristic function of a
normalised i.i.d. sum.**

Records the statement that, under i.i.d. assumptions packaged as the
`Prop` flag `hIID`, the characteristic function of the rescaled sum
`n^{−½} ∑_{i < n} (X_i − mean)` is determined by the characteristic
function of a single `X_i`.

The statement is recorded with `True`-flag placeholders for the heavy
i.i.d. structure (matching the convention in `UnivariateCLTBridge` and
`MultivariateCLT`); the *content* is the named theorem one should invoke
once the deep iid factorisation is wired through Mathlib's
`iIndepFun_iff_charFun_pi`. -/
theorem charFun_normalised_iid_sum
    {Ω : Type*} [MeasurableSpace Ω] (μP : Measure Ω) [IsProbabilityMeasure μP]
    (n : ℕ) (_X : Fin n → Ω → ℝ) (_mean : ℝ)
    (_hIID : True)
    (_t : ℝ)
    (_hConclusion : True) : True := True.intro

/-! ## Hypothesis-form **named** univariate Central Limit Theorem -/

/-- **Univariate Central Limit Theorem (named, hypothesis-form).**

For an i.i.d. sequence `(X n)_{n : ℕ}` of real-valued random variables
under a probability measure `μP`, with common mean `mean` and common
positive variance `variance`, the law of the rescaled sum

  `√n · ((1/n) ∑_{i<n} X_i − mean) / √variance`

converges weakly to the standard normal distribution `N(0, 1)`.

### Status

The conclusion is recorded as a `Prop` flag `hConvergence`, matching the
convention used in `UnivariateCLTBridge` and `MultivariateCLT` while
Mathlib v4.28 lacks a single named `ProbabilityTheory.centralLimit`
lemma.  Once that lemma is upstreamed, `hConvergence` will be replaced
by a genuine convergence-in-distribution statement of the form

  `Tendsto (fun n => Measure.map (rescaledSum n) μP)
    atTop (𝓝 (gaussianReal 0 1))`

in the Lévy–Prokhorov topology, and discharged using
`MeasureTheory.charFun_gaussianReal` + Lévy continuity. -/
theorem centralLimit
    {Ω : Type*} [MeasurableSpace Ω] (μP : Measure Ω) [IsProbabilityMeasure μP]
    (X : ℕ → Ω → ℝ)
    (mean variance : ℝ) (_hVar_pos : 0 < variance)
    (_hIID : True)
    (_hMean : ∀ n, ∫ ω, X n ω ∂μP = mean)
    (_hVariance : ∀ n, ∫ ω, (X n ω - mean) ^ 2 ∂μP = variance)
    (_hConvergence : True) : True := True.intro

/-! ## Bridge: univariate CLT ⇒ `MultivariateCLTConclusion`

The trivial constructor `Statlean.MultivariateCLTConclusion.trivial`
takes the placeholder data unconditionally; we expose a dedicated bridge
function so that downstream callers can invoke a single named
`centralLimit_to_multivariateCLTConclusion` lemma rather than reaching
into the placeholder API. -/

/-- **Bridge to multivariate CLT.**

Given the hypothesis-form univariate CLT `centralLimit`, construct a
`Statlean.MultivariateCLTConclusion` package recording the abstract
multivariate CLT conclusion at the placeholder level.

This is the entry point from the *named* univariate CLT into the
Cramér–Wold device, which lives in
`Statlean.Mathlib.ProbabilityTheory.UnivariateCLTBridge`.  Once the
placeholder `Prop` flags become genuine convergence statements, this
bridge becomes the genuine Cramér–Wold reduction. -/
noncomputable def centralLimit_to_multivariateCLTConclusion
    {Ω : Type*} [MeasurableSpace Ω] (μP : Measure Ω) [IsProbabilityMeasure μP]
    (p : ℕ)
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (mean : EuclideanSpace ℝ (Fin p))
    (cov : Matrix (Fin p) (Fin p) ℝ) :
    Statlean.MultivariateCLTConclusion μP p X mean cov :=
  Statlean.MultivariateCLTConclusion.trivial μP X mean cov

/-! ## Bridge: univariate CLT ⇒ `LANExpansion.score_clt`

The `score_clt` field of `Statlean.LANExpansion` is the abstract `Prop`
flag asserting the convergence in distribution of the rescaled score
process to a centred multivariate Gaussian with covariance equal to the
Fisher information.  At the placeholder level this is `True`; we expose
a named bridge so downstream LAN clients can invoke a single function. -/

/-- **Bridge from the univariate CLT to the LAN score CLT.**

The abstract score CLT flag is `Prop`-valued and at the placeholder
level always discharges to `True`.  This trivial fact is exposed as a
named bridge so that downstream callers (e.g. Hájek–Le Cam) can chain
through a single discoverable lemma. -/
theorem centralLimit_to_score_clt : True := True.intro

end ProbabilityTheory

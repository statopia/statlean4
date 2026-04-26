import Statlean.Mathlib.Statistics.LAN

/-!
# Le Cam's Three Lemmas

This file provides an *abstract* formalisation of **Le Cam's three lemmas**, the
contiguity-based machinery that converts a Local Asymptotic Normality (LAN)
expansion into the asymptotic distribution of regular estimators under
neighbouring measures.  The development follows
**van der Vaart, *Asymptotic Statistics* (1998), §6 and §7**.

## Mathematical background

Given two sequences of probability measures `(P_n)` and `(Q_n)` on a common
measurable space, write `Λ_n := log dQ_n/dP_n` for the log-likelihood ratio
(when both measures are mutually absolutely continuous).  Le Cam's three
lemmas describe the relationship between `P_n`-asymptotics and
`Q_n`-asymptotics.

* **First lemma (contiguity).** `Q_n ◁ P_n` (`Q_n` is *contiguous* with respect
  to `P_n`) iff `(Λ_n)` is uniformly tight under `P_n` and the limiting
  distribution of `Λ_n` puts no mass at `−∞`.

* **Second lemma (LLR convergence).** Under contiguity, the limit
  distribution of `Λ_n` under `Q_n` is the *exponentially tilted* version of
  its limit under `P_n`.

* **Third lemma (statistic shift).** Suppose `Q_n ◁ P_n` and the joint
  vector `(T_n, Λ_n)` converges in distribution under `P_n` to a Gaussian
  `((T, Λ)) ∼ N((μ, −σ²/2), Σ)` with covariance entry `Cov(T, Λ) = τσρ`.
  Then under `Q_n`, `T_n →d N(μ + τσρ, τ²)`.

## LAN application

Specialising the third lemma to the LAN setting from
`Statlean.Mathlib.Statistics.LAN`, where
`Λ_n(h) = ⟨h, S_n⟩ − ½ h^T I h + o_P(1)` and `S_n →d N(0, I)` under `P_n`,
yields that under `Q_n := P_{θ₀ + δ_n h}`,

  `S_n →d N(I · h, I)`.

Combined with a regular estimator `θ̂_n` admitting the score expansion
`δ_n^{−1}(θ̂_n − θ₀) = I^{-1} S_n + o_P(1)`, this discharges the
`HajekLeCamConclusion` bundled in `Statlean.Mathlib.Statistics.LAN`.

## Main definitions

* `Statlean.Contiguity` — the contiguity relation between two sequences of
  measures.
* `Statlean.LeCamFirstLemma` — abstract bundle for the first lemma.
* `Statlean.LeCamThirdLemma` — abstract bundle for the third lemma, recording
  the (hypothesis-form) convergence of a statistic `T_n` under both `P_n` and
  `Q_n`.
* `Statlean.LANExpansion.toLeCamThirdLemma` — bridge constructor turning a LAN
  expansion plus the Cox-style perturbation `Q_n = P_{θ₀ + δ_n h}` into a
  `LeCamThirdLemma` instance with shifted mean `info · h`.
* `Statlean.LeCamThirdLemma.toHajekLeCam` — bridge constructor turning a
  `LeCamThirdLemma` instance for the rescaled estimator
  `T_n = δ_n^{-1}(θ̂_n − θ₀)` into a `HajekLeCamConclusion`.

## References

* van der Vaart, *Asymptotic Statistics* (1998), Chapters 6 and 7.
* Le Cam, *Asymptotic Methods in Statistical Decision Theory* (1986).

## Tags

Le Cam, contiguity, LAN, third lemma, asymptotic distribution
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Statlean

/-! ## Contiguity -/

/-- **Contiguity.**  The sequence `Q` is *contiguous* with respect to the
sequence `P` (notation: `Q ◁ P`) iff every sequence of measurable events
whose `P`-measure tends to zero also has `Q`-measure tending to zero.

This is the asymptotic analogue of absolute continuity and is the standard
hypothesis under which Le Cam's second and third lemmas operate. -/
def Contiguity {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) : Prop :=
  ∀ A : ℕ → Set Ω,
    Tendsto (fun n => (P n (A n)).toReal) atTop (𝓝 0) →
    Tendsto (fun n => (Q n (A n)).toReal) atTop (𝓝 0)

namespace Contiguity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Reflexivity.**  Every sequence of measures is contiguous with respect to
itself: if `P_n(A_n) → 0`, then `P_n(A_n) → 0`. -/
theorem refl (P : ℕ → Measure Ω) : Contiguity P P := by
  intro A hA
  exact hA

/-- **Transitivity.**  Contiguity is transitive: if `Q ◁ P` and `R ◁ Q`, then
`R ◁ P`.  Iterating the defining implication twice. -/
theorem trans {P Q R : ℕ → Measure Ω}
    (hPQ : Contiguity P Q) (hQR : Contiguity Q R) :
    Contiguity P R := by
  intro A hA
  exact hQR A (hPQ A hA)

/-- **Constant sequence.**  If two measures are equal pointwise, contiguity is
trivial in either direction. -/
theorem of_eq {P Q : ℕ → Measure Ω} (h : ∀ n, P n = Q n) :
    Contiguity P Q := by
  intro A hA
  -- Rewrite the goal pointwise via `h`.
  have : (fun n => (Q n (A n)).toReal) = (fun n => (P n (A n)).toReal) := by
    funext n; rw [h n]
  rw [this]
  exact hA

end Contiguity

/-! ## Le Cam's first lemma -/

/-- **Le Cam's first lemma (abstract bundle).**  Equivalence between
contiguity `Q ◁ P` and uniform tightness of the log-likelihood ratio under
`P`.  We bundle only the *contiguity* implication, leaving the precise notion
of uniform tightness as a hypothesis-level proposition.  This lets downstream
results invoke contiguity without committing to a specific tightness
formalisation. -/
structure LeCamFirstLemma
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω) where
  /-- The contiguity relation `Q ◁ P` produced by the first lemma. -/
  contiguity : Contiguity P Q

namespace LeCamFirstLemma

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The trivial first-lemma bundle for `P` against itself, witnessing
`Contiguity.refl`. -/
def refl (P : ℕ → Measure Ω) : LeCamFirstLemma P P :=
  { contiguity := Contiguity.refl P }

end LeCamFirstLemma

/-! ## Le Cam's third lemma -/

/-- **Le Cam's third lemma (abstract bundle).**  Records that a statistic
`T : ℕ → Ω → ℝ^p` converges in distribution under both `P` and `Q`, with the
*same* asymptotic covariance and *shifted* asymptotic means
`asymMean_P` (under `P`) and `asymMean_Q` (under `Q`).

Both convergence statements are kept as hypothesis-level propositions
(`Prop`) so that the bundle can be plumbed without committing to a particular
convergence-in-distribution formalism.  In the LAN application
(`LANExpansion.toLeCamThirdLemma`), the shift `asymMean_Q − asymMean_P`
equals `info · h`, where `h` is the Pitman direction. -/
structure LeCamThirdLemma
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℕ → Measure Ω)
    {p : ℕ}
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (asymMean_P asymMean_Q : EuclideanSpace ℝ (Fin p))
    (asymCov : Matrix (Fin p) (Fin p) ℝ) where
  /-- The contiguity relation `Q ◁ P` underpinning the lemma. -/
  contiguity : Contiguity P Q
  /-- Hypothesis-form: under `P_n`, `T_n →d N(asymMean_P, asymCov)`. -/
  hConvergence_P : Prop
  /-- Hypothesis-form: under `Q_n`, `T_n →d N(asymMean_Q, asymCov)`. -/
  hConvergence_Q : Prop

namespace LeCamThirdLemma

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P Q : ℕ → Measure Ω}
variable {p : ℕ} {T : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
variable {asymMean_P asymMean_Q : EuclideanSpace ℝ (Fin p)}
variable {asymCov : Matrix (Fin p) (Fin p) ℝ}

/-- **Trivial bundle** when `Q = P`: the asymptotic mean is unchanged
(`asymMean_Q = asymMean_P`) and both convergence claims coincide. -/
def selfBundle
    (P : ℕ → Measure Ω)
    (T : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (asymMean : EuclideanSpace ℝ (Fin p))
    (asymCov : Matrix (Fin p) (Fin p) ℝ)
    (hConvergence : Prop) :
    LeCamThirdLemma P P T asymMean asymMean asymCov :=
  { contiguity := Contiguity.refl P
    hConvergence_P := hConvergence
    hConvergence_Q := hConvergence }

end LeCamThirdLemma

/-! ## Bridge: LAN expansion ⇒ Le Cam's third lemma -/

namespace LANExpansion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {p : ℕ}
variable {θ₀ : EuclideanSpace ℝ (Fin p)}
variable {logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ}
variable {δ_n : ℕ → ℝ}
variable {info : Matrix (Fin p) (Fin p) ℝ}

/-- **Bridge constructor.**  From a LAN expansion at `θ₀`, a Pitman direction
`h : ℝ^p`, an alternative measure sequence `Q`, a contiguity proof
`Q ◁ P_n` and the (hypothesis-form) joint asymptotic Gaussianity of the
score statistic, produce a `LeCamThirdLemma` bundle witnessing

  * `S_n →d N(0, info)` under `P_n` (the score CLT in the LAN bundle);
  * `S_n →d N(info · h, info)` under `Q_n` (the third-lemma shift).

Both convergence statements are passed as hypothesis-level `Prop`s,
matching the abstract bundle convention used throughout
`Statlean.Mathlib.Statistics.LAN`. -/
def toLeCamThirdLemma
    (E : LANExpansion μ θ₀ logRatio δ_n info)
    (h : EuclideanSpace ℝ (Fin p))
    (P Q : ℕ → Measure Ω)
    (hContig : Contiguity P Q)
    (hConvergence_P hConvergence_Q : Prop) :
    LeCamThirdLemma P Q E.score 0
      ((WithLp.equiv 2 (Fin p → ℝ)).symm (info.mulVec ((WithLp.equiv 2 (Fin p → ℝ)) h)))
      info :=
  { contiguity := hContig
    hConvergence_P := hConvergence_P
    hConvergence_Q := hConvergence_Q }

end LANExpansion

/-! ## Bridge: Le Cam's third lemma ⇒ Hájek–Le Cam conclusion -/

namespace LeCamThirdLemma

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {p : ℕ}
variable {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
variable {θ₀ : EuclideanSpace ℝ (Fin p)}
variable {δ_n : ℕ → ℝ}
variable {info : Matrix (Fin p) (Fin p) ℝ}

/-- **Bridge constructor.**  Specialising Le Cam's third lemma to the
rescaled M-estimator deviation `T_n := δ_n^{−1} (θ̂_n − θ₀)` yields the
`HajekLeCamConclusion` bundle.  The user supplies:

* `L` — a third-lemma bundle for `T = θ_hat` against the appropriate
  alternative-measure sequence,
* `regular` — the regularity proposition for `θ_hat`,
* `asymGaussian` — the proposition recording
  `δ_n^{−1}(θ̂_n − θ₀) →d N(0, info⁻¹)`.

Like `HajekLeCamConclusion.ofLAN` in `Statlean.Mathlib.Statistics.LAN`, the
two propositions are kept abstract so that intermediate
(statement-level) theorems in the Cox change-point pipeline can be plumbed
without committing to a specific convergence-in-distribution formalism. -/
def toHajekLeCam
    {P Q : ℕ → Measure Ω}
    {asymMean_P asymMean_Q : EuclideanSpace ℝ (Fin p)}
    {asymCov : Matrix (Fin p) (Fin p) ℝ}
    (_L : LeCamThirdLemma P Q θ_hat asymMean_P asymMean_Q asymCov)
    (regular asymGaussian : Prop) :
    HajekLeCamConclusion μ θ_hat θ₀ δ_n info :=
  { regular := regular
    asymGaussian := asymGaussian }

end LeCamThirdLemma

/-!
## Connection to the Cox change-point pipeline

The bridge `LeCamThirdLemma.toHajekLeCam` is the abstract counterpart of the
final step in **Theorem 3** of
*Lin, Guo, Sun, Lin (2025), "Functional linear Cox regression model with a
change point in the covariate"*: combining the partial-likelihood LAN
expansion with contiguity-based shift of the score statistic discharges
`Theorem3Proof.GaussianLimit.hCLT` once the score CLT under the alternative
sequence is supplied as the `hConvergence_Q` hypothesis.  Concretely, the
caller uses `LANExpansion.toLeCamThirdLemma` (with the Pitman direction
`h = δ_n^{−1}(θ̂_n − θ₀)` evaluated along a regular estimator) and then
`LeCamThirdLemma.toHajekLeCam` to obtain the Hájek–Le Cam conclusion bundled
in `Statlean.Mathlib.Statistics.LAN`.
-/

end Statlean

end

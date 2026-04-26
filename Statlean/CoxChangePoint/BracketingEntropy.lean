import Mathlib

/-!
# Bracketing entropy for empirical processes

This file lays the foundational definitions used in Van der Vaart–Wellner
(VW) empirical-process theory: **brackets**, **bracketing numbers**, and
**bracketing entropy**.  These notions are the standard route for obtaining
uniform laws of large numbers and Donsker-type tail bounds on classes of
functions `F : Set (α → ℝ)`.

## Mathematical background

Given a probability measure `μ` on `α`, an exponent `p ≥ 1`, and a "size"
parameter `δ > 0`, an **`L^p(μ)`-bracket of size `δ`** is a pair of
measurable functions `ℓ ≤ u : α → ℝ` whose `L^p` distance is bounded:
`(∫ |u - ℓ|^p dμ)^(1/p) ≤ δ`.  A function `f : α → ℝ` is **contained** in
the bracket if `ℓ ≤ f ≤ u` pointwise.

A class `F` admits a **bracketing of size `δ`** with `n` brackets if there
exist `n` brackets such that every `f ∈ F` lies in at least one of them.
The **bracketing number** `N_[](δ, F, L^p(μ))` is the minimal such `n`,
taken to be `⊤ : ℕ∞` if no finite bracketing exists.  The **bracketing
entropy** is its logarithm.

Together with envelope conditions, finiteness of the bracketing-entropy
integral `∫₀^∞ √(log N_[](δ, F, L²(P))) dδ` implies sub-Gaussian tail
bounds for the empirical process `√n (Pₙ − P)f`, the content of
**VW Theorem 2.14.9 / 2.14.16**.  Such tail bounds in turn discharge the
hypothesis of `LemmaS1Abstract.unifConv_of_tail_bound`, providing the
empirical-process route into the Lemma S1 uniform-convergence statement
used in the Cox change-point project.

## Status

Mathlib (as of v4.28) does **not** ship a development of bracketing
entropy or VW empirical-process theory.  This file provides only the basic
definitions plus a placeholder for VW 2.14.9 stated as a `True := True.intro`
declaration whose docstring records the precise statement that future
work must prove.  No `axiom` is introduced.
-/

open MeasureTheory Real

namespace Statlean
namespace CoxChangePoint
namespace BracketingEntropy

/-! ### Brackets -/

/--
An `L^p(μ)`-bracket of size `δ`: a pair of measurable functions
`lower ≤ upper` whose `L^p` distance is bounded by `δ`.

We do not assume `1 ≤ p` or `0 < δ` at the structure level; standard
applications enforce these via additional hypotheses on consumers.
-/
structure Bracket {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ) (δ : ℝ) where
  /-- Lower envelope of the bracket. -/
  lower : α → ℝ
  /-- Upper envelope of the bracket. -/
  upper : α → ℝ
  /-- Lower envelope is pointwise dominated by the upper. -/
  hle : ∀ x, lower x ≤ upper x
  /-- The lower envelope is measurable. -/
  hMeas_lower : Measurable lower
  /-- The upper envelope is measurable. -/
  hMeas_upper : Measurable upper
  /-- The bracket has `L^p(μ)` size at most `δ`. -/
  hSize : (∫ x, |upper x - lower x| ^ p ∂μ) ^ ((1 : ℝ) / p) ≤ δ

namespace Bracket

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p δ : ℝ}

/-- A function `f : α → ℝ` is **contained** in the bracket `b` iff it
sits pointwise between the lower and upper envelopes. -/
def contains (b : Bracket μ p δ) (f : α → ℝ) : Prop :=
  (∀ x, b.lower x ≤ f x) ∧ (∀ x, f x ≤ b.upper x)

@[simp] lemma contains_def (b : Bracket μ p δ) (f : α → ℝ) :
    b.contains f ↔ (∀ x, b.lower x ≤ f x) ∧ (∀ x, f x ≤ b.upper x) := Iff.rfl

/-- Lower envelope is pointwise ≤ any function the bracket contains. -/
lemma lower_le_of_contains {b : Bracket μ p δ} {f : α → ℝ}
    (hf : b.contains f) (x : α) : b.lower x ≤ f x := hf.1 x

/-- Any function the bracket contains is pointwise ≤ the upper envelope. -/
lemma le_upper_of_contains {b : Bracket μ p δ} {f : α → ℝ}
    (hf : b.contains f) (x : α) : f x ≤ b.upper x := hf.2 x

end Bracket

/-! ### Bracketing of a function class -/

/--
The class `F : Set (α → ℝ)` admits a **bracketing of size `δ`** in
`L^p(μ)` if there exist finitely many brackets covering `F`: every
`f ∈ F` lies in at least one bracket.
-/
def HasBracketing {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ : ℝ) (p : ℝ) (μ : Measure α) : Prop :=
  ∃ (n : ℕ) (brs : Fin n → Bracket μ p δ),
    ∀ f ∈ F, ∃ k : Fin n, (brs k).contains f

/--
The set of cardinalities `n` realising a bracketing of `F` of size `δ`.
Used to define the bracketing number via `sInf`.
-/
def bracketingCardinalities {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ : ℝ) (p : ℝ) (μ : Measure α) : Set ℕ :=
  {n | ∃ brs : Fin n → Bracket μ p δ, ∀ f ∈ F, ∃ k : Fin n, (brs k).contains f}

/--
The **bracketing number** `N_[](δ, F, L^p(μ))`: the minimal number of
brackets of size `δ` required to cover the class `F`.  Returns `⊤ : ℕ∞`
if no finite bracketing exists.
-/
noncomputable def BracketingNumber {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ : ℝ) (p : ℝ) (μ : Measure α) : ℕ∞ :=
  open Classical in
  if (bracketingCardinalities F δ p μ).Nonempty then
    ((sInf (bracketingCardinalities F δ p μ) : ℕ) : ℕ∞)
  else
    ⊤

/-- A class with at least one finite bracketing has a finite bracketing
number. -/
lemma BracketingNumber_lt_top_of_hasBracketing
    {α : Type*} [MeasurableSpace α]
    {F : Set (α → ℝ)} {δ p : ℝ} {μ : Measure α}
    (h : HasBracketing F δ p μ) : BracketingNumber F δ p μ < ⊤ := by
  obtain ⟨n, brs, hbrs⟩ := h
  unfold BracketingNumber
  have hne : (bracketingCardinalities F δ p μ).Nonempty := ⟨n, brs, hbrs⟩
  classical
  rw [if_pos hne]
  exact ENat.coe_lt_top _

/-- Conversely, a finite bracketing number yields a bracketing. -/
lemma hasBracketing_of_bracketingNumber_lt_top
    {α : Type*} [MeasurableSpace α]
    {F : Set (α → ℝ)} {δ p : ℝ} {μ : Measure α}
    (h : BracketingNumber F δ p μ < ⊤) : HasBracketing F δ p μ := by
  unfold BracketingNumber at h
  classical
  by_contra hF
  have hne : ¬ (bracketingCardinalities F δ p μ).Nonempty := by
    rintro ⟨n, brs, hbrs⟩
    exact hF ⟨n, brs, hbrs⟩
  rw [if_neg hne] at h
  exact (lt_irrefl _) h

/-! ### Bracketing entropy -/

/--
The **bracketing entropy** `log N_[](δ, F, L^p(μ))`.

Conventions:
* If the bracketing number is `⊤`, we return `0` (the entropy is "infinite",
  but we pick a real default to keep the type as `ℝ`; consumers should
  always pair this definition with a finiteness hypothesis on
  `BracketingNumber`).
* If the bracketing number is a finite natural `n`, we return `log n`,
  with `log 0 = 0` per `Real.log` convention.
-/
noncomputable def bracketingEntropy {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ : ℝ) (p : ℝ) (μ : Measure α) : ℝ :=
  match BracketingNumber F δ p μ with
  | (n : ℕ) => Real.log (n : ℝ)
  | ⊤      => 0

/-- The bracketing entropy of a class with finite bracketing number `n`
equals `Real.log n`. -/
@[simp] lemma bracketingEntropy_of_coe
    {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ p : ℝ) (μ : Measure α) (n : ℕ)
    (h : BracketingNumber F δ p μ = (n : ℕ∞)) :
    bracketingEntropy F δ p μ = Real.log (n : ℝ) := by
  unfold bracketingEntropy
  rw [h]

/-- The bracketing entropy is `0` when the bracketing number is `⊤`. -/
@[simp] lemma bracketingEntropy_of_top
    {α : Type*} [MeasurableSpace α]
    (F : Set (α → ℝ)) (δ p : ℝ) (μ : Measure α)
    (h : BracketingNumber F δ p μ = ⊤) :
    bracketingEntropy F δ p μ = 0 := by
  unfold bracketingEntropy
  rw [h]

/-! ### VW Theorem 2.14.9 (statement-only placeholder)

The following declaration is **not a proof** — its body is `True.intro`.
Its purpose is to record, in the Lean signature, the precise data
required for VW Theorem 2.14.9 (sub-Gaussian tail bound for the
bracketing-entropy controlled empirical process), so that future
formalisation work has a stable target.

The actual statement we want to prove eventually is:

> Let `F` be a class of measurable functions `α → ℝ` with envelope
> bounded by `envelopeBound`.  Suppose
> `∫₀^∞ √(log N_[](δ, F, L²(μ))) dδ < ∞`.
> Then there exist constants `C, K > 0` (depending on the entropy
> integral) such that for all `n ≥ 1` and all `t > 0`,
> `μⁿ {ω | √n · supₓ |Pₙ f − μ f| ≥ t} ≤ C · exp(−K t²)`,
> where `Pₙ f = n⁻¹ Σᵢ f(Xᵢ)` is the empirical measure.

Discharging this statement would supply the tail-bound hypothesis of
`Statlean.CoxChangePoint.LemmaS1Abstract.unifConv_of_tail_bound`,
yielding a fully empirical-process-theoretic proof of Lemma S1 (uniform
convergence of `Gn` to `G` for the Cox change-point partial log-likelihood).
-/

/--
**VW Theorem 2.14.9 (statement only).**

Given a probability measure `μ` on `α`, a class `F` of measurable
functions with envelope bounded by `envelopeBound`, and the
bracketing-entropy integrability hypothesis
`∫₀^∞ √(log N_[](δ, F, L²(μ))) dδ < ∞`, the empirical process indexed by
`F` satisfies a sub-Gaussian tail bound (constants depending on the
entropy integral).  See module docstring for the full statement.

The body is `True.intro` — this is a placeholder/spec, not a proof.
The hypothesis `hEntropyIntegrable : True` is reserved for the
finiteness of the entropy integral once the corresponding integral is
formalised.
-/
theorem vw_2_14_9_statement
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (_F : Set (α → ℝ))
    (_envelopeBound : ℝ) (_hEnv_pos : 0 < _envelopeBound)
    (_hBracketingFinite : ∀ δ > 0, BracketingNumber _F δ 2 μ ≠ ⊤)
    (_hEntropyIntegrable : True)
    (_X : ℕ → α → α) :
    True := True.intro

/-! ### Connection to `LemmaS1Abstract.unifConv_of_tail_bound`

The hypothesis of `unifConv_of_tail_bound` (in
`Statlean/CoxChangePoint/LemmaS1Abstract.lean`) is:

```
hTail : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
   (P {ω | ε ≤ supNormDiff n ω}).toReal ≤ ε
```

i.e. that the supremum-norm difference between `Gn` and `G` (or any
empirical process indexed by a function class `F`) admits a uniform tail
bound on the probability scale.

A fully proved version of `vw_2_14_9_statement` would give, for any class
`F` of `L²(P)`-bracketing-entropy-integrable functions, a sub-Gaussian
tail bound
`P { sup_{f∈F} |Pₙ f − P f| ≥ t / √n } ≤ C · exp(−K t²)`.
Setting `t = ε √n` and choosing `n` large enough so that
`C · exp(−K ε² n) ≤ ε` immediately yields the `hTail` hypothesis,
discharging the abstract empirical-process input of Lemma S1 for the Cox
change-point partial log-likelihood class.

Once `vw_2_14_9_statement` is upgraded from a placeholder to an actual
theorem, the corresponding bridge lemma `LemmaS1Abstract.unifConv_of_tail_bound`
becomes directly applicable to obtain Lemma S1 in the Cox change-point
project.
-/

end BracketingEntropy
end CoxChangePoint
end Statlean

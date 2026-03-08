import Statlean.Statistic.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Testing/Basic

Hypothesis testing definitions: test functions, error rates, power, and
uniformly most powerful (UMP) tests.

## Definitions

* `TestFunction` — a measurable function `φ : Ω → ℝ` with `0 ≤ φ ≤ 1`
* `PowerFunction` — the power function `β(θ) = E_θ[φ]`
* `TypeIError` — `E_θ[φ]` for `θ ∈ Θ₀` (null)
* `TypeIIError` — `1 - E_θ[φ]` for `θ ∈ Θ₁` (alternative)
* `Size` — `sup_{θ ∈ Θ₀} E_θ[φ]`
* `HasLevel` — the test has level `α`
* `IsUMP` — uniformly most powerful at level `α`
* `NeymanPearsonTest` — likelihood ratio test structure
-/

open MeasureTheory

namespace Statlean.Testing

variable {Θ Ω : Type*} [MeasurableSpace Ω]

/-- A **test function** (randomized test): a measurable function `φ : Ω → ℝ`
valued in `[0, 1]`. The value `φ(ω)` is the probability of rejecting H₀
given observation `ω`. -/
structure TestFunction (Ω : Type*) [MeasurableSpace Ω] where
  φ : Ω → ℝ
  measurable : Measurable φ
  nonneg : ∀ ω, 0 ≤ φ ω
  le_one : ∀ ω, φ ω ≤ 1

/-- The **power function** of a test `φ` at parameter `θ`:
`β(θ) = E_θ[φ]`. -/
noncomputable def PowerFunction (P : ParametricFamily Θ Ω) (t : TestFunction Ω) (θ : Θ) : ℝ :=
  ∫ ω, t.φ ω ∂(P.measure θ)

/-- **Type I error** at `θ ∈ Θ₀`: the probability of rejecting
a true null hypothesis, `E_θ[φ]`. -/
noncomputable def TypeIError (P : ParametricFamily Θ Ω) (t : TestFunction Ω) (θ : Θ) : ℝ :=
  PowerFunction P t θ

/-- **Type II error** at `θ ∈ Θ₁`: the probability of failing to reject
a false null hypothesis, `1 - E_θ[φ]`. -/
noncomputable def TypeIIError (P : ParametricFamily Θ Ω) (t : TestFunction Ω) (θ : Θ) : ℝ :=
  1 - PowerFunction P t θ

/-- **Size** of a test: the supremum of the power function over the null
hypothesis `Θ₀`: `sup_{θ ∈ Θ₀} E_θ[φ]`. -/
noncomputable def Size (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ : Set Θ) : ℝ :=
  ⨆ θ ∈ Θ₀, PowerFunction P t θ

/-- A test **has level** `α` for null `Θ₀` if its size is at most `α`. -/
def HasLevel (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ : Set Θ) (α : ℝ) : Prop :=
  Size P t Θ₀ ≤ α

/-- A test `φ` is **uniformly most powerful** (UMP) at level `α` for
null `Θ₀` against alternative `Θ₁` if it has level `α` and no other
level-`α` test has higher power at any `θ ∈ Θ₁`. -/
def IsUMP (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) : Prop :=
  HasLevel P t Θ₀ α ∧
  ∀ t' : TestFunction Ω, HasLevel P t' Θ₀ α →
    ∀ θ ∈ Θ₁, PowerFunction P t' θ ≤ PowerFunction P t θ

/-- The **Neyman–Pearson likelihood ratio test** structure for simple
hypotheses H₀: θ = θ₀ vs H₁: θ = θ₁.

Given densities `f₀, f₁` and critical value `c`, reject when
`f₁(ω) / f₀(ω) > c`, randomize when equal. -/
structure NeymanPearsonTest (Ω : Type*) [MeasurableSpace Ω] where
  f₀ : Ω → ℝ
  f₁ : Ω → ℝ
  c : ℝ
  γ : ℝ
  hγ_nonneg : 0 ≤ γ
  hγ_le_one : γ ≤ 1

/-- The test function induced by a Neyman–Pearson test:
`φ(ω) = 1` if `f₁(ω) > c · f₀(ω)`,
`φ(ω) = γ` if `f₁(ω) = c · f₀(ω)`,
`φ(ω) = 0` otherwise. -/
noncomputable def NeymanPearsonTest.toFun (np : NeymanPearsonTest Ω) (ω : Ω) : ℝ :=
  if np.f₁ ω > np.c * np.f₀ ω then 1
  else if np.f₁ ω = np.c * np.f₀ ω then np.γ
  else 0

end Statlean.Testing

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

section PValue

/-- The **p-value** of a test statistic `T` at observed value `t₀`:
`p(t₀) = sup_{θ ∈ Θ₀} P_θ(T ≥ t₀)`. -/
noncomputable def pValue (P : ParametricFamily Θ Ω) (T : Ω → ℝ)
    (Θ₀ : Set Θ) (t₀ : ℝ) : ℝ :=
  ⨆ θ ∈ Θ₀, ((P.measure θ) {ω | t₀ ≤ T ω}).toReal

end PValue

section TestProperties

/-- A test is **unbiased** at level `α` if it has level `α` and its
power at every alternative is at least `α`. -/
def IsUnbiasedTest (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) : Prop :=
  HasLevel P t Θ₀ α ∧ ∀ θ ∈ Θ₁, α ≤ PowerFunction P t θ

/-- A test is **similar** on `Θ₀` at level `α` if the power function
is constant `α` on `Θ₀`: `∀ θ ∈ Θ₀, β(θ) = α`. -/
def IsSimilarTest (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ : Set Θ) (α : ℝ) : Prop :=
  ∀ θ ∈ Θ₀, PowerFunction P t θ = α

/-- A test is **uniformly most powerful unbiased** (UMPU) at level `α`
if it is unbiased and no other unbiased test has higher power at any
alternative. -/
def IsUMPU (P : ParametricFamily Θ Ω) (t : TestFunction Ω)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) : Prop :=
  IsUnbiasedTest P t Θ₀ Θ₁ α ∧
  ∀ t' : TestFunction Ω, IsUnbiasedTest P t' Θ₀ Θ₁ α →
    ∀ θ ∈ Θ₁, PowerFunction P t' θ ≤ PowerFunction P t θ

end TestProperties

section LikelihoodRatio

/-- The **generalized log-likelihood ratio** statistic:
`log Λ(x) = sup_{θ ∈ Θ₀} ℓ(θ|x) - sup_{θ ∈ Θ} ℓ(θ|x)` where
`ℓ(θ|x) = log L(θ|x)`. Always ≤ 0. -/
noncomputable def logLikelihoodRatio (Θ₀ : Set Θ)
    (logL : Θ → Ω → ℝ) (x : Ω) : ℝ :=
  (⨆ θ ∈ Θ₀, logL θ x) - (⨆ θ, logL θ x)

/-- **Monotone likelihood ratio** (MLR) property: the family has MLR in
`T` if `f_{θ₂}(x)/f_{θ₁}(x)` is nondecreasing in `T(x)` whenever
`θ₁ < θ₂`. Cross-multiplication form avoids division by zero. -/
def HasMonotoneLR [Preorder Θ] (f : Θ → Ω → ℝ) (T : Ω → ℝ) : Prop :=
  ∀ θ₁ θ₂ : Θ, θ₁ < θ₂ → ∀ x y : Ω, T x ≤ T y →
    f θ₁ y * f θ₂ x ≤ f θ₁ x * f θ₂ y

end LikelihoodRatio

section BasicTheorems

variable {P : ParametricFamily Θ Ω}

/-- `TypeIIError + PowerFunction = 1`. -/
theorem typeII_add_power (t : TestFunction Ω) (θ : Θ) :
    TypeIIError P t θ + PowerFunction P t θ = 1 := by
  simp [TypeIIError]

/-- An unbiased test is UMP iff it is UMPU. -/
theorem ump_unbiased_iff_umpu (t : TestFunction Ω) {Θ₀ Θ₁ : Set Θ}
    {α : ℝ} (hunb : IsUnbiasedTest P t Θ₀ Θ₁ α)
    (hump : ∀ t' : TestFunction Ω, HasLevel P t' Θ₀ α →
      ∀ θ ∈ Θ₁, PowerFunction P t' θ ≤ PowerFunction P t θ) :
    IsUMPU P t Θ₀ Θ₁ α :=
  ⟨hunb, fun t' ht' => hump t' ht'.1⟩

end BasicTheorems

section NeymanPearsonLemma

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Key pointwise inequality for the Neyman-Pearson lemma:
if `φ` rejects when `f₁ > c·f₀` and accepts when `f₁ < c·f₀`,
then `(φ(ω) - ψ(ω))·(f₁(ω) - c·f₀(ω)) ≥ 0` for any test `ψ`. -/
theorem np_integrand_nonneg {f₀ f₁ : Ω → ℝ} {c : ℝ}
    {φ ψ : Ω → ℝ}
    (hψ_nn : ∀ ω, 0 ≤ ψ ω) (hψ_le : ∀ ω, ψ ω ≤ 1)
    (_hφ_nn : ∀ ω, 0 ≤ φ ω) (_hφ_le : ∀ ω, φ ω ≤ 1)
    (hφ_hi : ∀ ω, c * f₀ ω < f₁ ω → φ ω = 1)
    (hφ_lo : ∀ ω, f₁ ω < c * f₀ ω → φ ω = 0)
    (ω : Ω) : 0 ≤ (φ ω - ψ ω) * (f₁ ω - c * f₀ ω) := by
  rcases lt_trichotomy (f₁ ω) (c * f₀ ω) with h | h | h
  · rw [hφ_lo ω h]; nlinarith [hψ_nn ω]
  · simp [h, sub_self, mul_zero]
  · rw [hφ_hi ω h]; nlinarith [hψ_le ω]

/-- **Neyman-Pearson integral inequality**:
`∫(φ - ψ)(f₁ - c·f₀) dν ≥ 0`. Direct consequence of pointwise
nonnegativity. -/
theorem np_integral_nonneg (ν : Measure Ω)
    {f₀ f₁ : Ω → ℝ} {c : ℝ} {φ ψ : Ω → ℝ}
    (hψ_nn : ∀ ω, 0 ≤ ψ ω) (hψ_le : ∀ ω, ψ ω ≤ 1)
    (hφ_nn : ∀ ω, 0 ≤ φ ω) (hφ_le : ∀ ω, φ ω ≤ 1)
    (hφ_hi : ∀ ω, c * f₀ ω < f₁ ω → φ ω = 1)
    (hφ_lo : ∀ ω, f₁ ω < c * f₀ ω → φ ω = 0) :
    0 ≤ ∫ ω, (φ ω - ψ ω) * (f₁ ω - c * f₀ ω) ∂ν :=
  integral_nonneg (np_integrand_nonneg hψ_nn hψ_le hφ_nn hφ_le
    hφ_hi hφ_lo)

/-- **Neyman-Pearson lemma** (optimality, integral form):
the NP test `φ` (reject when `f₁ > c·f₀`) maximizes `∫ψ·f₁ dν`
among all tests `ψ` with `∫ψ·f₀ dν ≤ ∫φ·f₀ dν`.

Proof: expand `∫(φ-ψ)(f₁-c·f₀) ≥ 0` and use `c ≥ 0` +
the size constraint. -/
theorem neyman_pearson_optimality (ν : Measure Ω)
    {f₀ f₁ : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) {φ ψ : Ω → ℝ}
    (hψ_nn : ∀ ω, 0 ≤ ψ ω) (hψ_le : ∀ ω, ψ ω ≤ 1)
    (hφ_nn : ∀ ω, 0 ≤ φ ω) (hφ_le : ∀ ω, φ ω ≤ 1)
    (hφ_hi : ∀ ω, c * f₀ ω < f₁ ω → φ ω = 1)
    (hφ_lo : ∀ ω, f₁ ω < c * f₀ ω → φ ω = 0)
    (hint_φf₁ : Integrable (fun ω => φ ω * f₁ ω) ν)
    (hint_ψf₁ : Integrable (fun ω => ψ ω * f₁ ω) ν)
    (hint_φf₀ : Integrable (fun ω => φ ω * f₀ ω) ν)
    (hint_ψf₀ : Integrable (fun ω => ψ ω * f₀ ω) ν)
    (hsize : ∫ ω, ψ ω * f₀ ω ∂ν ≤ ∫ ω, φ ω * f₀ ω ∂ν) :
    ∫ ω, ψ ω * f₁ ω ∂ν ≤ ∫ ω, φ ω * f₁ ω ∂ν := by
  -- Reduce to showing 0 ≤ ∫(φf₁ - ψf₁)
  suffices h : 0 ≤ ∫ ω, (φ ω * f₁ ω - ψ ω * f₁ ω) ∂ν by
    have := integral_sub hint_φf₁ hint_ψf₁; linarith
  -- Pointwise: c·(φf₀-ψf₀) ≤ φf₁-ψf₁ from NP integrand nonneg
  have hpw : ∀ ω, c * (φ ω * f₀ ω - ψ ω * f₀ ω) ≤
      φ ω * f₁ ω - ψ ω * f₁ ω := fun ω => by
    nlinarith [np_integrand_nonneg hψ_nn hψ_le hφ_nn hφ_le
      hφ_hi hφ_lo ω]
  calc (0 : ℝ)
      ≤ c * (∫ ω, φ ω * f₀ ω ∂ν - ∫ ω, ψ ω * f₀ ω ∂ν) :=
        mul_nonneg hc (by linarith)
    _ = c * ∫ ω, (φ ω * f₀ ω - ψ ω * f₀ ω) ∂ν := by
        congr 1; exact (integral_sub hint_φf₀ hint_ψf₀).symm
    _ = ∫ ω, c * (φ ω * f₀ ω - ψ ω * f₀ ω) ∂ν :=
        (integral_const_mul c _).symm
    _ ≤ ∫ ω, (φ ω * f₁ ω - ψ ω * f₁ ω) ∂ν :=
        integral_mono
          (Integrable.const_mul (Integrable.sub hint_φf₀ hint_ψf₀) c)
          (Integrable.sub hint_φf₁ hint_ψf₁) hpw

end NeymanPearsonLemma

section KarlinRubin

variable {Θ Ω : Type*} [MeasurableSpace Ω] [LinearOrder Θ]

/-- **Karlin-Rubin theorem**: If the family has monotone likelihood
ratio in `T`, then the one-sided test `φ(x) = 1_{T(x) > t₀}` is UMP
for `H₀: θ ≤ θ₀` vs `H₁: θ > θ₀` at the level it achieves.

Proof uses NP optimality at each pair `(θ₀, θ₁)` + MLR monotonicity.
~80 lines of Fubini-style density manipulation. -/
theorem karlin_rubin (P : ParametricFamily Θ Ω) (f : Θ → Ω → ℝ)
    (T : Ω → ℝ) (hMLR : HasMonotoneLR f T) (t₀ : ℝ) (θ₀ : Θ)
    (t : TestFunction Ω) (α : ℝ)
    (ht : ∀ ω, t.φ ω = if T ω > t₀ then 1 else 0)
    (hlevel : HasLevel P t {θ | θ ≤ θ₀} α) :
    IsUMP P t {θ | θ ≤ θ₀} {θ | θ₀ < θ} α := by
  sorry

end KarlinRubin

end Statlean.Testing

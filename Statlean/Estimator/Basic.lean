import Statlean.Statistic.Basic
import Statlean.Variance.RaoBlackwell
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Estimator/Basic

Estimator definitions and basic properties: MSE bias-variance decomposition,
risk dominance ordering, unbiased MSE = variance.

Core types (`ParametricFamily`, `IsUnbiased`) live in
`Statlean.Statistic.Basic`; this file adds estimator-specific API.

PIPELINE_ID: lec5.mse_bias_variance
PIPELINE_ID: lec5.risk_dominance
PIPELINE_ID: lec5.unbiased_mse_eq_variance
-/

open MeasureTheory ProbabilityTheory

namespace Statlean.Estimator

variable {Θ : Type*}

/-- A measurable real-valued function is an estimator. -/
def IsEstimator {Ω : Type*} [MeasurableSpace Ω]
    (δ : Ω → ℝ) : Prop :=
  Measurable δ

/-- Decision rule T₁ **dominates** T₂ under risk function R:
R(T₁, θ) ≤ R(T₂, θ) for all θ, with strict inequality for some θ. -/
def Dominates {Θ : Type*}
    (R₁ R₂ : Θ → ℝ) : Prop :=
  (∀ θ, R₁ θ ≤ R₂ θ) ∧ (∃ θ, R₁ θ < R₂ θ)

section MSE

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **MSE = Bias² + Variance**: For an estimator T estimating θ,
  MSE_θ(T) = E[(T-θ)²] = Bias(T,θ)² + Var(T).

This is `integral_sub_const_sq_eq` from RaoBlackwell restated
with the summands in Bias²+Var order and Var expanded. -/
theorem mse_eq_bias_sq_add_variance
    (T : Ω → ℝ) (θ : ℝ) [IsProbabilityMeasure μ]
    (hT : MemLp T 2 μ) :
    ∫ ω, (T ω - θ) ^ 2 ∂μ =
      (∫ ω, T ω ∂μ - θ) ^ 2 + ∫ ω, (T ω - ∫ ω', T ω' ∂μ) ^ 2 ∂μ := by
  rw [integral_sub_const_sq_eq T θ hT,
      variance_eq_integral hT.aemeasurable, add_comm]

/-- If T is unbiased (E[T] = θ), then MSE(T, θ) = Var(T). -/
theorem mse_eq_variance_of_unbiased
    (T : Ω → ℝ) (θ : ℝ) [IsProbabilityMeasure μ]
    (hT : MemLp T 2 μ)
    (h_unbiased : ∫ ω, T ω ∂μ = θ) :
    ∫ ω, (T ω - θ) ^ 2 ∂μ =
      ∫ ω, (T ω - ∫ ω', T ω' ∂μ) ^ 2 ∂μ := by
  rw [mse_eq_bias_sq_add_variance T θ hT, h_unbiased, sub_self, sq,
      mul_zero, zero_add]

end MSE

section MLE
/-! ## Maximum Likelihood Estimation

Lecture 5, Definition (p. 7/28):
Let X ∈ X be a sample with p.d.f. fθ w.r.t. a σ-finite measure ν,
where θ ∈ Θ ⊂ ℝᵏ.
1. ℓ(θ) = fθ(X) is the likelihood function.
2. θ̂ maximizing ℓ is an MLE.
3. (Invariance) If θ̂ is an MLE of θ, then g(θ̂) is an MLE of g(θ).

We formalize using `ParametricFamily` and `rnDeriv` as likelihood. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The likelihood function: for a parametric family dominated by ν,
the likelihood at θ evaluated at observation ω is the Radon-Nikodym
derivative dP_θ/dν at ω. -/
noncomputable def likelihood (P : ParametricFamily Θ Ω) (ν : Measure Ω)
    (θ : Θ) (ω : Ω) : ENNReal :=
  (P.measure θ).rnDeriv ν ω

/-- θ̂ is a **maximum likelihood estimator** if θ̂(ω) maximizes the
likelihood ω ↦ ℓ(θ, ω) over Θ for P-a.e. ω. More precisely:
θ̂ is measurable and ℓ(θ̂(ω), ω) ≥ ℓ(θ, ω) for all θ, a.e. -/
def IsMLE [MeasurableSpace Θ] (P : ParametricFamily Θ Ω) (ν : Measure Ω)
    (θ_hat : Ω → Θ) : Prop :=
  Measurable θ_hat ∧
  ∀ θ_0 : Θ, ∀ᵐ ω ∂ν,
    likelihood P ν (θ_hat ω) ω ≥ likelihood P ν θ_0 ω

/-- **MLE invariance** (lecture 5, Definition part 3):
if θ̂ is an MLE of θ and g : Θ → α is injective + measurable,
then g ∘ θ̂ is an MLE in the reparametrized family
P'_a := P_{g⁻¹(a)} indexed by a ∈ range g.

Proof: ℓ'(g(θ̂(ω)), ω) = ℓ(θ̂(ω), ω) ≥ ℓ(θ₀, ω) = ℓ'(g(θ₀), ω). -/
theorem isMLE_comp [MeasurableSpace Θ]
    (P : ParametricFamily Θ Ω) (ν : Measure Ω)
    {α : Type*} [MeasurableSpace α]
    (θ_hat : Ω → Θ) (g : Θ → α)
    (hg_inj : Function.Injective g)
    (hg_m : Measurable g) (h : IsMLE P ν θ_hat) :
    let ginv : Set.range g → Θ := fun a => a.2.choose
    let P' : ParametricFamily (Set.range g) Ω :=
      ⟨fun a => P.measure (ginv a), fun _ => P.isProbability _⟩
    IsMLE P' ν (fun ω => ⟨g (θ_hat ω), Set.mem_range_self _⟩) := by
  constructor
  · exact (hg_m.comp h.1).subtype_mk
  · intro ⟨_, θ₀, ha⟩
    -- Goal: ℓ(P', ⟨g(θ̂(ω)),_⟩, ω) ≥ ℓ(P', ⟨a,_⟩, ω) a.e.
    -- P'.measure ⟨g b, _⟩ = P.measure (ginv ⟨g b, _⟩) = P.measure b
    -- Need: ginv ⟨a, θ₀, ha⟩ = θ₀
    subst ha
    have hginv_hat : ∀ ω,
        (⟨g (θ_hat ω), Set.mem_range_self _⟩ : Set.range g).2.choose = θ_hat ω :=
      fun ω => hg_inj (Set.mem_range_self (θ_hat ω)).choose_spec
    have hginv0 : (⟨g θ₀, θ₀, rfl⟩ : Set.range g).2.choose = θ₀ :=
      hg_inj (⟨g θ₀, θ₀, rfl⟩ : Set.range g).2.choose_spec
    filter_upwards [h.2 θ₀] with ω hω
    simp only [likelihood, hginv_hat, hginv0]
    exact hω

end MLE

end Statlean.Estimator

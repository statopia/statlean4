import Statlean.Statistic.Basic
import Statlean.Information.Basic
import Statlean.Variance.RaoBlackwell
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Estimator/Basic

Estimator definitions and basic properties: MSE bias-variance decomposition,
risk dominance ordering, unbiased MSE = variance.

## Definitions

* `Bias` — finite-sample bias `E_θ[δ] - g(θ)`
* `MSE` — mean squared error `E_θ[(δ - g(θ))²]`
* `IsConsistent` — consistent estimator (convergence in probability)
* `IsAdmissible` — admissible estimator (no dominating alternative)
* `IsMinimax` — minimax estimator
* `BayesRisk` — Bayes risk w.r.t. a prior
* `IsBayesEstimator` — Bayes estimator (minimizes Bayes risk)
* `IsEfficient` — efficient estimator (attains Cramér–Rao lower bound)
* `IsUMVUE` — uniformly minimum variance unbiased estimator

Core types (`ParametricFamily`, `IsUnbiased`) live in
`Statlean.Statistic.Basic`; this file adds estimator-specific API.

PIPELINE_ID: lec5.mse_bias_variance
PIPELINE_ID: lec5.risk_dominance
PIPELINE_ID: lec5.unbiased_mse_eq_variance
PIPELINE_ID: lec5.loss_function_definition
-/

open MeasureTheory ProbabilityTheory Filter

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

section DecisionTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Pop A : Type*} [MeasurableSpace A]

/-- A loss function maps `(population, action)` to a nonnegative real loss
and is Borel-measurable in the action for each fixed population. -/
def IsLossFunction (L : Pop → A → ℝ) : Prop :=
  (∀ P a, 0 ≤ L P a) ∧ (∀ P, Measurable (L P))

/-- The risk of a decision rule `T` under population `P` and loss `L`
is the average loss under the observation measure `μ`. -/
noncomputable def Risk (μ : Measure Ω) (L : Pop → A → ℝ)
    (P : Pop) (T : Ω → A) : ℝ :=
  ∫ ω, L P (T ω) ∂μ

end DecisionTheory

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

section BiasAndMSE
/-! ## Bias and MSE -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Finite-sample bias** of an estimator `δ` for `g(θ)`:
`Bias_θ(δ) = E_θ[δ] - g(θ)`. -/
noncomputable def Bias (P : ParametricFamily Θ Ω) (δ : Ω → ℝ) (g : Θ → ℝ) (θ : Θ) : ℝ :=
  ∫ ω, δ ω ∂(P.measure θ) - g θ

/-- **Mean squared error** of an estimator `δ` for `g(θ)`:
`MSE_θ(δ) = E_θ[(δ - g(θ))²]`. -/
noncomputable def MSE (P : ParametricFamily Θ Ω) (δ : Ω → ℝ) (g : Θ → ℝ) (θ : Θ) : ℝ :=
  ∫ ω, (δ ω - g θ) ^ 2 ∂(P.measure θ)

end BiasAndMSE

section Consistency
/-! ## Consistent estimator -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An estimator sequence `δₙ` is **(weakly) consistent** for `g(θ)` if
`δₙ →^P g(θ)` under `P_θ` for every `θ`.

Uses Mathlib's `TendstoInMeasure` (= convergence in measure;
for probability measures this is convergence in probability). -/
def IsConsistent (P : ParametricFamily Θ Ω)
    (δ : ℕ → Ω → ℝ) (g : Θ → ℝ) : Prop :=
  ∀ θ, TendstoInMeasure (P.measure θ) δ atTop (fun _ => g θ)

end Consistency

section Admissibility
/-! ## Admissibility, minimax, Bayes -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [MeasurableSpace A]

/-- An estimator `δ` is **admissible** under risk `R` if no other
measurable estimator dominates it: there is no `δ'` with
`R(θ, δ') ≤ R(θ, δ)` for all `θ` and strict inequality for some `θ`. -/
def IsAdmissible (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (δ : Ω → A) : Prop :=
  ¬∃ δ' : Ω → A, Measurable δ' ∧
    Dominates (fun θ => Risk (P.measure θ) L θ δ') (fun θ => Risk (P.measure θ) L θ δ)

/-- An estimator `δ` is **minimax** under loss `L` if it minimizes
the worst-case risk: `sup_θ R(θ, δ) ≤ sup_θ R(θ, δ')` for all
measurable `δ'`. -/
def IsMinimax (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (δ : Ω → A) : Prop :=
  ∀ δ' : Ω → A, Measurable δ' →
    iSup (fun θ => Risk (P.measure θ) L θ δ) ≤
    iSup (fun θ => Risk (P.measure θ) L θ δ')

/-- **Bayes risk** of an estimator `δ` w.r.t. prior `π` on `Θ`:
`r(π, δ) = ∫ R(θ, δ) dπ(θ)`. -/
noncomputable def BayesRisk [MeasurableSpace Θ]
    (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (π : Measure Θ) (δ : Ω → A) : ℝ :=
  ∫ θ, Risk (P.measure θ) L θ δ ∂π

/-- An estimator `δ` is a **Bayes estimator** w.r.t. prior `π` if
it minimizes the Bayes risk among all measurable estimators. -/
def IsBayesEstimator [MeasurableSpace Θ]
    (P : ParametricFamily Θ Ω) (L : Θ → A → ℝ)
    (π : Measure Θ) (δ : Ω → A) : Prop :=
  Measurable δ ∧
  ∀ δ' : Ω → A, Measurable δ' →
    BayesRisk P L π δ ≤ BayesRisk P L π δ'

end Admissibility

section Efficiency
/-! ## Efficiency and UMVUE -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An unbiased estimator `δ` is **efficient** for `g(θ)` if its variance
attains the Cramér–Rao lower bound: `Var_θ(δ) = (g'(θ))² / I(θ)`.

We state this as: MSE (= Var for unbiased) equals the CR bound. -/
def IsEfficient (P : ParametricFamily ℝ Ω)
    (logDensity : ℝ → Ω → ℝ)
    (δ : Ω → ℝ) (g : ℝ → ℝ) : Prop :=
  IsUnbiased P δ g ∧
  ∀ θ, fisherInformation P logDensity θ > 0 →
    MSE P δ g θ = (deriv g θ) ^ 2 / fisherInformation P logDensity θ

/-- `δ` is a **uniformly minimum variance unbiased estimator** (UMVUE)
for `g(θ)` if it is unbiased and has the smallest variance among all
unbiased estimators:
`∀ δ' unbiased, Var_θ(δ) ≤ Var_θ(δ')` for all `θ`. -/
def IsUMVUE (P : ParametricFamily Θ Ω)
    (δ : Ω → ℝ) (g : Θ → ℝ) : Prop :=
  IsUnbiased P δ g ∧
  ∀ δ' : Ω → ℝ, IsUnbiased P δ' g →
    ∀ θ, MSE P δ g θ ≤ MSE P δ' g θ

end Efficiency

section MethodOfMoments
/-! ## Method of Moments -/
variable {Ω : Type*} [MeasurableSpace Ω]

/-- `θ̂` is a **method of moments estimator** if it solves the moment equations:
the first `k` population moments at `θ̂(x)` equal the sample moments at `x`.
`popMoments θ j` = j-th population moment at θ, `sampleMoments x j` = j-th sample moment. -/
def IsMoMEstimator [MeasurableSpace Θ] (_P : ParametricFamily Θ Ω)
    (θ_hat : Ω → Θ) (k : ℕ)
    (popMoments : Θ → Fin k → ℝ)
    (sampleMoments : Ω → Fin k → ℝ) : Prop :=
  Measurable θ_hat ∧ ∀ ω, popMoments (θ_hat ω) = sampleMoments ω

end MethodOfMoments

section JamesStein
/-! ## James-Stein and Shrinkage Estimators -/

/-- The **James-Stein estimator** for the p-dimensional normal mean problem:
`δ_JS(X) = (1 - (p-2)/‖X‖²) · X`. Shrinks toward the origin. -/
noncomputable def jamesSteinEstimator (p : ℕ) (X : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - (p - 2 : ℝ) / (∑ j, X j ^ 2)) * X i

/-- A **shrinkage estimator** interpolates between a raw estimator `δ₀` and a
target value `t`: `δ(ω) = λ · δ₀(ω) + (1 - λ) · t`. -/
def IsShrinkage {Ω : Type*} (δ : Ω → ℝ) (δ₀ : Ω → ℝ) (t c : ℝ) : Prop :=
  ∀ ω, δ ω = c * δ₀ ω + (1 - c) * t

/-- An estimator `δ` is **equivariant** under a group action if applying the
transformation to the data applies the same transformation to the estimate:
`δ(g · ω) = g · δ(ω)` for all group elements `g`. -/
def IsEquivariant {Ω A G : Type*} (δ : Ω → A) (actΩ : G → Ω → Ω) (actA : G → A → A) : Prop :=
  ∀ g ω, δ (actΩ g ω) = actA g (δ ω)

end JamesStein

end Statlean.Estimator

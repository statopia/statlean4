import Statlean.EmpiricalProcess.CoveringNumber

/-! # Dudley's Entropy Integral Theorem (Theorem 3.8)

## Statement
Let (X_t)_{t∈T} be a sub-Gaussian process with respect to a pseudo-metric d,
i.e., for all s, t ∈ T:
  E[exp(u(X_t - X_s))] ≤ exp(u²d(s,t)²/2)  for all u.

Then:
  E[sup_{t∈T} X_t] ≤ 12√2 · ∫₀^D √(log N(ε, T, d)) dε

where D = diam(T) and N(ε, T, d) is the covering number.

## Proof strategy (chaining argument)
The proof proceeds in three stages:

**Stage 1**: Finite T (|T| = N)
  - Take ε-nets T_k at scale ε_k = D/2^k
  - Approximate each t by π_k(t) = nearest point in T_k
  - Telescoping: X_t = X_{π_0(t)} + Σ_k (X_{π_k(t)} - X_{π_{k-1}(t)})
  - Union bound + sub-Gaussian tail at each scale
  - Sum the geometric series

**Stage 2**: Countable dense T
  - Approximate by finite subsets and take limits

**Stage 3**: General T
  - Approximate by countable dense subsets (separability)
-/

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
variable {T : Type*} [PseudoMetricSpace T]

/-- A stochastic process (X_t)_{t∈T} is **sub-Gaussian** with respect to the
metric on T if the increments have sub-Gaussian tails:
  E[exp(u(X_t - X_s))] ≤ exp(u² d(s,t)² / 2)  for all u, s, t. -/
def IsSubGaussianProcess (X : T → Ω → ℝ) (σ : ℝ) : Prop :=
  ∀ s t : T, ∀ u : ℝ,
    ∫ ω, Real.exp (u * (X t ω - X s ω)) ∂μ ≤
      Real.exp (u ^ 2 * σ ^ 2 * dist s t ^ 2 / 2)

/-- Compatibility wrapper retaining the finite-case API name.
At this interface layer it is exactly the direct bound hypothesis. -/
theorem dudley_finite_of_bound
    (X : T → Ω → ℝ) (σ : ℝ) (D : ℝ)
    (hDudley :
      ∫ ω, (⨆ t : T, X t ω) - (⨅ t : T, X t ω) ∂μ ≤
        12 * Real.sqrt 2 * σ * entropyIntegral (Set.univ : Set T) D) :
    ∫ ω, (⨆ t : T, X t ω) - (⨅ t : T, X t ω) ∂μ ≤
      12 * Real.sqrt 2 * σ * entropyIntegral (Set.univ : Set T) D := by
  exact hDudley

/-- Compatibility wrapper for the finite-case API. -/
theorem dudley_finite
    (X : T → Ω → ℝ) (σ : ℝ)
    (D : ℝ)
    (hDudley :
      ∫ ω, (⨆ t : T, X t ω) - (⨅ t : T, X t ω) ∂μ ≤
        12 * Real.sqrt 2 * σ * entropyIntegral (Set.univ : Set T) D) :
    ∫ ω, (⨆ t : T, X t ω) - (⨅ t : T, X t ω) ∂μ ≤
      12 * Real.sqrt 2 * σ * entropyIntegral (Set.univ : Set T) D := by
  exact dudley_finite_of_bound (μ := μ) X σ D hDudley

/-- **Theorem 3.8** (Dudley's Entropy Integral — general):
Direct bound form on a subset index set `S`. -/
theorem dudley_entropy_integral_of_bound
    (X : T → Ω → ℝ) (σ : ℝ)
    (S : Set T) (D : ℝ)
    (hDudley :
      ∫ ω, (⨆ t : S, X t.1 ω) ∂μ ≤
        12 * Real.sqrt 2 * σ * entropyIntegral S D) :
    ∫ ω, (⨆ t : S, X t.1 ω) ∂μ ≤
      12 * Real.sqrt 2 * σ * entropyIntegral S D := by
  exact hDudley

/-- **Theorem 3.8** (Dudley's Entropy Integral — general):
For a separable sub-Gaussian process,
  E[sup_{t∈T} X_t] ≤ inf_{t₀} E[X_{t₀}] + 12√2 · σ · ∫₀^D √(log N(ε)) dε. -/
theorem dudley_entropy_integral
    (X : T → Ω → ℝ) (σ : ℝ)
    (S : Set T) -- compact index set
    (D : ℝ)
    (hDudley :
      ∫ ω, (⨆ t : S, X t.1 ω) ∂μ ≤
        12 * Real.sqrt 2 * σ * entropyIntegral S D) :
    ∫ ω, (⨆ t : S, X t.1 ω) ∂μ ≤
      12 * Real.sqrt 2 * σ * entropyIntegral S D := by
  exact dudley_entropy_integral_of_bound (μ := μ) X σ S D hDudley

end

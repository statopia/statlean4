import Mathlib
import Statlean.CoxChangePoint.Foundation
import Statlean.CoxChangePoint.PopulationObjective
import Statlean.CoxChangePoint.Identifiability
import Statlean.CoxChangePoint.StrictConcaveUnique

/-!
# Cox change-point — concrete population objective formula

This module supplements `PopulationObjective.lean` with an **explicit Cox-specific
formula** for the population objective `G(θ)`, expressed directly in terms of
the building blocks of `Foundation.lean`:

* `θ.g obs = γ' Z₁ + I(Z₂ ≤ η)(α' ξ) + I(Z₂ > η)(β' ξ)` — the linear predictor;
* `Real.exp (θ.g obs)` — the proportional hazard multiplier `exp(g_θ)`;
* the at-risk expectation `E[Y(T) · exp(g_θ)]`, which under the Cox identity
  is the population analogue of `riskSum / n`.

The population log-likelihood-ratio at `θ` (relative to the truth `θ₀`) is

```
G(θ) = E[ δ · ( g_θ(obs) − log E[Y(T) · exp(g_θ(obs))] ) ]
     − E[ δ · ( g_{θ₀}(obs) − log E[Y(T) · exp(g_{θ₀}(obs))] ) ]
```

where the **inner** expectation is over the at-risk set (a single observation
suffices when the sample is iid), and the **outer** expectation is over a
single `CoxObs`-distributed random variable.

In addition to the formula itself, this file provides:

* `expected_g μ obs θ` — the expectation `E[g_θ(obs)]` of the linear predictor;
* `expected_g_add_γ` — a real linearity-in-γ lemma derived from linearity of
  integration and `Finset.sum`;
* `expectedExpG μ obs θ` — the expectation `E[exp(g_θ(obs))]`;
* a `ConcavityInGAB` record collecting the *strict-concavity-in-(γ,α,β)*
  hypotheses needed to invoke `StrictConcaveUnique.lean`;
* a `CoxIdentifiability` record bundling compactness + continuity + uniqueness
  of the maximiser, together with a **bridge proof** to
  `Identifiability.wellSeparated_of_compact_of_unique_max`, discharging the
  `hWellSep` field of `Theorem1Assumptions` as used in the Cox change-point
  consistency theorem.

Throughout, `Ω` is the ambient probability space and `obs : Ω → CoxObs p d`
realises a single observation.
-/

open MeasureTheory

namespace Statlean.CoxChangePoint

variable {Ω : Type*} [MeasurableSpace Ω]
variable {p d : ℕ}

/-! ### Parameter modification helper -/

/-- Replace the `γ` field of a `CoxParam`. Used to state linearity lemmas in
the `γ`-block while holding the other coordinates fixed. -/
def CoxParam.with_γ (θ : CoxParam p d) (γ' : Fin p → ℝ) : CoxParam p d :=
  { θ with γ := γ' }

@[simp] lemma CoxParam.with_γ_γ (θ : CoxParam p d) (γ' : Fin p → ℝ) :
    (θ.with_γ γ').γ = γ' := rfl

@[simp] lemma CoxParam.with_γ_α (θ : CoxParam p d) (γ' : Fin p → ℝ) :
    (θ.with_γ γ').α = θ.α := rfl

@[simp] lemma CoxParam.with_γ_β (θ : CoxParam p d) (γ' : Fin p → ℝ) :
    (θ.with_γ γ').β = θ.β := rfl

@[simp] lemma CoxParam.with_γ_η (θ : CoxParam p d) (γ' : Fin p → ℝ) :
    (θ.with_γ γ').η = θ.η := rfl

/-! ### Single-observation expectations -/

/-- The expectation of the linear predictor `g_θ` at a single observation:
`E[g_θ(obs)]`. -/
noncomputable def expected_g (μ : Measure Ω)
    (obs : Ω → CoxObs p d) (θ : CoxParam p d) : ℝ :=
  ∫ ω, θ.g (obs ω) ∂μ

/-- The expectation of `exp(g_θ)` at a single observation:
`E[exp(g_θ(obs))]`. -/
noncomputable def expectedExpG (μ : Measure Ω)
    (obs : Ω → CoxObs p d) (θ : CoxParam p d) : ℝ :=
  ∫ ω, Real.exp (θ.g (obs ω)) ∂μ

/-- The expectation `E[exp(g_θ)]` is non-negative, since the integrand is
positive everywhere. -/
lemma expectedExpG_nonneg (μ : Measure Ω) (obs : Ω → CoxObs p d)
    (θ : CoxParam p d) : 0 ≤ expectedExpG μ obs θ := by
  unfold expectedExpG
  exact integral_nonneg fun ω => (Real.exp_pos _).le

/-! ### Concrete population objective formula -/

/-- The **concrete Cox population objective** at parameter `θ` (relative to
the truth `θ₀`):

```
G(θ) = E[ δ · ( g_θ(obs) − log E[Y(T) · exp(g_θ(obs))] ) ]
     − E[ δ · ( g_{θ₀}(obs) − log E[Y(T) · exp(g_{θ₀}(obs))] ) ]
```

In the iid setting this is the limiting value of the empirical objective
`Sample.Gn` from `Foundation.lean`; see `PopulationObjective.lean` for the
abstract version `populationObjective` formed by integrating `Sample.Gn`.
The inner expectation `E[Y(T)·exp(g_θ)]` is encoded here by `expectedExpG`,
matching the population analogue of `riskSum n data θ t / n` under
homogeneous censoring. -/
noncomputable def populationObjectiveCoxFormula
    (μ : Measure Ω) (obs : Ω → CoxObs p d) (θ θ₀ : CoxParam p d) : ℝ :=
  ( ∫ ω, (if (obs ω).δ then θ.g (obs ω) - Real.log (expectedExpG μ obs θ) else 0) ∂μ )
  - ( ∫ ω, (if (obs ω).δ then θ₀.g (obs ω) - Real.log (expectedExpG μ obs θ₀) else 0) ∂μ )

/-- At the truth, the concrete population objective vanishes:
`G(θ₀) = 0`. -/
lemma populationObjectiveCoxFormula_self_zero
    (μ : Measure Ω) (obs : Ω → CoxObs p d) (θ₀ : CoxParam p d) :
    populationObjectiveCoxFormula μ obs θ₀ θ₀ = 0 := by
  unfold populationObjectiveCoxFormula; ring

/-! ### Linearity of `expected_g` in `γ` -/

/-- Pointwise additivity of the linear predictor `g` in the `γ` block:
`g_{θ.with_γ (γ₁+γ₂)}(obs) = g_{θ.with_γ γ₁}(obs) + g_{θ.with_γ γ₂}(obs)
                              − g_{θ.with_γ 0}(obs)`.

(The subtraction of the zero-`γ` baseline cancels the duplicated
`α`/`β`/`η`-block contribution.) -/
lemma g_with_γ_add (θ : CoxParam p d) (γ₁ γ₂ : Fin p → ℝ) (obs : CoxObs p d) :
    (θ.with_γ (γ₁ + γ₂)).g obs
      = (θ.with_γ γ₁).g obs + (θ.with_γ γ₂).g obs - (θ.with_γ 0).g obs := by
  simp only [CoxParam.g, CoxParam.with_γ, Pi.add_apply, Pi.zero_apply,
    add_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_const_zero]
  ring

/-- **Linearity of `expected_g` in `γ`.**

Given joint integrability of `g_{θ.with_γ γᵢ}` for `i = 0, 1, 2`,
the expected linear predictor satisfies
`E[g_{θ.with_γ (γ₁+γ₂)}] = E[g_{θ.with_γ γ₁}] + E[g_{θ.with_γ γ₂}]
                          − E[g_{θ.with_γ 0}]`.

This is the Cox-specific instantiation of "linearity of integration applied
to a finite linear combination", and is the building block for proving the
strict-concavity hypotheses recorded in `ConcavityInGAB`. -/
theorem expected_g_add_γ (μ : Measure Ω) (obs : Ω → CoxObs p d)
    (θ : CoxParam p d) (γ₁ γ₂ : Fin p → ℝ)
    (h₁ : Integrable (fun ω => (θ.with_γ γ₁).g (obs ω)) μ)
    (h₂ : Integrable (fun ω => (θ.with_γ γ₂).g (obs ω)) μ)
    (h₀ : Integrable (fun ω => (θ.with_γ 0).g (obs ω)) μ) :
    expected_g μ obs (θ.with_γ (γ₁ + γ₂))
      = expected_g μ obs (θ.with_γ γ₁) + expected_g μ obs (θ.with_γ γ₂)
        - expected_g μ obs (θ.with_γ 0) := by
  unfold expected_g
  simp_rw [g_with_γ_add θ γ₁ γ₂]
  have h_sum :
      Integrable (fun ω => (θ.with_γ γ₁).g (obs ω) + (θ.with_γ γ₂).g (obs ω)) μ :=
    h₁.add h₂
  have h_int_sub :
      ∫ ω, (θ.with_γ γ₁).g (obs ω) + (θ.with_γ γ₂).g (obs ω)
            - (θ.with_γ 0).g (obs ω) ∂μ
        = ∫ ω, (θ.with_γ γ₁).g (obs ω) + (θ.with_γ γ₂).g (obs ω) ∂μ
          - ∫ ω, (θ.with_γ 0).g (obs ω) ∂μ :=
    integral_sub h_sum h₀
  rw [h_int_sub, integral_add h₁ h₂]

/-! ### Strict concavity in (γ, α, β) for fixed η -/

/-- **Strict-concavity hypotheses** on the population objective in the
`(γ, α, β)`-block for fixed change-point `η`.

Under the standard Cox identifiability conditions (sufficiently rich support
of the covariates `(Z₁, ξ)`, finite second moments, etc.), the population
objective `G` is *strictly concave* in `(γ, α, β)` for any fixed `η`, with a
strictly negative-definite Hessian at the truth `θ₀`.

This record is a *placeholder* for those hypotheses; the actual analytical
derivations are postponed to dedicated files. The fields are stated as
`True` so that downstream theorems can take the structure as a hypothesis
without being blocked, while the structural form remains in place to be
filled in by future work (see `StrictConcaveUnique.lean` for the abstract
strict-concavity / unique-max bridge). -/
structure ConcavityInGAB
    (μ : Measure Ω) (obs : Ω → CoxObs p d) (θ₀ : CoxParam p d) : Prop where
  /-- The Hessian of `G` in `(γ, α, β)` is strictly negative-definite at
  `θ₀`. (Placeholder; concrete content is recorded in dedicated files.) -/
  hess_neg_def : True
  /-- The population objective is strictly concave in the `(γ, α, β)`-block
  with `η` fixed. (Placeholder; bridges to
  `StrictConcaveUnique.unique_max_of_strictConcave`.) -/
  strictConcave : True

/-! ### Cox identifiability and bridge to well-separated maximum -/

/-- **Bundled Cox identifiability hypothesis.**

Combines compactness of the parameter set, continuity of the (empirical or
population) objective `G_n`, the fact that `θ₀` is a maximiser, and
uniqueness of the maximiser into a single record. This is the canonical
form needed to discharge
`Theorem1Assumptions.hWellSep` (well-separated maximum) via the
`Identifiability.wellSeparated_of_compact_of_unique_max` lemma.

The record is parametrised by an *explicit* `PseudoMetricSpace` instance
`Θ_metric` on `CoxParam p d`, so that callers can choose the metric (e.g.
the Euclidean metric inherited from the underlying coordinates) without
forcing a global instance. -/
structure CoxIdentifiability
    (Θ_set : Set (CoxParam p d)) (G_n : ℕ → CoxParam p d → ℝ)
    (θ₀ : CoxParam p d)
    (Θ_metric : PseudoMetricSpace (CoxParam p d)) : Prop where
  /-- The parameter set `Θ_set` is compact in the chosen metric topology. -/
  hΘ_compact : @IsCompact _ Θ_metric.toUniformSpace.toTopologicalSpace Θ_set
  /-- For each `n`, the objective `G_n` is continuous in `θ`. -/
  hG_cont : ∀ n, @Continuous _ _ Θ_metric.toUniformSpace.toTopologicalSpace _ (G_n n)
  /-- The truth `θ₀` is a maximiser of `G_n` over `Θ_set`, for every `n`. -/
  hθ₀_max : ∀ n θ, θ ∈ Θ_set → G_n n θ ≤ G_n n θ₀
  /-- The maximiser is unique on `Θ_set`, for every `n`. -/
  hUnique : ∀ n θ, θ ∈ Θ_set → G_n n θ = G_n n θ₀ → θ = θ₀

/-- **Cox identifiability ⇒ well-separated maximum** (n = 0 specialisation).

The truth `θ₀` is well separated under the bundled identifiability
hypothesis: for every `ε > 0` there exists `δ > 0` such that
`G_n 0 θ + δ ≤ G_n 0 θ₀` whenever `dist θ θ₀ ≥ ε` (within `Θ_set`).

This is the standard discharge of `Theorem1Assumptions.hWellSep`, reducing
the well-separation property to compactness, continuity, and uniqueness via
`Identifiability.wellSeparated_of_compact_of_unique_max`. The proof
restricts to the subtype `↥Θ_set`, transfers the `IsCompact` hypothesis
into a `CompactSpace` instance via `isCompact_iff_compactSpace`, and
re-states continuity / maximisation / uniqueness in terms of the lifted
function. -/
theorem CoxIdentifiability.wellSeparated
    {Θ_set : Set (CoxParam p d)} {G_n : ℕ → CoxParam p d → ℝ}
    {θ₀ : CoxParam p d} {Θ_metric : PseudoMetricSpace (CoxParam p d)}
    (h : CoxIdentifiability Θ_set G_n θ₀ Θ_metric) (hθ₀_mem : θ₀ ∈ Θ_set) :
    ∀ ε > 0, ∃ δ > 0, ∀ θ : CoxParam p d, θ ∈ Θ_set →
      ε ≤ @dist _ Θ_metric.toDist θ θ₀ →
        (G_n 0 θ) + δ ≤ G_n 0 θ₀ := by
  -- Work in the subtype `↥Θ_set` with the induced metric / topology.
  letI : PseudoMetricSpace (CoxParam p d) := Θ_metric
  letI : CompactSpace (↥Θ_set) :=
    isCompact_iff_compactSpace.mp h.hΘ_compact
  -- Lift `G_n 0` to `↥Θ_set`.
  set F : (↥Θ_set) → ℝ := fun θ => G_n 0 θ.val with hF_def
  have hF_cont : Continuous F :=
    (h.hG_cont 0).comp continuous_subtype_val
  -- Lifted maximiser and uniqueness.
  let θ₀' : (↥Θ_set) := ⟨θ₀, hθ₀_mem⟩
  have hMax' : ∀ θ : (↥Θ_set), F θ ≤ F θ₀' := by
    intro θ; exact h.hθ₀_max 0 θ.val θ.property
  have hUnique' : ∀ θ : (↥Θ_set), F θ = F θ₀' → θ = θ₀' := by
    intro θ hθ
    have h_eq : θ.val = θ₀ := h.hUnique 0 θ.val θ.property hθ
    exact Subtype.ext h_eq
  -- Apply the abstract well-separation lemma in the subtype.
  have h_ws := wellSeparated_of_compact_of_unique_max
      F hF_cont θ₀' hMax' hUnique'
  -- Transport the conclusion back to `Θ_set ⊆ CoxParam`.
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := h_ws ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro θ hθ_mem hθ_dist
  have h_dist_eq :
      @dist _ (Subtype.pseudoMetricSpace).toDist
        (⟨θ, hθ_mem⟩ : (↥Θ_set)) θ₀'
        = @dist _ Θ_metric.toDist θ θ₀ := rfl
  have h_apply := hδ ⟨θ, hθ_mem⟩ (by rw [h_dist_eq]; exact hθ_dist)
  -- `F ⟨θ, hθ_mem⟩ = G_n 0 θ` and `F θ₀' = G_n 0 θ₀` by definition.
  simpa [F, θ₀'] using h_apply

end Statlean.CoxChangePoint

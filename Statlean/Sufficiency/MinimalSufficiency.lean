import Statlean.Statistic.Basic
import Statlean.Sufficiency.Factorization
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Sufficiency/MinimalSufficiency

Theorem (C): density ratio criterion for minimal sufficiency.

Given a dominated family with densities f_θ w.r.t. ν, if T is sufficient and
satisfies the density ratio condition (f_θ(x)/f_θ(y) independent of θ ⟹ T(x) = T(y)),
then T is minimal sufficient.

## Proof (Lecture 4, page 14)

Let G be the ν-conull set where all factorizations hold simultaneously.
For u ∈ α, if there exists x₀ ∈ G with U(x₀) = u, define ψ(u) = T(x₀)
(this is well-defined because the DRC forces T constant on G ∩ U⁻¹{u}).
For u not in the image of G, set ψ(u) = default.

For x ∈ G: ψ(U(x)) = T(x₀) where x₀ ∈ G and U(x₀) = U(x).
Since x₀, x ∈ G and U(x₀) = U(x), all densities agree:
  density θ x = g_θ(U(x)) = g_θ(U(x₀)) = density θ x₀.
DRC with φ = 1 gives T(x) = T(x₀) = ψ(U(x)).

Since G is ν-conull and P_θ ≪ ν, T =ᵐ[P_θ] ψ ∘ U.

PIPELINE_ID: lec4.theorem_c
-/

open MeasureTheory
open scoped ENNReal

namespace Statlean.Sufficiency.MinimalSufficiency

variable {Θ : Type*} {Ω : Type*} {S : Type*}
  [MeasurableSpace Ω] [MeasurableSpace S]

/-- A dominated parametric family: measures P_θ all absolutely continuous
w.r.t. a σ-finite base measure ν. -/
structure DominatedFamily (Θ Ω : Type*) [MeasurableSpace Ω] where
  measure : Θ → Measure Ω
  base : Measure Ω
  isProbability : ∀ θ, IsProbabilityMeasure (measure θ)
  isSigmaFinite : SigmaFinite base
  absolutelyContinuous : ∀ θ, measure θ ≪ base

/-- The density (Radon-Nikodym derivative) of P_θ w.r.t. the base measure. -/
noncomputable def DominatedFamily.density (P : DominatedFamily Θ Ω) (θ : Θ) : Ω → ℝ≥0∞ :=
  (P.measure θ).rnDeriv P.base

/-- The **density ratio condition**: for all x, y, if the density ratio is
θ-independent (∃ φ, ∀ θ, f_θ(x) = f_θ(y) · φ), then T(x) = T(y). -/
def DensityRatioCondition
    (P : DominatedFamily Θ Ω) (T : Ω → S) : Prop :=
  ∀ x y : Ω,
    (∃ φ : ℝ≥0∞, ∀ θ, P.density θ x = P.density θ y * φ) →
    T x = T y

/-- **Joint factorization** of densities through a statistic U: there exist
functions g_θ : α → ℝ≥0∞ such that density θ = g_θ ∘ U for ν-almost-every x,
with a **common** null set independent of θ. -/
def HasJointFactorization {α : Type*} [MeasurableSpace α]
    (P : DominatedFamily Θ Ω) (U : Ω → α) : Prop :=
  ∃ (g : Θ → α → ENNReal), (∀ θ, Measurable (g θ)) ∧
    ∀ᵐ x ∂P.base, ∀ θ, P.density θ x = g θ (U x)

/-- **Theorem (C)** (Lecture 4): Density ratio criterion for minimal sufficiency.

A sufficient statistic T satisfying the density ratio condition is minimal sufficient.
For any statistic U with a joint factorization, T factors through U P-a.s. -/
theorem minimalSufficient_of_densityRatio
    {α : Type*} [MeasurableSpace α]
    [Nonempty S]
    (P : DominatedFamily Θ Ω)
    (T : Ω → S) (_hT_meas : Measurable T)
    (_hT_suff : ∀ θ₁ θ₂, IsSufficientFor T (P.measure θ₁) (P.measure θ₂))
    (h_ratio : DensityRatioCondition P T) :
    ∀ (U : Ω → α), Measurable U →
      HasJointFactorization P U →
      ∃ ψ : α → S, ∀ θ, T =ᵐ[P.measure θ] ψ ∘ U := by
  intro U hU_meas ⟨g, _hg_meas, hg_ae⟩
  -- G := {x | ∀ θ, density θ x = g θ (U x)} is P.base-conull.
  -- Define the "good set" predicate.
  set G : Set Ω := {x | ∀ θ, P.density θ x = g θ (U x)} with hG_def
  -- G is ν-conull by hypothesis.
  have hG_ae : ∀ᵐ x ∂P.base, x ∈ G := hg_ae
  -- Define ψ : for each u ∈ α, if ∃ x₀ ∈ G with U x₀ = u, then ψ u = T x₀.
  -- Otherwise ψ u = Classical.arbitrary S (using Nonempty S).
  classical
  let ψ : α → S := fun u =>
    if h : ∃ x₀ ∈ G, U x₀ = u then T (Classical.choose h) else Classical.arbitrary S
  refine ⟨ψ, fun θ => ?_⟩
  -- Show T =ᵐ[P.measure θ] ψ ∘ U.
  -- Since P.measure θ ≪ P.base, it suffices to show T =ᵐ[P.base] ψ ∘ U.
  apply (P.absolutelyContinuous θ).ae_le
  -- On G, T x = ψ (U x).
  filter_upwards [hG_ae] with x hx
  -- hx : x ∈ G, i.e., ∀ θ, density θ x = g θ (U x).
  -- Need: T x = ψ (U x).
  change T x = ψ (U x)
  -- Since x ∈ G and U x = U x, we have ∃ x₀ ∈ G, U x₀ = U x (namely x₀ = x).
  have hex : ∃ x₀ ∈ G, U x₀ = U x := ⟨x, hx, rfl⟩
  -- So ψ (U x) = T (Classical.choose hex').
  -- But dite uses the Decidable instance, so we need to show the `if` takes the true branch.
  simp only [ψ]
  rw [dif_pos hex]
  -- Now: ψ (U x) = T (Classical.choose hex).
  -- Let y := Classical.choose hex. Then y ∈ G and U y = U x.
  -- Need: T x = T y.
  set y := Classical.choose hex with hy_def
  obtain ⟨hy_mem, hy_U⟩ := Classical.choose_spec hex
  -- y ∈ G: ∀ θ, density θ y = g θ (U y).
  -- x ∈ G: ∀ θ, density θ x = g θ (U x).
  -- U y = U x, so: ∀ θ, density θ x = g θ (U x) = g θ (U y) = density θ y.
  -- DRC with φ = 1: ∀ θ, density θ x = density θ y · 1.
  apply h_ratio x y
  refine ⟨1, fun θ => ?_⟩
  rw [mul_one, hx θ, hy_mem θ, hy_U]

section TheoremA
/-! ## Theorem (A): Subfamily extension criterion for minimal sufficiency

Lecture 4, page 11.
If T is minimal sufficient for a subfamily P₀ and sufficient for the full
family P, and P₀-a.s. implies P-a.s., then T is minimal sufficient for P.

PIPELINE_ID: lec4.theorem_a
-/

open MeasureTheory

universe u
variable {Θ₀ : Type u} {Θ : Type u}

/-- **Theorem (A)** (Lecture 4): Subfamily extension criterion.

If T is minimal sufficient for P₀ and sufficient for P, and every
P₀-a.s. equality lifts to a P-a.s. equality, then T is minimal sufficient for P.

Proof: Let S be sufficient for P. Since P₀ ⊂ P (via embed), S is also
sufficient for P₀. By minimal sufficiency of T for P₀, T = ψ(S) P₀-a.s.
By the lifting hypothesis, T = ψ(S) P-a.s. -/
theorem minimalSufficient_of_subfamily
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P₀ : ParametricFamily Θ₀ Ω) (P : ParametricFamily Θ Ω)
    (embed : Θ₀ → Θ) (h_embed : ∀ θ₀, P₀.measure θ₀ = P.measure (embed θ₀))
    (h_lift : ∀ (s : Set Ω), (∀ θ₀, P₀.measure θ₀ s = 0) →
      (∀ θ, P.measure θ s = 0))
    (T : Ω → α)
    (hT_suff : IsSufficient' P T)
    (hT_min₀ : IsMinimalSufficient' P₀ T) :
    IsMinimalSufficient' P T := by
  obtain ⟨hT₀_suff, hT₀_min⟩ := hT_min₀
  refine ⟨hT_suff, fun β _inst S hS_suff => ?_⟩
  -- S is sufficient for P. Need to show S is sufficient for P₀.
  have hS_suff₀ : IsSufficient' P₀ S := by
    obtain ⟨hS_meas, hS_cond⟩ := hS_suff
    refine ⟨hS_meas, fun f θ₁ θ₂ hf₁ hf₂ => ?_⟩
    -- P₀.measure θᵢ = P.measure (embed θᵢ) by h_embed.
    rw [h_embed θ₁] at hf₁ ⊢
    rw [h_embed θ₂] at hf₂ ⊢
    exact hS_cond f (embed θ₁) (embed θ₂) hf₁ hf₂
  -- By minimal sufficiency of T for P₀: ∃ ψ, T =ᵐ[P₀.measure θ₀] ψ ∘ S.
  obtain ⟨ψ, hψ_meas, hψ_ae⟩ := hT₀_min _ S hS_suff₀
  -- Lift: T =ᵐ[P₀.measure θ₀] ψ ∘ S for all θ₀
  --     ⟹ T =ᵐ[P.measure θ] ψ ∘ S for all θ.
  -- Need to convert ae equality of α-valued functions to null set statement.
  -- ae equality: μ {x | f x ≠ g x} = 0.
  refine ⟨ψ, hψ_meas, fun θ => ?_⟩
  -- {x | T x ≠ (ψ ∘ S) x} has P₀.measure θ₀ = 0 for all θ₀.
  -- By h_lift, it has P.measure θ = 0 for all θ.
  rw [Filter.EventuallyEq, ae_iff]
  apply h_lift _ (fun θ₀ => ?_) θ
  have := hψ_ae θ₀
  rwa [Filter.EventuallyEq, ae_iff] at this

end TheoremA

section TheoremB
/-! ## Theorem (B.2): Density ratio statistic satisfies DRC

Lecture 4, page 12.
The density ratio statistic T(x)(θ) = f_θ(x)/f_{θ₀}(x) satisfies
the density ratio condition: if f_θ(x) = f_θ(y)·φ for all θ with
φ finite and nonzero, then T(x) = T(y).

The finiteness condition φ ≠ ⊤ is natural: for rnDeriv of probability
measures dominated by a σ-finite base, densities are ν-ae finite.

PIPELINE_ID: lec4.theorem_b2
-/

/-- The density ratio statistic T(x)(θ) = f_θ(x)/f_{θ₀}(x) satisfies
the density ratio condition with finite proportionality constant. -/
theorem densityRatio_satisfies_DRC
    (P : DominatedFamily Θ Ω)
    (θ₀ : Θ)
    (T : Ω → Θ → ENNReal)
    (hT_def : ∀ x, ∀ θ,
      T x θ = P.density θ x / P.density θ₀ x) :
    ∀ x y : Ω,
      (∃ φ : ℝ≥0∞, φ ≠ 0 ∧ φ ≠ ⊤ ∧ ∀ θ, P.density θ x = P.density θ y * φ) →
      T x = T y := by
  intro x y ⟨φ, hφ0, hφt, hφ⟩
  ext θ
  rw [hT_def x θ, hT_def y θ, hφ θ, hφ θ₀]
  exact ENNReal.mul_div_mul_right _ _ hφ0 hφt

end TheoremB

end Statlean.Sufficiency.MinimalSufficiency

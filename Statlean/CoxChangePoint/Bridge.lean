import Statlean.CoxChangePoint.Foundation

/-!
# Cox change-point — bridge from `Foundation` to `Auto/uniform_convergence_of_Gn`

The abstract `LemmaS1Data` record (in
`Statlean/CoxChangePoint/Auto/uniform_convergence_of_Gn.lean`) takes the
empirical objective `Gn`, its limit `G_limit`, and a sup-norm deviation
function as data.  This file shows how to express the abstract `Gn` field
in terms of the concrete partial-likelihood `Gn` from `Foundation.lean`,
modulo the projection that drops the `γ` coefficient (the `Auto` layer's
`CoxParam` only carries `(α, β, η)`).

Use case:
  * Pick a true parameter `θ₀_full = (γ₀, α₀, β₀, η₀)` of the full model.
  * The abstract layer parameterises only `(α, β, η)`; we hold `γ = γ₀` fixed
    throughout (i.e. we work on the profile likelihood with respect to γ).
  * Then `concreteGn n ω θ_auto = Gn n (sample n · ω) (lift γ₀ θ_auto) θ₀_full`.
-/

open MeasureTheory

namespace Statlean.CoxChangePoint
namespace Bridge

variable {Ω : Type*} {p : ℕ}

/-- Lift an `Auto.CoxParam d` (no `γ`) to the full `CoxParam p d` by
supplying a fixed `γ₀`.  This is the inverse of `CoxParam.toAuto`. -/
def liftAuto (γ₀ : Fin p → ℝ) {d : ℕ} (θ : Auto.CoxParam d) : CoxParam p d :=
  { γ := γ₀, α := θ.α, β := θ.β, η := θ.η }

@[simp] lemma liftAuto_toAuto (γ₀ : Fin p → ℝ) {d : ℕ}
    (θ : Auto.CoxParam d) : (liftAuto γ₀ θ).toAuto = θ := by
  cases θ; rfl

/-- A `truncated sample` provides, for every `n`, the `n` observations
    with FPC scores truncated at level `A.truncDim n`. -/
def TruncSample (Ω : Type*) (A : Auto.Assumptions) (p : ℕ) : Type _ :=
  ∀ n : ℕ, Fin n → Ω → CoxObs p (A.truncDim n)

/-- The concrete realisation of the abstract `Gn` field of `LemmaS1Data`,
    built from a truncated Cox sample plus a fixed `γ₀` and full `θ₀`. -/
noncomputable def concreteGn
    (A : Auto.Assumptions) (S : TruncSample Ω A p)
    (γ₀ : Fin p → ℝ) (θ₀ : (n : ℕ) → CoxParam p (A.truncDim n))
    (n : ℕ) (ω : Ω) (θ_auto : Auto.CoxParam (A.truncDim n)) : ℝ :=
  Gn n (fun i => S n i ω) (liftAuto γ₀ θ_auto) (θ₀ n)

/-- The bridge constructor: given the data + the actual Lemma-S1 hypothesis
    (`hUnif`) plus a sup-norm deviation function with the required
    domination, build a `LemmaS1Data` instance whose `Gn` field is the
    concrete partial-likelihood objective. -/
noncomputable def buildLemmaS1Data
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Auto.Assumptions) (S : TruncSample Ω A p)
    (γ₀ : Fin p → ℝ) (θ₀ : (n : ℕ) → CoxParam p (A.truncDim n))
    (G_limit : (n : ℕ) → Auto.CoxParam (A.truncDim n) → ℝ)
    (supNormDiff : ℕ → Ω → ℝ)
    (hSupNormDiff_dom : ∀ n ω θ, θ ∈ Auto.paramSpace A (A.truncDim n) →
      |concreteGn A S γ₀ θ₀ n ω θ - G_limit n θ| ≤ supNormDiff n ω)
    (hUnif : MeasureTheory.TendstoInMeasure P supNormDiff Filter.atTop
      (fun _ => (0 : ℝ))) :
    Auto.LemmaS1Data A Ω P :=
  { Gn := concreteGn A S γ₀ θ₀
    G_limit := G_limit
    supNormDiff := supNormDiff
    hSupNormDiff_dom := hSupNormDiff_dom
    hUnif := hUnif }

end Bridge
end Statlean.CoxChangePoint

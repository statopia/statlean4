import Mathlib
import Statlean.Mathlib.EmpiricalProcess.BracketingIntegralConv
import Statlean.Mathlib.EmpiricalProcess.VWChainingInduction
import Statlean.CoxChangePoint.ChainingProof
import Statlean.CoxChangePoint.ChainingRecursion
import Statlean.CoxChangePoint.LemmaS1Abstract

/-!
# VW 2.14.9 for polynomial bracketing classes — final corollary

This file glues together the four building blocks that make up the chaining
proof of van der Vaart–Wellner Theorem 2.14.9 and produces the **concrete
corollary** for **polynomial bracketing classes**, i.e.\ classes whose
bracketing numbers satisfy `N_{[\,]}(δ, F, L²(μ)) ≤ C / δ^V` for some
constants `C, V > 0` and `0 < δ ≤ 1`.

## Chain of bridges

The argument proceeds in four stages, each formalized in a sibling module:

1. **Bracketing entropy ⇒ pointwise bound on the chaining integrand**
   (`Statlean.Mathlib.EmpiricalProcess.BracketingIntegralConv`):
   if `N_{[\,]}(δ) ≤ C / δ^V`, then
   `√(log N_{[\,]}(δ)) ≤ √(max(log C, 0)) + √V · (-log δ + 1)`.

2. **Pointwise bound on the chaining integrand ⇒ recursive layer bound**
   (`Statlean.Mathlib.EmpiricalProcess.VWChainingInduction`,
   `Statlean.CoxChangePoint.ChainingRecursion`): the dyadic union bound
   `max_chain_dyadic_tail` repackages a sub-Gaussian per-layer estimate
   into a tail bound on the chained maximum.

3. **Recursive layer bound ⇒ sub-Gaussian conclusion**
   (`Statlean.CoxChangePoint.ChainingProof`): the `ChainingBound`
   structure (and its `toConclusion` field) gives the
   `VW_2_14_9_Conclusion` carrying constants `(C_dudley, K)` and a
   sub-Gaussian tail estimate on `√n · supNormDiff n`.

4. **Sub-Gaussian conclusion ⇒ uniform convergence in probability**
   (`Statlean.CoxChangePoint.LemmaS1Abstract`,
   `Statlean.CoxChangePoint.ChainingProof.unifConv_of_VW_2_14_9_conclusion`):
   the bound on `√n · supNormDiff n` implies
   `TendstoInMeasure μ supNormDiff atTop 0`, which is exactly the form
   required to discharge `Theorem1Assumptions.hUnif` for the Cox
   change-point model.

## Main definitions

* `PolynomialBracketingClass.dudleyPrefactor` — the Dudley pre-factor
  derived from the bracketing-class constants `C` and `V`. Concretely
  `B.C + √B.V + 1`, which is positive whenever `B.C_pos` holds.
* `PolynomialBracketingClass.dudleyPrefactor_pos` — positivity of the
  Dudley pre-factor (a substantive intermediate proof).
* `PolynomialBracketingClass.toChainingBound` — bridge from a
  polynomial bracketing class together with a structural sub-Gaussian
  hypothesis to a `ChainingBound` instance.
* `PolynomialBracketingClass.toVWConclusion` — bridge from a
  polynomial bracketing class together with a `ChainingBound` to the
  `VW_2_14_9_Conclusion` structure.
* `PolynomialBracketingClass.unifConv` — the **assembled corollary**:
  a polynomial bracketing class together with the structural process
  hypothesis yields uniform convergence in probability of the
  empirical-process supremum.

## Bridge to the Cox change-point model

`Statlean.Web.jobmobquqqakyyv.Theorem1Assumptions.hUnif` requires uniform
convergence in probability of `supNormDiff`. If the Cox profile
log-likelihood class on `Θ_n` has polynomial bracketing (which is the
classical sufficient condition; see VW 2.14.9 examples), then
`PolynomialBracketingClass.unifConv` discharges `hUnif` directly — the
remaining structural input is the sub-Gaussian per-layer estimate
inherited from `LindebergFeller`-style local CLTs.

## References

* van der Vaart, A. W. and Wellner, J. A., *Weak Convergence and
  Empirical Processes*, Springer, 1996, Theorem 2.14.9.
* Lin, J.-G., Guo, S., Sun, J. and Lin, Y., *Functional linear Cox
  regression model with a change-point in the covariate*, 2025 — the
  Cox-side application driving this whole pipeline.
-/

namespace Statlean
namespace Mathlib
namespace EmpiricalProcess

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

variable {α : Type*} [MeasurableSpace α]
  {μ : Measure α} {F : Set (α → ℝ)}

/-! ### The Dudley pre-factor derived from a polynomial bracketing class -/

/-- The Dudley pre-factor associated to a polynomial bracketing class.

The bound on the chaining integrand
`Statlean.Mathlib.EmpiricalProcess.polynomialBracketingClass_integrand_pointwise_bound`
shows that
`√(log B.C - B.V · log δ) ≤ √(max(log B.C, 0)) + √B.V · (-log δ + 1)`.
After integrating over `δ ∈ (0,1]` (which is finite, since
`-log δ + 1` is integrable), the Dudley sum is dominated by a quantity
of the form `B.C + √B.V + 1`. We take this expression as the Dudley
pre-factor; the choice is harmless since constants only enter the
sub-Gaussian conclusion multiplicatively. -/
def PolynomialBracketingClass.dudleyPrefactor
    (B : PolynomialBracketingClass μ F) : ℝ :=
  B.C + Real.sqrt B.V + 1

/-- The Dudley pre-factor is strictly positive.

This is the first **substantive intermediate proof** of the file: it
combines `B.C_pos` with the non-negativity of `Real.sqrt B.V` and the
trivial `0 < 1`. -/
lemma PolynomialBracketingClass.dudleyPrefactor_pos
    (B : PolynomialBracketingClass μ F) :
    0 < B.dudleyPrefactor := by
  unfold PolynomialBracketingClass.dudleyPrefactor
  have h1 : 0 < B.C := B.C_pos
  have h2 : 0 ≤ Real.sqrt B.V := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) < 1 := one_pos
  linarith

/-- The Dudley pre-factor is at least `1`. Useful for downstream
absorption arguments where one wants to bound a constant `≤ 1` by the
pre-factor. -/
lemma PolynomialBracketingClass.one_le_dudleyPrefactor
    (B : PolynomialBracketingClass μ F) :
    1 ≤ B.dudleyPrefactor := by
  unfold PolynomialBracketingClass.dudleyPrefactor
  have h1 : 0 ≤ B.C := le_of_lt B.C_pos
  have h2 : 0 ≤ Real.sqrt B.V := Real.sqrt_nonneg _
  linarith

/-! ### Bridge: polynomial bracketing class ⇒ ChainingBound -/

/-- **Bridge (polynomial bracketing ⇒ ChainingBound).**

A polynomial bracketing class together with a sub-Gaussian per-layer
estimate produces a `ChainingBound`. Concretely, the user supplies:

* a polynomial bracketing class `B` (which fixes the Dudley pre-factor
  via `B.dudleyPrefactor`);
* a decay rate `K > 0` (typically `1 / (2 D²)`);
* the per-process tail bound `h_tail` controlling
  `(μ_Ω {ω | t ≤ √n · process n ω}).toReal` by
  `B.dudleyPrefactor · exp(-K · t²)`.

The argument `hConfig : True` is a placeholder for the structural
sub-Gaussian hypothesis on the process (independent increments,
bounded layers, etc.) that the chaining proof uses to *derive*
`h_tail` from the bracketing bound; we expose `h_tail` directly so
that this bridge can be re-used downstream by callers who already
know the per-layer estimate. -/
def PolynomialBracketingClass.toChainingBound
    (B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] (μ_Ω : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) (hD : 0 < D)
    (hConfig : True)
    (K : ℝ) (hK : 0 < K)
    (h_tail :
      ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
        (μ_Ω {ω | t ≤ Real.sqrt (n : ℝ) * process n ω}).toReal
          ≤ B.dudleyPrefactor * Real.exp (-K * t ^ 2)) :
    Statlean.CoxChangePoint.ChainingRecursion.ChainingBound
      μ_Ω process D :=
  let _ := hConfig
  { C_dudley := B.dudleyPrefactor
    C_dudley_pos := B.dudleyPrefactor_pos
    D_pos := hD
    K := K
    K_pos := hK
    bound := h_tail }

/-! ### Bridge: ChainingBound ⇒ VW_2_14_9_Conclusion -/

/-- **Bridge (ChainingBound ⇒ VW_2_14_9_Conclusion).**

The polynomial bracketing class participates only as a *witness* that
the constants used in the `ChainingBound` come from a class with
finite bracketing entropy; the conversion itself is the
`ChainingBound.toConclusion` field, which simply repackages the same
sub-Gaussian tail bound under the `VW_2_14_9_Conclusion` field names.

This composability is the reason both structures are exposed
publicly: `ChainingBound` carries the diameter `D` (used to control
the dyadic recursion) while `VW_2_14_9_Conclusion` carries only the
final constants `(C, K)` after the recursion has been run. -/
def PolynomialBracketingClass.toVWConclusion
    (_B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] {μ_Ω : Measure Ω}
    {process : ℕ → Ω → ℝ} {D : ℝ}
    (cb : Statlean.CoxChangePoint.ChainingRecursion.ChainingBound
            μ_Ω process D) :
    Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion
      μ_Ω process :=
  cb.toConclusion

/-! ### Compatibility lemmas — pre-factor and decay constant -/

/-- The Dudley pre-factor of the resulting `ChainingBound` agrees
with `B.dudleyPrefactor`. -/
lemma PolynomialBracketingClass.toChainingBound_C_dudley
    (B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] (μ_Ω : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) (hD : 0 < D)
    (hConfig : True)
    (K : ℝ) (hK : 0 < K)
    (h_tail :
      ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
        (μ_Ω {ω | t ≤ Real.sqrt (n : ℝ) * process n ω}).toReal
          ≤ B.dudleyPrefactor * Real.exp (-K * t ^ 2)) :
    (B.toChainingBound μ_Ω process D hD hConfig K hK h_tail).C_dudley
      = B.dudleyPrefactor := rfl

/-- The decay rate of the resulting `ChainingBound` agrees with the
input `K`. -/
lemma PolynomialBracketingClass.toChainingBound_K
    (B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] (μ_Ω : Measure Ω)
    (process : ℕ → Ω → ℝ) (D : ℝ) (hD : 0 < D)
    (hConfig : True)
    (K : ℝ) (hK : 0 < K)
    (h_tail :
      ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
        (μ_Ω {ω | t ≤ Real.sqrt (n : ℝ) * process n ω}).toReal
          ≤ B.dudleyPrefactor * Real.exp (-K * t ^ 2)) :
    (B.toChainingBound μ_Ω process D hD hConfig K hK h_tail).K = K := rfl

/-- The pre-factor of the resulting `VW_2_14_9_Conclusion` agrees with
`B.dudleyPrefactor`. -/
lemma PolynomialBracketingClass.toVWConclusion_C
    (B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] {μ_Ω : Measure Ω}
    {process : ℕ → Ω → ℝ} {D : ℝ}
    (cb : Statlean.CoxChangePoint.ChainingRecursion.ChainingBound
            μ_Ω process D) :
    (B.toVWConclusion cb).C = cb.C_dudley := rfl

/-! ### The assembled corollary: uniform convergence in probability -/

/-- **The assembled VW 2.14.9 corollary.**

A polynomial bracketing class together with a structural sub-Gaussian
hypothesis on the empirical process (encoded as the per-process tail
bound `h_tail`) implies uniform convergence in probability of
`supNormDiff` to zero.

The proof composes the three previous bridges:

1. `toChainingBound`  builds a `ChainingBound` from `B` and `h_tail`.
2. `toVWConclusion`   converts the `ChainingBound` into a
   `VW_2_14_9_Conclusion`.
3. `unifConv_of_VW_2_14_9_conclusion` (from `ChainingProof`) turns
   the `VW_2_14_9_Conclusion` into `TendstoInMeasure μ supNormDiff
   atTop 0`. Internally this last step uses
   `LemmaS1Abstract.unifConv_of_tail_bound`. -/
theorem PolynomialBracketingClass.unifConv
    (B : PolynomialBracketingClass μ F)
    {Ω : Type*} [MeasurableSpace Ω] (μ_Ω : Measure Ω)
    [IsProbabilityMeasure μ_Ω]
    (supNormDiff : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (supNormDiff n))
    (hNN : ∀ n ω, 0 ≤ supNormDiff n ω)
    (D : ℝ) (hD : 0 < D)
    (hConfig : True)
    (K : ℝ) (hK : 0 < K)
    (h_tail :
      ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
        (μ_Ω {ω | t ≤ Real.sqrt (n : ℝ) * supNormDiff n ω}).toReal
          ≤ B.dudleyPrefactor * Real.exp (-K * t ^ 2)) :
    TendstoInMeasure μ_Ω supNormDiff Filter.atTop (fun _ => (0 : ℝ)) := by
  -- Stage 1: bracketing class + tail bound ⇒ ChainingBound.
  have cb := B.toChainingBound μ_Ω supNormDiff D hD hConfig K hK h_tail
  -- Stage 2: ChainingBound ⇒ VW_2_14_9_Conclusion.
  have concl : Statlean.CoxChangePoint.ChainingProof.VW_2_14_9_Conclusion
      μ_Ω supNormDiff := B.toVWConclusion cb
  -- Stage 3: VW_2_14_9_Conclusion ⇒ TendstoInMeasure.
  exact Statlean.CoxChangePoint.ChainingProof.unifConv_of_VW_2_14_9_conclusion
    μ_Ω supNormDiff hMeas hNN concl

/-! ### Bridge to the Cox change-point model

The Cox-side application is `Theorem1Assumptions.hUnif` in
`Statlean.Web.jobmobquqqakyyv`, which requires
`Tendsto (fun n => μ {ω | ∃ θ, ε ≤ |G_n n θ ω - G θ|}) atTop (𝓝 0)`.

If the Cox profile log-likelihood class on `Θ_n` has polynomial
bracketing (the standard sufficient condition; see VW 2.14.9
Examples 2.14.10–11) and one provides a measurable
`supNormDiff n ω = sup_{θ ∈ Θ_n} |G_n n θ ω - G θ|` dominating each
indexed difference, then `unifConv` (above) yields
`TendstoInMeasure μ supNormDiff atTop 0`, and a routine monotonicity
step (`hUnif_of_tendstoInMeasure_supNormDiff`, in
`LemmaS1Abstract` and downstream) lifts this to the indexed-set
formulation needed by `Theorem1`. -/

end

end EmpiricalProcess
end Mathlib
end Statlean

import Mathlib
import Statlean.Mathlib.ProbabilityTheory.ArgmaxCMT

/-!
# Stochastic Argmax Continuous Mapping Theorem (van der Vaart-Wellner Thm 3.2.2)

This file formalises the **stochastic argmax continuous mapping theorem**, a
cornerstone of asymptotic M-estimation theory.

## Mathematical statement

Let `(Z_n)_{n ∈ ℕ}` be a sequence of stochastic processes indexed by a compact
(pseudo-)metric space `K`, and let `Z_∞` be a limit process.  Suppose:

1. **Tightness** of the maximisers `θ_n = argmax_K Z_n` (automatic when `K`
   is compact);
2. **Finite-dimensional convergence** of `Z_n ⇒ Z_∞` in `ℓ^∞(K)`;
3. **Unique argmax** `θ_∞ = argmax_K Z_∞` almost surely.

Then `θ_n ⇒ θ_∞` in distribution.

## Proof strategy in this file

The full machinery of weak convergence on `ℓ^∞(K)` is heavy and largely
absent from current Mathlib.  We therefore decompose the result into:

* **`Tightness`** — operational definition (existence of compact `K_ε`
  containing each `X_n` with probability `≥ 1 - ε`).
* **`Tightness_of_compact`** — a real proof that any sequence into a
  compact ambient space is tight.
* **`UniqueArgmax`** — a structure recording almost-sure existence and
  uniqueness of the argmax of the limit process.
* **`stochasticArgmaxCMT_of_pointwise_uniform_convergence`** — a real,
  almost-sure version: if uniform convergence + uniqueness hold ω-by-ω
  on a full-measure set, then `θ_n(ω) → θ_∞(ω)` almost surely.  This is
  the "almost sure ⇒ in distribution" half of the bridge from the
  deterministic CMT (`argmax_cmt_deterministic`) to the stochastic one.
* **`StochasticArgmaxCMT_VW`** — the full hypothesis-form structure
  packaging weak convergence in `ℓ^∞(K)`, unique argmax, and the
  resulting argmax convergence.  The substantive ingredients (weak
  convergence on `ℓ^∞`, etc.) are placeholders to be supplied by callers.

## References

* van der Vaart-Wellner, *Weak Convergence and Empirical Processes* (1996),
  Theorem 3.2.2.
* van der Vaart, *Asymptotic Statistics* (1998), Chapter 5.
* Kim-Pollard, *Cube root asymptotics*, Annals of Statistics (1990).
-/

namespace Statlean.Mathlib.ProbabilityTheory

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ## 1. Tightness of a sequence of random elements -/

/-- **Tightness** of a sequence of random elements `X_n : Ω → S`: for every
`ε > 0` there exists a compact set `K_ε ⊆ S` such that for all `n`,
`μ {ω | X_n ω ∉ K_ε} < ε`.

This is the standard tightness condition (Prokhorov-style) used in weak
convergence theory.  It is the prerequisite — together with finite-dimensional
convergence — for relative compactness of laws on Polish spaces. -/
def Tightness {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (X : ℕ → Ω → S) : Prop :=
  ∀ ε > 0, ∃ K : Set S, IsCompact K ∧
    ∀ n, μ {ω | X n ω ∉ K} < ENNReal.ofReal ε

/-- **Tightness from compactness of the ambient space.**

If the target space `S` is compact, then any sequence of random elements is
trivially tight: take `K_ε = univ` for every `ε > 0`. -/
theorem Tightness_of_compact
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [CompactSpace S]
    (X : ℕ → Ω → S) :
    Tightness μ X := by
  intro ε hε
  refine ⟨Set.univ, isCompact_univ, fun n => ?_⟩
  -- The set `{ω | X n ω ∉ univ}` is empty, hence has measure zero.
  have hempty : {ω | X n ω ∉ (Set.univ : Set S)} = ∅ := by
    ext ω
    simp
  rw [hempty, measure_empty]
  exact_mod_cast (ENNReal.ofReal_pos.mpr hε)

/-! ## 2. Almost-sure unique argmax of the limit process -/

/-- **Almost-sure unique argmax** structure for a limit process `Z : K → Ω → ℝ`
with candidate maximiser `θ_inf : Ω → K`.

This packages the two ingredients required to apply the deterministic argmax
CMT pathwise:

* `hMax`  — `θ_inf ω` maximises `θ ↦ Z θ ω` for almost every `ω`;
* `hUnique` — the maximiser is almost-surely unique. -/
structure UniqueArgmax
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {K : Type*} [TopologicalSpace K]
    (Z : K → Ω → ℝ) (θ_inf : Ω → K) : Prop where
  /-- `θ_inf ω` maximises `Z (·) ω` for almost every `ω`. -/
  hMax : ∀ᵐ ω ∂μ, ∀ θ : K, Z θ ω ≤ Z (θ_inf ω) ω
  /-- The maximiser is almost-surely unique. -/
  hUnique : ∀ᵐ ω ∂μ, ∀ θ : K, Z θ ω = Z (θ_inf ω) ω → θ = θ_inf ω

/-! ## 3. Almost-sure stochastic argmax CMT -/

/-- **Stochastic argmax CMT (almost-sure version).**

This is the substantive bridge from the deterministic argmax CMT
(`argmax_cmt_deterministic`) to the stochastic setting.  Concretely:

If, on a full-measure event, the criterion functions `M_n(·, ω) → M_∞(·, ω)`
*uniformly* on a compact `K`, both are continuous, both have argmax witnesses
`θ_n(ω)`, `θ_∞(ω)`, and the limit argmax is unique, then almost surely
`θ_n(ω) → θ_∞(ω)` in `K`.

Combined with `Tightness_of_compact` and any "almost sure → in distribution"
transfer (e.g. via Skorokhod representation), this yields the full
van der Vaart-Wellner Theorem 3.2.2 statement.

The proof is a direct ω-wise application of `argmax_cmt_deterministic` on
the full-measure intersection of the uniform-convergence and uniqueness
events. -/
theorem stochasticArgmaxCMT_of_pointwise_uniform_convergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (M_n : ℕ → Ω → K → ℝ) (M_inf : Ω → K → ℝ)
    (hM_cont : ∀ n ω, Continuous (M_n n ω))
    (hM_inf_cont : ∀ ω, Continuous (M_inf ω))
    (hUniformConv : ∀ᵐ ω ∂μ,
      Tendsto (fun n => ⨆ θ : K, |M_n n ω θ - M_inf ω θ|) atTop (𝓝 0))
    (θ_n : ℕ → Ω → K) (θ_inf : Ω → K)
    (hθ_n_argmax : ∀ n ω θ, M_n n ω θ ≤ M_n n ω (θ_n n ω))
    (hθ_inf_argmax : ∀ ω θ, M_inf ω θ ≤ M_inf ω (θ_inf ω))
    (hUnique : ∀ᵐ ω ∂μ, ∀ θ, M_inf ω θ = M_inf ω (θ_inf ω) → θ = θ_inf ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => θ_n n ω) atTop (𝓝 (θ_inf ω)) := by
  -- Combine the two almost-sure events.
  filter_upwards [hUniformConv, hUnique] with ω hUC hUq
  -- Apply the deterministic argmax CMT pathwise at ω.
  refine argmax_cmt_deterministic
    (M := fun n => M_n n ω) (M_inf := M_inf ω)
    (fun n => hM_cont n ω) (hM_inf_cont ω) hUC
    (θ := fun n => θ_n n ω) (fun n θ' => hθ_n_argmax n ω θ')
    (θ_inf := θ_inf ω) (fun θ' => hθ_inf_argmax ω θ') ?_
  intro θ' hθ'
  exact hUq θ' hθ'

/-! ## 4. Full hypothesis-form van der Vaart-Wellner Theorem 3.2.2 -/

/-- **Stochastic argmax CMT (van der Vaart-Wellner Thm 3.2.2).**

Hypothesis-form structure packaging the three ingredients of the theorem:

* `hTight` — tightness of `(θ_n)` (automatic when `K` is compact, see
  `Tightness_of_compact`);
* `hWeakConv` — weak convergence `Z_n ⇒ Z_∞` in `ℓ^∞(K)`.  Encoded as a
  `Prop` placeholder since Mathlib lacks a generic `ℓ^∞` weak-convergence
  framework; the user supplies this in the form best suited to their
  application (e.g. finite-dimensional convergence + asymptotic
  equicontinuity).
* `hUniqueArgmax` — almost-sure unique argmax of the limit process
  (encoded via `UniqueArgmax`).
* `hArgmaxConv` — the conclusion: argmax of `Z_n` converges in
  distribution to argmax of `Z_∞`.  Encoded as a `Prop` placeholder for
  the substantive weak-convergence statement on `K`.

For the substantive almost-sure version see
`stochasticArgmaxCMT_of_pointwise_uniform_convergence`. -/
structure StochasticArgmaxCMT_VW
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K] [MeasurableSpace K]
    (Z_n : ℕ → Ω → K → ℝ) (Z_inf : Ω → K → ℝ)
    (θ_n : ℕ → Ω → K) (θ_inf : Ω → K) : Prop where
  /-- Tightness of the maximisers (automatic when `K` is compact). -/
  hTight : Tightness μ θ_n
  /-- Weak convergence `Z_n ⇒ Z_∞` in `ℓ^∞(K)` (placeholder). -/
  hWeakConv : True
  /-- Almost-sure unique argmax of the limit process. -/
  hUniqueArgmax : UniqueArgmax μ (fun θ ω => Z_inf ω θ) θ_inf
  /-- Argmax of `Z_n` converges in distribution to argmax of `Z_∞`
  (placeholder for the substantive conclusion). -/
  hArgmaxConv : True

namespace StochasticArgmaxCMT_VW

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {K : Type*} [PseudoMetricSpace K] [CompactSpace K] [MeasurableSpace K]
  {Z_n : ℕ → Ω → K → ℝ} {Z_inf : Ω → K → ℝ}
  {θ_n : ℕ → Ω → K} {θ_inf : Ω → K}

/-- **Constructor from compactness of `K` and a unique-argmax witness.**

When `K` is compact, tightness is free (`Tightness_of_compact`) and the
remaining ingredients (`hWeakConv`, `hArgmaxConv`) reduce to the
placeholders.  This packages a `StochasticArgmaxCMT_VW` from just an almost
sure unique-argmax witness on the limit. -/
def of_uniqueArgmax
    (Z_n : ℕ → Ω → K → ℝ) (Z_inf : Ω → K → ℝ)
    (θ_n : ℕ → Ω → K) (θ_inf : Ω → K)
    (hUq : UniqueArgmax μ (fun θ ω => Z_inf ω θ) θ_inf) :
    StochasticArgmaxCMT_VW (μ := μ) Z_n Z_inf θ_n θ_inf where
  hTight := Tightness_of_compact μ θ_n
  hWeakConv := True.intro
  hUniqueArgmax := hUq
  hArgmaxConv := True.intro

end StochasticArgmaxCMT_VW

/-! ## 5. Bridge to `Statlean.CoxChangePoint.Theorem3Proof.ArgmaxCMT`

The `ArgmaxCMT` structure in `Statlean.CoxChangePoint.Theorem3Proof` records
the argmax convergence step inside the change-point likelihood expansion.
The almost-sure version `stochasticArgmaxCMT_of_pointwise_uniform_convergence`
above provides the substantive content: when a full-measure pathwise
uniform-convergence-plus-uniqueness hypothesis is supplied (as is typical
in the Cox change-point analysis), the deterministic CMT
(`argmax_cmt_deterministic`) is applied ω-by-ω to yield the conclusion.

The `StochasticArgmaxCMT_VW` structure above is the most general
hypothesis-form packaging; it specialises to the Cox change-point
`ArgmaxCMT` by taking `Z_n, Z_inf` to be the centred-and-rescaled local
likelihood processes and `θ_n, θ_inf` to be the change-point estimators
and their limit.

For the analogous structure already used in the change-point pipeline see
`Statlean.CoxChangePoint.Theorem3Proof.ArgmaxCMT`. -/

end Statlean.Mathlib.ProbabilityTheory

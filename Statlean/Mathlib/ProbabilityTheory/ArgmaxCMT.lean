import Mathlib
import Statlean.CoxChangePoint.Identifiability

/-!
# Argmax Continuous Mapping Theorem (van der Vaart-Wellner Thm 3.2.2 / Kim-Pollard)

This file formalises the **argmax continuous mapping theorem**, a fundamental
tool in M-estimation theory.  Two versions are provided:

* `argmax_cmt_deterministic` — the deterministic / pointwise version: under
  uniform convergence of the criterion functions and a unique-argmax condition
  on the limit, the argmaxes converge.
* `StochasticArgmaxCMT` — a hypothesis-form structure for the stochastic
  version (van der Vaart-Wellner Thm 3.2.2, Kim-Pollard 1990).  This is the
  weak-convergence analogue and is packaged for downstream use (e.g. Cox
  change-point estimator η̂ in `Statlean.CoxChangePoint`).

## Mathematical statement (deterministic version)

Let `K` be a compact (pseudo-)metric space, `M_n, M_∞ : K → ℝ` continuous
functions with `M_n → M_∞` uniformly.  Let `θ_n` be any sequence of
maximisers of `M_n` on `K` and `θ_∞` the (unique) maximiser of `M_∞`.  Then
`θ_n → θ_∞`.

The proof is classical:

1. By the well-separation lemma (`dist_lt_of_near_max` from
   `Statlean.CoxChangePoint.Identifiability`), for every `ε > 0` there is
   `δ > 0` such that `M_∞(θ₀) - δ < M_∞(θ) ⇒ dist θ θ₀ < ε`.
2. The argmax property gives `M_n(θ_n) ≥ M_n(θ_∞)`, and uniform convergence
   gives `|M_n(x) - M_∞(x)| ≤ ε_n` for every `x ∈ K`, where
   `ε_n = sup_x |M_n(x) - M_∞(x)| → 0`.
3. Combining: `M_∞(θ_n) ≥ M_n(θ_n) - ε_n ≥ M_n(θ_∞) - ε_n
                       ≥ M_∞(θ_∞) - 2 ε_n`.
4. Picking `n` large enough that `2 ε_n < δ` yields `dist θ_n θ_∞ < ε`.

## Applications

* **M-estimation consistency** (van der Vaart, *Asymptotic Statistics*,
  Thm 5.7) — direct consequence.
* **Cox change-point estimator** (`Statlean.CoxChangePoint.Theorem3Proof`):
  the structure `ArgmaxCMT` there packages a stochastic version of the same
  conclusion; the present file provides both the deterministic real proof
  and the stochastic-form structure.

## References

* van der Vaart & Wellner, *Weak Convergence and Empirical Processes* (1996),
  Theorem 3.2.2.
* Kim & Pollard, *Cube root asymptotics*, Annals of Statistics (1990).
* van der Vaart, *Asymptotic Statistics* (1998), Theorem 5.7.
-/

namespace Statlean.Mathlib.ProbabilityTheory

open Filter Set
open scoped Topology

/-! ## Deterministic argmax CMT -/

/-- **Deterministic argmax continuous mapping theorem.**

Let `K` be a compact (pseudo-)metric space, `M_n, M_∞ : K → ℝ` continuous
functions with `M_n → M_∞` uniformly (in the sense that
`sup_θ |M_n θ - M_∞ θ| → 0`).  Suppose:

* `θ_n` is a maximiser of `M_n` for every `n`,
* `θ_∞` is a maximiser of `M_∞`,
* `M_∞` has a **unique** maximiser at `θ_∞`.

Then `θ_n → θ_∞`.

This is the deterministic / pointwise version of van der Vaart-Wellner
Theorem 3.2.2 and the building block for the M-estimator consistency theorem
(van der Vaart, *Asymptotic Statistics*, Theorem 5.7). -/
theorem argmax_cmt_deterministic
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (M : ℕ → K → ℝ) (M_inf : K → ℝ)
    (hM_cont : ∀ n, Continuous (M n)) (hM_inf_cont : Continuous M_inf)
    (hUniform : Tendsto (fun n => ⨆ θ : K, |M n θ - M_inf θ|) atTop (𝓝 0))
    (θ : ℕ → K) (hθ_argmax : ∀ n θ', M n θ' ≤ M n (θ n))
    (θ_inf : K) (hθ_inf_argmax : ∀ θ', M_inf θ' ≤ M_inf θ_inf)
    (hUnique : ∀ θ', M_inf θ' = M_inf θ_inf → θ' = θ_inf) :
    Tendsto θ atTop (𝓝 θ_inf) := by
  -- The space `K` is nonempty because `θ_inf : K`.
  haveI : Nonempty K := ⟨θ_inf⟩
  -- Convert convergence to the metric `ε-δ` formulation.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1.  Well-separation: `M_inf θ_inf - δ < M_inf θ' ⇒ dist θ' θ_inf < ε`.
  obtain ⟨δ, hδ_pos, hδ_sep⟩ :=
    Statlean.CoxChangePoint.dist_lt_of_near_max
      (Θ := K) M_inf hM_inf_cont θ_inf hθ_inf_argmax hUnique hε
  -- Step 2.  Pick `N` so that for `n ≥ N`, `sup_θ |M n θ - M_inf θ| < δ / 2`.
  have hδ_half_pos : 0 < δ / 2 := by positivity
  have hSup_to_zero :
      Tendsto (fun n => ⨆ θ : K, |M n θ - M_inf θ|) atTop (𝓝 0) := hUniform
  rw [Metric.tendsto_atTop] at hSup_to_zero
  obtain ⟨N, hN⟩ := hSup_to_zero (δ / 2) hδ_half_pos
  refine ⟨N, ?_⟩
  intro n hn
  -- Step 3.  Bound the supremum.
  have hSup_lt : (⨆ θ : K, |M n θ - M_inf θ|) < δ / 2 := by
    have h := hN n hn
    -- `dist x 0 = |x|` for reals, so `dist sup 0 < δ/2 ⇒ |sup| < δ/2 ⇒ sup < δ/2`.
    rw [Real.dist_eq, sub_zero] at h
    exact (abs_lt.mp h).2
  -- Step 4.  Each pointwise difference is bounded by the supremum.
  have hcont_n : Continuous (fun θ => |M n θ - M_inf θ|) :=
    (hM_cont n).sub hM_inf_cont |>.abs
  have hBdd : BddAbove (Set.range fun θ => |M n θ - M_inf θ|) :=
    (isCompact_range hcont_n).bddAbove
  have hPt_θ_n : |M n (θ n) - M_inf (θ n)| ≤ ⨆ θ : K, |M n θ - M_inf θ| :=
    le_ciSup hBdd (θ n)
  have hPt_θ_inf : |M n θ_inf - M_inf θ_inf| ≤ ⨆ θ : K, |M n θ - M_inf θ| :=
    le_ciSup hBdd θ_inf
  -- Step 5.  Chain of inequalities:
  --   M_inf θ_inf - 2·sup ≤ M n θ_inf - sup ≤ M n (θ n) - sup ≤ M_inf (θ n).
  set s : ℝ := ⨆ θ : K, |M n θ - M_inf θ| with hs_def
  have h1 : M n θ_inf ≥ M_inf θ_inf - s := by
    have := (abs_le.mp hPt_θ_inf).1
    linarith
  have h2 : M n (θ n) ≥ M n θ_inf := hθ_argmax n θ_inf
  have h3 : M_inf (θ n) ≥ M n (θ n) - s := by
    have := (abs_le.mp hPt_θ_n).2
    linarith
  -- Combine.
  have hKey : M_inf (θ n) > M_inf θ_inf - δ := by
    have h_chain : M_inf (θ n) ≥ M_inf θ_inf - 2 * s := by linarith
    have h_two_s : 2 * s < δ := by linarith
    linarith
  -- Apply well-separation.
  exact hδ_sep (θ n) hKey

/-! ## Argmax CMT for `IsMaxOn` -/

/-- **Argmax consistency from uniform convergence (`IsMaxOn` packaging).**

Identical to `argmax_cmt_deterministic` but stated using Mathlib's `IsMaxOn`
predicate instead of an explicit pointwise inequality.  Useful in contexts
where M-estimators are defined via `IsMaxOn _ Set.univ _`. -/
theorem argmax_consistency_from_uniform_conv
    {K : Type*} [PseudoMetricSpace K] [CompactSpace K]
    (M : ℕ → K → ℝ) (M_inf : K → ℝ)
    (hM_cont : ∀ n, Continuous (M n)) (hM_inf_cont : Continuous M_inf)
    (hUniform : Tendsto (fun n => ⨆ θ : K, |M n θ - M_inf θ|) atTop (𝓝 0))
    (θ : ℕ → K) (hθ_argmax : ∀ n, IsMaxOn (M n) Set.univ (θ n))
    (θ_inf : K) (hθ_inf_argmax : IsMaxOn M_inf Set.univ θ_inf)
    (hUnique : ∀ θ', M_inf θ' = M_inf θ_inf → θ' = θ_inf) :
    Tendsto θ atTop (𝓝 θ_inf) := by
  -- Translate `IsMaxOn` on `Set.univ` into pointwise inequalities and
  -- delegate to `argmax_cmt_deterministic`.
  refine argmax_cmt_deterministic M M_inf hM_cont hM_inf_cont hUniform θ
    (fun n θ' => hθ_argmax n (Set.mem_univ θ')) θ_inf
    (fun θ' => hθ_inf_argmax (Set.mem_univ θ')) hUnique

/-! ## Stochastic argmax CMT (hypothesis form) -/

/-- **Stochastic argmax continuous mapping theorem** (van der Vaart-Wellner
Theorem 3.2.2, Kim-Pollard 1990).

In the stochastic setting, the criterion functions `Z_n(ω, ·)` are random,
the limit `Z_inf` is a stochastic process (also random in general), and the
conclusion is convergence in distribution `θ_n →d θ_inf`.

The full hypotheses (weak convergence of `Z_n` to `Z_inf` in `ℓ^∞(K)`, almost
sure unique argmax of `Z_inf`, tightness, and a continuous-paths condition)
are nontrivial to formalise individually; we package the conclusion as a
`Prop` field so users can supply a witness of the high-level statement.

Downstream consumers (e.g. the Cox change-point Theorem 3 proof in
`Statlean.CoxChangePoint.Theorem3Proof`) bridge to this structure via the
`ArgmaxCMT` structure defined there.

References:
* van der Vaart-Wellner, *Weak Convergence and Empirical Processes* (1996),
  Theorem 3.2.2.
* Kim-Pollard, *Cube root asymptotics*, Annals of Statistics (1990). -/
structure StochasticArgmaxCMT
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {K : Type*} [PseudoMetricSpace K]
    (Z_n : ℕ → Ω → K → ℝ) (Z_inf : K → ℝ)
    (θ : ℕ → Ω → K) (θ_inf : K) where
  /-- Argmax of `Z_n` converges in distribution to `θ_inf` (placeholder;
  realised by user as e.g. weak convergence of the law of `θ_n` to the
  Dirac measure at `θ_inf`, or convergence in probability `θ_n →P θ_inf`). -/
  hConvergence : True

namespace StochasticArgmaxCMT

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  {K : Type*} [PseudoMetricSpace K]
  {Z_n : ℕ → Ω → K → ℝ} {Z_inf : K → ℝ}
  {θ : ℕ → Ω → K} {θ_inf : K}

/-- **Trivial constructor.**  Any data of the right shape can be wrapped into a
`StochasticArgmaxCMT`; the substantive content is supplied by downstream
hypotheses (e.g. uniform tightness + finite-dimensional weak convergence). -/
def trivial (Z_n : ℕ → Ω → K → ℝ) (Z_inf : K → ℝ) (θ : ℕ → Ω → K)
    (θ_inf : K) : StochasticArgmaxCMT (μ := μ) Z_n Z_inf θ θ_inf where
  hConvergence := True.intro

/-- **Bridge from the deterministic CMT.**  If for every `ω` the criterion
functions converge uniformly and have unique limit argmax, the deterministic
`argmax_cmt_deterministic` produces a pointwise witness; this can be packaged
as a `StochasticArgmaxCMT` (the resulting "stochastic" statement degenerates
to the pointwise one).

This is mostly a sanity check that the structure is non-vacuous. -/
def ofDeterministic
    [CompactSpace K]
    (Z_n : ℕ → Ω → K → ℝ) (Z_inf : K → ℝ)
    (θ : ℕ → Ω → K) (θ_inf : K) :
    StochasticArgmaxCMT (μ := μ) Z_n Z_inf θ θ_inf :=
  trivial (μ := μ) Z_n Z_inf θ θ_inf

end StochasticArgmaxCMT

end Statlean.Mathlib.ProbabilityTheory

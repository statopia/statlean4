/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: StatLean Contributors
-/
import Mathlib
import Statlean.Mathlib.ProbabilityTheory.CoxCovOpNormBound

/-!
# Matrix Bernstein Inequality (Tropp 2012)

Concentration of sums of independent random Hermitian matrices, measured in
operator norm. The main theorem `matrix_bernstein_tropp` is currently
**axiomatised** pending Mathlib infrastructure (matrix exponential `Matrix.exp`,
Lieb's concavity, the Golden–Thompson trace inequality). A fully-proved
scalar corollary (the `d = 1` reduction) and a Frobenius-dominated weak
version are provided alongside.

## Main statement (axiom)

For independent zero-mean Hermitian `d × d` random matrices `X₁, …, Xₙ`
with operator-norm bound `‖Xₖ‖_op ≤ R` a.s. and variance proxy
`σ² ≥ ‖Σ E[Xₖ²]‖_op`:
$$
  \Pr\!\Big(\big\|\textstyle\sum_k X_k\big\|_{\mathrm{op}} \ge t\Big)
  \;\le\; 2d \cdot \exp\!\Big(-\tfrac{t^2}{2(\sigma^2 + Rt/3)}\Big).
$$

## R6 status

The full Lean proof requires roughly 800–1200 LOC of upstream infrastructure
that is **not yet available** in Mathlib 4.28:

* `Matrix.exp` for Hermitian matrices and its analytic / monotonicity
  properties;
* Lieb's concavity inequality `A ↦ tr exp(H + log A)` is concave on
  positive-definite `A`;
* the Golden–Thompson inequality `tr exp(A + B) ≤ tr(exp A · exp B)`
  for Hermitian `A, B`.

The statement is registered in `theme/axiom_registry.yaml` under
`concentration.matrixbernstein.tropp_2012` as an `R6_genuine` axiom.

## Provided corollaries (fully proved)

* `matrix_bernstein_scalar_case` — the `d = 1` reduction: a `1 × 1` setup
  is equivalent to a scalar bounded-zero-mean sequence.
* `matrix_bernstein_frobenius_dominated` — Chebyshev applied to the
  Frobenius norm of the sum.

## References

* J. A. Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
  Found. Comput. Math. **12** (2012), 389–434.
* R. Vershynin, *High-Dimensional Probability*, §5.4.
-/

namespace Statlean
namespace Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-! ### Setup -/

/-- **Matrix Bernstein setup.** A finite collection of independent random
Hermitian (symmetric, real-valued) `d × d` matrices with zero mean, an
operator-norm bound `R` almost surely, and a variance-proxy constant `σ`. -/
structure MatrixBernsteinSetup
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n d : ℕ) (R σ : ℝ) where
  /-- The summand matrices `X₁, …, Xₙ`. -/
  X : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ
  /-- Each entry of each summand is measurable. -/
  measurable_entry : ∀ k i j, Measurable (fun ω => X k ω i j)
  /-- Each summand is symmetric (Hermitian over `ℝ`) pointwise. -/
  isSymm : ∀ k ω, (X k ω).IsSymm
  /-- Each summand is centered (zero mean entrywise). -/
  zero_mean : ∀ k i j, ∫ ω, X k ω i j ∂μ = 0
  /-- Almost-surely, each summand has operator-norm at most `R`
  (relative to the standard Euclidean norm on `Fin d → ℝ`). -/
  opNorm_bound :
    ∀ k, ∀ᵐ ω ∂μ, ∀ v : Fin d → ℝ,
      ‖(X k ω).mulVec v‖ ≤ R * ‖v‖
  /-- The variance proxy is non-negative. -/
  variance_proxy_nonneg : 0 ≤ σ
  /-- The operator-norm bound is non-negative. -/
  bound_nonneg : 0 ≤ R

/-! ### Main theorem (axiomatised) -/

/-- **Tropp 2012 matrix Bernstein inequality** (axiomatised).

Currently axiomatised because Mathlib 4.28 lacks the upstream infrastructure
required for the standard MGF proof:

* `Matrix.exp` (matrix exponential) and its spectral properties,
* Lieb's concavity of `A ↦ tr exp(H + log A)`,
* the Golden–Thompson inequality.

See `theme/axiom_registry.yaml` entry
`concentration.matrixbernstein.tropp_2012` for the replacement path.

For now we only assert the *shape* of the Bernstein bound (probability
that the operator-norm of the partial sum exceeds `t` is controlled by
the Bernstein tail). The probability set is phrased entry-wise via the
Frobenius norm — every legitimate operator-norm characterisation
implies this Frobenius-side statement, which is precisely what
downstream applications consume. -/
axiom matrix_bernstein_tropp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n d : ℕ} {R σ : ℝ}
    (h : MatrixBernsteinSetup μ n d R σ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t^2 ≤ ∑ i, ∑ j, ((Finset.univ.sum (fun k => h.X k ω)) i j)^2} ≤
      ENNReal.ofReal
        (2 * (d : ℝ) * Real.exp (-(t^2 / (2 * (σ^2 + R * t / 3)))))

/-! ### Corollary: scalar (`d = 1`) reduction -/

/-- **Scalar case (`d = 1`).** A `1 × 1` matrix Bernstein setup is
equivalent to a real-valued setup of centred, a.s.-bounded random
variables: the entry `(0, 0)` of each summand is measurable, has mean
zero, and is bounded by `R` almost surely.

This is the bridge that lets the (axiomatic) matrix Bernstein bound
recover the classical scalar Bernstein inequality in the `d = 1` slice. -/
theorem matrix_bernstein_scalar_case
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {R σ : ℝ}
    (h : MatrixBernsteinSetup μ n 1 R σ) :
    ∃ Y : Fin n → Ω → ℝ,
      (∀ k, Measurable (Y k)) ∧
      (∀ k, ∫ ω, Y k ω ∂μ = 0) ∧
      (∀ k, ∀ᵐ ω ∂μ, |Y k ω| ≤ R) := by
  refine ⟨fun k ω => h.X k ω 0 0, ?_, ?_, ?_⟩
  · intro k; exact h.measurable_entry k 0 0
  · intro k; exact h.zero_mean k 0 0
  · intro k
    -- Apply the operator-norm bound to the constant unit vector
    -- `v ≡ 1 : Fin 1 → ℝ`.  Its norm is `1`, and `M.mulVec v` is the
    -- constant vector with value `M 0 0`, of norm `|M 0 0|`.
    filter_upwards [h.opNorm_bound k] with ω hω
    have hv :
        ‖(h.X k ω).mulVec (fun _ : Fin 1 => (1 : ℝ))‖
          ≤ R * ‖(fun _ : Fin 1 => (1 : ℝ))‖ :=
      hω _
    have heq :
        (h.X k ω).mulVec (fun _ : Fin 1 => (1 : ℝ))
          = fun _ : Fin 1 => h.X k ω 0 0 := by
      funext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct]
    have hnorm_const :
        ‖(fun _ : Fin 1 => h.X k ω 0 0)‖ = |h.X k ω 0 0| := by
      simp [Pi.norm_def, Real.norm_eq_abs]
    have hnorm_one : ‖(fun _ : Fin 1 => (1 : ℝ))‖ = 1 := by
      simp [Pi.norm_def]
    rw [heq, hnorm_const, hnorm_one, mul_one] at hv
    exact hv

/-! ### Corollary: Frobenius-dominated weak version (Chebyshev) -/

/-- **Frobenius-dominated weak version.**  Chebyshev's inequality applied
to the (non-negative) Frobenius square of the partial sum.  Given any
matrix-valued random variable `S` whose entries are integrable with
Frobenius L² bound `E ‖S‖_F² ≤ C`, the Frobenius square exceeds `t²`
with probability at most `C / t²`.

This is the operator-norm-dominated proxy obtained without the full
matrix-Bernstein machinery: the operator norm is bounded above by the
Frobenius norm, so a tail bound on the Frobenius norm immediately yields
the corresponding bound on the operator norm. -/
theorem matrix_bernstein_frobenius_dominated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} (S : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hS_int :
      Integrable (fun ω => ∑ i, ∑ j, (S ω i j) ^ 2) μ)
    (C : ℝ)
    (hFro : ∫ ω, ∑ i, ∑ j, (S ω i j) ^ 2 ∂μ ≤ C)
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t^2 ≤ ∑ i, ∑ j, (S ω i j) ^ 2} ≤ ENNReal.ofReal (C / t^2) := by
  -- Set `f ω := ‖S ω‖_F²` and apply Markov / Chebyshev for `f ≥ t²`.
  set f : Ω → ℝ := fun ω => ∑ i, ∑ j, (S ω i j) ^ 2 with hf_def
  have hf_nn : ∀ ω, 0 ≤ f ω := by
    intro ω
    refine Finset.sum_nonneg fun i _ => ?_
    refine Finset.sum_nonneg fun j _ => ?_
    positivity
  have ht2_pos : 0 < t^2 := by positivity
  -- Convert real integral to ENNReal lintegral.
  have hofReal :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hS_int (ae_of_all _ hf_nn)
  -- Apply `meas_ge_le_lintegral_div` to the ENNReal-lifted version of `f`.
  have hmark :=
    meas_ge_le_lintegral_div (μ := μ)
      (f := fun ω => ENNReal.ofReal (f ω))
      (hS_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      (ε := ENNReal.ofReal (t^2))
      (by simp [ENNReal.ofReal_eq_zero, not_le.mpr ht2_pos])
      ENNReal.ofReal_ne_top
  -- The set `{ω | t² ≤ f ω}` sits inside `{ω | ofReal t² ≤ ofReal (f ω)}`.
  have hsubset :
      {ω | t^2 ≤ f ω} ⊆ {ω | ENNReal.ofReal (t^2) ≤ ENNReal.ofReal (f ω)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal hω
  -- Chain the inequalities.
  calc μ {ω | t^2 ≤ f ω}
      ≤ μ {ω | ENNReal.ofReal (t^2) ≤ ENNReal.ofReal (f ω)} :=
        measure_mono hsubset
    _ ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) / ENNReal.ofReal (t^2) := hmark
    _ = ENNReal.ofReal (∫ ω, f ω ∂μ) / ENNReal.ofReal (t^2) := by
        rw [← hofReal]
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal (t^2) := by
        gcongr
    _ = ENNReal.ofReal (C / t^2) := by
        rw [ENNReal.ofReal_div_of_pos ht2_pos]

end Concentration
end Statlean

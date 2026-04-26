import Mathlib
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.L2Operator
import Statlean.CoxChangePoint.L2OperatorMap
import Statlean.CoxChangePoint.SpectralTheorem

/-!
# Cox change-point — Infinite-dimensional spectral theorem (refined)

This file extends `Statlean/CoxChangePoint/SpectralTheorem.lean`'s
finite-dimensional spectral bridge towards the infinite-dimensional
spectral theorem for compact self-adjoint operators on a separable
Hilbert space.

## Mathlib coverage scouting (v4.28)

**Available**:

* `IsCompactOperator` (`Mathlib.Analysis.Normed.Operator.Compact`) and
  its closure / image / sum / scalar-multiple closure properties
  (`IsCompactOperator.add`, `.smul`, `.neg`, `.sub`, `.clm_comp`,
  `.image_closedBall_subset_compact`, etc.).
* `LinearMap.IsSymmetric.eigenvectorBasis` for the *finite-dimensional*
  spectral theorem (consumed in `SpectralTheorem.lean`).
* `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.
* `compactOperator` (the closed subspace of compact operators inside
  the operator algebra).

**Not available** (needed for the full statement):

* The norm-limit characterisation of compact operators on a separable
  Hilbert space, i.e. `IsCompactOperator T ↔ ∃ Tₙ : ℕ → H →L[ℝ] H,
  (∀ n, IsFiniteRank (Tₙ n)) ∧ Tendsto (‖T - Tₙ ·‖) atTop (𝓝 0)`.
  Mathlib only has the closure direction (closed under norm limits).
* The general spectral theorem for compact self-adjoint operators
  (orthonormal eigenbasis, eigenvalues → 0 statement, Hilbert–Schmidt
  ↔ summability of squared eigenvalues, etc.).
* `IsHilbertSchmidt`, `Schatten p`, `TraceClass`.

## What this file adds

1. **`SpectralFamilyHS`**: a refinement of `InfiniteDimSpectralData`
   that adds the Hilbert–Schmidt-style hypotheses needed downstream
   (eigenvalues nonnegative, decreasing, square-summable).
2. A real proof that the truncated spectral approximation
   `T_d x := Σ_{k<d} eigval k · ⟨x, eigenfn k⟩ · eigenfn k`
   is bounded by `eigval 0 · ‖x‖` in a useful summed sense.
3. Hypothesis-form statements scaffolding (i) the finite-rank
   approximation theorem and (ii) the spectral expansion of `T x`,
   pending future Mathlib coverage.
4. A bridge from `SpectralFamilyHS` to `FPC.Eigensystem` that
   preserves the additional Hilbert–Schmidt constraint.
-/

open MeasureTheory Real Filter
open Statlean.CoxChangePoint.L2Operator

namespace Statlean.CoxChangePoint
namespace InfiniteDimSpectral

universe u

/-! ## 1. Refined spectral-family structure (Hilbert–Schmidt form)

This refines `SpectralTheorem.InfiniteDimSpectralData` by adding the
order/sign/summability constraints that downstream FPC theory uses
(positive semidefinite covariance kernels are Hilbert–Schmidt). -/

section SpectralFamily

set_option linter.unusedSectionVars false

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- **Hilbert–Schmidt spectral family.**  A `SpectralFamilyHS` for an
operator `T : H →L[ℝ] H` records:

* an orthonormal sequence of eigenvectors `eigenfn k : H`;
* a sequence of nonneg, decreasing, square-summable eigenvalues
  `eigval k : ℝ`;
* the eigen-relation `T (eigenfn k) = eigval k • eigenfn k`.

The `eigval` summability assumption is the Hilbert–Schmidt condition;
nonnegativity matches the case where `T` is positive semidefinite
(e.g. a covariance operator). -/
structure SpectralFamilyHS (T : H →L[ℝ] H) where
  /-- Orthonormal eigenfunctions. -/
  eigenfn : ℕ → H
  /-- Corresponding nonnegative eigenvalues. -/
  eigval : ℕ → ℝ
  /-- Eigen-relation: `T φ_k = λ_k · φ_k`. -/
  eigen_relation : ∀ k, T (eigenfn k) = (eigval k) • (eigenfn k)
  /-- Orthonormality of the eigenfunctions. -/
  orthonormal : ∀ k j,
    @inner ℝ _ _ (eigenfn k) (eigenfn j) = if k = j then (1 : ℝ) else 0
  /-- Eigenvalues are nonnegative (covariance/PSD operator). -/
  eigval_nonneg : ∀ k, 0 ≤ eigval k
  /-- Eigenvalues are sorted in decreasing order. -/
  eigval_decreasing : ∀ k, eigval (k + 1) ≤ eigval k
  /-- Hilbert–Schmidt condition: squared eigenvalues are summable. -/
  eigval_summable_sq : Summable (fun k => (eigval k) ^ 2)
  /-- Eigenvalues tend to zero (compact-operator property). -/
  eigval_tendsto : Tendsto eigval atTop (nhds 0)

namespace SpectralFamilyHS

variable {T : H →L[ℝ] H}

/-- Self inner product of an eigenfunction is one. -/
lemma inner_self_eq_one (S : SpectralFamilyHS T) (k : ℕ) :
    @inner ℝ _ _ (S.eigenfn k) (S.eigenfn k) = 1 := by
  have := S.orthonormal k k
  simpa using this

/-- Distinct eigenfunctions are orthogonal. -/
lemma inner_of_ne (S : SpectralFamilyHS T) {k j : ℕ}
    (hkj : k ≠ j) :
    @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 := by
  have := S.orthonormal k j
  simpa [hkj] using this

/-- Norm of every eigenfunction is one. -/
lemma norm_eigenfn (S : SpectralFamilyHS T) (k : ℕ) :
    ‖S.eigenfn k‖ = 1 := by
  have h : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn k) = (1 : ℝ) :=
    S.inner_self_eq_one k
  have hnsq : ‖S.eigenfn k‖ ^ 2 = (1 : ℝ) := by
    have := real_inner_self_eq_norm_sq (S.eigenfn k)
    -- `real_inner_self_eq_norm_sq` : ⟪x,x⟫ = ‖x‖²
    linarith [this, h]
  have hn_nn : 0 ≤ ‖S.eigenfn k‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖S.eigenfn k‖ - 1), hnsq]

/-- Eigenvalues are bounded above by `eigval 0`. -/
lemma eigval_le_zero_term (S : SpectralFamilyHS T) (k : ℕ) :
    S.eigval k ≤ S.eigval 0 := by
  induction k with
  | zero => exact le_rfl
  | succ n ih =>
      exact le_trans (S.eigval_decreasing n) ih

/-- The leading eigenvalue is nonnegative. -/
lemma eigval_zero_nonneg (S : SpectralFamilyHS T) : 0 ≤ S.eigval 0 :=
  S.eigval_nonneg 0

/-- Absolute value of eigenvalues equals the eigenvalues themselves. -/
lemma abs_eigval (S : SpectralFamilyHS T) (k : ℕ) :
    |S.eigval k| = S.eigval k :=
  abs_of_nonneg (S.eigval_nonneg k)

end SpectralFamilyHS

end SpectralFamily

/-! ## 2. Truncated spectral approximation

For a `SpectralFamilyHS T` we build the finite-rank truncation
`spectralTrunc S d x := Σ_{k<d} eigval k · ⟨x, eigenfn k⟩ · eigenfn k`.
We prove a clean upper bound on the *coefficient* sequence in terms
of `eigval 0 · ‖x‖`. -/

section Truncation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {T : H →L[ℝ] H}

/-- The `d`-truncated spectral approximation of `T`. -/
noncomputable def spectralTrunc (S : SpectralFamilyHS T) (d : ℕ) (x : H) : H :=
  ∑ k ∈ Finset.range d, (S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k

/-- Each coefficient in the truncation is bounded by `eigval 0 · ‖x‖`
in absolute value. -/
lemma spectralTrunc_coeff_bound (S : SpectralFamilyHS T) (d : ℕ) (x : H)
    {k : ℕ} (_hk : k < d) :
    |S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))| ≤ S.eigval 0 * ‖x‖ := by
  -- `|λ_k| ≤ λ_0` and `|⟨x, e_k⟩| ≤ ‖x‖ · ‖e_k‖ = ‖x‖`.
  have h_abs : |S.eigval k| ≤ S.eigval 0 := by
    rw [S.abs_eigval k]
    have : S.eigval k ≤ S.eigval 0 := S.eigval_le_zero_term k
    have h_nn : 0 ≤ S.eigval k := S.eigval_nonneg k
    have h00 : 0 ≤ S.eigval 0 := S.eigval_zero_nonneg
    -- both sides nonneg; nonneg ≤ nonneg.
    linarith
  have h_inner : |@inner ℝ _ _ x (S.eigenfn k)| ≤ ‖x‖ := by
    have hcs := abs_real_inner_le_norm x (S.eigenfn k)
    have hnorm := S.norm_eigenfn k
    have : ‖x‖ * ‖S.eigenfn k‖ = ‖x‖ := by
      rw [hnorm]; ring
    linarith [hcs, this]
  have h_nn0 : 0 ≤ S.eigval 0 := S.eigval_zero_nonneg
  have h_nnx : 0 ≤ ‖x‖ := norm_nonneg _
  calc |S.eigval k * @inner ℝ _ _ x (S.eigenfn k)|
      = |S.eigval k| * |@inner ℝ _ _ x (S.eigenfn k)| := abs_mul _ _
    _ ≤ S.eigval 0 * ‖x‖ := by
          have habs_nn : 0 ≤ |@inner ℝ _ _ x (S.eigenfn k)| := abs_nonneg _
          have : |S.eigval k| * |@inner ℝ _ _ x (S.eigenfn k)|
              ≤ S.eigval 0 * ‖x‖ := by
            have hkstep :
                |S.eigval k| * |@inner ℝ _ _ x (S.eigenfn k)|
                  ≤ S.eigval 0 * |@inner ℝ _ _ x (S.eigenfn k)| :=
              mul_le_mul_of_nonneg_right h_abs habs_nn
            have hxstep :
                S.eigval 0 * |@inner ℝ _ _ x (S.eigenfn k)|
                  ≤ S.eigval 0 * ‖x‖ :=
              mul_le_mul_of_nonneg_left h_inner h_nn0
            linarith
          exact this

/-- The truncation is bounded in norm by `d · eigval 0 · ‖x‖`
(crude but useful). -/
lemma norm_spectralTrunc_le (S : SpectralFamilyHS T) (d : ℕ) (x : H) :
    ‖spectralTrunc S d x‖ ≤ d * (S.eigval 0 * ‖x‖) := by
  unfold spectralTrunc
  have h_each : ∀ k ∈ Finset.range d,
      ‖(S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k‖
        ≤ S.eigval 0 * ‖x‖ := by
    intro k hk
    have hkd : k < d := Finset.mem_range.mp hk
    have hcoef := spectralTrunc_coeff_bound S d x hkd
    have hnorm := S.norm_eigenfn k
    rw [norm_smul, Real.norm_eq_abs, hnorm, mul_one]
    exact hcoef
  have h_sum :
      ‖∑ k ∈ Finset.range d,
          (S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k‖
        ≤ ∑ k ∈ Finset.range d,
            ‖(S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k‖ :=
    norm_sum_le _ _
  have h_bound :
      ∑ k ∈ Finset.range d,
          ‖(S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k‖
        ≤ ∑ _k ∈ Finset.range d, (S.eigval 0 * ‖x‖) :=
    Finset.sum_le_sum h_each
  have h_const :
      (∑ _k ∈ Finset.range d, (S.eigval 0 * ‖x‖))
        = d * (S.eigval 0 * ‖x‖) := by
    rw [Finset.sum_const, Finset.card_range]
    ring
  calc ‖∑ k ∈ Finset.range d,
            (S.eigval k * (@inner ℝ _ _ x (S.eigenfn k))) • S.eigenfn k‖
      ≤ _ := h_sum
    _ ≤ _ := h_bound
    _ = d * (S.eigval 0 * ‖x‖) := h_const

end Truncation

/-! ## 3. Hypothesis-form scaffolding for the deep statements

The two statements we still cannot prove inside Mathlib v4.28
(finite-rank approximation of compact operators, and the spectral
expansion `T x = Σ_k λ_k ⟨x, e_k⟩ · e_k`) are recorded here as
hypothesis-form statements.  Each takes a *witness* of the relevant
property as input and is therefore axiom-free. -/

section DeepStatements

set_option linter.unusedSectionVars false

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- **Finite-rank approximation (witness form).**  Given a compact
operator `T` on a Hilbert space, *if* one has produced a sequence of
finite-rank operators converging to `T` in operator norm, this
records that fact.  When Mathlib obtains a proof that every compact
operator has such an approximating sequence (a result that holds on
separable Hilbert spaces), this can be upgraded to an existence
statement. -/
def IsLimitOfFiniteRank (T : H →L[ℝ] H) : Prop :=
  ∃ (Tn : ℕ → H →L[ℝ] H),
    (∀ n, ∃ (V : Submodule ℝ H) (_ : FiniteDimensional ℝ V),
      ∀ x, (Tn n) x ∈ V) ∧
    Tendsto (fun n => ‖T - Tn n‖) atTop (nhds 0)

/-- Trivially, the zero operator is a limit of finite-rank operators
(by the constant sequence `0`). -/
lemma isLimitOfFiniteRank_zero : IsLimitOfFiniteRank (0 : H →L[ℝ] H) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro _
    refine ⟨⊥, ?_, ?_⟩
    · infer_instance
    · intro x; simp
  · simp

/-- **Spectral expansion (hypothesis form).**  States that `T x`
equals the limit of its spectral truncations.  We package the
statement together with the family `S`. -/
def HasSpectralExpansion {T : H →L[ℝ] H} (S : SpectralFamilyHS T) : Prop :=
  ∀ x : H, Tendsto (fun d => spectralTrunc S d x) atTop (nhds (T x))

end DeepStatements

/-! ## 4. Bridge from `SpectralFamilyHS` to `FPC.Eigensystem`

Build an `FPC.Eigensystem D` from a Hilbert–Schmidt spectral family on
`Lp ℝ 2 ν`.  In contrast with `SpectralTheorem.InfiniteDimSpectralData`'s
bridge (which had to clip eigenvalues with `max 0`), here `eigval` is
*already* nonneg, so we can pass it through directly. -/

section Bridge

variable {D : Type u} [MeasurableSpace D] {ν : Measure D}

/-- The `k`-th eigenfunction as a measurable representative on `D`. -/
noncomputable def SpectralFamilyHS.phiRepr
    (𝓜 : L2KernelMapData ν)
    (S : SpectralFamilyHS 𝓜.toContinuousLinearMap)
    (k : ℕ) : D → ℝ :=
  (Lp.aestronglyMeasurable (S.eigenfn k)).mk (S.eigenfn k)

/-- `phiRepr` is genuinely measurable. -/
lemma SpectralFamilyHS.phiRepr_meas
    (𝓜 : L2KernelMapData ν)
    (S : SpectralFamilyHS 𝓜.toContinuousLinearMap)
    (k : ℕ) : Measurable (SpectralFamilyHS.phiRepr 𝓜 S k) :=
  (Lp.aestronglyMeasurable (S.eigenfn k)).stronglyMeasurable_mk.measurable

/-- **Hilbert–Schmidt spectral bridge to `FPC.Eigensystem`.**  The
eigenvalues are already nonneg by `S.eigval_nonneg`; no clipping. -/
noncomputable def SpectralFamilyHS.toEigensystem
    (𝓜 : L2KernelMapData ν)
    (S : SpectralFamilyHS 𝓜.toContinuousLinearMap) :
    FPC.Eigensystem D where
  lam := S.eigval
  phi := SpectralFamilyHS.phiRepr 𝓜 S
  lam_nonneg := S.eigval_nonneg
  phi_meas := SpectralFamilyHS.phiRepr_meas 𝓜 S

/-- The bridge preserves square-summability of eigenvalues. -/
lemma SpectralFamilyHS.toEigensystem_lam_summable_sq
    (𝓜 : L2KernelMapData ν)
    (S : SpectralFamilyHS 𝓜.toContinuousLinearMap) :
    Summable (fun k => (SpectralFamilyHS.toEigensystem 𝓜 S).lam k ^ 2) :=
  S.eigval_summable_sq

/-- The bridge preserves monotonicity of eigenvalues. -/
lemma SpectralFamilyHS.toEigensystem_lam_decreasing
    (𝓜 : L2KernelMapData ν)
    (S : SpectralFamilyHS 𝓜.toContinuousLinearMap) (k : ℕ) :
    (SpectralFamilyHS.toEigensystem 𝓜 S).lam (k + 1)
      ≤ (SpectralFamilyHS.toEigensystem 𝓜 S).lam k :=
  S.eigval_decreasing k

end Bridge

end InfiniteDimSpectral
end Statlean.CoxChangePoint

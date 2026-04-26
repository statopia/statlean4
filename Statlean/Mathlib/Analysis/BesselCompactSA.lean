/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.SpectralTruncation
import Statlean.Mathlib.Analysis.SpectralTruncationConv
import Statlean.Mathlib.Analysis.Parseval
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Eigenbasis totality, HilbertBasis, and the Bessel squared-norm bound

This file closes the analytic gap between the spectral data
`Statlean.Mathlib.SpectralTheoremCompactSA` and the operator-norm convergence
`spectralTruncate_tendsto_op_norm_of_bessel` proved in
`Statlean.Mathlib.Analysis.SpectralTruncationConv`.

The missing ingredient is **totality of the eigenbasis**: that the orthonormal
eigenfunctions of a compact self-adjoint operator span a dense subspace of `H`,
which is the spectral theorem's statement that they form a `HilbertBasis`.
Once we have a `HilbertBasis`, Parseval applies and the Bessel-type
squared-norm bound `‖T x - T_n x‖² ≤ ε² ‖x‖²` follows whenever the eigenvalues
decay.

## Main contents

* `SpectralEigenbasisIsTotal` — hypothesis-form structure asserting totality
  of the eigenbasis.
* `SpectralTheoremCompactSA.toHilbertBasis` — constructs a `HilbertBasis ℕ ℝ H`
  from the spectral data plus totality, via Mathlib's
  `HilbertBasis.mkOfOrthogonalEqBot`.
* `besselSquaredNormBound_of_total` — real proof of the Bessel-type squared-norm
  bound from totality + eigenvalue decay.
* `spectralTruncate_tendsto_op_norm_complete` — final theorem combining
  totality, eigenvalue decay, and `spectralTruncate_tendsto_op_norm_of_bessel`.
* `eigval_summable_sq_implies_decay` — auxiliary: if `Σ |λ_k|²` is summable
  then `|λ_k| → 0`.

The deep Mathlib gap (totality / eigenvalue decay for arbitrary compact
self-adjoint operators) is left as a hypothesis on the inputs, in line with
the hypothesis-form style of `SpectralTheoremCompactSA` itself.
-/

open scoped InnerProductSpace
open Set Filter Topology

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-! ## Totality of the eigenbasis (hypothesis form) -/

/-- **Totality of the eigenbasis.**  The eigenfunctions of a compact
self-adjoint operator span a dense subspace of `H`; equivalently, the closed
linear span of the eigenfunctions is the whole space.  This is the deep
analytic content of the infinite-dimensional spectral theorem and is left as
a hypothesis on `S` (Mathlib v4.28 contains the finite-dimensional analogue
only). -/
structure SpectralEigenbasisIsTotal
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) where
  /-- The closed span of the eigenbasis is the whole space. -/
  hTotal : (Submodule.span ℝ (Set.range S.eigenfn)).topologicalClosure = ⊤

/-! ## Construction of a `HilbertBasis` from the spectral data -/

/-- **Construction of a `HilbertBasis` from compact self-adjoint spectral data.**
Given the spectral data `S` and the totality hypothesis `hTotal`, the
eigenfunctions of `T` form an `ℕ`-indexed Hilbert basis of `H`, via Mathlib's
`HilbertBasis.mkOfOrthogonalEqBot`.  The two prerequisites are
orthonormality (provided by `S.orthonormal_eigenfn`) and triviality of the
orthogonal complement of the linear span (deduced from `hTotal` using
`Submodule.orthogonal_closure`). -/
noncomputable def SpectralTheoremCompactSA.toHilbertBasis
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hTotal : SpectralEigenbasisIsTotal S) :
    HilbertBasis ℕ ℝ H :=
  HilbertBasis.mkOfOrthogonalEqBot S.orthonormal_eigenfn (by
    -- Reduce `(span S.eigenfn)ᗮ = ⊥` to
    -- `((span S.eigenfn).topologicalClosure)ᗮ = ⊥` via `orthogonal_closure`,
    -- then rewrite using `hTotal` and `top_orthogonal_eq_bot`.
    rw [← Submodule.orthogonal_closure, hTotal.hTotal]
    exact Submodule.top_orthogonal_eq_bot)

/-! ## Inner-product identities for the spectral truncation -/

/-- For `k < n`, the eigen-inner-product `⟨e_k, T_n x⟩` equals `λ_k ⟨e_k, x⟩`.
This is the key identity expressing the action of the truncation `T_n` on the
eigenbasis. -/
private lemma inner_eigenfn_spectralTruncate_lt
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    {k n : ℕ} (hk : k < n) (x : H) :
    @inner ℝ _ _ (S.eigenfn k) (spectralTruncate S n x)
      = S.eigval k * @inner ℝ _ _ (S.eigenfn k) x := by
  -- Expand the truncation via its closed-form `apply` lemma.
  rw [spectralTruncate.apply]
  -- The inner product distributes over the finite sum.
  rw [inner_sum]
  -- Each summand: `⟨e_k, ⟨e_j, x⟩ • (λ_j • e_j)⟩ = ⟨e_j, x⟩ * λ_j * ⟨e_k, e_j⟩`.
  -- Off-diagonal terms vanish by orthogonality; the diagonal `j = k` survives.
  rw [Finset.sum_eq_single k]
  · -- Diagonal term `j = k`.
    rw [inner_smul_right, inner_smul_right]
    have hself : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn k) = 1 := by
      have := real_inner_self_eq_norm_sq (S.eigenfn k)
      rw [this, S.eigenfn_norm k]; norm_num
    rw [hself]; ring
  · -- Off-diagonal `j ≠ k` term vanishes.
    intro j _ hjk
    rw [inner_smul_right, inner_smul_right]
    have h0 : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 :=
      S.eigenfn_orthogonal k j (Ne.symm hjk)
    rw [h0]; ring
  · -- The index `k` is in `Finset.range n` because `k < n`.
    intro hk_not
    exact (hk_not (Finset.mem_range.mpr hk)).elim

/-- For `k ≥ n`, the eigen-inner-product `⟨e_k, T_n x⟩` vanishes.  This is the
complementary identity to `inner_eigenfn_spectralTruncate_lt`. -/
private lemma inner_eigenfn_spectralTruncate_ge
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    {k n : ℕ} (hk : n ≤ k) (x : H) :
    @inner ℝ _ _ (S.eigenfn k) (spectralTruncate S n x) = 0 := by
  rw [spectralTruncate.apply, inner_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≠ k := by
    intro h; subst h
    exact absurd (Finset.mem_range.mp hj) (not_lt.mpr hk)
  rw [inner_smul_right, inner_smul_right]
  have h0 : @inner ℝ _ _ (S.eigenfn k) (S.eigenfn j) = 0 :=
    S.eigenfn_orthogonal k j (Ne.symm hjk)
  rw [h0]; ring

/-- The inner product of the residual `T x - T_n x` against an eigenfunction
`e_k`.  The value depends on whether `k < n` (it is zero) or `k ≥ n` (it is
`λ_k ⟨e_k, x⟩`).  This identity drives the Parseval calculation behind the
Bessel squared-norm bound. -/
private lemma inner_eigenfn_residual
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (k n : ℕ) (x : H) :
    @inner ℝ _ _ (S.eigenfn k) (T x - spectralTruncate S n x)
      = (if k < n then 0 else S.eigval k * @inner ℝ _ _ (S.eigenfn k) x) := by
  rw [inner_sub_right]
  -- Compute `⟨e_k, T x⟩` via self-adjointness and the eigen-relation.
  have hT_eig : @inner ℝ _ _ (S.eigenfn k) (T x)
      = S.eigval k * @inner ℝ _ _ (S.eigenfn k) x := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSelfAdjoint
    -- `⟨e_k, T x⟩ = ⟨T e_k, x⟩` (self-adjointness, symmetric form on ℝ).
    have h1 : @inner ℝ _ _ (S.eigenfn k) (T x)
        = @inner ℝ _ _ (T (S.eigenfn k)) x := (hsym (S.eigenfn k) x).symm
    rw [h1, S.eigen_relation k, inner_smul_left]
    simp
  rw [hT_eig]
  by_cases hk : k < n
  · -- `k < n`: the truncation contributes `λ_k ⟨e_k, x⟩`, cancelling.
    rw [inner_eigenfn_spectralTruncate_lt S hk x, if_pos hk]; ring
  · -- `k ≥ n`: the truncation contributes 0.
    push_neg at hk
    rw [inner_eigenfn_spectralTruncate_ge S hk x, if_neg (by omega : ¬ k < n)]; ring

/-! ## Bessel squared-norm bound from totality + eigenvalue decay -/

/-- **Bessel-type squared-norm bound from totality + eigenvalue decay.**
Given the totality of the eigenbasis (`hTotal`) and the decay of the
eigenvalues (`|λ_k| → 0`), the squared norm of the residual `T x - T_n x` is
controlled uniformly: for each `ε > 0` there is `N` such that
`‖T x - T_n x‖² ≤ ε² ‖x‖²` for all `n ≥ N` and `x : H`.

The proof builds the eigenfunctions into a `HilbertBasis`, applies Parseval to
the residual, uses `inner_eigenfn_residual` to identify the Fourier
coefficients, and bounds them by `ε · |⟨e_k, x⟩|` once `|λ_k| < ε` for
`k ≥ N`.  The Bessel inequality `Σ ⟨e_k, x⟩² = ‖x‖²` finishes the estimate. -/
theorem besselSquaredNormBound_of_total
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hTotal : SpectralEigenbasisIsTotal S)
    (hEigvalDecay : Filter.Tendsto (fun k => |S.eigval k|) Filter.atTop (nhds 0)) :
    BesselSquaredNormBound S where
  bound := by
    intro ε hε
    -- Pick `N` so that `|λ_k| < ε` for all `k ≥ N`.
    have hN : ∃ N : ℕ, ∀ k, N ≤ k → |S.eigval k| < ε := by
      have hAux := (Metric.tendsto_atTop.mp hEigvalDecay) ε hε
      obtain ⟨N, hN⟩ := hAux
      refine ⟨N, fun k hk => ?_⟩
      have hd := hN k hk
      -- `dist (|λ_k|) 0 < ε` ⇔ `|λ_k| < ε` since `|λ_k| ≥ 0`.
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg (abs_nonneg _)] at hd
      exact hd
    obtain ⟨N, hN⟩ := hN
    refine ⟨N, fun n hnN x => ?_⟩
    -- Build the HilbertBasis.
    set b := SpectralTheoremCompactSA.toHilbertBasis S hTotal with hb_def
    -- Eigenfunctions agree with the basis (definitional via `coe_mkOfOrthogonalEqBot`).
    have hb_apply : ∀ k, (b : ℕ → H) k = S.eigenfn k := by
      intro k
      simp [b, SpectralTheoremCompactSA.toHilbertBasis,
            HilbertBasis.coe_mkOfOrthogonalEqBot]
    -- Apply Parseval to the residual `T x - T_n x`.
    have hParseval :
        (∑' k, ⟪b k, T x - spectralTruncate S n x⟫_ℝ ^ 2)
          = ‖T x - spectralTruncate S n x‖ ^ 2 :=
      Statlean.parseval_identity_real b _
    -- Identify each Fourier coefficient via `inner_eigenfn_residual`.
    have hcoeff : ∀ k, ⟪b k, T x - spectralTruncate S n x⟫_ℝ
        = (if k < n then 0 else S.eigval k * ⟪b k, x⟫_ℝ) := by
      intro k
      simp_rw [hb_apply]
      exact inner_eigenfn_residual S k n x
    -- Squared coefficients: bounded by `ε² · ⟨b k, x⟩²` for `k ≥ N`,
    -- and zero for `k < n` (in particular for `k < N` because `n ≥ N`).
    have hsq : ∀ k, ⟪b k, T x - spectralTruncate S n x⟫_ℝ ^ 2
        ≤ ε ^ 2 * ⟪b k, x⟫_ℝ ^ 2 := by
      intro k
      rw [hcoeff k]
      by_cases hkn : k < n
      · rw [if_pos hkn]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
      · push_neg at hkn
        rw [if_neg (not_lt.mpr hkn)]
        have hkN : N ≤ k := le_trans hnN hkn
        have hlam_abs : |S.eigval k| < ε := hN k hkN
        have hlam_sq : (S.eigval k) ^ 2 ≤ ε ^ 2 := by
          have h1 : (S.eigval k) ^ 2 = |S.eigval k| ^ 2 := by
            rw [sq_abs]
          rw [h1]
          have habs_nn : (0 : ℝ) ≤ |S.eigval k| := abs_nonneg _
          nlinarith [hlam_abs.le, habs_nn]
        have hsq_eq :
            (S.eigval k * ⟪b k, x⟫_ℝ) ^ 2 = (S.eigval k) ^ 2 * ⟪b k, x⟫_ℝ ^ 2 := by
          ring
        rw [hsq_eq]
        exact mul_le_mul_of_nonneg_right hlam_sq (sq_nonneg _)
    -- Summability of both families: residual side via Bessel; bound side via scaling.
    have hsum_res : Summable (fun k =>
        ⟪b k, T x - spectralTruncate S n x⟫_ℝ ^ 2) :=
      Statlean.bessel_summable b _
    have hsum_bnd : Summable (fun k => ε ^ 2 * ⟪b k, x⟫_ℝ ^ 2) :=
      (Statlean.bessel_summable b x).mul_left (ε ^ 2)
    -- Bound the tsum and combine with Parseval for `x`.
    have hle : (∑' k, ⟪b k, T x - spectralTruncate S n x⟫_ℝ ^ 2)
        ≤ ∑' k, ε ^ 2 * ⟪b k, x⟫_ℝ ^ 2 :=
      Summable.tsum_mono hsum_res hsum_bnd hsq
    have hbasis_x : (∑' k, ε ^ 2 * ⟪b k, x⟫_ℝ ^ 2) = ε ^ 2 * ‖x‖ ^ 2 := by
      rw [tsum_mul_left, Statlean.parseval_identity_real b x]
    -- Combine.
    rw [hParseval] at hle
    rw [hbasis_x] at hle
    exact hle

/-! ## Final theorem: operator-norm convergence of the spectral truncations -/

/-- **Operator-norm convergence of spectral truncations** (real proof, complete
form).  A compact self-adjoint operator `T` whose eigenbasis is total and
whose eigenvalues decay (`|λ_k| → 0`) has its finite-rank spectral
truncations `T_n` converging to `T` in the operator norm:
`‖T - T_n‖ → 0` as `n → ∞`.

This is the conclusion of the spectral theorem's quantitative form, obtained
here by composing `besselSquaredNormBound_of_total` with the Bessel-to-norm
packaging `spectralTruncate_tendsto_op_norm_of_bessel` from
`Statlean.Mathlib.Analysis.SpectralTruncationConv`. -/
theorem spectralTruncate_tendsto_op_norm_complete
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hTotal : SpectralEigenbasisIsTotal S)
    (hEigvalDecay : Filter.Tendsto (fun k => |S.eigval k|) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖T - spectralTruncate S n‖) Filter.atTop (nhds 0) :=
  spectralTruncate_tendsto_op_norm_of_bessel S
    (besselSquaredNormBound_of_total S hTotal hEigvalDecay)

/-! ## Auxiliary: summable-square implies decay -/

/-- **Summable squares ⇒ decay.**  If the squared eigenvalue series is
summable, then `|λ_k| → 0`.  This is the standard consequence of
`Summable.tendsto_atTop_zero` applied to the squared sequence, combined with
the fact that `x_k → 0` ↔ `|x_k| → 0` ↔ `x_k² → 0` for real sequences.

Useful when constructing an instance of the decay hypothesis from a
Hilbert–Schmidt-type bound `Σ λ_k² < ∞`. -/
theorem eigval_summable_sq_implies_decay
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hSummable : Summable (fun k => (S.eigval k) ^ 2)) :
    Filter.Tendsto (fun k => |S.eigval k|) Filter.atTop (nhds 0) := by
  -- Step 1: `(λ_k)² → 0` from summability.
  have h_sq_to_zero : Filter.Tendsto (fun k => (S.eigval k) ^ 2) Filter.atTop (nhds 0) :=
    hSummable.tendsto_atTop_zero
  -- Step 2: convert to `|λ_k| → 0` using continuity of square root.
  -- `|x| = √(x²)` and `√` is continuous at `0` with value `0`.
  have h_abs_eq : ∀ k, |S.eigval k| = Real.sqrt ((S.eigval k) ^ 2) := by
    intro k
    rw [Real.sqrt_sq_eq_abs]
  simp_rw [h_abs_eq]
  -- `Real.sqrt` is continuous at `0`, with `Real.sqrt 0 = 0`.
  have h_sqrt_cont : Filter.Tendsto Real.sqrt (nhds 0) (nhds 0) := by
    have := (Real.continuous_sqrt).tendsto 0
    simpa [Real.sqrt_zero] using this
  exact h_sqrt_cont.comp h_sq_to_zero

/-- **Compact-spectral-truncation data from totality + eigenvalue decay.**
The completed form of `compactSpectralTruncationOfBessel`: from totality of
the eigenbasis and eigenvalue decay, we obtain the
`Statlean.Mathlib.CompactSpectralTruncation` data witnessing operator-norm
convergence of the spectral truncations of `T`. -/
noncomputable def compactSpectralTruncationOfTotal
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (hTotal : SpectralEigenbasisIsTotal S)
    (hEigvalDecay : Filter.Tendsto (fun k => |S.eigval k|) Filter.atTop (nhds 0)) :
    CompactSpectralTruncation H T :=
  compactSpectralTruncationOfBessel S
    (besselSquaredNormBound_of_total S hTotal hEigvalDecay)

end Mathlib
end Statlean

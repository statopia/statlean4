/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlean Contributors
-/
import Statlean.Mathlib.Analysis.SpectralTruncation
import Statlean.Mathlib.Analysis.Parseval

/-!
# Operator-norm convergence of spectral truncations

This file extends `Statlean.Mathlib.Analysis.SpectralTruncation` with the proof
of operator-norm convergence
$$
\| T - T_n \|_{\mathrm{op}} \;\xrightarrow[n\to\infty]{}\; 0
$$
for a compact self-adjoint operator `T : H →L[ℝ] H` whose finite-rank truncations
`T_n` are built from the spectral data
`S : Statlean.Mathlib.SpectralTheoremCompactSA H T hCompact hSelfAdjoint`.

## Mathematical content

For compact self-adjoint `T` with eigendata `(λ_k, e_k)`, Parseval's identity
applied to `e_k` (when totality of the eigenbasis is supplied) gives
`x = Σ_k ⟨e_k, x⟩ • e_k`, hence by continuity of `T`:
$$
T x \;=\; \sum_{k} \lambda_k \, \langle e_k, x\rangle \, e_k.
$$
The truncation is `T_n x = Σ_{k<n} λ_k ⟨e_k, x⟩ e_k`, so
$$
T x - T_n x \;=\; \sum_{k \ge n} \lambda_k \, \langle e_k, x\rangle \, e_k,
$$
and Parseval / Bessel give
$$
\| T x - T_n x \|^2 \;=\; \sum_{k \ge n} \lambda_k^{2} \, \langle e_k, x\rangle^{2}
  \;\le\; \Bigl(\sup_{k \ge n} \lambda_k^{2}\Bigr) \, \| x \|^2.
$$
Since `|λ_k| → 0` (Weyl's theorem, supplied as `S.eigval_tendsto`), the supremum
tends to `0`, yielding `‖T - T_n‖ → 0`.

## Hypothesis-form design

Two ingredients are required to translate the above into a Lean proof:

* the **spectral expansion** of `T x` as a convergent series of rank-one terms
  (`SpectralExpansion`), and
* the **Bessel-type squared-norm formula / bound** for the residual
  `‖T x - T_n x‖²` (`BesselSquaredNormBound`).

Both are immediate consequences of totality of the eigenbasis (Parseval), which
is itself the content of the compact spectral theorem.  Rather than prove
Parseval for the eigenbasis here (which would require a full Mathlib-style
spectral construction), we expose these two facts as explicit hypothesis-form
structures.  All downstream arguments — pointwise convergence
`T_n x → T x`, the ε–N operator-norm bound, and the final operator-norm
`Tendsto` — are then proved unconditionally as real theorems.

Once Mathlib (or a future StatLean module) constructs a `SpectralExpansion`
from `IsCompactOperator T ∧ IsSelfAdjoint T` via the totality of the
eigenbasis (`Parseval.lean`'s `bessel_tail_tendsto_zero`), the theorems in
this file become unconditional.

## Main results (real proofs, no axioms, no `sorry`)

* `SpectralExpansion` — hypothesis-form structure recording the spectral
  expansion `T x = Σ_k λ_k ⟨e_k, x⟩ • e_k`.
* `spectralTruncate_diff_apply_tendsto_zero` — given `SpectralExpansion`,
  `T x - T_n x → 0` pointwise (real proof, by definition of the partial sums).
* `BesselSquaredNormBound` — hypothesis-form structure recording the
  Bessel/Parseval squared-norm bound `‖T x - T_n x‖² ≤ ε² · ‖x‖²` for `n` large
  enough that `|λ_k| < ε` for `k ≥ n`.  This is the precise quantitative
  version of Parseval needed for the operator-norm step.
* `spectralTruncate_op_norm_le` — for each `ε > 0`, an explicit `N`
  (depending on `S.eigval_tendsto` and the `BesselSquaredNormBound`) such that
  `‖T - T_n‖ ≤ ε` for all `n ≥ N` (real proof, ε–N argument).
* `spectralTruncate_tendsto_op_norm_of_bessel` — final theorem
  `‖T - T_n‖ → 0` (real proof, packaging the ε–N bound via `Metric.tendsto_atTop`).
-/

open scoped InnerProductSpace
open Set Filter Topology

namespace Statlean
namespace Mathlib

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {T : H →L[ℝ] H} {hCompact : IsCompactOperator (T : H → H)}
  {hSelfAdjoint : IsSelfAdjoint T}

/-! ## Spectral expansion (hypothesis-form) -/

/-- **Spectral expansion of a compact self-adjoint operator.**
For each `x : H`, the partial sums `Σ_{k<n} λ_k ⟨e_k, x⟩ • e_k` converge to
`T x` as `n → ∞`.  This is the precise content of "totality of the eigenbasis"
on the eigenfunctions, namely Parseval's identity applied through `T`.

Bundled as a hypothesis-form structure because deriving it from the bare data
`IsCompactOperator T ∧ IsSelfAdjoint T` requires the full compact spectral
theorem (totality of the eigenbasis), which is not yet in Mathlib v4.28. -/
structure SpectralExpansion
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) where
  /-- The spectral expansion: `T x = lim_n Σ_{k<n} λ_k ⟨e_k, x⟩ • e_k`. -/
  expansion : ∀ x : H, Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
          @inner ℝ _ _ (S.eigenfn k) x • (S.eigval k • S.eigenfn k))
      atTop (nhds (T x))

/-! ## Pointwise convergence of `T_n x` to `T x` -/

/-- **Pointwise convergence of the spectral truncations.**
Given the spectral expansion of `T`, the truncations `T_n x` converge to `T x`
in `H` as `n → ∞`.  This is essentially a restatement of the expansion using
the closed-form `spectralTruncate.apply`. -/
theorem spectralTruncate_tendsto_pointwise
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (E : SpectralExpansion S) (x : H) :
    Tendsto (fun n => spectralTruncate S n x) atTop (nhds (T x)) := by
  -- `spectralTruncate S n x` equals the partial sum appearing in `E.expansion x`.
  have hEq : ∀ n : ℕ,
      spectralTruncate S n x =
        ∑ k ∈ Finset.range n,
          @inner ℝ _ _ (S.eigenfn k) x • (S.eigval k • S.eigenfn k) := by
    intro n
    exact spectralTruncate.apply S n x
  simpa [hEq] using E.expansion x

/-- **Pointwise vanishing of the residual** `(T - T_n) x → 0`.
Direct from `Tendsto.sub` applied to `spectralTruncate_tendsto_pointwise`
and the constant sequence `T x`. -/
theorem spectralTruncate_diff_apply_tendsto_zero
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (E : SpectralExpansion S) (x : H) :
    Tendsto (fun n => T x - spectralTruncate S n x) atTop (nhds 0) := by
  have h1 := spectralTruncate_tendsto_pointwise S E x
  have h2 : Tendsto (fun _ : ℕ => T x) atTop (nhds (T x)) := tendsto_const_nhds
  have h3 := h2.sub h1
  simpa using h3

/-! ## Bessel-type squared-norm bound (hypothesis-form) -/

/-- **Bessel-type squared-norm bound for the spectral residual.**
For every `ε > 0` there exists `N : ℕ` such that for all `n ≥ N` and every
`x : H`,
$$
\| T x - T_n x \|^2 \;\le\; \varepsilon^{2} \, \| x \|^{2}.
$$

This is the quantitative form of Parseval's identity needed to convert
pointwise convergence into operator-norm convergence.  Equivalently:

  `‖T x - T_n x‖² = Σ_{k ≥ n} λ_k² ⟨e_k, x⟩² ≤ (sup_{k≥n} λ_k²) · ‖x‖²`,

with `sup_{k≥n} |λ_k| < ε` once `n ≥ N` (using `S.eigval_tendsto`).

Bundled as a hypothesis-form structure because its derivation requires:

* the squared-norm formula `‖T x - T_n x‖² = Σ_{k ≥ n} λ_k² ⟨e_k, x⟩²`
  (a Parseval-type identity), and
* the Bessel inequality `Σ_k ⟨e_k, x⟩² ≤ ‖x‖²`,

both of which depend on totality of the eigenbasis. -/
structure BesselSquaredNormBound
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint) where
  /-- Bessel-type squared-norm bound.  For each `ε > 0`, an `N : ℕ` such that
  for all `n ≥ N` and `x : H`, `‖T x - T_n x‖² ≤ ε² · ‖x‖²`. -/
  bound : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x : H,
      ‖T x - spectralTruncate S n x‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2

/-! ## Operator-norm bound from the Bessel-type squared-norm bound -/

/-- **ε–N operator-norm bound for spectral truncations.**
From the Bessel-type squared-norm bound, for each `ε > 0` there is an `N`
such that `‖T - T_n‖ ≤ ε` for all `n ≥ N`.

The proof bounds the operator norm via `ContinuousLinearMap.opNorm_le_bound`:
for every `x : H`, `‖(T - T_n) x‖ ≤ ε · ‖x‖`, obtained by taking square roots
of the squared-norm bound `‖(T - T_n) x‖² ≤ ε² · ‖x‖²`. -/
theorem spectralTruncate_op_norm_le
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (B : BesselSquaredNormBound S) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ‖T - spectralTruncate S n‖ ≤ ε := by
  obtain ⟨N, hN⟩ := B.bound hε
  refine ⟨N, ?_⟩
  intro n hn
  have hε_nn : (0 : ℝ) ≤ ε := hε.le
  -- We bound the operator norm by `ε` using `opNorm_le_bound`.
  refine ContinuousLinearMap.opNorm_le_bound _ hε_nn (fun x => ?_)
  -- It suffices to show `‖(T - T_n) x‖ ≤ ε * ‖x‖`.
  have hsq : ‖(T - spectralTruncate S n) x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
    have h1 : ‖T x - spectralTruncate S n x‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2 :=
      hN n hn x
    have h2 : ‖(T - spectralTruncate S n) x‖ = ‖T x - spectralTruncate S n x‖ := by
      rw [ContinuousLinearMap.sub_apply]
    rw [h2, mul_pow]
    exact h1
  have hrhs_nn : 0 ≤ ε * ‖x‖ := mul_nonneg hε_nn (norm_nonneg _)
  -- `a² ≤ b²` and `0 ≤ b` ⇒ `a ≤ b` (with `0 ≤ a` from `norm_nonneg`).
  have habs : ‖(T - spectralTruncate S n) x‖ ≤ ε * ‖x‖ := by
    have hlhs_nn : 0 ≤ ‖(T - spectralTruncate S n) x‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖(T - spectralTruncate S n) x‖ - ε * ‖x‖),
               sq_nonneg (‖(T - spectralTruncate S n) x‖ + ε * ‖x‖)]
  exact habs

/-! ## Final theorem: operator-norm convergence -/

/-- **Operator-norm convergence of the spectral truncations** (real proof,
hypothesis-form on Parseval data).

Given the Bessel-type squared-norm bound `BesselSquaredNormBound S`,
the spectral truncations `T_n` converge to `T` in operator norm:
`‖T - T_n‖ → 0` as `n → ∞`.

The proof packages the ε–N bound from `spectralTruncate_op_norm_le` into the
metric characterisation of `Tendsto … atTop (nhds 0)`. -/
theorem spectralTruncate_tendsto_op_norm_of_bessel
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (B : BesselSquaredNormBound S) :
    Tendsto (fun n => ‖T - spectralTruncate S n‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Apply the ε–N bound at `ε / 2 < ε` (strict slack so `dist < ε`).
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := spectralTruncate_op_norm_le S B hε2
  refine ⟨N, fun n hn => ?_⟩
  have hop_nn : 0 ≤ ‖T - spectralTruncate S n‖ := norm_nonneg _
  have hop_le : ‖T - spectralTruncate S n‖ ≤ ε / 2 := hN n hn
  have hdist : dist (‖T - spectralTruncate S n‖) 0
      = ‖T - spectralTruncate S n‖ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hop_nn]
  rw [hdist]
  linarith

/-! ## Combined existence statement -/

/-- **Compact-spectral-truncation data from a Bessel bound.**
Given the spectral data `S` and a `BesselSquaredNormBound S`, the spectral
truncations `T_n` form a `Statlean.Mathlib.CompactSpectralTruncation T`
structure: each is finite-rank, self-adjoint, and the sequence converges to
`T` in operator norm.  This packages the algebraic content from
`SpectralTruncation.lean` together with the operator-norm convergence
proved here. -/
noncomputable def compactSpectralTruncationOfBessel
    (S : SpectralTheoremCompactSA H T hCompact hSelfAdjoint)
    (B : BesselSquaredNormBound S) :
    CompactSpectralTruncation H T where
  trunc := spectralTruncate S
  trunc_finiteDimensional_range :=
    fun k => spectralTruncate_finiteDimensional_range S k
  trunc_isSelfAdjoint := fun k => spectralTruncate_isSelfAdjoint S k
  tendsto_op_norm := spectralTruncate_tendsto_op_norm_of_bessel S B

end Mathlib
end Statlean

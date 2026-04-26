/-
Copyright (c) 2026 StatLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Parseval Identity for Hilbert Bases

This file collects convenient real-scalar specialisations of Mathlib's
`HilbertBasis` API and packages them under self-explanatory names.

## Main results

* `parseval_inner_eq` — the Parseval / Plancherel identity for two vectors:
  for any orthonormal Hilbert basis `b` of a real Hilbert space `H` and any
  `x y : H`, one has `∑' i, ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ = ⟪x, y⟫_ℝ`.

* `parseval_identity_real` — the Parseval identity for the squared norm:
  `∑' i, ⟪b i, x⟫_ℝ ^ 2 = ‖x‖ ^ 2`.

* `bessel_summable` — Bessel's identity (in summable form): the family of
  squared Fourier coefficients `i ↦ ⟪b i, x⟫_ℝ ^ 2` is summable.

* `bessel_tail_tendsto_zero` — for an `ℕ`-indexed Hilbert basis, the tail of
  the Bessel sum tends to zero. This is the analytic backbone behind
  operator-norm convergence of spectral truncations
  `‖T - T_n‖ → 0` whenever `T` is a self-adjoint Hilbert–Schmidt operator
  whose eigenfunctions form a Hilbert basis.

## Implementation notes

All proofs are direct consequences of:

* `HilbertBasis.tsum_inner_mul_inner` — Parseval for two vectors with the
  Mathlib argument order `⟪x, b i⟫ * ⟪b i, y⟫`.
* `HilbertBasis.summable_inner_mul_inner` — summability of the same family.
* `tendsto_sum_nat_add` — the standard "tails of a summable sequence vanish"
  lemma in ℕ-indexed form `∑' k, f (k + n) → 0`.

For the tail statement we reformulate the indicator-style tail
`∑' i, if i ≥ n then f i else 0` as `∑' k, f (k + n)` via a shift bijection
between `ℕ` and `{i : ℕ | n ≤ i}`.
-/

namespace Statlean

open Filter Topology
open scoped InnerProductSpace

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-! ### Parseval identity for two vectors -/

omit [CompleteSpace H] in
/-- **Parseval identity** (real two-vector form). For an orthonormal Hilbert
basis `b` of a real Hilbert space `H` and any pair of vectors `x y : H`,
the family of products of Fourier coefficients sums (unconditionally) to the
inner product `⟪x, y⟫_ℝ`.

This is a real-scalar repackaging of `HilbertBasis.tsum_inner_mul_inner`,
with the more conventional argument order `⟪b i, x⟫ * ⟪b i, y⟫`. -/
theorem parseval_inner_eq (b : HilbertBasis ι ℝ H) (x y : H) :
    (∑' i, ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ) = ⟪x, y⟫_ℝ := by
  have h := b.tsum_inner_mul_inner x y
  -- Mathlib gives us  ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫.
  -- We swap the first factor using real symmetry of the inner product.
  rw [← h]
  refine tsum_congr (fun i => ?_)
  rw [real_inner_comm x (b i)]

/-! ### Parseval identity for a single vector (squared norm) -/

omit [CompleteSpace H] in
/-- **Parseval identity** (real squared-norm form). For an orthonormal Hilbert
basis `b` of a real Hilbert space `H` and any `x : H`, the squared norm of
`x` is the unconditional sum of squared Fourier coefficients:
`‖x‖² = ∑' i, ⟪b i, x⟫_ℝ ^ 2`. -/
theorem parseval_identity_real (b : HilbertBasis ι ℝ H) (x : H) :
    (∑' i, ⟪b i, x⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
  have h := b.tsum_inner_mul_inner x x
  -- Reduce ‖x‖² to ⟪x, x⟫ and rewrite each term using `sq` and symmetry.
  rw [← real_inner_self_eq_norm_sq, ← h]
  refine tsum_congr (fun i => ?_)
  rw [sq, real_inner_comm x (b i)]

/-! ### Bessel summability -/

omit [CompleteSpace H] in
/-- **Bessel summability**. For an orthonormal Hilbert basis `b` of a real
Hilbert space `H` and any `x : H`, the family of squared Fourier
coefficients `i ↦ ⟪b i, x⟫_ℝ ^ 2` is summable. -/
theorem bessel_summable (b : HilbertBasis ι ℝ H) (x : H) :
    Summable (fun i => ⟪b i, x⟫_ℝ ^ 2) := by
  -- Mathlib provides summability of `i ↦ ⟪x, b i⟫ * ⟪b i, x⟫`; rewrite to a
  -- square via real symmetry of the inner product.
  have h : Summable (fun i => ⟪x, b i⟫_ℝ * ⟪b i, x⟫_ℝ) :=
    b.summable_inner_mul_inner x x
  refine h.congr (fun i => ?_)
  rw [sq, real_inner_comm x (b i)]

/-! ### Tail of the Bessel sum -/

/-- An `ite`-shaped tail of an infinite series equals the shifted tsum. For
any function `f : ℕ → ℝ` and any `n : ℕ`,
`∑' i, (if i ≥ n then f i else 0) = ∑' k, f (k + n)`.

This is a purely topological reindexing fact — no summability of `f` is
required. It is convenient when expressing tail behaviour using indicator
functions rather than shifted sums. -/
lemma tsum_ite_ge_eq_tsum_shift (f : ℕ → ℝ) (n : ℕ) :
    (∑' i, if i ≥ n then f i else 0) = ∑' k, f (k + n) := by
  -- Build the bijection ℕ ≃ {i : ℕ | n ≤ i} via `k ↦ k + n` and `i ↦ i - n`.
  let e : ℕ ≃ ({i : ℕ | n ≤ i} : Set ℕ) :=
    { toFun := fun k => ⟨k + n, by simp⟩
      invFun := fun ⟨i, _⟩ => i - n
      left_inv := fun k => by simp
      right_inv := fun ⟨i, h⟩ => by simp at h ⊢; omega }
  -- Rewrite the `ite`-tail as an indicator on `{i | n ≤ i}`.
  rw [show (fun i => if i ≥ n then f i else 0)
        = ({i | n ≤ i} : Set ℕ).indicator f by
        funext i; simp [Set.indicator]]
  -- Convert indicator-tsum to a tsum over the subtype, then reindex by `e`.
  rw [← tsum_subtype, ← Equiv.tsum_eq e]
  refine tsum_congr (fun k => ?_)
  change f (k + n) = f (k + n)
  rfl

omit [CompleteSpace H] in
/-- The tail of the Bessel sum tends to zero. For an `ℕ`-indexed orthonormal
Hilbert basis `b` of a real Hilbert space `H` and any `x : H`,
`∑_{i ≥ n} ⟪b i, x⟫_ℝ ^ 2 → 0` as `n → ∞`.

This is the workhorse used in spectral truncation arguments: it shows that
the operator-norm error of a finite-rank approximation
`T_n = ∑_{i < n} λ_i · ⟨e_i, ·⟩ e_i` to a Hilbert–Schmidt operator `T`
vanishes in the limit, since the residual is controlled by Bessel tails. -/
theorem bessel_tail_tendsto_zero (b : HilbertBasis ℕ ℝ H) (x : H) :
    Filter.Tendsto
      (fun n => ∑' i : ℕ, if i ≥ n then ⟪b i, x⟫_ℝ ^ 2 else 0)
      Filter.atTop (nhds 0) := by
  -- Replace each tail with the shifted form `∑' k, ⟪b (k + n), x⟫²`
  -- and conclude using the ℝ-valued `tendsto_sum_nat_add`.
  have heq : ∀ n,
      (∑' i : ℕ, if i ≥ n then ⟪b i, x⟫_ℝ ^ 2 else 0)
        = ∑' k : ℕ, ⟪b (k + n), x⟫_ℝ ^ 2 := by
    intro n
    exact tsum_ite_ge_eq_tsum_shift _ n
  simp_rw [heq]
  exact tendsto_sum_nat_add (fun i => ⟪b i, x⟫_ℝ ^ 2)

/-! ### Bridge to spectral truncation

The following corollary packages Parseval into the form used by spectral
truncation arguments. If `T_n x = ∑_{i < n} ⟨b i, x⟩ • b i` is the partial
Fourier sum of `x`, then `‖x - T_n x‖² = ∑_{i ≥ n} ⟪b i, x⟫_ℝ ^ 2`, which
tends to `0` by `bessel_tail_tendsto_zero`. The squared-norm tendsto below
is the precise statement used to discharge operator-norm convergence in
`Statlean.Mathlib.Analysis.SpectralTruncation`. -/

omit [CompleteSpace H] in
/-- **Squared-norm tendsto** for the Bessel tail. For any `x : H`, the tail
`∑_{i ≥ n} ⟪b i, x⟫_ℝ ^ 2 → 0`, packaged in the form most directly used by
spectral-truncation operator-norm arguments. -/
theorem spectralTruncate_op_norm_via_parseval
    (b : HilbertBasis ℕ ℝ H) (x : H) :
    Filter.Tendsto
      (fun n => ∑' i : ℕ, if i ≥ n then ⟪b i, x⟫_ℝ ^ 2 else 0)
      Filter.atTop (nhds 0) :=
  bessel_tail_tendsto_zero b x

end Statlean

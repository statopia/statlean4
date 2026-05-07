/-
Copyright (c) 2026 Statlean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! # Compressed Sensing — Restricted Isometry Property

The Candès–Tao (2005) RIP framework and the L¹ recovery guarantee of
Candès (2008) for sparse signals.  The key result is: if a measurement
matrix `A : ℝ^{m × n}` satisfies the Restricted Isometry Property of
order `2s` with sufficiently small isometry constant `δ < √2 − 1`, then
`ℓ¹` minimisation
`min ‖z‖₁  s.t.  A z = A x`
recovers any `s`-sparse signal `x` exactly from the compressed
measurements `y = A x`.

## Contents

* `Statlean.CompressedSensing.IsSSparse x s` — `x : Fin n → ℝ` is
  `s`-sparse, i.e. has at most `s` nonzero entries.
* `Statlean.CompressedSensing.IsRIP A s δ` — `A` satisfies the
  `(s, δ)`-Restricted Isometry Property.
* `Statlean.CompressedSensing.l1RecoveryThreshold` — the Candès 2008
  threshold `√2 − 1`, with `0 < · < 1`.
* `Statlean.CompressedSensing.candes_tao_recovery` — the L¹ recovery
  statement (proof requires the null-space property + cone argument
  and is left as a `sorry`).

## References

* E. J. Candès and T. Tao, *Decoding by linear programming*, IEEE
  Transactions on Information Theory **51** (2005), 4203–4215.
* E. J. Candès, *The restricted isometry property and its implications
  for compressed sensing*, Comptes Rendus Mathematique **346** (2008),
  589–592.
* S. Foucart and H. Rauhut, *A Mathematical Introduction to Compressive
  Sensing*, Springer, 2013.
-/

open Matrix
open scoped Matrix BigOperators

namespace Statlean.CompressedSensing

variable {m n : ℕ}

/-- A vector `x : Fin n → ℝ` is **`s`-sparse** if it has at most `s`
nonzero entries. -/
def IsSSparse (x : Fin n → ℝ) (s : ℕ) : Prop :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ s

/-- A matrix `A : ℝ^{m × n}` satisfies the **`(s, δ)`-Restricted
Isometry Property** if for every `s`-sparse `x`,
`(1 − δ) ‖x‖² ≤ ‖A x‖² ≤ (1 + δ) ‖x‖²`. -/
def IsRIP (A : Matrix (Fin m) (Fin n) ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, IsSSparse x s →
    (1 - δ) * (∑ i, (x i) ^ 2) ≤ ∑ i, ((A.mulVec x) i) ^ 2 ∧
    (∑ i, ((A.mulVec x) i) ^ 2) ≤ (1 + δ) * (∑ i, (x i) ^ 2)

/-- The Candès–Tao 2005 / Candès 2008 RIP recovery threshold `√2 − 1`. -/
noncomputable def l1RecoveryThreshold : ℝ := Real.sqrt 2 - 1

section ThresholdLemmas

/-- Auxiliary: `1 < √2`. -/
private theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h_sq : (1 : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    norm_num
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- Auxiliary: `√2 < 2`. -/
private theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h_sq : (Real.sqrt 2) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    norm_num
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The Candès recovery threshold is positive: `0 < √2 − 1`. -/
theorem l1RecoveryThreshold_pos : 0 < l1RecoveryThreshold := by
  unfold l1RecoveryThreshold
  linarith [one_lt_sqrt_two]

/-- The Candès recovery threshold is strictly less than `1`. -/
theorem l1RecoveryThreshold_lt_one : l1RecoveryThreshold < 1 := by
  unfold l1RecoveryThreshold
  linarith [sqrt_two_lt_two]

/-- The Candès recovery threshold lies in the open interval `(0, 1)`. -/
theorem l1RecoveryThreshold_mem_Ioo : l1RecoveryThreshold ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨l1RecoveryThreshold_pos, l1RecoveryThreshold_lt_one⟩

end ThresholdLemmas

section SparsityLemmas

/-- The zero vector is `s`-sparse for every `s`. -/
theorem zero_isSSparse (s : ℕ) : IsSSparse (0 : Fin n → ℝ) s := by
  unfold IsSSparse
  simp

/-- Sparsity is monotone in the sparsity level: `s ≤ s'` ⇒ every
`s`-sparse vector is also `s'`-sparse. -/
theorem IsSSparse.mono {x : Fin n → ℝ} {s s' : ℕ} (hs : s ≤ s')
    (hx : IsSSparse x s) : IsSSparse x s' :=
  hx.trans hs

/-- Negation preserves sparsity: if `x` is `s`-sparse then so is `-x`. -/
theorem IsSSparse.neg {x : Fin n → ℝ} {s : ℕ} (hx : IsSSparse x s) :
    IsSSparse (-x) s := by
  unfold IsSSparse at hx ⊢
  refine le_trans ?_ hx
  apply le_of_eq
  congr 1
  ext i
  simp [Pi.neg_apply, neg_eq_zero]

/-- Scalar multiplication by a nonzero scalar preserves sparsity:
if `x` is `s`-sparse and `c ≠ 0`, then `c • x` is `s`-sparse. -/
theorem IsSSparse.smul {x : Fin n → ℝ} {s : ℕ} (c : ℝ) (hc : c ≠ 0)
    (hx : IsSSparse x s) : IsSSparse (c • x) s := by
  unfold IsSSparse at hx ⊢
  refine le_trans ?_ hx
  apply le_of_eq
  congr 1
  ext i
  simp [Pi.smul_apply, smul_eq_mul, hc]

end SparsityLemmas

section RIPLemmas

/-- Vacuous RIP: any matrix `A` is `(s, δ)`-RIP at the zero vector. -/
theorem isRIP_zero_vector
    (A : Matrix (Fin m) (Fin n) ℝ) (_s : ℕ) (δ : ℝ) :
    (1 - δ) * (∑ i, ((0 : Fin n → ℝ) i) ^ 2) ≤
        ∑ i, ((A.mulVec (0 : Fin n → ℝ)) i) ^ 2 ∧
      (∑ i, ((A.mulVec (0 : Fin n → ℝ)) i) ^ 2) ≤
        (1 + δ) * (∑ i, ((0 : Fin n → ℝ) i) ^ 2) := by
  refine ⟨?_, ?_⟩ <;> simp [Matrix.mulVec_zero]

end RIPLemmas

/-- **Candès–Tao 2005 / Candès 2008 ℓ¹ recovery**: under the
`(2s, δ)`-Restricted Isometry Property with `δ < √2 − 1`, ℓ¹
minimisation exactly recovers any `s`-sparse signal `x` from the
compressed measurements `A x`.

The statement says that `x` is a minimiser of the ℓ¹ norm among all
vectors `z` whose image under `A` matches `A x`.  The full proof of
this theorem proceeds via the *null-space property* combined with a
cone-constraint argument (see Foucart–Rauhut §6); we leave the proof
as a `sorry` for now. -/
theorem candes_tao_recovery
    {A : Matrix (Fin m) (Fin n) ℝ} {s : ℕ} {δ : ℝ}
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < l1RecoveryThreshold)
    (_hRIP : IsRIP A (2 * s) δ)
    (x : Fin n → ℝ) (_hx : IsSSparse x s) :
    ∀ z : Fin n → ℝ, A.mulVec z = A.mulVec x →
      ∑ i, |x i| ≤ ∑ i, |z i| := by
  sorry

end Statlean.CompressedSensing

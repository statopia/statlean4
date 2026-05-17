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

/-- The sum of an `s₁`-sparse vector and an `s₂`-sparse vector is
`(s₁ + s₂)`-sparse.  (Disjointness of supports is *not* required: the
support of `u + v` is always contained in the union of the supports.) -/
theorem IsSSparse.add_disjoint {u v : Fin n → ℝ} {s₁ s₂ : ℕ}
    (hu : IsSSparse u s₁) (hv : IsSSparse v s₂) :
    IsSSparse (u + v) (s₁ + s₂) := by
  classical
  unfold IsSSparse at *
  have hsub : (Finset.univ.filter (fun i => (u + v) i ≠ 0)) ⊆
              (Finset.univ.filter (fun i => u i ≠ 0)) ∪
              (Finset.univ.filter (fun i => v i ≠ 0)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.add_apply] at *
    by_contra hcon
    push_neg at hcon
    obtain ⟨hui, hvi⟩ := hcon
    apply hi
    rw [hui, hvi, add_zero]
  calc (Finset.univ.filter (fun i => (u + v) i ≠ 0)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => u i ≠ 0)).card +
        (Finset.univ.filter (fun i => v i ≠ 0)).card := Finset.card_union_le _ _
    _ ≤ s₁ + s₂ := Nat.add_le_add hu hv

/-- The difference of an `s₁`-sparse vector and an `s₂`-sparse vector is
`(s₁ + s₂)`-sparse. -/
theorem IsSSparse.sub_disjoint {u v : Fin n → ℝ} {s₁ s₂ : ℕ}
    (hu : IsSSparse u s₁) (hv : IsSSparse v s₂) :
    IsSSparse (u - v) (s₁ + s₂) := by
  classical
  unfold IsSSparse at *
  have hsub : (Finset.univ.filter (fun i => (u - v) i ≠ 0)) ⊆
              (Finset.univ.filter (fun i => u i ≠ 0)) ∪
              (Finset.univ.filter (fun i => v i ≠ 0)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.sub_apply] at *
    by_contra hcon
    push_neg at hcon
    obtain ⟨hui, hvi⟩ := hcon
    apply hi
    rw [hui, hvi, sub_zero]
  calc (Finset.univ.filter (fun i => (u - v) i ≠ 0)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => u i ≠ 0)).card +
        (Finset.univ.filter (fun i => v i ≠ 0)).card := Finset.card_union_le _ _
    _ ≤ s₁ + s₂ := Nat.add_le_add hu hv

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

/-! ## Sub-lemmas for the Candès–Tao recovery proof

The proof of `candes_tao_recovery` decomposes into the following ingredients
(see Foucart–Rauhut §6 or Mixon's blog *Short, Fat Matrices*):

1. **Cone constraint** — if `‖z‖₁ ≤ ‖x‖₁` with `x` supported on `T₀`, then the
   error `h = z − x` has its `T₀ᶜ`-mass dominated by its `T₀`-mass.
2. **Restricted orthogonality** — `(s₁ + s₂, δ)`-RIP forces
   `|⟨A u, A v⟩| ≤ δ ‖u‖₂ ‖v‖₂` whenever `u, v` are sparse with disjoint
   supports; proved by polarisation on `A(u ± v)`.
3. **Sparse tail bound** — sorting `T₀ᶜ` into blocks of size `s` of decreasing
   magnitude yields `‖h_{(T₀∪T₁)ᶜ}‖₂ ≤ s^{−1/2} ‖h_{T₀ᶜ}‖₁`.
4. **Kernel triviality (NSP)** — combining 2 and 3 in the RIP lower bound
   contracts the recursion when `δ < √2 − 1`, forcing `h = 0` on `ker A`.
-/

section CandesTaoIngredients

/-- The error vector `h = z − x` between an `s`-sparse target `x` (supported
on a set `T₀` of cardinality at most `s`) and any `z` with `ℓ¹` norm not
exceeding that of `x` satisfies the **cone constraint**:
`‖h‖₁` on `T₀ᶜ` is dominated by `‖h‖₁` on `T₀`. -/
theorem cone_constraint {n : ℕ} {x z : Fin n → ℝ} (T₀ : Finset (Fin n))
    (hx_supp : ∀ i ∉ T₀, x i = 0)
    (hz_le : ∑ i, |z i| ≤ ∑ i, |x i|) :
    (∑ i ∈ T₀ᶜ, |(z - x) i|) ≤ (∑ i ∈ T₀, |(z - x) i|) := by
  classical
  -- Step 1: ∑_i |x i| = ∑_{T₀} |x i| since x vanishes outside T₀.
  have hxsum : ∑ i, |x i| = ∑ i ∈ T₀, |x i| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ T₀)
    intro i _ hi
    have : x i = 0 := hx_supp i hi
    simp [this]
  -- Step 2: ∑_i |z i| = ∑_{T₀} |z i| + ∑_{T₀ᶜ} |z i|.
  have hzsplit : ∑ i, |z i| = ∑ i ∈ T₀, |z i| + ∑ i ∈ T₀ᶜ, |z i| := by
    rw [← Finset.sum_add_sum_compl T₀ (fun i => |z i|)]
  -- Step 3: on T₀ᶜ, x i = 0 so |z i| = |(z - x) i|.
  have hcompl_eq : ∑ i ∈ T₀ᶜ, |z i| = ∑ i ∈ T₀ᶜ, |(z - x) i| := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ∉ T₀ := by simpa using hi
    have hxi : x i = 0 := hx_supp i hi'
    simp [Pi.sub_apply, hxi]
  -- Step 4: on T₀, reverse triangle: |x i| - |(z - x) i| ≤ |z i|.
  have hT₀_lower :
      ∑ i ∈ T₀, |x i| - ∑ i ∈ T₀, |(z - x) i| ≤ ∑ i ∈ T₀, |z i| := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h1 : |x i| - |z i| ≤ |x i - z i| := abs_sub_abs_le_abs_sub (x i) (z i)
    have h2 : |x i - z i| = |(z - x) i| := by
      rw [Pi.sub_apply]
      rw [show x i - z i = -(z i - x i) by ring, abs_neg]
    linarith
  -- Combine: ∑|x| = ∑_T₀ |x| ≥ ∑|z| = ∑_T₀|z| + ∑_T₀ᶜ|(z-x)|
  --                      ≥ (∑_T₀|x| - ∑_T₀|(z-x)|) + ∑_T₀ᶜ|(z-x)|.
  linarith [hz_le, hxsum, hzsplit, hcompl_eq, hT₀_lower]

/-- **Restricted orthogonality** (Candès–Romberg–Tao 2006): under
`(s₁ + s₂, δ)`-RIP, vectors `u, v` that are `s₁`- and `s₂`-sparse with
disjoint supports satisfy
`|⟨A u, A v⟩| ≤ δ · ‖u‖₂ · ‖v‖₂`. -/
theorem rip_restricted_orthogonality
    {A : Matrix (Fin m) (Fin n) ℝ} {s₁ s₂ : ℕ} {δ : ℝ}
    (hRIP : IsRIP A (s₁ + s₂) δ)
    {u v : Fin n → ℝ}
    (hu : IsSSparse u s₁) (hv : IsSSparse v s₂)
    (h_disjoint : ∀ i, u i ≠ 0 → v i = 0) :
    |∑ i, (A.mulVec u) i * (A.mulVec v) i| ≤
      δ * Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) := by
  classical
  set U : ℝ := ∑ i, (u i) ^ 2 with hU_def
  set V : ℝ := ∑ i, (v i) ^ 2 with hV_def
  have hU_nn : 0 ≤ U := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hV_nn : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- Handle degenerate cases U = 0 (i.e. u = 0) or V = 0.
  rcases eq_or_lt_of_le hU_nn with hU_eq | hU_pos
  · have hU_zero : U = 0 := hU_eq.symm
    have hu_zero : ∀ i, u i = 0 := by
      intro i
      have hsum : ∀ j ∈ Finset.univ, 0 ≤ (u j)^2 := fun j _ => sq_nonneg _
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp (hU_def ▸ hU_zero)
      have h2 := h1 i (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    have hu_fun : u = 0 := funext hu_zero
    have hAu : A.mulVec u = 0 := by rw [hu_fun]; exact Matrix.mulVec_zero A
    have hLHS : ∑ i, (A.mulVec u) i * (A.mulVec v) i = 0 := by
      rw [hAu]; simp
    have hsqrtU : Real.sqrt U = 0 := by rw [hU_zero, Real.sqrt_zero]
    rw [hLHS, abs_zero, hsqrtU]
    have hsqrtV_nn : 0 ≤ Real.sqrt (∑ i, (v i) ^ 2) := Real.sqrt_nonneg _
    nlinarith [hsqrtV_nn]
  rcases eq_or_lt_of_le hV_nn with hV_eq | hV_pos
  · have hV_zero : V = 0 := hV_eq.symm
    have hv_zero : ∀ i, v i = 0 := by
      intro i
      have hsum : ∀ j ∈ Finset.univ, 0 ≤ (v j)^2 := fun j _ => sq_nonneg _
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp (hV_def ▸ hV_zero)
      have h2 := h1 i (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    have hv_fun : v = 0 := funext hv_zero
    have hAv : A.mulVec v = 0 := by rw [hv_fun]; exact Matrix.mulVec_zero A
    have hLHS : ∑ i, (A.mulVec u) i * (A.mulVec v) i = 0 := by
      rw [hAv]; simp
    have hsqrtV : Real.sqrt V = 0 := by rw [hV_zero, Real.sqrt_zero]
    rw [hLHS, abs_zero, hsqrtV]
    have hsqrtU_nn : 0 ≤ Real.sqrt (∑ i, (u i) ^ 2) := Real.sqrt_nonneg _
    nlinarith [hsqrtU_nn]
  -- Generic case: U > 0 and V > 0.  Rescale `u → u / √U`, `v → v / √V`.
  set sU := Real.sqrt U with hsU_def
  set sV := Real.sqrt V with hsV_def
  have hsU_pos : 0 < sU := Real.sqrt_pos.mpr hU_pos
  have hsV_pos : 0 < sV := Real.sqrt_pos.mpr hV_pos
  have hsU_ne : sU ≠ 0 := ne_of_gt hsU_pos
  have hsV_ne : sV ≠ 0 := ne_of_gt hsV_pos
  set u' : Fin n → ℝ := (sU⁻¹) • u with hu'_def
  set v' : Fin n → ℝ := (sV⁻¹) • v with hv'_def
  have hu' : IsSSparse u' s₁ := IsSSparse.smul (sU⁻¹) (inv_ne_zero hsU_ne) hu
  have hv' : IsSSparse v' s₂ := IsSSparse.smul (sV⁻¹) (inv_ne_zero hsV_ne) hv
  -- Disjointness is preserved under scalar multiplication.
  have h_disjoint' : ∀ i, u' i ≠ 0 → v' i = 0 := by
    intro i hi
    simp only [hu'_def, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero,
      inv_eq_zero] at hi
    push_neg at hi
    have hu_i : u i ≠ 0 := hi.2
    have hv_i : v i = 0 := h_disjoint i hu_i
    simp [hv'_def, Pi.smul_apply, smul_eq_mul, hv_i]
  -- After rescaling, ‖u'‖² = ‖v'‖² = 1.
  have h_norm_u' : ∑ i, (u' i) ^ 2 = 1 := by
    have hpt : ∀ i, (u' i) ^ 2 = sU⁻¹ ^ 2 * (u i) ^ 2 := by
      intro i; simp only [hu'_def, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [hpt, ← Finset.mul_sum, ← hU_def]
    rw [sq, show sU⁻¹ * sU⁻¹ * U = (sU * sU)⁻¹ * U by field_simp,
        hsU_def, Real.mul_self_sqrt hU_nn]
    field_simp
  have h_norm_v' : ∑ i, (v' i) ^ 2 = 1 := by
    have hpt : ∀ i, (v' i) ^ 2 = sV⁻¹ ^ 2 * (v i) ^ 2 := by
      intro i; simp only [hv'_def, Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [hpt, ← Finset.mul_sum, ← hV_def]
    rw [sq, show sV⁻¹ * sV⁻¹ * V = (sV * sV)⁻¹ * V by field_simp,
        hsV_def, Real.mul_self_sqrt hV_nn]
    field_simp
  -- `u' ± v'` are `(s₁ + s₂)`-sparse.
  have h_u'v'_add_sparse : IsSSparse (u' + v') (s₁ + s₂) :=
    IsSSparse.add_disjoint hu' hv'
  have h_u'v'_sub_sparse : IsSSparse (u' - v') (s₁ + s₂) :=
    IsSSparse.sub_disjoint hu' hv'
  -- Disjoint supports ⇒ cross term `u' · v'` vanishes pointwise.
  have huv'_zero : ∀ i, u' i * v' i = 0 := by
    intro i
    by_cases hu'_i : u' i = 0
    · simp [hu'_i]
    · have hv'_i : v' i = 0 := h_disjoint' i hu'_i
      simp [hv'_i]
  -- Pointwise expansion gives ‖u' + v'‖² = ‖u' - v'‖² = 2.
  have h_norm_u'_add_v' : ∑ i, ((u' + v') i) ^ 2 = 2 := by
    have hpt : ∀ i, ((u' + v') i) ^ 2 =
        (u' i)^2 + (v' i)^2 + 2 * (u' i * v' i) := by
      intro i; rw [Pi.add_apply]; ring
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : ∑ i, 2 * (u' i * v' i) = 0 := by
      have hzero : ∀ i ∈ Finset.univ, 2 * (u' i * v' i) = 0 := by
        intro i _; rw [huv'_zero i]; ring
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    rw [hcross, h_norm_u', h_norm_v']
    ring
  have h_norm_u'_sub_v' : ∑ i, ((u' - v') i) ^ 2 = 2 := by
    have hpt : ∀ i, ((u' - v') i) ^ 2 =
        (u' i)^2 + (v' i)^2 - 2 * (u' i * v' i) := by
      intro i; rw [Pi.sub_apply]; ring
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hcross : ∑ i, 2 * (u' i * v' i) = 0 := by
      have hzero : ∀ i ∈ Finset.univ, 2 * (u' i * v' i) = 0 := by
        intro i _; rw [huv'_zero i]; ring
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    rw [hcross, h_norm_u', h_norm_v']
    ring
  -- Apply the RIP bounds to `u' + v'` and `u' - v'`.
  obtain ⟨h_RIP_add_lo, h_RIP_add_hi⟩ := hRIP (u' + v') h_u'v'_add_sparse
  obtain ⟨h_RIP_sub_lo, h_RIP_sub_hi⟩ := hRIP (u' - v') h_u'v'_sub_sparse
  rw [h_norm_u'_add_v'] at h_RIP_add_lo h_RIP_add_hi
  rw [h_norm_u'_sub_v'] at h_RIP_sub_lo h_RIP_sub_hi
  -- Polarisation identity: `4⟨A u', A v'⟩ = ‖A(u'+v')‖² - ‖A(u'-v')‖²`.
  have h_polar' :
      4 * (∑ i, (A.mulVec u') i * (A.mulVec v') i) =
        (∑ i, ((A.mulVec (u' + v')) i) ^ 2) -
        (∑ i, ((A.mulVec (u' - v')) i) ^ 2) := by
    have hAadd : A.mulVec (u' + v') = A.mulVec u' + A.mulVec v' :=
      Matrix.mulVec_add A u' v'
    have hAsub : A.mulVec (u' - v') = A.mulVec u' - A.mulVec v' :=
      Matrix.mulVec_sub A u' v'
    rw [hAadd, hAsub]
    have hpt : ∀ i, ((A.mulVec u' + A.mulVec v') i) ^ 2 -
              ((A.mulVec u' - A.mulVec v') i) ^ 2 =
              4 * ((A.mulVec u') i * (A.mulVec v') i) := by
      intro i; rw [Pi.add_apply, Pi.sub_apply]; ring
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hpt i),
        ← Finset.mul_sum]
  -- Subtracting the two RIP bounds gives `|⟨A u', A v'⟩| ≤ δ`.
  have h_inner_le : |∑ i, (A.mulVec u') i * (A.mulVec v') i| ≤ δ := by
    have h_inner_up :
        (∑ i, (A.mulVec u') i * (A.mulVec v') i) ≤ δ := by linarith
    have h_inner_lo :
        -δ ≤ (∑ i, (A.mulVec u') i * (A.mulVec v') i) := by linarith
    rw [abs_le]; exact ⟨h_inner_lo, h_inner_up⟩
  -- Translate back: `A u' = sU⁻¹ • A u` and `A v' = sV⁻¹ • A v` by linearity.
  have hAu' : A.mulVec u' = sU⁻¹ • A.mulVec u := by
    simp only [hu'_def]; exact Matrix.mulVec_smul A (sU⁻¹) u
  have hAv' : A.mulVec v' = sV⁻¹ • A.mulVec v := by
    simp only [hv'_def]; exact Matrix.mulVec_smul A (sV⁻¹) v
  have h_inner_eq :
      (∑ i, (A.mulVec u') i * (A.mulVec v') i) =
      sU⁻¹ * sV⁻¹ * (∑ i, (A.mulVec u) i * (A.mulVec v) i) := by
    rw [hAu', hAv', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_inner_eq, abs_mul] at h_inner_le
  have hpos : 0 < sU⁻¹ * sV⁻¹ :=
    mul_pos (inv_pos.mpr hsU_pos) (inv_pos.mpr hsV_pos)
  rw [abs_of_pos hpos] at h_inner_le
  -- Multiply both sides by `sU * sV ≥ 0` to clear the rescaling.
  have hsUV_nn : 0 ≤ sU * sV :=
    mul_nonneg (le_of_lt hsU_pos) (le_of_lt hsV_pos)
  have hstep :
      sU * sV * (sU⁻¹ * sV⁻¹ * |∑ i, (A.mulVec u) i * (A.mulVec v) i|) ≤
      sU * sV * δ :=
    mul_le_mul_of_nonneg_left h_inner_le hsUV_nn
  have hsimp :
      sU * sV * (sU⁻¹ * sV⁻¹ * |∑ i, (A.mulVec u) i * (A.mulVec v) i|) =
      |∑ i, (A.mulVec u) i * (A.mulVec v) i| := by
    field_simp
  rw [hsimp] at hstep
  -- The goal becomes `|⟨A u, A v⟩| ≤ δ * √U * √V`, which matches `hstep`.
  linarith

/-- **Sparse tail bound**: choose `T₀` and a *next-best* block `T₁ ⊆ T₀ᶜ` of
cardinality `s` capturing the largest entries of `|h|` on `T₀ᶜ`.  Then the
remainder satisfies
`(∑_{i ∉ T₀ ∪ T₁} (h i)²)^{1/2} ≤ s^{-1/2} · (∑_{i ∉ T₀} |h i|)`. -/
theorem sparse_tail_bound {n : ℕ} {s : ℕ} (hs : 1 ≤ s) (h : Fin n → ℝ)
    (T₀ T₁ : Finset (Fin n))
    (hT₀T₁ : Disjoint T₀ T₁) (hT₁_card : T₁.card = s)
    (h_chooses_largest :
      ∀ i ∈ T₁, ∀ j ∈ (T₀ ∪ T₁)ᶜ, |h j| ≤ |h i|) :
    Real.sqrt (∑ i ∈ (T₀ ∪ T₁)ᶜ, (h i) ^ 2) ≤
      (Real.sqrt s)⁻¹ * (∑ i ∈ T₀ᶜ, |h i|) := by
  classical
  -- `T₁ ⊆ T₀ᶜ` and `(T₀ ∪ T₁)ᶜ` is disjoint from `T₁`.
  have hT₁_subset_T₀c : T₁ ⊆ T₀ᶜ := by
    intro i hi
    simp only [Finset.mem_compl]
    exact Finset.disjoint_right.mp hT₀T₁ hi
  have hUc_disjoint_T₁ : Disjoint (T₀ ∪ T₁)ᶜ T₁ := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_compl, Finset.mem_union] at hi₁
    exact hi₁ (Or.inr hi₂)
  -- Partition of the support: `(T₀ ∪ T₁)ᶜ ∪ T₁ = T₀ᶜ`.
  have h_partition_set : (T₀ ∪ T₁)ᶜ ∪ T₁ = T₀ᶜ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_union]
    constructor
    · rintro (h₁ | h₂)
      · intro hT₀; exact h₁ (Or.inl hT₀)
      · intro hT₀
        exact (Finset.disjoint_left.mp hT₀T₁ hT₀) h₂
    · intro hT₀
      by_cases hT₁ : i ∈ T₁
      · exact Or.inr hT₁
      · exact Or.inl (fun hor => hor.elim hT₀ hT₁)
  set L1c : ℝ := ∑ i ∈ (T₀ ∪ T₁)ᶜ, |h i| with hL1c_def
  set L1T₁ : ℝ := ∑ i ∈ T₁, |h i| with hL1T₁_def
  set L1T₀c : ℝ := ∑ i ∈ T₀ᶜ, |h i| with hL1T₀c_def
  set L2sq : ℝ := ∑ i ∈ (T₀ ∪ T₁)ᶜ, (h i) ^ 2 with hL2sq_def
  have hL1c_nn : 0 ≤ L1c := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hL1T₁_nn : 0 ≤ L1T₁ := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hL1T₀c_nn : 0 ≤ L1T₀c := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hL2sq_nn : 0 ≤ L2sq := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hs)
  have hs_nn : (0 : ℝ) ≤ s := le_of_lt hs_pos
  -- Step 1 (partition):  `L1c + L1T₁ = L1T₀c`.
  have h_partition : L1c + L1T₁ = L1T₀c := by
    rw [hL1c_def, hL1T₁_def, hL1T₀c_def, ← h_partition_set]
    exact (Finset.sum_union hUc_disjoint_T₁).symm
  -- Step 2 (min ≤ average):  for `j ∈ (T₀ ∪ T₁)ᶜ`, `s · |h j| ≤ L1T₁`.
  have h_pointwise : ∀ j ∈ (T₀ ∪ T₁)ᶜ, (s : ℝ) * |h j| ≤ L1T₁ := by
    intro j hj
    have hbound : ∀ i ∈ T₁, |h j| ≤ |h i| :=
      fun i hi => h_chooses_largest i hi j hj
    have hsum_le : ∑ _i ∈ T₁, |h j| ≤ ∑ i ∈ T₁, |h i| := Finset.sum_le_sum hbound
    rw [Finset.sum_const, hT₁_card, nsmul_eq_mul] at hsum_le
    exact hsum_le
  -- Step 3 (square the pointwise bound):  `(h j)^2 ≤ |h j| · (L1T₁ / s)`.
  have h_pointwise_sq : ∀ j ∈ (T₀ ∪ T₁)ᶜ, (h j) ^ 2 ≤ |h j| * (L1T₁ / s) := by
    intro j hj
    have hp := h_pointwise j hj
    have hj_nn : 0 ≤ |h j| := abs_nonneg _
    have habs_le : |h j| ≤ L1T₁ / s := by
      rw [le_div_iff₀ hs_pos]
      linarith [hp]
    calc (h j) ^ 2 = |h j| * |h j| := by rw [← sq_abs, sq]
      _ ≤ |h j| * (L1T₁ / s) := mul_le_mul_of_nonneg_left habs_le hj_nn
  -- Step 4 (sum):  `L2sq ≤ L1c · L1T₁ / s`.
  have h_L2sq_bound : L2sq ≤ L1c * L1T₁ / s := by
    have hsum : L2sq ≤ ∑ j ∈ (T₀ ∪ T₁)ᶜ, |h j| * (L1T₁ / s) :=
      Finset.sum_le_sum h_pointwise_sq
    rw [show (∑ j ∈ (T₀ ∪ T₁)ᶜ, |h j| * (L1T₁ / s)) =
            (∑ j ∈ (T₀ ∪ T₁)ᶜ, |h j|) * (L1T₁ / s) from
      (Finset.sum_mul _ _ _).symm] at hsum
    rw [← hL1c_def] at hsum
    rw [mul_div_assoc]
    exact hsum
  -- Step 5 (AM–GM):  `4 · (L1c · L1T₁) ≤ L1T₀c²`.
  have h_AMGM : 4 * (L1c * L1T₁) ≤ L1T₀c ^ 2 :=
    by nlinarith [sq_nonneg (L1c - L1T₁), h_partition, hL1c_nn, hL1T₁_nn]
  -- Step 6 (combine):  `L2sq ≤ L1T₀c² / s` (looser than `/(4s)`, suffices here).
  have h_L2sq_final : L2sq ≤ L1T₀c ^ 2 / s := by
    have h1 : L2sq * s ≤ L1c * L1T₁ := by
      rw [le_div_iff₀ hs_pos] at h_L2sq_bound
      exact h_L2sq_bound
    rw [le_div_iff₀ hs_pos]
    nlinarith [h1, h_AMGM, sq_nonneg L1T₀c]
  -- Step 7 (take square root):  `√L2sq ≤ (√s)⁻¹ · L1T₀c`.
  have hgoal_sq : L2sq ≤ ((Real.sqrt s)⁻¹ * L1T₀c) ^ 2 := by
    rw [mul_pow]
    rw [show ((Real.sqrt s)⁻¹) ^ 2 = 1 / s from ?_]
    · rw [one_div, inv_mul_eq_div]
      exact h_L2sq_final
    · rw [inv_pow, Real.sq_sqrt hs_nn]
      ring
  have hrhs_nn : 0 ≤ (Real.sqrt s)⁻¹ * L1T₀c :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hL1T₀c_nn
  calc Real.sqrt L2sq
      ≤ Real.sqrt (((Real.sqrt s)⁻¹ * L1T₀c) ^ 2) := Real.sqrt_le_sqrt hgoal_sq
    _ = (Real.sqrt s)⁻¹ * L1T₀c := Real.sqrt_sq hrhs_nn

/-- **Helper definition for the kernel-triviality proof.**  Given `h : Fin n → ℝ`
and a finset `S`, `restrictTo S h` is the vector that equals `h` on `S` and `0`
elsewhere.  This is the standard "indicator restriction" used throughout the
proof of Candès 2008. -/
def restrictTo (S : Finset (Fin n)) (h : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then h i else 0

@[simp] theorem restrictTo_apply_mem {S : Finset (Fin n)} {h : Fin n → ℝ} {i : Fin n}
    (hi : i ∈ S) : restrictTo S h i = h i := by simp [restrictTo, hi]

@[simp] theorem restrictTo_apply_not_mem {S : Finset (Fin n)} {h : Fin n → ℝ} {i : Fin n}
    (hi : i ∉ S) : restrictTo S h i = 0 := by simp [restrictTo, hi]

/-- `restrictTo S h` is `S.card`-sparse. -/
theorem restrictTo_isSSparse (S : Finset (Fin n)) (h : Fin n → ℝ) :
    IsSSparse (restrictTo S h) S.card := by
  classical
  unfold IsSSparse
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra h_notin
  exact hi (restrictTo_apply_not_mem h_notin)

/-- Decomposition: `restrictTo S h + restrictTo Sᶜ h = h`. -/
theorem restrictTo_add_compl (S : Finset (Fin n)) (h : Fin n → ℝ) :
    restrictTo S h + restrictTo Sᶜ h = h := by
  ext i
  simp only [Pi.add_apply, restrictTo]
  by_cases hi : i ∈ S
  · simp [hi, Finset.mem_compl]
  · simp [hi, Finset.mem_compl.mpr hi]

/-- Sum of squares: `∑ i, (restrictTo S h i)² = ∑ i ∈ S, (h i)²`. -/
theorem restrictTo_sum_sq (S : Finset (Fin n)) (h : Fin n → ℝ) :
    ∑ i, (restrictTo S h i) ^ 2 = ∑ i ∈ S, (h i) ^ 2 := by
  classical
  unfold restrictTo
  rw [show (∑ i, (if i ∈ S then h i else 0) ^ 2) =
         ∑ i, (if i ∈ S then (h i)^2 else 0) from by
    congr 1; ext i; split_ifs <;> simp]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Sum of absolute values: `∑ i, |restrictTo S h i| = ∑ i ∈ S, |h i|`. -/
theorem restrictTo_sum_abs (S : Finset (Fin n)) (h : Fin n → ℝ) :
    ∑ i, |restrictTo S h i| = ∑ i ∈ S, |h i| := by
  classical
  unfold restrictTo
  rw [show (∑ i, |if i ∈ S then h i else 0|) =
         ∑ i, (if i ∈ S then |h i| else 0) from by
    congr 1; ext i; split_ifs <;> simp]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Linearity: `A.mulVec (restrictTo S h) + A.mulVec (restrictTo Sᶜ h) = A.mulVec h`. -/
theorem mulVec_restrictTo_add (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n))
    (h : Fin n → ℝ) :
    A.mulVec (restrictTo S h) + A.mulVec (restrictTo Sᶜ h) = A.mulVec h := by
  rw [← Matrix.mulVec_add, restrictTo_add_compl]

/-- Disjoint supports: if `Disjoint S T`, then `restrictTo S h` and `restrictTo T h`
have disjoint supports. -/
theorem restrictTo_disjoint_supports (S T : Finset (Fin n)) (hST : Disjoint S T)
    (h : Fin n → ℝ) :
    ∀ i, restrictTo S h i ≠ 0 → restrictTo T h i = 0 := by
  intro i hi
  simp only [restrictTo, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
  obtain ⟨hiS, _⟩ := hi
  exact restrictTo_apply_not_mem (Finset.disjoint_left.mp hST hiS)

/-- **Top-`k` selection by `|h|`**: for any `S : Finset (Fin n)` and `k ≤ S.card`,
there exists `T ⊆ S` with `T.card = k` capturing the `k` largest entries of `|h|`
on `S`, i.e. `|h j| ≤ |h i|` for every `i ∈ T` and `j ∈ S \ T`.

The construction is by strong induction on `k`: at each step, pick a maximizer
of `|h|` on the remaining set and add it to the accumulator. -/
theorem exists_top_k_by_abs (h : Fin n → ℝ) (S : Finset (Fin n)) (k : ℕ)
    (hk : k ≤ S.card) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card = k ∧
      ∀ i ∈ T, ∀ j ∈ S \ T, |h j| ≤ |h i| := by
  classical
  induction k with
  | zero =>
    refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
    intros i hi; exact absurd hi (Finset.notMem_empty _)
  | succ k ih =>
    -- Step 1: invoke IH with `k`.
    have hk' : k ≤ S.card := le_of_lt hk
    obtain ⟨T, hT_sub, hT_card, hT_largest⟩ := ih hk'
    -- Step 2: `S \ T` is nonempty (since `T.card = k < S.card`).
    have hSdT_nonempty : (S \ T).Nonempty := by
      rw [← Finset.card_pos]
      have hcard_sdiff : (S \ T).card = S.card - T.card :=
        Finset.card_sdiff_of_subset hT_sub
      rw [hcard_sdiff, hT_card]
      omega
    -- Step 3: pick a maximizer of `|h|` on `S \ T`.
    obtain ⟨a, ha_mem, ha_max⟩ := Finset.exists_max_image (S \ T) (fun i => |h i|) hSdT_nonempty
    -- Step 4: form the new accumulator `T' = insert a T`.
    have ha_in_S : a ∈ S := (Finset.mem_sdiff.mp ha_mem).1
    have ha_not_in_T : a ∉ T := (Finset.mem_sdiff.mp ha_mem).2
    refine ⟨insert a T, ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha_in_S
      · exact hT_sub hi
    · rw [Finset.card_insert_of_notMem ha_not_in_T, hT_card]
    · intro i hi j hj
      -- hj : j ∈ S \ insert a T = (S \ T) ∩ ({a}ᶜ)
      have hj_in_S : j ∈ S := (Finset.mem_sdiff.mp hj).1
      have hj_not_in : j ∉ insert a T := (Finset.mem_sdiff.mp hj).2
      have hj_ne_a : j ≠ a := by
        intro heq; apply hj_not_in; rw [heq]; exact Finset.mem_insert_self _ _
      have hj_not_T : j ∉ T := fun hT => hj_not_in (Finset.mem_insert_of_mem hT)
      have hj_in_SdT : j ∈ S \ T := Finset.mem_sdiff.mpr ⟨hj_in_S, hj_not_T⟩
      -- Case on whether i = a or i ∈ T
      rcases Finset.mem_insert.mp hi with rfl | hi_T
      · exact ha_max j hj_in_SdT
      · exact hT_largest i hi_T j hj_in_SdT

/-! ### Block decomposition helpers for Candès 2008 Step 5

The following two helper lemmas package the analytic content of
Foucart–Rauhut Lemma 6.10 / Corollary 6.13 — a Mathlib-PR-scale
contribution (~150–200 LOC of new infrastructure) involving:

1. **Block partition** of a finset into ordered blocks of size `≤ s`
   sorted by a real-valued key (here `|h|`).
2. **Telescoping inequality** bounding `∑_k ‖h_{B_k}‖₂` by an `ℓ¹` tail
   bound through the sparse-tail decay.

Both helpers are now proved (2026-05-17):
* `exists_block_partition` constructs the sorted block decomposition by
  greedy iteration (extending the IH with a clause "blocks before the last
  have cardinality exactly `s`", which is required by the telescope step).
* `block_l2_telescope` bounds `∑_k √(∑_{B_k} h²)` by `(√s)⁻¹ · ∑_{T₀ᶜ} |h|`
  using direct per-block AM-GM plus a `Finset.sum_bij` reindexing
  (k = 0 contributes via `T₁`; k ≥ 1 contributes via `B_{k-1}`).
-/

/-- **R6 helper (Foucart–Rauhut Lem 6.10, decomposition step)**:
sorted block partition of a finset.

Given a vector `h : Fin n → ℝ`, a finset `U : Finset (Fin n)`, and a
block size `s ≥ 1`, there exists a finite list of blocks
`B : Fin K → Finset (Fin n)` such that

* each block is a subset of `U`;
* the blocks are pairwise disjoint and their union is `U`;
* each block has cardinality `≤ s`;
* the blocks are sorted by `|h|` in the sense that for any `k < K - 1`,
  every entry in `B (k+1)` has `|h|` value `≤` every entry in `B k`.

The construction is by greedy iteration: pick the top-`s` entries by
`|h|` from `U` (using `exists_top_k_by_abs`), remove them from `U`, and
recurse.  We package the result as a `Finset`-valued function indexed
by `Fin K` for some `K`.

The proof is by strong induction on `U.card`.  In the base case (`U = ∅`)
we return `K = 0` (vacuously).  In the inductive step we extract the
top-`t` entries of `U` with `t := min s U.card` using
`exists_top_k_by_abs`, call this block `T`, and recurse on `U \ T`,
prepending `T` to the resulting list of blocks via `Fin.cases`. -/
theorem exists_block_partition (h : Fin n → ℝ) (U : Finset (Fin n))
    {s : ℕ} (hs : 1 ≤ s) :
    ∃ (K : ℕ) (B : Fin K → Finset (Fin n)),
      (∀ k, B k ⊆ U) ∧
      (∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (B k₁) (B k₂)) ∧
      (Finset.univ.biUnion B = U) ∧
      (∀ k, (B k).card ≤ s) ∧
      (∀ k : Fin K, ∀ (hk : k.val + 1 < K),
        ∀ i ∈ B ⟨k.val + 1, hk⟩, ∀ j ∈ B k, |h i| ≤ |h j|) ∧
      (∀ k : Fin K, k.val + 1 < K → (B k).card = s) ∧
      (K = 0 ∨ U.Nonempty) := by
  classical
  induction hN : U.card using Nat.strong_induction_on generalizing U with
  | _ N ih =>
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- Base case: `U = ∅`, return `K = 0`.
      subst hN0
      have hUempty : U = ∅ := Finset.card_eq_zero.mp hN
      refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun k => Fin.elim0 k
      · exact fun k₁ _ _ => Fin.elim0 k₁
      · simp [hUempty]
      · exact fun k => Fin.elim0 k
      · exact fun k => Fin.elim0 k
      · exact fun k => Fin.elim0 k
      · exact Or.inl rfl
    · -- Inductive step: pick top-`t` entries of `U` with `t := min s U.card`.
      set t : ℕ := min s U.card with ht_def
      have ht_le : t ≤ U.card := min_le_right _ _
      have ht_pos : 0 < t := by
        rw [ht_def]; exact lt_min hs (hN ▸ hNpos)
      have ht_le_s : t ≤ s := min_le_left _ _
      obtain ⟨T, hT_sub, hT_card, hT_largest⟩ :=
        exists_top_k_by_abs h U t ht_le
      -- The remaining set `U' = U \ T` has cardinality `< N`.
      set U' := U \ T with hU'_def
      have hU'_card : U'.card = U.card - t := by
        rw [hU'_def, Finset.card_sdiff_of_subset hT_sub, hT_card]
      have hU'_lt : U'.card < N := by
        rw [hU'_card, hN]; omega
      -- Apply IH to `U'`.
      obtain ⟨K', B', hB'_sub, hB'_disj, hB'_union, hB'_card, hB'_sorted, hB'_full, hB'_NE⟩ :=
        ih U'.card hU'_lt U' rfl
      -- Construct `B : Fin (K'+1) → Finset (Fin n)` by prepending `T`.
      refine ⟨K' + 1, Fin.cases T B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- (1) Each block is a subset of `U`.
        intro k
        refine Fin.cases ?_ ?_ k
        · exact hT_sub
        · intro j
          change B' j ⊆ U
          exact (hB'_sub j).trans Finset.sdiff_subset
      · -- (2) Blocks are pairwise disjoint.
        intro k₁ k₂ hne
        refine Fin.cases (motive := fun k₁ =>
            k₁ ≠ k₂ → Disjoint
              ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k₁)
              ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k₂))
          ?_ ?_ k₁ hne
        · -- k₁ = 0
          intro hne0
          refine Fin.cases (motive := fun k₂ =>
              (0 : Fin (K'+1)) ≠ k₂ → Disjoint
                ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) 0)
                ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k₂))
            ?_ ?_ k₂ hne0
          · intro hne'; exact absurd rfl hne'
          · intro j _
            change Disjoint T (B' j)
            refine Finset.disjoint_left.mpr ?_
            intro x hxT hxB'
            have hxU' : x ∈ U' := hB'_sub j hxB'
            rw [hU'_def, Finset.mem_sdiff] at hxU'
            exact hxU'.2 hxT
        · -- k₁ = j₁.succ
          intro j₁ hne1
          refine Fin.cases (motive := fun k₂ =>
              j₁.succ ≠ k₂ → Disjoint
                ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) j₁.succ)
                ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k₂))
            ?_ ?_ k₂ hne1
          · intro _
            change Disjoint (B' j₁) T
            refine Finset.disjoint_left.mpr ?_
            intro x hxB' hxT
            have hxU' : x ∈ U' := hB'_sub j₁ hxB'
            rw [hU'_def, Finset.mem_sdiff] at hxU'
            exact hxU'.2 hxT
          · intro j₂ hne2
            change Disjoint (B' j₁) (B' j₂)
            apply hB'_disj
            intro heq
            exact hne2 (congrArg Fin.succ heq)
      · -- (3) Union of blocks equals `U`.
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, hk⟩
          revert hk
          refine Fin.cases ?_ ?_ k
          · intro h0; exact hT_sub h0
          · intro j hj
            change x ∈ B' j at hj
            have hxU' : x ∈ U' := hB'_sub j hj
            rw [hU'_def, Finset.mem_sdiff] at hxU'
            exact hxU'.1
        · intro hxU
          by_cases hxT : x ∈ T
          · refine ⟨0, ?_⟩
            change x ∈ T; exact hxT
          · have hxU' : x ∈ U' := by
              rw [hU'_def, Finset.mem_sdiff]; exact ⟨hxU, hxT⟩
            have hbu : x ∈ Finset.univ.biUnion B' := by
              rw [hB'_union]; exact hxU'
            rcases Finset.mem_biUnion.mp hbu with ⟨j, _, hj⟩
            refine ⟨j.succ, ?_⟩
            change x ∈ B' j; exact hj
      · -- (4) Each block has cardinality `≤ s`.
        intro k
        refine Fin.cases ?_ ?_ k
        · change T.card ≤ s
          rw [hT_card]; exact ht_le_s
        · intro j; exact hB'_card j
      · -- (5) Blocks sorted by `|h|`.
        intro k hk i hi j hj
        refine Fin.cases (motive := fun k =>
          ∀ (hk : k.val + 1 < K' + 1),
          ∀ i ∈ (Fin.cases T B' : Fin (K'+1) → Finset (Fin n))
                  ⟨k.val + 1, hk⟩,
          ∀ j ∈ (Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k,
          |h i| ≤ |h j|) ?_ ?_ k hk i hi j hj
        · -- k = 0: B ⟨1, _⟩ = B' 0, B 0 = T.
          intro _ i hi j hj
          have hi' : i ∈ B' ⟨0, by omega⟩ := hi
          have hj' : j ∈ T := hj
          have hi_U' : i ∈ U' := hB'_sub _ hi'
          rw [hU'_def] at hi_U'
          exact hT_largest j hj' i hi_U'
        · -- k = k'.succ: B ⟨k.val+1, _⟩ = B' ⟨k'.val+1, _⟩, B k.succ = B' k'.
          intro k' hk' i hi j hj
          have hk'' : k'.val + 1 < K' := by
            have : k'.val + 1 + 1 < K' + 1 := hk'
            omega
          have hi' : i ∈ B' ⟨k'.val + 1, hk''⟩ := hi
          have hj' : j ∈ B' k' := hj
          exact hB'_sorted k' hk'' i hi' j hj'
      · -- (6) Blocks with a successor have cardinality exactly `s`.
        intro k hk
        refine Fin.cases (motive := fun k =>
          ∀ (_hk : k.val + 1 < K' + 1),
          ((Fin.cases T B' : Fin (K'+1) → Finset (Fin n)) k).card = s) ?_ ?_ k hk
        · -- k = 0: B 0 = T.  Need T.card = s.  Since K' + 1 > 1, K' ≥ 1, so by
          -- IH clause (7), either K' = 0 (contradiction) or U' is nonempty.
          intro hk0
          have hK'_pos : 0 < K' := by simpa using hk0
          have hU'_nonempty : U'.Nonempty :=
            hB'_NE.resolve_left (fun h0 => by omega)
          have hU'pos : 0 < U'.card := Finset.card_pos.mpr hU'_nonempty
          -- U'.card > 0 means U.card > t, so t = min(s, U.card) < U.card hence t = s.
          have hUcard_gt_t : t < U.card := by
            rw [hU'_card] at hU'pos; omega
          have ht_eq_s : t = s := by
            rcases Nat.lt_or_ge U.card s.succ with h_lt | h_ge
            · -- U.card < s + 1, i.e., U.card ≤ s, so t = U.card; but t < U.card.  Contradiction.
              have hUle : U.card ≤ s := Nat.lt_succ_iff.mp h_lt
              have : t = U.card := by rw [ht_def]; exact min_eq_right hUle
              omega
            · -- U.card ≥ s + 1, so s < U.card, hence t = s.
              have : s ≤ U.card := Nat.le_of_succ_le h_ge
              rw [ht_def]; exact min_eq_left this
          show T.card = s
          rw [hT_card, ht_eq_s]
        · -- k = j.succ: B (j.succ) = B' j, use IH clause (6) for B'.
          intro j hjsucc
          have hj_lt : j.val + 1 < K' := by
            have : j.val + 1 + 1 < K' + 1 := hjsucc
            omega
          change (B' j).card = s
          exact hB'_full j hj_lt
      · -- (7) K' + 1 ≠ 0, so we provide U.Nonempty.
        right
        rw [← hN] at hNpos
        exact Finset.card_pos.mp hNpos

/-- **Matrix `mulVec` distributes over Finset sums.**  Convenience
restatement of `mulVec_add` for an indexed family `B : Fin K → Fin n → ℝ`.
Used to decompose `A.mulVec r` along a block partition of `r`'s support. -/
theorem mulVec_finset_sum {m n K : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin K → Fin n → ℝ) :
    A.mulVec (∑ k, B k) = ∑ k, A.mulVec (B k) := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Matrix.mulVec_add, ih]

/-- **Block-telescope bound on the `ℓ²` norms of remainder pieces.**

Given a block partition `B : Fin K → Finset (Fin n)` of `(T₀ ∪ T₁)ᶜ`
into pieces of size `≤ s`, sorted by `|h|` (entries in `B k₊₁` are
dominated by entries in `B k`, and the entries in `T₁` dominate every
entry in `(T₀ ∪ T₁)ᶜ`), the sum of `ℓ²` norms of the remainder pieces
is controlled by the `ℓ¹` mass of `h` on `T₀ᶜ`:
`∑_k √(∑_{B_k} h²) ≤ (√s)⁻¹ · ∑_{T₀ᶜ} |h|`.

This is the iterated form of `sparse_tail_bound` (Foucart–Rauhut
Lemma 6.10) — applied to the prefix sums of the sorted blocks.

**Status**: proved (2026-05-17).  The proof uses the additional hypothesis
`hB_full : ∀ k, k.val + 1 < K → (B k).card = s` — i.e., every block except
possibly the last has size exactly `s`.  This holds for the greedy partition
returned by `exists_block_partition` (since each iteration takes
`min(s, |remaining|)` and only the last block can be shorter).

The argument is direct, not iterated `sparse_tail_bound`:
* For each `i ∈ B_k`, sorting gives `|h_i| ≤ |h_j|` for all `j ∈ T₁` (when `k=0`)
  or `j ∈ B_{k-1}` (when `k≥1`).  Summing over `j`, with `|T₁| = s` or
  `|B_{k-1}| = s`, gives `s · |h_i| ≤ L¹` of the comparison block.
* Hence `|h_i|² ≤ |h_i| · (L¹_prev / s)`, so
  `∑_{B_k} h² ≤ (L¹_{B_k}) · (L¹_prev / s) ≤ (L¹_prev)² / s` by `|B_k| ≤ s`
  and AM-GM (or directly Cauchy-Schwarz).  Actually we use the simpler bound
  `|h_i|² ≤ (L¹_prev / s)²` and sum: `‖h_{B_k}‖² ≤ |B_k| · (L¹_prev/s)² ≤ (L¹_prev)²/s`.
* Take square roots: `‖h_{B_k}‖₂ ≤ L¹_prev / √s`.
* Telescope: `∑_k ‖h_{B_k}‖₂ ≤ (L¹_{T₁} + ∑_{k=0}^{K-2} L¹_{B_k}) / √s
                            ≤ (L¹_{T₁} + L¹_{(T₀∪T₁)ᶜ}) / √s = L¹_{T₀ᶜ} / √s`. -/
theorem block_l2_telescope {n : ℕ} {s : ℕ} (hs : 1 ≤ s) (h : Fin n → ℝ)
    (T₀ T₁ : Finset (Fin n))
    (_hT₀T₁ : Disjoint T₀ T₁) (hT₁_card : T₁.card = s)
    (h_T₁_largest :
      ∀ i ∈ T₁, ∀ j ∈ (T₀ ∪ T₁)ᶜ, |h j| ≤ |h i|)
    {K : ℕ} (B : Fin K → Finset (Fin n))
    (hB_sub : ∀ k, B k ⊆ (T₀ ∪ T₁)ᶜ)
    (_hB_disj : ∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (B k₁) (B k₂))
    (hB_union : Finset.univ.biUnion B = ((T₀ ∪ T₁)ᶜ : Finset (Fin n)))
    (hB_card : ∀ k, (B k).card ≤ s)
    (hB_sorted : ∀ k : Fin K, ∀ (hk : k.val + 1 < K),
      ∀ i ∈ B ⟨k.val + 1, hk⟩, ∀ j ∈ B k, |h i| ≤ |h j|)
    (hB_full : ∀ k : Fin K, k.val + 1 < K → (B k).card = s) :
    ∑ k, Real.sqrt (∑ i ∈ B k, (h i) ^ 2) ≤
      (Real.sqrt s)⁻¹ * (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) := by
  classical
  have hs_real_pos : (0 : ℝ) < s :=
    by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hs
  have hs_real_nn : (0 : ℝ) ≤ s := le_of_lt hs_real_pos
  have hsqrt_s_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_real_pos
  have hsqrt_s_nn : 0 ≤ Real.sqrt s := le_of_lt hsqrt_s_pos
  -- Per-block L¹ shorthand.
  set L1 : Fin K → ℝ := fun k => ∑ i ∈ B k, |h i| with hL1_def
  have hL1_nn : ∀ k, 0 ≤ L1 k :=
    fun k => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set L1T₁ : ℝ := ∑ i ∈ T₁, |h i| with hL1T₁_def
  have hL1T₁_nn : 0 ≤ L1T₁ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  -- Define the "comparison L¹" function: cmp k = L1T₁ if k.val = 0, else L1 of
  -- the preceding block.  We use a function defined on Fin (K+1) shifted view.
  -- A cleaner approach: define cmp : Fin K → ℝ by cases on k.val.
  set cmp : Fin K → ℝ := fun k =>
    if h0 : k.val = 0 then L1T₁
    else L1 ⟨k.val - 1, by
      have : 0 < k.val := Nat.pos_of_ne_zero h0
      omega⟩ with hcmp_def
  have hcmp_nn : ∀ k, 0 ≤ cmp k := by
    intro k
    simp only [hcmp_def]
    by_cases h0 : k.val = 0
    · simp [h0, hL1T₁_nn]
    · simp [h0, hL1_nn]
  -- Per-block bound: ∑_{B k} h² ≤ |B k| · (cmp k / s)².  Then take sqrt and use
  -- |B k| ≤ s to get √(∑_{B k} h²) ≤ cmp k / √s.
  -- Key step: s · |h i| ≤ cmp k for every i ∈ B k.
  have h_pointwise : ∀ k : Fin K, ∀ i ∈ B k, (s : ℝ) * |h i| ≤ cmp k := by
    intro k i hi
    simp only [hcmp_def]
    by_cases h0 : k.val = 0
    · -- k = 0: dominating set is T₁.
      simp only [h0, ↓reduceDIte]
      have hi_compl : i ∈ ((T₀ ∪ T₁)ᶜ : Finset (Fin n)) := hB_sub k hi
      have hbound : ∀ j ∈ T₁, |h i| ≤ |h j| :=
        fun j hj => h_T₁_largest j hj i hi_compl
      have hsum_le : ∑ _j ∈ T₁, |h i| ≤ ∑ j ∈ T₁, |h j| := Finset.sum_le_sum hbound
      rw [Finset.sum_const, hT₁_card, nsmul_eq_mul] at hsum_le
      exact hsum_le
    · -- k.val ≥ 1: dominating set is B ⟨k.val - 1, _⟩.
      simp only [h0, ↓reduceDIte]
      have hk_pos : 0 < k.val := Nat.pos_of_ne_zero h0
      set k' : Fin K := ⟨k.val - 1, by omega⟩
      have hk'_succ_eq : k'.val + 1 = k.val := by show k.val - 1 + 1 = k.val; omega
      have hk'_succ_lt : k'.val + 1 < K := by rw [hk'_succ_eq]; exact k.isLt
      have hk'_card_eq_s : (B k').card = s := hB_full k' hk'_succ_lt
      have h_index_eq : (B ⟨k'.val + 1, hk'_succ_lt⟩ : Finset (Fin n)) = B k := by
        congr 1
        exact Fin.ext hk'_succ_eq
      have hsorted := hB_sorted k' hk'_succ_lt
      have hi' : i ∈ B ⟨k'.val + 1, hk'_succ_lt⟩ := h_index_eq ▸ hi
      have hbound : ∀ j ∈ B k', |h i| ≤ |h j| :=
        fun j hj => hsorted i hi' j hj
      have hsum_le : ∑ _j ∈ B k', |h i| ≤ ∑ j ∈ B k', |h j| := Finset.sum_le_sum hbound
      rw [Finset.sum_const, hk'_card_eq_s, nsmul_eq_mul] at hsum_le
      exact hsum_le
  -- Derived: for i ∈ B k, |h i| ≤ cmp k / s, so (h i)² ≤ (cmp k / s)².
  have h_pointwise_div : ∀ k : Fin K, ∀ i ∈ B k, |h i| ≤ cmp k / s := by
    intro k i hi
    rw [le_div_iff₀ hs_real_pos]
    have := h_pointwise k i hi
    linarith
  have h_per_block_sq_sum : ∀ k : Fin K,
      (∑ i ∈ B k, (h i) ^ 2) ≤ (cmp k) ^ 2 / s := by
    intro k
    -- ∑_{B k} h² ≤ |B k| · max² ≤ s · (cmp k / s)² = cmp k² / s.
    have h1 : ∀ i ∈ B k, (h i) ^ 2 ≤ (cmp k / s) ^ 2 := by
      intro i hi
      have habs := h_pointwise_div k i hi
      have habs_nn : 0 ≤ |h i| := abs_nonneg _
      have hcmpdiv_nn : 0 ≤ cmp k / s := div_nonneg (hcmp_nn k) hs_real_nn
      calc (h i) ^ 2 = |h i| ^ 2 := by rw [sq_abs]
        _ ≤ (cmp k / s) ^ 2 := by
            apply sq_le_sq'
            · linarith
            · exact habs
    have h2 : (∑ i ∈ B k, (h i) ^ 2) ≤ ∑ _i ∈ B k, (cmp k / s) ^ 2 :=
      Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hcard_real : ((B k).card : ℝ) ≤ s := by exact_mod_cast hB_card k
    have hsq_nn : 0 ≤ (cmp k / s) ^ 2 := sq_nonneg _
    have h3 : ((B k).card : ℝ) * (cmp k / s) ^ 2 ≤ s * (cmp k / s) ^ 2 :=
      mul_le_mul_of_nonneg_right hcard_real hsq_nn
    calc (∑ i ∈ B k, (h i) ^ 2)
        ≤ ((B k).card : ℝ) * (cmp k / s) ^ 2 := h2
      _ ≤ s * (cmp k / s) ^ 2 := h3
      _ = (cmp k) ^ 2 / s := by
          have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_real_pos
          field_simp
  -- Take square roots.
  have h_per_block_sqrt : ∀ k : Fin K,
      Real.sqrt (∑ i ∈ B k, (h i) ^ 2) ≤ cmp k / Real.sqrt s := by
    intro k
    have hbound := h_per_block_sq_sum k
    have hrhs_eq : (cmp k) ^ 2 / s = (cmp k / Real.sqrt s) ^ 2 := by
      have hsqrt_sq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs_real_nn
      rw [div_pow, hsqrt_sq]
    rw [hrhs_eq] at hbound
    have hrhs_nn : 0 ≤ cmp k / Real.sqrt s :=
      div_nonneg (hcmp_nn k) hsqrt_s_nn
    calc Real.sqrt (∑ i ∈ B k, (h i) ^ 2)
        ≤ Real.sqrt ((cmp k / Real.sqrt s) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = cmp k / Real.sqrt s := Real.sqrt_sq hrhs_nn
  -- Sum the bounds.
  have h_sum_bound : ∑ k, Real.sqrt (∑ i ∈ B k, (h i) ^ 2) ≤
      (∑ k, cmp k) / Real.sqrt s := by
    have hsum : ∑ k, Real.sqrt (∑ i ∈ B k, (h i) ^ 2) ≤ ∑ k, cmp k / Real.sqrt s :=
      Finset.sum_le_sum (fun k _ => h_per_block_sqrt k)
    have heq : ∑ k, cmp k / Real.sqrt s = (∑ k, cmp k) / Real.sqrt s :=
      (Finset.sum_div _ _ _).symm
    linarith
  -- Now bound ∑ k, cmp k by L1T₁ + L¹ over (T₀ ∪ T₁)ᶜ ≤ L1T₀ᶜ.
  -- ∑ k, cmp k = L1T₁ * (1 if K ≥ 1 else 0) + ∑_{k.val ≥ 1} L1 ⟨k.val - 1, _⟩
  --            = (if K = 0 then 0 else L1T₁) + ∑_{k : Fin K, k.val + 1 < K} L1 k
  -- ≤ L1T₁ + ∑_{k : Fin K} L1 k * [k.val + 1 < K]
  -- ≤ L1T₁ + ∑_{k : Fin K} L1 k  (since L1 k ≥ 0)
  -- ≤ L1T₁ + L¹_{(T₀∪T₁)ᶜ}        (by hB_union)
  -- ≤ L¹_{T₀ᶜ}                    (since T₁ ⊆ T₀ᶜ and (T₀∪T₁)ᶜ ⊆ T₀ᶜ disjointly)
  -- ∑ k, cmp k:  for each k, cmp k = L1T₁ or L1 k'.  We can bound it pointwise
  -- by L1T₁ + L1 k' (both nonneg).  Better: bound ∑ cmp ≤ L1T₁ + ∑ L1.
  set SumCmp : ℝ := ∑ k, cmp k with hSumCmp_def
  -- Use the structure of cmp: split SumCmp into the k = 0 contribution (= L1T₁ if K ≥ 1)
  -- plus the k ≠ 0 contributions (each = L1 ⟨k.val - 1, _⟩, indexed bijectively by
  -- the filter set {j : j.val + 1 < K}).
  have h_SumCmp_bound : SumCmp ≤ L1T₁ + ∑ k ∈ Finset.univ.filter
      (fun k : Fin K => k.val + 1 < K), L1 k := by
    -- Split sum on K = 0 vs K ≥ 1.
    by_cases hK : K = 0
    · subst hK
      have hSumCmp_zero : SumCmp = 0 := by
        rw [hSumCmp_def]; simp
      have hfilter_nn : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin 0 => k.val + 1 < 0), L1 k :=
        Finset.sum_nonneg (fun _ _ => hL1_nn _)
      linarith
    · have hK_pos : 0 < K := Nat.pos_of_ne_zero hK
      -- Decompose ∑ k, cmp k = cmp ⟨0, hK_pos⟩ + ∑ (k ≠ 0) cmp k.
      -- cmp ⟨0, _⟩ = L1T₁.
      -- For k ≠ ⟨0, _⟩ : cmp k = L1 ⟨k.val - 1, _⟩.
      -- Reindex via k ↦ ⟨k.val - 1, _⟩ : Finset.univ.erase ⟨0, _⟩ → filter (fun j => j.val + 1 < K).
      have h_zero_cmp : cmp ⟨0, hK_pos⟩ = L1T₁ := by
        simp [hcmp_def]
      have h_split : SumCmp = cmp ⟨0, hK_pos⟩ +
          ∑ k ∈ Finset.univ.erase (⟨0, hK_pos⟩ : Fin K), cmp k := by
        rw [hSumCmp_def, ← Finset.sum_erase_add _ _ (Finset.mem_univ (⟨0, hK_pos⟩ : Fin K))]
        ring
      rw [h_split, h_zero_cmp]
      -- Now we need ∑_{k ≠ 0} cmp k ≤ ∑_{filter (j.val + 1 < K)} L1 j.
      -- For k ≠ 0: cmp k = L1 ⟨k.val - 1, _⟩.  The map k ↦ ⟨k.val - 1, _⟩ is a
      -- bijection from Finset.univ.erase 0 onto filter (j.val + 1 < K).
      have h_rest_eq : ∑ k ∈ Finset.univ.erase (⟨0, hK_pos⟩ : Fin K), cmp k =
          ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val + 1 < K), L1 k := by
        -- Build the bijection.
        refine Finset.sum_bij
          (fun k _ =>
            ⟨k.val - 1, by
              have hk_ne : k ≠ ⟨0, hK_pos⟩ := (Finset.mem_erase.mp ‹_›).1
              have hk_val_ne : k.val ≠ 0 := fun heq => hk_ne (Fin.ext heq)
              have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk_val_ne
              omega⟩) ?_ ?_ ?_ ?_
        · -- maps into the filter set
          intro k hk_mem
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hk_ne : k ≠ ⟨0, hK_pos⟩ := (Finset.mem_erase.mp hk_mem).1
          have hk_val_ne : k.val ≠ 0 := fun heq => hk_ne (Fin.ext heq)
          have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk_val_ne
          show k.val - 1 + 1 < K
          have hk_isLt := k.isLt
          omega
        · -- injectivity
          intro k₁ hk₁_mem k₂ hk₂_mem heq
          have hk₁_ne : k₁ ≠ ⟨0, hK_pos⟩ := (Finset.mem_erase.mp hk₁_mem).1
          have hk₁_val_ne : k₁.val ≠ 0 := fun he => hk₁_ne (Fin.ext he)
          have hk₂_ne : k₂ ≠ ⟨0, hK_pos⟩ := (Finset.mem_erase.mp hk₂_mem).1
          have hk₂_val_ne : k₂.val ≠ 0 := fun he => hk₂_ne (Fin.ext he)
          have hval_eq : k₁.val - 1 = k₂.val - 1 := congrArg Fin.val heq
          apply Fin.ext
          omega
        · -- surjectivity
          intro j hj_mem
          rw [Finset.mem_filter] at hj_mem
          have hj_succ_lt : j.val + 1 < K := hj_mem.2
          refine ⟨⟨j.val + 1, hj_succ_lt⟩, ?_, ?_⟩
          · rw [Finset.mem_erase]
            refine ⟨?_, Finset.mem_univ _⟩
            intro heq
            have hval : j.val + 1 = 0 := congrArg Fin.val heq
            omega
          · apply Fin.ext
            show j.val + 1 - 1 = j.val
            omega
        · -- value matches
          intro k hk_mem
          have hk_ne : k ≠ ⟨0, hK_pos⟩ := (Finset.mem_erase.mp hk_mem).1
          have hk_val_ne : k.val ≠ 0 := fun he => hk_ne (Fin.ext he)
          simp only [hcmp_def, hk_val_ne, ↓reduceDIte]
      rw [h_rest_eq]
  -- Use: L1T₁ + ∑_{filter} L1 k ≤ L1T₁ + ∑ all L1 k = L1T₁ + L¹_{(T₀∪T₁)ᶜ}.
  have h_filter_le_all : ∑ k ∈ Finset.univ.filter
      (fun k : Fin K => k.val + 1 < K), L1 k ≤ ∑ k, L1 k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intros; exact hL1_nn _
  -- ∑ k, L1 k = L¹_{(T₀∪T₁)ᶜ} via biUnion.
  -- This requires that the blocks are disjoint, which we have (hB_disj).
  -- But the present hypothesis name is `_hB_disj` with underscore.  Use ∑ over biUnion
  -- of disjoint blocks = ∑ over each block.
  have h_sum_L1_eq : ∑ k, L1 k = ∑ i ∈ ((T₀ ∪ T₁)ᶜ : Finset (Fin n)), |h i| := by
    simp only [hL1_def]
    -- Pairwise disjoint over the Finset.univ.
    have hpairwise : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint B := by
      intro k₁ _ k₂ _ hne
      exact _hB_disj k₁ k₂ hne
    rw [← Finset.sum_biUnion hpairwise, hB_union]
  -- Combine: ∑ k, cmp k ≤ L1T₁ + ∑ all L1 k = L1T₁ + L¹_{(T₀∪T₁)ᶜ}.
  have h_SumCmp_le : SumCmp ≤ L1T₁ + ∑ i ∈ ((T₀ ∪ T₁)ᶜ : Finset (Fin n)), |h i| := by
    rw [← h_sum_L1_eq]
    calc SumCmp ≤ L1T₁ + ∑ k ∈ Finset.univ.filter
                  (fun k : Fin K => k.val + 1 < K), L1 k := h_SumCmp_bound
      _ ≤ L1T₁ + ∑ k, L1 k := by linarith
  -- T₁ ⊆ T₀ᶜ and (T₀∪T₁)ᶜ ⊆ T₀ᶜ disjointly, so L1T₁ + L¹_{(T₀∪T₁)ᶜ} = L¹_{T₀ᶜ}.
  have hT₁_sub_T₀c : T₁ ⊆ T₀ᶜ := by
    intro i hi
    simp only [Finset.mem_compl]
    exact Finset.disjoint_right.mp _hT₀T₁ hi
  have hUc_disjoint_T₁ : Disjoint ((T₀ ∪ T₁)ᶜ : Finset (Fin n)) T₁ := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    simp only [Finset.mem_compl, Finset.mem_union] at hi₁
    exact hi₁ (Or.inr hi₂)
  have h_partition_set : ((T₀ ∪ T₁)ᶜ : Finset (Fin n)) ∪ T₁ = (T₀ : Finset (Fin n))ᶜ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_union]
    constructor
    · rintro (h₁ | h₂)
      · intro hT₀; exact h₁ (Or.inl hT₀)
      · intro hT₀; exact (Finset.disjoint_left.mp _hT₀T₁ hT₀) h₂
    · intro hT₀
      by_cases hT₁ : i ∈ T₁
      · exact Or.inr hT₁
      · exact Or.inl (fun hor => hor.elim hT₀ hT₁)
  have h_split_T₀c : ∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i| =
      ∑ i ∈ ((T₀ ∪ T₁)ᶜ : Finset (Fin n)), |h i| + L1T₁ := by
    rw [hL1T₁_def, ← Finset.sum_union hUc_disjoint_T₁, h_partition_set]
  -- Final combine.
  have h_SumCmp_le_T₀c : SumCmp ≤ ∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i| := by
    rw [h_split_T₀c]; linarith
  -- Conclude.
  calc ∑ k, Real.sqrt (∑ i ∈ B k, (h i) ^ 2)
      ≤ SumCmp / Real.sqrt s := h_sum_bound
    _ ≤ (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) / Real.sqrt s := by
        exact div_le_div_of_nonneg_right h_SumCmp_le_T₀c hsqrt_s_nn
    _ = (Real.sqrt s)⁻¹ * (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) := by
        rw [div_eq_inv_mul]

-- Raise heartbeats: the proof of block_inner_product_bound chains many
-- nlinarith / Cauchy-Schwarz / AM-GM steps over ℝ-valued auxiliaries.
set_option maxHeartbeats 800000 in
/-- **R6 helper (Foucart–Rauhut Cor 6.13, inner-product bound)**:
the analytic heart of Candès–Tao 2005 / Candès 2008.

For an `(s + s')`-RIP matrix `A`, an `s`-sparse vector `g`, and a
remainder `r` supported disjointly from `g` (with `r` arising as
`h|_{Sᶜ}` for some `h` and `S ⊇ supp g`), the block-decomposition of
`Sᶜ` into pieces of size `≤ s'` sorted by `|h|` gives the bound

  `|⟨A g, A r⟩| ≤ √2 · δ · ‖g‖₂² ` (Foucart–Rauhut Cor 6.13)

after combining restricted orthogonality on each `(g, r|_{B_k})` pair
with the telescoping sparse-tail inequality.

The `√2` factor is the Foucart–Rauhut tightening obtained by splitting
`g = h|_{T₀} + h|_{T₁}` and applying `√(a² + b²) ≤ √2 · max(a, b)` to
combine the two telescoping bounds — this yields the recovery
threshold `δ < √2 − 1` (sharper than the `δ < 1/3` of the original
Candès–Tao 2005).

**Hypothesis fix (2026-05-17)**: the bound `√2 · δ · G2` (with `G2 = ‖g‖²`)
is mathematically false **without** a cone-type assumption controlling the
`ℓ¹` mass of `h` on `(T₀ ∪ T₁)ᶜ` by its mass on `T₀`.  A direct
counterexample with `h ≡ 1` shows the right-hand side fails to absorb the
remainder term `R2/G2`, which can be arbitrarily large in the presence of
2s-RIP alone.  We therefore add the **cone constraint**
`∑_{T₀ᶜ} |h| ≤ ∑_{T₀} |h|` as an explicit hypothesis, matching the
context in which the lemma is consumed by `candes_2008_kernel_contraction`.

The proof itself is decomposed as:
* Step 1 — block-decompose `(T₀ ∪ T₁)ᶜ` via `exists_block_partition`,
* Step 2 — split `g = h|_{T₀} + h|_{T₁}` and apply
  `rip_restricted_orthogonality` block-by-block,
* Step 3 — telescope via `block_l2_telescope`,
* Step 4 — combine with cone + Cauchy-Schwarz to absorb the `(√s)⁻¹ · ‖h‖_{T₀ᶜ,1}`
  factor into `√G2`,
* Step 5 — final `√(a²+b²) ≤ √2 · √(a²+b²)` yields the `√2` factor.

**Status**: fully proved (2026-05-17).  `block_l2_telescope` was closed
the same day via direct per-block AM-GM plus a `Finset.sum_bij`
reindexing of the comparison-block sum, completing the Candès 2008 chain.
The heartbeat limit is raised because the proof chains together
Cauchy–Schwarz, AM–GM, restricted orthogonality, and the telescope bound
through many ℝ-valued auxiliaries. -/
theorem block_inner_product_bound
    {A : Matrix (Fin m) (Fin n) ℝ} {s : ℕ} {δ : ℝ}
    (hRIP : IsRIP A (2 * s) δ) (hδ_pos : 0 < δ)
    (hs_pos : 1 ≤ s)
    {h : Fin n → ℝ} (T₀ T₁ : Finset (Fin n))
    (hT₀T₁_disj : Disjoint T₀ T₁) (hT₀_card : T₀.card ≤ s)
    (hT₁_card : T₁.card = s)
    (h_T₁_largest :
      ∀ i ∈ T₁, ∀ j ∈ (T₀ ∪ T₁)ᶜ, |h j| ≤ |h i|)
    (h_cone : (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ≤ (∑ i ∈ T₀, |h i|)) :
    |∑ i, (A.mulVec (restrictTo (T₀ ∪ T₁) h)) i *
          (A.mulVec (restrictTo (T₀ ∪ T₁)ᶜ h)) i| ≤
      Real.sqrt 2 * δ * (∑ i, (restrictTo (T₀ ∪ T₁) h i) ^ 2) := by
  classical
  -- Reduce 2s-RIP to (s+s)-RIP (definitionally equal: 2*s = s+s).
  have hRIP' : IsRIP A (s + s) δ := by
    have : s + s = 2 * s := by ring
    rw [this]; exact hRIP
  -- Setup: S = T₀ ∪ T₁, g = h|_S, r = h|_{Sᶜ}.
  set S : Finset (Fin n) := T₀ ∪ T₁ with hS_def
  set g : Fin n → ℝ := restrictTo S h with hg_def
  set r : Fin n → ℝ := restrictTo Sᶜ h with hr_def
  set G2 : ℝ := ∑ i, (g i) ^ 2 with hG2_def
  have hG2_nn : 0 ≤ G2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Split g = g₀ + g₁ where g_j := h|_{T_j}.
  set g0 : Fin n → ℝ := restrictTo T₀ h with hg0_def
  set g1 : Fin n → ℝ := restrictTo T₁ h with hg1_def
  have hg0_sparse : IsSSparse g0 s :=
    (restrictTo_isSSparse T₀ h).mono hT₀_card
  have hg1_sparse : IsSSparse g1 s := by
    have := restrictTo_isSSparse T₁ h
    rw [hT₁_card] at this; exact this
  -- g = g0 + g1 (since T₀, T₁ disjoint and S = T₀ ∪ T₁).
  have hg_split : g = g0 + g1 := by
    funext i
    simp only [hg_def, hg0_def, hg1_def, Pi.add_apply, restrictTo, hS_def,
      Finset.mem_union]
    by_cases hi₀ : i ∈ T₀
    · have hi₁ : i ∉ T₁ := Finset.disjoint_left.mp hT₀T₁_disj hi₀
      simp [hi₀, hi₁]
    · by_cases hi₁ : i ∈ T₁
      · simp [hi₀, hi₁]
      · simp [hi₀, hi₁]
  -- Block-decompose (T₀ ∪ T₁)ᶜ via exists_block_partition.
  obtain ⟨K, B, hB_sub, hB_disj, hB_union, hB_card, hB_sorted, hB_full, _⟩ :=
    exists_block_partition h Sᶜ hs_pos
  -- Each r_k := restrictTo (B k) h is s-sparse.
  set r_blk : Fin K → Fin n → ℝ := fun k => restrictTo (B k) h with hr_blk_def
  have hr_blk_sparse : ∀ k, IsSSparse (r_blk k) s := fun k =>
    (restrictTo_isSSparse (B k) h).mono (hB_card k)
  -- r = ∑_k r_blk k.
  have hr_sum : r = ∑ k, r_blk k := by
    funext i
    simp only [Finset.sum_apply, hr_blk_def]
    by_cases hi : i ∈ (S : Finset (Fin n))ᶜ
    · rw [hr_def, restrictTo_apply_mem hi]
      have hi' : i ∈ Finset.univ.biUnion B := by rw [hB_union]; exact hi
      obtain ⟨k, _, hk_in⟩ := Finset.mem_biUnion.mp hi'
      have h_one : ∀ k', k' ≠ k → restrictTo (B k') h i = 0 := by
        intro k' hne
        have hdisj : Disjoint (B k') (B k) := hB_disj k' k hne
        have hi_not : i ∉ B k' := by
          intro hi_in
          exact (Finset.disjoint_left.mp hdisj hi_in) hk_in
        exact restrictTo_apply_not_mem hi_not
      have hkey : restrictTo (B k) h i = h i := restrictTo_apply_mem hk_in
      have : ∑ k', restrictTo (B k') h i =
              restrictTo (B k) h i + ∑ k' ∈ Finset.univ.erase k, restrictTo (B k') h i := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]; ring
      rw [this]
      have hzero : ∑ k' ∈ Finset.univ.erase k, restrictTo (B k') h i = 0 := by
        apply Finset.sum_eq_zero
        intro k' hk'
        exact h_one k' (Finset.mem_erase.mp hk').1
      rw [hzero, add_zero, hkey]
    · rw [hr_def, restrictTo_apply_not_mem hi]
      symm
      apply Finset.sum_eq_zero
      intro k _
      have hi_not : i ∉ B k := fun hi_in => hi (hB_sub k hi_in)
      exact restrictTo_apply_not_mem hi_not
  -- Disjoint supports between g0/g1 and each r_blk k.
  have hg0_r_disj : ∀ k i, g0 i ≠ 0 → r_blk k i = 0 := by
    intro k i hi
    have : i ∈ T₀ := by
      by_contra h_not
      apply hi
      exact restrictTo_apply_not_mem h_not
    have : i ∉ B k := by
      intro hi_B
      have : i ∈ Sᶜ := hB_sub k hi_B
      rw [Finset.mem_compl, hS_def] at this
      exact this (Finset.mem_union_left _ ‹i ∈ T₀›)
    exact restrictTo_apply_not_mem this
  have hg1_r_disj : ∀ k i, g1 i ≠ 0 → r_blk k i = 0 := by
    intro k i hi
    have : i ∈ T₁ := by
      by_contra h_not
      apply hi
      exact restrictTo_apply_not_mem h_not
    have : i ∉ B k := by
      intro hi_B
      have : i ∈ Sᶜ := hB_sub k hi_B
      rw [Finset.mem_compl, hS_def] at this
      exact this (Finset.mem_union_right _ ‹i ∈ T₁›)
    exact restrictTo_apply_not_mem this
  -- Per-block bound (g0 side): |⟨A g0, A r_blk k⟩| ≤ δ · √G0 · √R_k.
  have h_block_g0 : ∀ k,
      |∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i| ≤
        δ * Real.sqrt (∑ i, (g0 i) ^ 2) *
            Real.sqrt (∑ i, (r_blk k i) ^ 2) := fun k =>
    rip_restricted_orthogonality hRIP' hg0_sparse (hr_blk_sparse k) (hg0_r_disj k)
  have h_block_g1 : ∀ k,
      |∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i| ≤
        δ * Real.sqrt (∑ i, (g1 i) ^ 2) *
            Real.sqrt (∑ i, (r_blk k i) ^ 2) := fun k =>
    rip_restricted_orthogonality hRIP' hg1_sparse (hr_blk_sparse k) (hg1_r_disj k)
  set G0 : ℝ := ∑ i, (g0 i) ^ 2 with hG0_def
  set G1 : ℝ := ∑ i, (g1 i) ^ 2 with hG1_def
  have hG0_nn : 0 ≤ G0 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG1_nn : 0 ≤ G1 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsqrt_G0_nn : 0 ≤ Real.sqrt G0 := Real.sqrt_nonneg _
  have hsqrt_G1_nn : 0 ≤ Real.sqrt G1 := Real.sqrt_nonneg _
  -- Key: G0 + G1 = G2 (disjoint support of T₀, T₁; S = T₀ ∪ T₁).
  have hG0G1_eq_G2 : G0 + G1 = G2 := by
    have : ∑ i, (g0 i + g1 i) ^ 2 = G2 := by
      rw [hG2_def, hg_def]
      apply Finset.sum_congr rfl
      intro i _
      have hpt : g0 i + g1 i = g i := by rw [hg_split]; rfl
      rw [hpt]
    have hcross : ∀ i, g0 i * g1 i = 0 := by
      intro i
      by_cases hi₀ : i ∈ T₀
      · have hi₁ : i ∉ T₁ := Finset.disjoint_left.mp hT₀T₁_disj hi₀
        rw [hg1_def, restrictTo_apply_not_mem hi₁, mul_zero]
      · rw [hg0_def, restrictTo_apply_not_mem hi₀, zero_mul]
    have hexpand : ∀ i, (g0 i + g1 i) ^ 2 = (g0 i) ^ 2 + (g1 i) ^ 2 := by
      intro i; have := hcross i; nlinarith [this]
    rw [show (∑ i, (g0 i + g1 i) ^ 2) = ∑ i, ((g0 i)^2 + (g1 i)^2) from
        Finset.sum_congr rfl (fun i _ => hexpand i)] at this
    rw [Finset.sum_add_distrib] at this
    rw [hG0_def, hG1_def]; exact this
  -- Decompose ⟨A g, A r⟩ along the block partition + g0/g1 split.
  have h_Ag_split : A.mulVec g = A.mulVec g0 + A.mulVec g1 := by
    rw [hg_split, Matrix.mulVec_add]
  have h_Ar_split : A.mulVec r = ∑ k, A.mulVec (r_blk k) := by
    rw [hr_sum]; exact mulVec_finset_sum A r_blk
  have h_inner_decompose :
      ∑ i, (A.mulVec g) i * (A.mulVec r) i =
        ∑ k, (∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i) +
        ∑ k, (∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i) := by
    rw [h_Ag_split, h_Ar_split]
    simp only [Pi.add_apply, Finset.sum_apply]
    have step1 : ∀ i, ((A.mulVec g0) i + (A.mulVec g1) i) *
                      (∑ k, A.mulVec (r_blk k) i) =
                ∑ k, ((A.mulVec g0) i * (A.mulVec (r_blk k)) i +
                      (A.mulVec g1) i * (A.mulVec (r_blk k)) i) := by
      intro i; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [Finset.sum_congr rfl (fun i _ => step1 i)]
    rw [Finset.sum_comm]
    have step2 : ∀ k, (∑ i, ((A.mulVec g0) i * (A.mulVec (r_blk k)) i +
                              (A.mulVec g1) i * (A.mulVec (r_blk k)) i)) =
                   (∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i) +
                   (∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i) := by
      intro k; exact Finset.sum_add_distrib
    rw [Finset.sum_congr rfl (fun k _ => step2 k)]
    rw [Finset.sum_add_distrib]
  -- Telescope: ∑_k √(∑_{B_k} h²) ≤ (√s)⁻¹ · ‖h‖_{T₀ᶜ,1}.
  have h_r_blk_sum_sq : ∀ k, (∑ i, (r_blk k i) ^ 2) = ∑ i ∈ B k, (h i) ^ 2 := by
    intro k; rw [hr_blk_def]; exact restrictTo_sum_sq (B k) h
  set Sk_r : ℝ := ∑ k, Real.sqrt (∑ i, (r_blk k i) ^ 2) with hSk_r_def
  have hSk_r_eq : Sk_r = ∑ k, Real.sqrt (∑ i ∈ B k, (h i) ^ 2) := by
    rw [hSk_r_def]
    apply Finset.sum_congr rfl
    intro k _; rw [h_r_blk_sum_sq k]
  have hSk_r_nn : 0 ≤ Sk_r :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have h_telescope : Sk_r ≤ (Real.sqrt s)⁻¹ * (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) := by
    rw [hSk_r_eq]
    have hB_sub' : ∀ k, B k ⊆ ((T₀ ∪ T₁)ᶜ : Finset (Fin n)) := hB_sub
    have hB_union' : Finset.univ.biUnion B = ((T₀ ∪ T₁)ᶜ : Finset (Fin n)) := hB_union
    exact block_l2_telescope hs_pos h T₀ T₁ hT₀T₁_disj hT₁_card h_T₁_largest
      B hB_sub' hB_disj hB_union' hB_card hB_sorted hB_full
  -- Per-side aggregated bound.
  have h_side_bound_g0 :
      ∑ k, |∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i| ≤
        δ * Real.sqrt G0 * Sk_r := by
    have h1 : ∑ k, |∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i| ≤
              ∑ k, δ * Real.sqrt G0 *
                Real.sqrt (∑ i, (r_blk k i) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      have hb := h_block_g0 k
      rw [hG0_def]; exact hb
    have h2 : ∑ k, δ * Real.sqrt G0 *
                Real.sqrt (∑ i, (r_blk k i) ^ 2) =
              δ * Real.sqrt G0 * Sk_r := by
      rw [← Finset.mul_sum]
    linarith
  have h_side_bound_g1 :
      ∑ k, |∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i| ≤
        δ * Real.sqrt G1 * Sk_r := by
    have h1 : ∑ k, |∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i| ≤
              ∑ k, δ * Real.sqrt G1 *
                Real.sqrt (∑ i, (r_blk k i) ^ 2) := by
      apply Finset.sum_le_sum
      intro k _
      have hb := h_block_g1 k
      rw [hG1_def]; exact hb
    have h2 : ∑ k, δ * Real.sqrt G1 *
                Real.sqrt (∑ i, (r_blk k i) ^ 2) =
              δ * Real.sqrt G1 * Sk_r := by
      rw [← Finset.mul_sum]
    linarith
  -- Combined inner-product bound (triangle + per-side).
  have h_inner_le :
      |∑ i, (A.mulVec g) i * (A.mulVec r) i| ≤
        δ * (Real.sqrt G0 + Real.sqrt G1) * Sk_r := by
    rw [h_inner_decompose]
    set X : ℝ := ∑ k, ∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i with hX_def
    set Y : ℝ := ∑ k, ∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i with hY_def
    have h_tri : |X + Y| ≤ |X| + |Y| := by
      have h1 : X + Y ≤ |X| + |Y| := add_le_add (le_abs_self _) (le_abs_self _)
      have h2 : -(X + Y) ≤ |X| + |Y| := by
        have := add_le_add (neg_le_abs X) (neg_le_abs Y); linarith
      exact abs_le.mpr ⟨by linarith, h1⟩
    have h_abs_sum_le_g0 : |X| ≤ ∑ k, |∑ i, (A.mulVec g0) i * (A.mulVec (r_blk k)) i| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_abs_sum_le_g1 : |Y| ≤ ∑ k, |∑ i, (A.mulVec g1) i * (A.mulVec (r_blk k)) i| :=
      Finset.abs_sum_le_sum_abs _ _
    nlinarith [h_tri, h_abs_sum_le_g0, h_abs_sum_le_g1,
               h_side_bound_g0, h_side_bound_g1, hSk_r_nn, hδ_pos.le,
               hsqrt_G0_nn, hsqrt_G1_nn]
  -- Cauchy-Schwarz: √G0 + √G1 ≤ √2 · √G2.
  have h_sqrt_add_le : Real.sqrt G0 + Real.sqrt G1 ≤ Real.sqrt 2 * Real.sqrt G2 := by
    have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
    have hsqrt2_nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsqrtG2_nn : 0 ≤ Real.sqrt G2 := Real.sqrt_nonneg _
    have hlhs_nn : 0 ≤ Real.sqrt G0 + Real.sqrt G1 := by positivity
    have hrhs_nn : 0 ≤ Real.sqrt 2 * Real.sqrt G2 := mul_nonneg hsqrt2_nn hsqrtG2_nn
    have hsq_le : (Real.sqrt G0 + Real.sqrt G1) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt G2) ^ 2 := by
      have hG0_sq : (Real.sqrt G0) ^ 2 = G0 := Real.sq_sqrt hG0_nn
      have hG1_sq : (Real.sqrt G1) ^ 2 = G1 := Real.sq_sqrt hG1_nn
      have hG2_sq : (Real.sqrt G2) ^ 2 = G2 := Real.sq_sqrt hG2_nn
      have h2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt h2_nn
      have hmul_sq : (Real.sqrt 2 * Real.sqrt G2) ^ 2 = 2 * G2 := by
        rw [mul_pow, h2_sq, hG2_sq]
      have h_sum_sq : (Real.sqrt G0 + Real.sqrt G1) ^ 2 =
                      G0 + G1 + 2 * (Real.sqrt G0 * Real.sqrt G1) := by
        rw [add_pow_two, hG0_sq, hG1_sq]; ring
      rw [hmul_sq, h_sum_sq, ← hG0G1_eq_G2]
      have hAMGM : 2 * (Real.sqrt G0 * Real.sqrt G1) ≤ G0 + G1 := by
        have : 0 ≤ (Real.sqrt G0 - Real.sqrt G1) ^ 2 := sq_nonneg _
        have hG0_sq : (Real.sqrt G0) ^ 2 = G0 := Real.sq_sqrt hG0_nn
        have hG1_sq : (Real.sqrt G1) ^ 2 = G1 := Real.sq_sqrt hG1_nn
        nlinarith [this, hG0_sq, hG1_sq]
      linarith
    exact (abs_le_of_sq_le_sq' hsq_le hrhs_nn).2
  -- Cone + Cauchy-Schwarz on T₀: ‖h‖_{T₀ᶜ,1} ≤ √s · √G0.
  have hs_real_pos : (0 : ℝ) < s := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hs_pos
  have hs_real_nn : (0 : ℝ) ≤ s := le_of_lt hs_real_pos
  have hsqrt_s_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_real_pos
  have hsqrt_s_nn : 0 ≤ Real.sqrt s := le_of_lt hsqrt_s_pos
  have h_T₀_CS : (∑ i ∈ T₀, |h i|) ^ 2 ≤ s * ∑ i ∈ T₀, (h i) ^ 2 := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq T₀ (fun _ => (1 : ℝ)) (fun i => |h i|)
    have hL : ∑ i ∈ T₀, (1 : ℝ) * |h i| = ∑ i ∈ T₀, |h i| := by
      apply Finset.sum_congr rfl; intros; ring
    have hR : ∑ i ∈ T₀, (1 : ℝ) ^ 2 = (T₀.card : ℝ) := by
      rw [show (fun i : Fin n => (1 : ℝ) ^ 2) = (fun _ : Fin n => (1 : ℝ)) from by
        funext; ring]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hL, hR] at hCS
    have h3 : ∑ i ∈ T₀, |h i| ^ 2 = ∑ i ∈ T₀, (h i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => sq_abs (h i))
    rw [h3] at hCS
    have hT₀_card_real : ((T₀.card : ℝ)) ≤ s := by exact_mod_cast hT₀_card
    have hsumsq_nn : 0 ≤ ∑ i ∈ T₀, (h i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h4 : (T₀.card : ℝ) * ∑ i ∈ T₀, (h i) ^ 2 ≤ s * ∑ i ∈ T₀, (h i) ^ 2 :=
      mul_le_mul_of_nonneg_right hT₀_card_real hsumsq_nn
    linarith
  have h_T₀_sumsq_eq_G0 : ∑ i ∈ T₀, (h i) ^ 2 = G0 := by
    rw [hG0_def, hg0_def]; rw [restrictTo_sum_sq]
  have h_sumT₀_nn : 0 ≤ ∑ i ∈ T₀, |h i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_sumT₀c_nn : 0 ≤ ∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_T₀c_bound_sq : (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ^ 2 ≤ s * G0 := by
    have h_cone_sq : (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ^ 2 ≤
                     (∑ i ∈ T₀, |h i|) ^ 2 := by
      have hmul := mul_self_le_mul_self h_sumT₀c_nn h_cone
      rw [sq, sq]; exact hmul
    have h_T₀_sq_le : (∑ i ∈ T₀, |h i|) ^ 2 ≤ s * G0 := by
      rw [← h_T₀_sumsq_eq_G0]; exact h_T₀_CS
    exact le_trans h_cone_sq h_T₀_sq_le
  have h_T₀c_le_sqrt : (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ≤
                       Real.sqrt s * Real.sqrt G0 := by
    have hrhs_nn : 0 ≤ Real.sqrt s * Real.sqrt G0 :=
      mul_nonneg hsqrt_s_nn hsqrt_G0_nn
    have hrhs_sq : (Real.sqrt s * Real.sqrt G0) ^ 2 = s * G0 := by
      rw [mul_pow, Real.sq_sqrt hs_real_nn, Real.sq_sqrt hG0_nn]
    have hsq_le : (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ^ 2 ≤
                  (Real.sqrt s * Real.sqrt G0) ^ 2 := by
      rw [hrhs_sq]; exact h_T₀c_bound_sq
    exact (abs_le_of_sq_le_sq' hsq_le hrhs_nn).2
  -- Sk_r ≤ √G0 ≤ √G2.
  have hSk_r_le_sqrt_G0 : Sk_r ≤ Real.sqrt G0 := by
    have hstep : (Real.sqrt s)⁻¹ * (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) ≤
                 (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt G0) :=
      mul_le_mul_of_nonneg_left h_T₀c_le_sqrt (inv_nonneg.mpr hsqrt_s_nn)
    have hsimp : (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt G0) = Real.sqrt G0 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrt_s_pos), one_mul]
    calc Sk_r
        ≤ (Real.sqrt s)⁻¹ * (∑ i ∈ (T₀ : Finset (Fin n))ᶜ, |h i|) := h_telescope
      _ ≤ (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt G0) := hstep
      _ = Real.sqrt G0 := hsimp
  have hsqrt_G0_le_G2 : Real.sqrt G0 ≤ Real.sqrt G2 :=
    Real.sqrt_le_sqrt (by linarith [hG0G1_eq_G2, hG1_nn])
  have hSk_r_le_sqrt_G2 : Sk_r ≤ Real.sqrt G2 := le_trans hSk_r_le_sqrt_G0 hsqrt_G0_le_G2
  -- Final: combine all bounds into √2 · δ · G2.
  have hG2_sqrt_sq : Real.sqrt G2 * Real.sqrt G2 = G2 :=
    Real.mul_self_sqrt hG2_nn
  have h_chain : δ * (Real.sqrt G0 + Real.sqrt G1) * Sk_r ≤
                 Real.sqrt 2 * δ * G2 := by
    have hδ_nn : 0 ≤ δ := hδ_pos.le
    have hsqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hSk_r_nn' : 0 ≤ Sk_r := hSk_r_nn
    have hsqrtG2_nn : 0 ≤ Real.sqrt G2 := Real.sqrt_nonneg _
    have h_left_factor : Real.sqrt G0 + Real.sqrt G1 ≤ Real.sqrt 2 * Real.sqrt G2 :=
      h_sqrt_add_le
    have h_step1 : δ * (Real.sqrt G0 + Real.sqrt G1) * Sk_r ≤
                   δ * (Real.sqrt 2 * Real.sqrt G2) * Real.sqrt G2 := by
      have hL : 0 ≤ δ * (Real.sqrt G0 + Real.sqrt G1) :=
        mul_nonneg hδ_nn (by linarith [hsqrt_G0_nn, hsqrt_G1_nn])
      have hL2 : 0 ≤ δ * (Real.sqrt 2 * Real.sqrt G2) :=
        mul_nonneg hδ_nn (mul_nonneg hsqrt2_nn hsqrtG2_nn)
      nlinarith [mul_le_mul h_left_factor hSk_r_le_sqrt_G2 hSk_r_nn'
                  (mul_nonneg hsqrt2_nn hsqrtG2_nn), hδ_nn, hSk_r_nn']
    have h_step2 : δ * (Real.sqrt 2 * Real.sqrt G2) * Real.sqrt G2 =
                   Real.sqrt 2 * δ * G2 := by
      rw [show δ * (Real.sqrt 2 * Real.sqrt G2) * Real.sqrt G2 =
              Real.sqrt 2 * δ * (Real.sqrt G2 * Real.sqrt G2) by ring,
          hG2_sqrt_sq]
    linarith
  linarith [h_inner_le, h_chain]

-- Raise heartbeats: the proof chains many nlinarith calls over ℝ-valued auxiliaries.
set_option maxHeartbeats 800000 in
/-- **Block-decomposition analytic core of Candès 2008**.  This packages the
analytic step that for a 2s-RIP matrix `A` and a vector `h ∈ ker A` satisfying
the cone constraint, in the non-degenerate regime `s ≥ 1, n > 2s`, the
restricted vector `restrictTo (T₀⁺ ∪ T₁) h` has zero `ℓ²` norm.

The proof (Foucart–Rauhut Theorem 6.9 / Candès 2008) partitions the support
outside `T₀⁺ ∪ T₁` into blocks of size `s` sorted by `|h|`, applies restricted
orthogonality (`rip_restricted_orthogonality`) to each block, telescopes the
bounds via the sparse-tail inequality (`sparse_tail_bound`), and extracts a
contraction `(1 − (√2+1)δ) ‖g‖² ≤ 0` which under `δ < √2 − 1` forces `g = 0`.

Raised heartbeats: the proof chains together Cauchy–Schwarz, the cone
constraint, the sparse-tail bound and the RIP contraction, exercising
`nlinarith` over many ℝ-valued auxiliaries. -/
theorem candes_2008_kernel_contraction
    {A : Matrix (Fin m) (Fin n) ℝ} {s : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt : δ < l1RecoveryThreshold)
    (hRIP : IsRIP A (2 * s) δ)
    {h : Fin n → ℝ} (hh_ker : A.mulVec h = 0)
    (T₀ : Finset (Fin n)) (hT₀_card : T₀.card ≤ s)
    (h_cone : (∑ i ∈ T₀ᶜ, |h i|) ≤ (∑ i ∈ T₀, |h i|))
    (hs_pos : 1 ≤ s) (hn_large : 2 * s < n) :
    h = 0 := by
  classical
  -- ============================================================================
  -- Step 1: select `T₁ ⊆ T₀ᶜ` of cardinality `s` capturing top-`s` `|h|` entries.
  -- ============================================================================
  have hT₀c_card : (T₀ᶜ : Finset (Fin n)).card = n - T₀.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hs_le_T₀c : s ≤ (T₀ᶜ : Finset (Fin n)).card := by
    rw [hT₀c_card]; omega
  obtain ⟨T₁, hT₁_sub, hT₁_card, hT₁_largest_sdiff⟩ :=
    exists_top_k_by_abs h T₀ᶜ s hs_le_T₀c
  -- Convert `hT₁_largest_sdiff : ∀ i ∈ T₁, ∀ j ∈ T₀ᶜ \ T₁, ...` to
  -- the form needed by `sparse_tail_bound`: `∀ i ∈ T₁, ∀ j ∈ (T₀ ∪ T₁)ᶜ, ...`.
  have hT₀T₁_disj : Disjoint T₀ T₁ := by
    rw [Finset.disjoint_right]
    intro i hi
    exact (Finset.mem_compl.mp (hT₁_sub hi))
  have hT₁_largest : ∀ i ∈ T₁, ∀ j ∈ (T₀ ∪ T₁)ᶜ, |h j| ≤ |h i| := by
    intro i hi j hj
    apply hT₁_largest_sdiff i hi
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · -- j ∈ T₀ᶜ since j ∉ T₀ ∪ T₁ ⟹ j ∉ T₀.
      rw [Finset.mem_compl]
      intro hjT₀
      exact (Finset.mem_compl.mp hj) (Finset.mem_union_left _ hjT₀)
    · intro hjT₁
      exact (Finset.mem_compl.mp hj) (Finset.mem_union_right _ hjT₁)
  -- ============================================================================
  -- Step 2: define `g := h|_{T₀ ∪ T₁}` (2s-sparse) and `r := h|_{(T₀∪T₁)ᶜ}`.
  -- ============================================================================
  set S : Finset (Fin n) := T₀ ∪ T₁ with hS_def
  have hS_card : S.card ≤ 2 * s := by
    rw [hS_def, Finset.card_union_of_disjoint hT₀T₁_disj, hT₁_card]
    omega
  set g : Fin n → ℝ := restrictTo S h with hg_def
  set r : Fin n → ℝ := restrictTo Sᶜ h with hr_def
  have hg_sparse : IsSSparse g (2 * s) :=
    (restrictTo_isSSparse S h).mono hS_card
  have hg_add_r : g + r = h := restrictTo_add_compl S h
  set G2 : ℝ := ∑ i, (g i) ^ 2 with hG2_def
  set R2 : ℝ := ∑ i, (r i) ^ 2 with hR2_def
  have hG2_eq : G2 = ∑ i ∈ S, (h i) ^ 2 := restrictTo_sum_sq S h
  have hR2_eq : R2 = ∑ i ∈ Sᶜ, (h i) ^ 2 := restrictTo_sum_sq Sᶜ h
  have hG2_nn : 0 ≤ G2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR2_nn : 0 ≤ R2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- ============================================================================
  -- Step 3: Sparse tail bound: √R2 ≤ (√s)⁻¹ · ∑_{T₀ᶜ} |h|.
  -- ============================================================================
  have hSc_eq : (Sᶜ : Finset (Fin n)) = (T₀ ∪ T₁)ᶜ := rfl
  have h_tail : Real.sqrt R2 ≤ (Real.sqrt s)⁻¹ * (∑ i ∈ T₀ᶜ, |h i|) := by
    rw [hR2_eq, hSc_eq]
    exact sparse_tail_bound hs_pos h T₀ T₁ hT₀T₁_disj hT₁_card hT₁_largest
  -- ============================================================================
  -- Step 4: Cauchy-Schwarz + cone: ∑_{T₀ᶜ} |h| ≤ √s · √G2, hence R2 ≤ G2.
  -- ============================================================================
  have hs_real_pos : (0 : ℝ) < s := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hs_pos
  have hs_real_nn : (0 : ℝ) ≤ s := le_of_lt hs_real_pos
  have hsqrt_s_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_real_pos
  have hsqrt_s_nn : 0 ≤ Real.sqrt s := le_of_lt hsqrt_s_pos
  have hT₀_card_real : ((T₀.card : ℝ)) ≤ s := by exact_mod_cast hT₀_card
  -- Cauchy-Schwarz: `(∑_{T₀} |h|)² ≤ |T₀| · ∑_{T₀} h² ≤ s · ∑_{T₀} h²`.
  -- Via `Finset.sum_mul_sq_le_sq_mul_sq` with f ≡ 1, g = |h|.
  have h_CS_T₀ : (∑ i ∈ T₀, |h i|) ^ 2 ≤ s * ∑ i ∈ T₀, (h i) ^ 2 := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq T₀ (fun _ => (1 : ℝ)) (fun i => |h i|)
    -- hCS : (∑ i ∈ T₀, 1 * |h i|)^2 ≤ (∑ i ∈ T₀, 1^2) * ∑ i ∈ T₀, |h i|^2
    have hCS' : (∑ i ∈ T₀, |h i|) ^ 2 ≤ (T₀.card : ℝ) * ∑ i ∈ T₀, |h i| ^ 2 := by
      have hL : ∑ i ∈ T₀, (1 : ℝ) * |h i| = ∑ i ∈ T₀, |h i| := by
        apply Finset.sum_congr rfl; intros; ring
      have hR : ∑ i ∈ T₀, (1 : ℝ) ^ 2 = (T₀.card : ℝ) := by
        rw [show (fun i : Fin n => (1 : ℝ) ^ 2) = (fun _ : Fin n => (1 : ℝ)) from by
          funext; ring]
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hL, hR] at hCS
      exact hCS
    have h3 : ∑ i ∈ T₀, |h i| ^ 2 = ∑ i ∈ T₀, (h i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => sq_abs (h i))
    rw [h3] at hCS'
    have hsumsq_nn : 0 ≤ ∑ i ∈ T₀, (h i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h4 : (T₀.card : ℝ) * ∑ i ∈ T₀, (h i) ^ 2 ≤ s * ∑ i ∈ T₀, (h i) ^ 2 :=
      mul_le_mul_of_nonneg_right hT₀_card_real hsumsq_nn
    linarith
  have hT₀_sub_S : T₀ ⊆ S := Finset.subset_union_left
  have h_sum_T₀_le_G2 : ∑ i ∈ T₀, (h i) ^ 2 ≤ G2 := by
    rw [hG2_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT₀_sub_S (fun _ _ _ => sq_nonneg _)
  have h_sumT₀_nn : 0 ≤ ∑ i ∈ T₀, |h i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_sumT₀c_nn : 0 ≤ ∑ i ∈ T₀ᶜ, |h i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_cone_sq : (∑ i ∈ T₀ᶜ, |h i|) ^ 2 ≤ (∑ i ∈ T₀, |h i|) ^ 2 := by
    nlinarith [h_cone, h_sumT₀_nn, h_sumT₀c_nn]
  have h_l1_sq_bound : (∑ i ∈ T₀ᶜ, |h i|) ^ 2 ≤ s * G2 := by
    calc (∑ i ∈ T₀ᶜ, |h i|) ^ 2
        ≤ (∑ i ∈ T₀, |h i|) ^ 2 := h_cone_sq
      _ ≤ s * ∑ i ∈ T₀, (h i) ^ 2 := h_CS_T₀
      _ ≤ s * G2 := by nlinarith [h_sum_T₀_le_G2, hs_real_nn]
  -- (∑_{T₀ᶜ} |h|) ≤ √s · √G2 by taking square roots.
  have h_sumT₀c_le_sqrt : (∑ i ∈ T₀ᶜ, |h i|) ≤ Real.sqrt s * Real.sqrt G2 := by
    have hrhs_nn : 0 ≤ Real.sqrt s * Real.sqrt G2 :=
      mul_nonneg hsqrt_s_nn (Real.sqrt_nonneg _)
    have hrhs_sq : (Real.sqrt s * Real.sqrt G2) ^ 2 = s * G2 := by
      rw [mul_pow, Real.sq_sqrt hs_real_nn, Real.sq_sqrt hG2_nn]
    nlinarith [h_l1_sq_bound, hrhs_nn, h_sumT₀c_nn, hrhs_sq,
               sq_nonneg ((∑ i ∈ T₀ᶜ, |h i|) - Real.sqrt s * Real.sqrt G2)]
  -- √R2 ≤ √G2  (combining `h_tail` and `h_sumT₀c_le_sqrt`).
  have h_sqrtR2_le_sqrtG2 : Real.sqrt R2 ≤ Real.sqrt G2 := by
    have hstep : (Real.sqrt s)⁻¹ * (∑ i ∈ T₀ᶜ, |h i|) ≤
                 (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt G2) :=
      mul_le_mul_of_nonneg_left h_sumT₀c_le_sqrt (inv_nonneg.mpr hsqrt_s_nn)
    have hsimp : (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt G2) = Real.sqrt G2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrt_s_pos), one_mul]
    linarith [h_tail, hstep, hsimp]
  -- Squared version: R2 ≤ G2.
  have h_R2_le_G2 : R2 ≤ G2 := by
    have h_sqrtR2_nn : 0 ≤ Real.sqrt R2 := Real.sqrt_nonneg _
    have h_sqrtG2_nn : 0 ≤ Real.sqrt G2 := Real.sqrt_nonneg _
    have h_R2_sq : (Real.sqrt R2) ^ 2 = R2 := Real.sq_sqrt hR2_nn
    have h_G2_sq : (Real.sqrt G2) ^ 2 = G2 := Real.sq_sqrt hG2_nn
    nlinarith [h_sqrtR2_le_sqrtG2, h_sqrtR2_nn, h_sqrtG2_nn, h_R2_sq, h_G2_sq]
  -- ============================================================================
  -- Step 5: Block-decomposition inner-product bound (R6 infrastructure pending).
  --
  -- This is the analytic heart of the theorem.  Partitioning `Sᶜ = (T₀ ∪ T₁)ᶜ`
  -- into blocks of size `≤ s` sorted by `|h|` and applying
  -- `rip_restricted_orthogonality` to each `(g, h|_{B_k})` pair gives:
  --
  --   |⟨A g, A r⟩| ≤ δ · √G2 · ∑_k √(∑_{B_k} h²).
  --
  -- The telescoping bound (Foucart–Rauhut Lem 6.10):
  --   ∑_k √(∑_{B_k} h²) ≤ (√s)⁻¹ · ∑_{T₀ᶜ} |h| ≤ √G2 (by Step 4)
  -- yields
  --   |⟨A g, A r⟩| ≤ δ · G2.
  --
  -- The "√2" factor below is the Foucart–Rauhut conservative bound (Cor 6.13)
  -- that combines `T₁` separately for the tighter recovery threshold `√2 − 1`.
  --
  -- Implementing this requires ≈ 150–200 LOC of new infrastructure:
  --   * `exists_block_partition` — sorted block decomposition,
  --   * `block_inner_product_bound` — the telescoping inner-product inequality.
  -- These are isolated as standalone helper lemmas above (each marked `sorry`,
  -- R6 / Mathlib-PR-scale).  Here we simply unfold definitions and apply the
  -- packaged Foucart–Rauhut bound.
  -- ============================================================================
  have h_inner_block_bound :
      |∑ i, (A.mulVec g) i * (A.mulVec r) i| ≤ Real.sqrt 2 * δ * G2 := by
    -- Convert `g`, `r`, `G2` to the form expected by `block_inner_product_bound`.
    have hg_eq : g = restrictTo (T₀ ∪ T₁) h := by rw [hg_def, hS_def]
    have hr_eq : r = restrictTo (T₀ ∪ T₁)ᶜ h := by rw [hr_def, hS_def]
    have hG2_eq' : G2 = ∑ i, (restrictTo (T₀ ∪ T₁) h i) ^ 2 := by
      rw [hG2_def, hg_eq]
    rw [hg_eq, hr_eq, hG2_eq']
    exact block_inner_product_bound hRIP hδ_pos hs_pos T₀ T₁
      hT₀T₁_disj hT₀_card hT₁_card hT₁_largest h_cone
  -- ============================================================================
  -- Step 6: ‖A g‖² = -⟨A g, A r⟩  (since A h = 0).
  -- ============================================================================
  have hAg_eq_neg_Ar : A.mulVec g = -A.mulVec r := by
    have hsum_zero : A.mulVec g + A.mulVec r = 0 := by
      rw [← Matrix.mulVec_add, hg_add_r, hh_ker]
    -- From `Ag + Ar = 0`, conclude `Ag = -Ar`.
    have := hsum_zero
    linear_combination this
  have hAg_sq_eq : (∑ i, ((A.mulVec g) i) ^ 2) =
                   -(∑ i, (A.mulVec g) i * (A.mulVec r) i) := by
    have hpt : ∀ i, ((A.mulVec g) i) ^ 2 = -((A.mulVec g) i * (A.mulVec r) i) := by
      intro i
      have : (A.mulVec g) i = -(A.mulVec r) i := by rw [hAg_eq_neg_Ar]; rfl
      rw [this]; ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i), ← Finset.sum_neg_distrib]
  -- ============================================================================
  -- Step 7: contraction inequality (1 - √2·δ) · G2 ≤ 0.
  -- ============================================================================
  obtain ⟨hRIP_lo, _⟩ := hRIP g hg_sparse
  -- (1 - δ) · G2 ≤ ‖A g‖² = -⟨A g, A r⟩ ≤ |⟨A g, A r⟩| ≤ √2 · δ · G2.
  -- Combining: (1 - δ) · G2 ≤ √2 · δ · G2, so (1 - (1+√2)·δ) · G2 ≤ 0.
  have hAbs_ge : -(∑ i, (A.mulVec g) i * (A.mulVec r) i) ≤
                 |∑ i, (A.mulVec g) i * (A.mulVec r) i| := neg_le_abs _
  have h1 : (1 - δ) * G2 ≤ ∑ i, ((A.mulVec g) i) ^ 2 := by
    rw [hG2_def]; exact hRIP_lo
  have h2 : ∑ i, ((A.mulVec g) i) ^ 2 ≤ Real.sqrt 2 * δ * G2 := by
    rw [hAg_sq_eq]; linarith [h_inner_block_bound, hAbs_ge]
  have h_contract : (1 - (1 + Real.sqrt 2) * δ) * G2 ≤ 0 := by
    have h12 : (1 - δ) * G2 ≤ Real.sqrt 2 * δ * G2 := le_trans h1 h2
    have hexpand : (1 - (1 + Real.sqrt 2) * δ) * G2 =
                   (1 - δ) * G2 - Real.sqrt 2 * δ * G2 := by ring
    linarith [h12, hexpand]
  -- ============================================================================
  -- Step 8: δ < √2 − 1  ⟹  1 - (1+√2)·δ > 0  ⟹  G2 = 0  ⟹  g = 0  ⟹  h = 0.
  -- ============================================================================
  have h_one_lt_sqrt2 : (1 : ℝ) < Real.sqrt 2 := one_lt_sqrt_two
  have h_sqrt2_pos : 0 < Real.sqrt 2 := lt_trans (by norm_num) h_one_lt_sqrt2
  have h_one_add_sqrt2_pos : 0 < 1 + Real.sqrt 2 := by linarith
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- Key identity: (1+√2)·(√2-1) = √2·√2 - 1 = 1.
  have h_key_eq : (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) = 1 := by
    nlinarith [h_sqrt2_sq]
  have h_one_sub_pos : 0 < 1 - (1 + Real.sqrt 2) * δ := by
    have hδ_lt' : δ < Real.sqrt 2 - 1 := hδ_lt
    -- (1+√2)·δ < (1+√2)·(√2-1) = 1.
    have h_step : (1 + Real.sqrt 2) * δ < (1 + Real.sqrt 2) * (Real.sqrt 2 - 1) :=
      mul_lt_mul_of_pos_left hδ_lt' h_one_add_sqrt2_pos
    linarith [h_step, h_key_eq]
  have hG2_zero : G2 = 0 := by
    have h_le : G2 ≤ 0 := by
      by_contra h_neg
      push_neg at h_neg
      have : 0 < (1 - (1 + Real.sqrt 2) * δ) * G2 := mul_pos h_one_sub_pos h_neg
      linarith
    linarith [h_le, hG2_nn]
  -- G2 = 0 ⟹ g = 0 pointwise.
  have hg_zero : ∀ i, g i = 0 := by
    intro i
    have h_sum_zero : ∑ i, (g i) ^ 2 = 0 := by rw [← hG2_def]; exact hG2_zero
    have h_each : (g i) ^ 2 = 0 := by
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ (g j) ^ 2 := fun j _ => sq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h_sum_zero i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_each
  -- g = 0 ⟹ h vanishes on S = T₀ ∪ T₁.
  have hh_S_zero : ∀ i ∈ S, h i = 0 := by
    intro i hi
    have := hg_zero i
    rw [hg_def, restrictTo_apply_mem hi] at this
    exact this
  -- In particular, h vanishes on T₁; since T₁ contains the top-`s` `|h|` entries
  -- of T₀ᶜ, h vanishes on all of T₀ᶜ.  Combined with h = 0 on T₀ ⊆ S, we get h = 0.
  have hh_T₁_zero : ∀ i ∈ T₁, h i = 0 := fun i hi =>
    hh_S_zero i (Finset.mem_union_right _ hi)
  have hh_T₀c_zero : ∀ j ∈ T₀ᶜ, h j = 0 := by
    intro j hj
    -- Case: j ∈ T₁ or j ∈ T₀ᶜ \ T₁.
    by_cases hjT₁ : j ∈ T₁
    · exact hh_T₁_zero j hjT₁
    · -- j ∈ T₀ᶜ \ T₁: pick any i ∈ T₁ (exists since |T₁| = s ≥ 1).
      have hT₁_nonempty : T₁.Nonempty := by
        rw [Finset.card_pos.symm] at *
        rw [hT₁_card]; exact hs_pos
      obtain ⟨i, hi⟩ := hT₁_nonempty
      have hjT₀c_sdiff : j ∈ T₀ᶜ \ T₁ := Finset.mem_sdiff.mpr ⟨hj, hjT₁⟩
      have hbound : |h j| ≤ |h i| := hT₁_largest_sdiff i hi j hjT₀c_sdiff
      have hi_zero : h i = 0 := hh_T₁_zero i hi
      have : |h j| ≤ 0 := by rw [hi_zero, abs_zero] at hbound; exact hbound
      have : |h j| = 0 := le_antisymm this (abs_nonneg _)
      exact abs_eq_zero.mp this
  have hh_T₀_zero : ∀ i ∈ T₀, h i = 0 :=
    fun i hi => hh_S_zero i (Finset.mem_union_left _ hi)
  funext i
  by_cases hi : i ∈ T₀
  · exact hh_T₀_zero i hi
  · exact hh_T₀c_zero i (Finset.mem_compl.mpr hi)

/-- **Kernel triviality from RIP** (the analytic core of Candès 2008):
if `A` satisfies `(2s, δ)`-RIP with `δ < √2 − 1`, then every `h ∈ ker A`
whose `T₀ᶜ`-ℓ¹ mass is dominated by its `T₀`-ℓ¹ mass is the zero vector.

**Proof structure**:
* If `s = 0`: the cone constraint becomes `‖h‖₁ ≤ 0`, forcing `h = 0`.
* If `s ≥ 1` and `n ≤ 2s`: `h` itself is automatically `2s`-sparse, and the
  RIP lower bound applied to the kernel relation `A h = 0` forces `‖h‖₂ = 0`.
* If `s ≥ 1` and `n > 2s`: the full Candès 2008 block-decomposition argument
  applies (delegated to `candes_2008_kernel_contraction`). -/
theorem rip_implies_zero_on_kernel
    {A : Matrix (Fin m) (Fin n) ℝ} {s : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt : δ < l1RecoveryThreshold)
    (hRIP : IsRIP A (2 * s) δ)
    {h : Fin n → ℝ} (hh_ker : A.mulVec h = 0)
    (T₀ : Finset (Fin n)) (hT₀_card : T₀.card ≤ s)
    (h_cone : (∑ i ∈ T₀ᶜ, |h i|) ≤ (∑ i ∈ T₀, |h i|)) :
    h = 0 := by
  classical
  -- Handle the degenerate special cases that don't need block decomposition,
  -- then delegate the analytic core to `candes_2008_kernel_contraction`.
  rcases Nat.eq_zero_or_pos s with hs0 | hs_pos_nat
  · -- Case 1: s = 0 ⟹ T₀ = ∅, cone forces h = 0 directly.
    subst hs0
    have hT₀_empty : T₀ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hT₀_card)
    have hsumT₀_zero : ∑ i ∈ T₀, |h i| = 0 := by rw [hT₀_empty]; simp
    have hsumT₀c_eq : ∑ i ∈ T₀ᶜ, |h i| = 0 := by
      have hnn : 0 ≤ ∑ i ∈ T₀ᶜ, |h i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith [h_cone, hsumT₀_zero]
    have hsum_all_zero : ∑ i, |h i| = 0 := by
      rw [← Finset.sum_add_sum_compl T₀ (fun i => |h i|), hsumT₀_zero, hsumT₀c_eq]
      ring
    have hh_zero : ∀ i, h i = 0 := fun i =>
      abs_eq_zero.mp <| (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => abs_nonneg (h j))).mp hsum_all_zero i (Finset.mem_univ i)
    funext i; exact hh_zero i
  -- Case 2: s ≥ 1.
  by_cases hn_small : n ≤ 2 * s
  · -- Case 2a: n ≤ 2s ⟹ h is automatically 2s-sparse ⟹ RIP forces h = 0.
    have hh_sparse : IsSSparse h (2 * s) := by
      unfold IsSSparse
      have h1 : (Finset.univ.filter (fun i => h i ≠ 0)).card ≤ Finset.univ.card :=
        Finset.card_filter_le _ _
      have h2 : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ]; exact Fintype.card_fin n
      omega
    have hδ_lt_one : δ < 1 := lt_trans hδ_lt l1RecoveryThreshold_lt_one
    obtain ⟨hRIP_lo, _⟩ := hRIP h hh_sparse
    have hAh_sum_sq : ∑ i, ((A.mulVec h) i) ^ 2 = 0 := by rw [hh_ker]; simp
    rw [hAh_sum_sq] at hRIP_lo
    -- (1 - δ) * ‖h‖² ≤ 0 with (1 - δ) > 0 ⟹ ‖h‖² = 0
    have h_one_sub_δ_pos : 0 < 1 - δ := by linarith
    have h_sum_nn : 0 ≤ ∑ i, (h i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_sum_zero : ∑ i, (h i) ^ 2 = 0 := by nlinarith
    have hh_zero : ∀ i, h i = 0 := fun i =>
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (h j))).mp
          h_sum_zero i (Finset.mem_univ i))
    funext i; exact hh_zero i
  -- Case 2b: n > 2s. Delegate to the block-decomposition lemma (Candès 2008 /
  -- Foucart–Rauhut §6).
  push_neg at hn_small
  exact candes_2008_kernel_contraction hδ_pos hδ_lt hRIP hh_ker T₀ hT₀_card h_cone
    hs_pos_nat hn_small

end CandesTaoIngredients

/-- **Candès–Tao 2005 / Candès 2008 ℓ¹ recovery**: under the
`(2s, δ)`-Restricted Isometry Property with `δ < √2 − 1`, ℓ¹
minimisation exactly recovers any `s`-sparse signal `x` from the
compressed measurements `A x`.

The statement says that `x` is a minimiser of the ℓ¹ norm among all
vectors `z` whose image under `A` matches `A x`.  The proof composes
`cone_constraint`, `rip_implies_zero_on_kernel`, and the sub-lemmas above
(see Foucart–Rauhut §6 / Mixon, *Short, Fat Matrices*). -/
theorem candes_tao_recovery
    {A : Matrix (Fin m) (Fin n) ℝ} {s : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt : δ < l1RecoveryThreshold)
    (hRIP : IsRIP A (2 * s) δ)
    (x : Fin n → ℝ) (hx : IsSSparse x s) :
    ∀ z : Fin n → ℝ, A.mulVec z = A.mulVec x →
      ∑ i, |x i| ≤ ∑ i, |z i| := by
  classical
  intro z hAz
  -- Let `T₀` be the support of `x`; it has cardinality `≤ s` since `x` is `s`-sparse.
  set T₀ : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0) with hT₀_def
  have hT₀_card : T₀.card ≤ s := hx
  have hx_supp : ∀ i ∉ T₀, x i = 0 := by
    intro i hi
    simp [T₀, Finset.mem_filter] at hi
    exact hi
  -- Suppose for contradiction `‖x‖₁ > ‖z‖₁`; we will rule this out below.
  by_contra h_not
  push_neg at h_not
  -- Set `h = z - x ∈ ker A`.
  set hvec : Fin n → ℝ := z - x with hvec_def
  have hh_ker : A.mulVec hvec = 0 := by
    rw [hvec_def, Matrix.mulVec_sub, hAz, sub_self]
  -- Cone constraint from the ‖z‖₁ ≤ ‖x‖₁ hypothesis.
  have h_cone : (∑ i ∈ T₀ᶜ, |hvec i|) ≤ (∑ i ∈ T₀, |hvec i|) :=
    cone_constraint T₀ hx_supp (le_of_lt h_not)
  -- Kernel triviality: `hvec = 0`, i.e. `z = x`, contradicting ‖z‖₁ < ‖x‖₁.
  have hvec_zero : hvec = 0 :=
    rip_implies_zero_on_kernel hδ_pos hδ_lt hRIP hh_ker T₀ hT₀_card h_cone
  have hzx : z = x := by
    have := hvec_zero
    rw [hvec_def, sub_eq_zero] at this
    exact this
  rw [hzx] at h_not
  exact lt_irrefl _ h_not

end Statlean.CompressedSensing

/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Statlean.Mathlib.Analysis.DavisKahan
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Davis-Kahan Sin-Theta Theorem — squared form via Bessel expansion

This file extends `Statlean.Mathlib.Analysis.DavisKahan` with the *squared*
sin-θ inequality

```
1 − ⟨v_A, v_B⟩² ≤ (ε / gap)²
```

in finite-dimensional real inner-product spaces, where `v_B` is one of the
eigenvectors of a symmetric operator `B` and `ε` controls
`‖B v_A − λ_B • v_A‖`.

The argument is the textbook Bessel/eigenbasis expansion:

* Expand `v_A = Σ_k ⟨e_k, v_A⟩ • e_k` in the eigenbasis of `B` (this is just an
  orthonormal-basis identity; we use `OrthonormalBasis.repr_apply_apply`).
* By Pythagoras, `‖v_A‖² = Σ_k ⟨e_k, v_A⟩²`.
* Compute coordinates of `B v_A − λ_B • v_A` against the eigenbasis: the
  `k`-th coordinate is `(μ_k − λ_B) · ⟨e_k, v_A⟩` (uses
  `IsSymmetric.apply_eigenvectorBasis` plus symmetry of `B`).
* Apply Pythagoras again: `‖B v_A − λ_B • v_A‖² = Σ_k ⟨e_k, v_A⟩² (μ_k − λ_B)²`.
* For `k = j` (the index of `v_B`) the coefficient `(μ_j − λ_B)²` vanishes; for
  `k ≠ j`, `(μ_k − λ_B)² ≥ gap²`.  Combining gives the squared bound.

This file does *not* close the operator-norm hypothesis — i.e. it does not prove
`|λ_A − λ_B| ≤ ‖A − B‖` (Weyl perturbation), which is itself a Mathlib gap.
Instead the user supplies `‖B v_A − λ_B • v_A‖ ≤ ε` directly (which already
includes the residual eigenvalue mismatch via the triangle inequality
`‖B v_A − λ_B v_A‖ ≤ ‖(A − B) v_A‖ + |λ_A − λ_B|`).

## Main results

* `bessel_norm_sq_eq_sum_inner_sq`: `‖v‖² = Σ_i ⟨b i, v⟩²` for an orthonormal
  basis `b`.  (Real proof.)
* `inner_eigenvectorBasis_apply_sub_smul_eq`: the coordinate identity
  `⟨e_k, B v − λ • v⟩ = (μ_k − λ) · ⟨e_k, v⟩`.  (Real proof.)
* `norm_apply_sub_eigenvalue_smul_sq`: the Pythagorean expansion
  `‖B v − λ • v‖² = Σ_k ⟨e_k, v⟩² · (μ_k − λ)²`.  (Real proof.)
* `one_sub_inner_sq_le_norm_apply_sub_div_gap_sq`: the *gap bound*
  `1 − ⟨v_A, e_j⟩² ≤ ‖B v_A − λ_B • v_A‖² / gap²`.  (Real proof.)
* `davis_kahan_finite_dim_squared`: the finite-dimensional squared sin-θ
  inequality.  (Real proof, assembling the gap bound with the triangle
  inequality `‖B v_A − λ_B • v_A‖ ≤ ε + |λ_A − λ_B|`.)

## References

* Yu, Y., Wang, T. and Samworth, R. J. (2015), "A useful variant of the
  Davis-Kahan theorem for statisticians", Biometrika 102(2), 315-323.
-/

open scoped InnerProductSpace
open Module Finset

namespace Mathlib.Analysis.DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Bessel identity for orthonormal bases -/

/-- **Bessel's norm identity** for a (finite) orthonormal basis: the squared
norm of a vector decomposes as the sum of squared coordinates.  This is the
`Fintype` specialisation of the standard Pythagorean expansion. -/
lemma bessel_norm_sq_eq_sum_inner_sq
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ H) (v : H) :
    ‖v‖ ^ 2 = ∑ i, (@inner ℝ _ _ (b i) v) ^ 2 := by
  rw [← b.repr.norm_map v, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs]

/-- **Unit vector** specialisation: `Σ_i ⟨b i, v⟩² = 1` when `‖v‖ = 1`. -/
lemma sum_inner_sq_eq_one_of_unit
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ H)
    (v : H) (hv : ‖v‖ = 1) :
    ∑ i, (@inner ℝ _ _ (b i) v) ^ 2 = 1 := by
  have h := bessel_norm_sq_eq_sum_inner_sq b v
  rw [hv] at h; linarith [h]

/-! ### Coordinate identity in the eigenbasis -/

/-- For a symmetric operator `B` with spectral basis `{e_k}` and eigenvalues
`{μ_k}`, the coordinate of `B v − λ • v` against `e_k` is
`(μ_k − λ) · ⟨e_k, v⟩`. -/
lemma inner_eigenvectorBasis_apply_sub_smul_eq
    [FiniteDimensional ℝ H] {n : ℕ}
    (B : H →ₗ[ℝ] H) (hB : B.IsSymmetric) (hn : Module.finrank ℝ H = n)
    (v : H) (lam : ℝ) (k : Fin n) :
    @inner ℝ _ _ (hB.eigenvectorBasis hn k) (B v - lam • v) =
      (hB.eigenvalues hn k - lam) *
        (@inner ℝ _ _ (hB.eigenvectorBasis hn k) v) := by
  rw [inner_sub_right, real_inner_smul_right]
  rw [show (@inner ℝ _ _ (hB.eigenvectorBasis hn k) (B v) : ℝ)
        = @inner ℝ _ _ (B (hB.eigenvectorBasis hn k)) v from (hB _ _).symm]
  rw [hB.apply_eigenvectorBasis, real_inner_smul_left]
  -- Goal involves `↑(hB.eigenvalues hn k)` where the coercion `ℝ → ℝ` is `id`.
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-! ### Pythagorean expansion of `‖B v − λ • v‖²` in the eigenbasis -/

/-- **Pythagorean expansion** of `‖B v − λ • v‖²` against the eigenbasis of `B`:

`‖B v − λ • v‖² = Σ_k ⟨e_k, v⟩² · (μ_k − λ)²`.

Proof: Bessel's identity applied to `w = B v − λ • v`, with the coordinate
identity `inner_eigenvectorBasis_apply_sub_smul_eq` plugged in. -/
lemma norm_apply_sub_eigenvalue_smul_sq
    [FiniteDimensional ℝ H] {n : ℕ}
    (B : H →ₗ[ℝ] H) (hB : B.IsSymmetric) (hn : Module.finrank ℝ H = n)
    (v : H) (lam : ℝ) :
    ‖B v - lam • v‖ ^ 2 =
      ∑ k, (@inner ℝ _ _ (hB.eigenvectorBasis hn k) v) ^ 2
            * (hB.eigenvalues hn k - lam) ^ 2 := by
  rw [bessel_norm_sq_eq_sum_inner_sq (hB.eigenvectorBasis hn) (B v - lam • v)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_eigenvectorBasis_apply_sub_smul_eq B hB hn v lam k]
  ring

/-! ### The gap bound -/

/-- **Gap bound** (core Davis-Kahan inequality, squared form).

If `B` is symmetric on a finite-dimensional real inner-product space, with
spectral basis `{e_k}` and eigenvalues `{μ_k}`, and the eigenvalue `μ_j = λ_B`
is separated from the others by `gap`, then for any unit vector `v_A`,

`1 − ⟨v_A, e_j⟩² ≤ ‖B v_A − λ_B • v_A‖² / gap²`.

The proof uses Bessel (`1 = Σ ⟨e_k, v_A⟩²`), the Pythagorean expansion of
`‖B v_A − λ_B • v_A‖²`, and the eigenvalue separation hypothesis to estimate
each off-diagonal term from below by `gap²`. -/
theorem one_sub_inner_sq_le_norm_apply_sub_div_gap_sq
    [FiniteDimensional ℝ H] {n : ℕ}
    (B : H →ₗ[ℝ] H) (hB : B.IsSymmetric) (hn : Module.finrank ℝ H = n)
    (v_A : H) (j : Fin n) (lam_B : ℝ)
    (_h_eig_j : hB.eigenvalues hn j = lam_B)
    (hv_A_norm : ‖v_A‖ = 1)
    (gap : ℝ) (hgap_pos : 0 < gap)
    (hgap : ∀ k, k ≠ j → gap ≤ |hB.eigenvalues hn k - lam_B|) :
    1 - (@inner ℝ _ _ v_A (hB.eigenvectorBasis hn j)) ^ 2
      ≤ ‖B v_A - lam_B • v_A‖ ^ 2 / gap ^ 2 := by
  -- Abbreviations.
  set b := hB.eigenvectorBasis hn with hb_def
  set μ : Fin n → ℝ := fun k => hB.eigenvalues hn k with hμ_def
  set c : Fin n → ℝ := fun k => @inner ℝ _ _ (b k) v_A with hc_def
  -- Bessel: `Σ_k c k ^ 2 = 1`.
  have hSum_one : ∑ k, c k ^ 2 = 1 := by
    have := bessel_norm_sq_eq_sum_inner_sq b v_A
    rw [hv_A_norm] at this; linarith [this]
  -- Real-symmetry of inner: `⟨v_A, e_j⟩ = ⟨e_j, v_A⟩ = c j`.
  have h_inner_swap : (@inner ℝ _ _ v_A (b j) : ℝ) = c j := real_inner_comm _ _
  -- Pythagorean expansion: `‖B v_A − λ_B • v_A‖² = Σ_k c k² (μ k − λ_B)²`.
  have hNorm_eq : ‖B v_A - lam_B • v_A‖ ^ 2
      = ∑ k, c k ^ 2 * (μ k - lam_B) ^ 2 := by
    rw [norm_apply_sub_eigenvalue_smul_sq B hB hn v_A lam_B]
  -- Per-index lower bound.
  -- Define `f k := c k ^ 2 * (μ k - lam_B) ^ 2` and `g k := if k = j then 0 else gap^2 * c k^2`.
  -- Then `g k ≤ f k` for all k.
  have hPerTerm : ∀ k, (if k = j then (0 : ℝ) else gap ^ 2 * c k ^ 2)
      ≤ c k ^ 2 * (μ k - lam_B) ^ 2 := by
    intro k
    by_cases hk : k = j
    · -- k = j: LHS = 0, RHS ≥ 0.
      simp only [if_pos hk]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · -- k ≠ j: estimate `(μ k − λ_B)² ≥ gap²`.
      simp only [if_neg hk]
      have h1 : gap ≤ |μ k - lam_B| := hgap k hk
      have h_le : gap ^ 2 ≤ (μ k - lam_B) ^ 2 := by
        have h2 : (0 : ℝ) ≤ gap := le_of_lt hgap_pos
        have h3 : gap ^ 2 ≤ |μ k - lam_B| ^ 2 := by
          have := mul_self_le_mul_self h2 h1
          simpa [sq] using this
        rwa [sq_abs] at h3
      have hck_sq : 0 ≤ c k ^ 2 := sq_nonneg _
      calc gap ^ 2 * c k ^ 2
          ≤ (μ k - lam_B) ^ 2 * c k ^ 2 :=
            mul_le_mul_of_nonneg_right h_le hck_sq
        _ = c k ^ 2 * (μ k - lam_B) ^ 2 := by ring
  -- Sum the per-index bound.
  have hSum_le_pre :
      ∑ k, (if k = j then (0 : ℝ) else gap ^ 2 * c k ^ 2)
        ≤ ∑ k, c k ^ 2 * (μ k - lam_B) ^ 2 :=
    Finset.sum_le_sum (fun k _ => hPerTerm k)
  -- Compute the LHS of `hSum_le_pre`.
  have hSum_lhs : ∑ k, (if k = j then (0 : ℝ) else gap ^ 2 * c k ^ 2)
      = gap ^ 2 * (1 - c j ^ 2) := by
    -- Split off term j (contributes 0), rewrite remainder.
    have h_split : ∑ k, (if k = j then (0 : ℝ) else gap ^ 2 * c k ^ 2)
        = ∑ k ∈ Finset.univ.erase j, gap ^ 2 * c k ^ 2 := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n))
            (fun k => if k = j then (0 : ℝ) else gap ^ 2 * c k ^ 2)
            (Finset.mem_univ j)]
      rw [if_pos rfl, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_erase] at hk
      rw [if_neg hk.1]
    rw [h_split, ← Finset.mul_sum]
    -- Show `Σ_{k ≠ j} c k² = 1 − c j²` via Bessel.
    have hRest : ∑ k ∈ Finset.univ.erase j, c k ^ 2 = 1 - c j ^ 2 := by
      have h := Finset.sum_erase_add _ (fun k => c k ^ 2) (Finset.mem_univ j)
      linarith [h, hSum_one]
    rw [hRest]
  have hSum_le : gap ^ 2 * (1 - c j ^ 2) ≤ ‖B v_A - lam_B • v_A‖ ^ 2 := by
    rw [hNorm_eq, ← hSum_lhs]; exact hSum_le_pre
  -- Conclude: `1 - c j² ≤ ‖…‖² / gap²`.
  have hgap_sq_pos : 0 < gap ^ 2 := by positivity
  rw [h_inner_swap, le_div_iff₀ hgap_sq_pos]
  linarith [hSum_le]

/-! ### Davis-Kahan in finite-dimensional H, squared form -/

/-- **Davis-Kahan, finite-dimensional squared form**.

Given two symmetric operators `A, B` on a finite-dimensional real inner-product
space, a unit `A`-eigenvector `v_A` for `λ_A`, a unit `B`-eigenvector `v_B = e_j`
appearing in the spectral basis of `B` (with `B`-eigenvalue `λ_B = μ_j`), and a
gap separating `λ_B` from the rest of the `B`-spectrum, then

`1 − ⟨v_A, v_B⟩² ≤ (ε + |λ_A − λ_B|)² / gap²`

where `ε` is any upper bound on `‖(A − B) v_A‖`.

The proof combines `one_sub_inner_sq_le_norm_apply_sub_div_gap_sq` (the gap
bound on `‖B v_A − λ_B • v_A‖²`) with the triangle inequality

`‖B v_A − λ_B • v_A‖ ≤ ‖(A − B) v_A‖ + ‖A v_A − λ_B • v_A‖`

and the identity `A v_A − λ_B • v_A = (λ_A − λ_B) • v_A` (from
`A v_A = λ_A • v_A`), giving `‖A v_A − λ_B • v_A‖ = |λ_A − λ_B|` since
`‖v_A‖ = 1`. -/
theorem davis_kahan_finite_dim_squared
    [FiniteDimensional ℝ H] {n : ℕ}
    (A B : H →ₗ[ℝ] H) (hB : B.IsSymmetric) (hn : Module.finrank ℝ H = n)
    (v_A : H) (j : Fin n) (lam_A lam_B : ℝ)
    (hv_A_eig : A v_A = lam_A • v_A)
    (h_eig_j : hB.eigenvalues hn j = lam_B)
    (hv_A_norm : ‖v_A‖ = 1)
    (gap : ℝ) (hgap_pos : 0 < gap)
    (hgap : ∀ k, k ≠ j → gap ≤ |hB.eigenvalues hn k - lam_B|)
    (ε : ℝ) (hε : ‖(A - B) v_A‖ ≤ ε) :
    1 - (@inner ℝ _ _ v_A (hB.eigenvectorBasis hn j)) ^ 2
      ≤ (ε + |lam_A - lam_B|) ^ 2 / gap ^ 2 := by
  -- Step 1: rewrite `B v_A − λ_B • v_A = − (A − B) v_A + (A v_A − λ_B • v_A)`.
  have h_decomp : B v_A - lam_B • v_A
      = - ((A - B) v_A) + (A v_A - lam_B • v_A) := by
    simp only [LinearMap.sub_apply]; abel
  -- Step 2: triangle inequality on this decomposition.
  have h_tri : ‖B v_A - lam_B • v_A‖
      ≤ ‖(A - B) v_A‖ + ‖A v_A - lam_B • v_A‖ := by
    rw [h_decomp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
  -- Step 3: `A v_A − λ_B • v_A = (λ_A − λ_B) • v_A`, so its norm is `|λ_A − λ_B|`.
  have h_resid : A v_A - lam_B • v_A = (lam_A - lam_B) • v_A := by
    rw [hv_A_eig, ← sub_smul]
  have h_resid_norm : ‖A v_A - lam_B • v_A‖ = |lam_A - lam_B| := by
    rw [h_resid, norm_smul, hv_A_norm, mul_one, Real.norm_eq_abs]
  -- Step 4: combine triangle with `hε` and `h_resid_norm`.
  have h_norm_le : ‖B v_A - lam_B • v_A‖ ≤ ε + |lam_A - lam_B| := by
    calc ‖B v_A - lam_B • v_A‖
        ≤ ‖(A - B) v_A‖ + ‖A v_A - lam_B • v_A‖ := h_tri
      _ ≤ ε + |lam_A - lam_B| := by
          rw [h_resid_norm]; linarith [hε]
  -- Step 5: square the triangle bound.
  have h_norm_nn : 0 ≤ ‖B v_A - lam_B • v_A‖ := norm_nonneg _
  have h_norm_sq_le : ‖B v_A - lam_B • v_A‖ ^ 2 ≤ (ε + |lam_A - lam_B|) ^ 2 := by
    have := mul_self_le_mul_self h_norm_nn h_norm_le
    simpa [sq] using this
  -- Step 6: gap bound + monotonicity of `· / gap²`.
  have h_gap_bound :
      1 - (@inner ℝ _ _ v_A (hB.eigenvectorBasis hn j)) ^ 2
        ≤ ‖B v_A - lam_B • v_A‖ ^ 2 / gap ^ 2 :=
    one_sub_inner_sq_le_norm_apply_sub_div_gap_sq B hB hn v_A j lam_B
      h_eig_j hv_A_norm gap hgap_pos hgap
  have hgap_sq_pos : 0 < gap ^ 2 := by positivity
  exact h_gap_bound.trans
    (div_le_div_of_nonneg_right h_norm_sq_le (le_of_lt hgap_sq_pos))

/-! ### Bridge to the abstract `DavisKahanSinTheta` structure

Given the *finite-dimensional* squared bound, we can construct a
`DavisKahanSinTheta` witness for `A, B` (treated as continuous linear maps).
The constant `C_DK` must absorb the `(ε + |λ_A − λ_B|)`-vs-`‖A − B‖` slack.

Under the additional hypothesis `|λ_A − λ_B| ≤ ‖A − B‖` (Weyl-type eigenvalue
stability — itself non-trivial in Mathlib v4.28), we obtain the textbook
`C_DK = 2` constant: `(ε + |λ_A − λ_B|)² ≤ (2ε)² = 4ε²`.

The bridge below packages all of these prerequisites into a single
hypothesis-form constructor.  Each pair `(v_A, v_B)` for which we want the
bound is supplied with: an index `j` for `v_B` in the spectral basis, the
operator-norm bound `‖(A − B) v_A‖ ≤ ‖A − B‖`, and the eigenvalue-stability
bound `|λ_A − λ_B| ≤ ‖A − B‖`.  All of these are themselves theorems for
honest symmetric operators, but Mathlib v4.28 lacks the requisite spectral
machinery, so we expose them as inputs. -/

/-- **Bridging constructor**: produces a `DavisKahanSinTheta` instance with
constant `C_DK = 2`, taking as inputs the eigenbasis index, the operator-norm
bound, and the eigenvalue-stability bound for each unit-vector pair satisfying
`DavisKahanSinTheta.bound`'s preconditions.

The bridge collapses `(ε + |λ_A − λ_B|)² ≤ (2ε)²` (using `|λ_A − λ_B| ≤ ε`)
to give the standard `(2 ‖A − B‖ / gap)²` bound. -/
noncomputable def davisKahanSinTheta_of_finiteDim_aux
    [FiniteDimensional ℝ H] {n : ℕ}
    (A B : H →L[ℝ] H) (hB_sym : (B : H →ₗ[ℝ] H).IsSymmetric)
    (hn : Module.finrank ℝ H = n) (gap : ℝ)
    (h_data : ∀ (v_A v_B : H) (lam_A lam_B : ℝ),
      (A : H →ₗ[ℝ] H) v_A = lam_A • v_A →
      (B : H →ₗ[ℝ] H) v_B = lam_B • v_B →
      ‖v_A‖ = 1 → ‖v_B‖ = 1 →
      gap ≤ |lam_B - lam_A| → 0 < gap →
      ∃ j : Fin n, hB_sym.eigenvalues hn j = lam_B
        ∧ v_B = hB_sym.eigenvectorBasis hn j
        ∧ (∀ k, k ≠ j → gap ≤ |hB_sym.eigenvalues hn k - lam_B|)
        ∧ ‖((A : H →ₗ[ℝ] H) - (B : H →ₗ[ℝ] H)) v_A‖ ≤ ‖A - B‖
        ∧ |lam_A - lam_B| ≤ ‖A - B‖) :
    DavisKahanSinTheta A B gap where
  C_DK := 2
  C_DK_pos := by norm_num
  bound := by
    intro v_A v_B lam_A lam_B hv_A_eig hv_B_eig hv_A_norm hv_B_norm h_gap_le hgap_pos
    obtain ⟨j, h_eig_j, hv_B_eq, hgap_off, h_op, h_stab⟩ :=
      h_data v_A v_B lam_A lam_B hv_A_eig hv_B_eig hv_A_norm hv_B_norm h_gap_le hgap_pos
    -- Apply the finite-dim squared bound with `ε := ‖A - B‖`.
    have h_finite := davis_kahan_finite_dim_squared
      (A : H →ₗ[ℝ] H) (B : H →ₗ[ℝ] H) hB_sym hn v_A j lam_A lam_B
      hv_A_eig h_eig_j hv_A_norm gap hgap_pos hgap_off ‖A - B‖ h_op
    -- Rewrite `⟨v_A, v_B⟩ = ⟨v_A, e_j⟩`.
    rw [hv_B_eq]
    -- Bound `(‖A - B‖ + |lam_A - lam_B|)² ≤ (2‖A - B‖)² = (2 ‖A - B‖ / gap)² · gap²`.
    have h_sum_le : ‖A - B‖ + |lam_A - lam_B| ≤ 2 * ‖A - B‖ := by
      linarith [h_stab]
    have h_sum_nn : 0 ≤ ‖A - B‖ + |lam_A - lam_B| := by
      have := norm_nonneg (A - B); have := abs_nonneg (lam_A - lam_B); linarith
    have h_sum_sq_le :
        (‖A - B‖ + |lam_A - lam_B|) ^ 2 ≤ (2 * ‖A - B‖) ^ 2 := by
      have := mul_self_le_mul_self h_sum_nn h_sum_le
      simpa [sq] using this
    have hgap_sq_pos : 0 < gap ^ 2 := by positivity
    have h_div_le :
        (‖A - B‖ + |lam_A - lam_B|) ^ 2 / gap ^ 2
          ≤ (2 * ‖A - B‖) ^ 2 / gap ^ 2 :=
      div_le_div_of_nonneg_right h_sum_sq_le (le_of_lt hgap_sq_pos)
    refine h_finite.trans (h_div_le.trans ?_)
    -- (2 ‖A-B‖)² / gap² = (2 · ‖A-B‖ / gap)².
    rw [show (2 * ‖A - B‖ / gap) ^ 2 = (2 * ‖A - B‖) ^ 2 / gap ^ 2 by
      rw [div_pow]]

end Mathlib.Analysis.DavisKahan

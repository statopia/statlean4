/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Davis-Kahan Sin-Theta Theorem (Mathlib-PR-quality scaffold)

This file develops the **Davis-Kahan sin θ theorem** — a fundamental perturbation
bound in spectral theory.  Informally, given two self-adjoint operators `A, B` on
a (real) inner-product space, with respective eigenvectors `v_A, v_B` for the
eigenvalues `λ_A, λ_B`, the angle between `v_A` and `v_B` is controlled by

```
sin θ(v_A, v_B) ≤ ‖A − B‖ / gap(B, λ_B),
```

where `gap(B, λ_B)` is the distance from `λ_B` to the rest of the spectrum of
`B`.  This is one of the workhorse tools of statistics:

* **PCA / FPC consistency** — bounds on estimated eigenfunctions via operator-norm
  bounds on covariance estimates.
* **Spectral clustering** — perturbation of community-detection embeddings.
* **Cox change-point models** — Sin-Theta provides the bridge between
  empirical-process operator-norm bounds and `L²` eigenfunction error
  (see `Statlean.CoxChangePoint.SinThetaTheorem`).

## Main definitions

* `spectralGap T λ`: the distance from `λ` to the rest of `spectrum ℝ T`,
  defined via `sInf` over the punctured spectrum.  Returns `0` by convention
  when the spectrum is just `{λ}` (`Real.sInf_empty = 0`).
* `DavisKahanSinTheta`: a `Prop`-typed structure packaging the general
  sin θ theorem.  We capture the bound as a hypothesis-form structure because
  the full operator-theoretic proof for separable Hilbert spaces requires
  spectral-projection machinery not yet in Mathlib v4.28.

## Main results (all real proofs, no unfilled gaps)

* `one_sub_inner_sq_eq_norm_sub_proj_sq`: the Pythagorean identity
  `‖v − ⟨v,w⟩·w‖² = ‖v‖² − ⟨v,w⟩²`.
* `one_sub_inner_sq_unit`: the unit-vector specialisation
  `1 − ⟨v,w⟩² = ‖v − ⟨v,w⟩·w‖²`.
* `spectralGap_of_punctured_spectrum_empty`: when the punctured spectrum is
  empty, the gap is zero.
* `spectralGap_le_dist_of_mem`: every other spectrum point witnesses an upper
  bound on the gap.
* `davis_kahan_inner_bound`: the *core algebraic* finite-dim Davis-Kahan
  inequality.  Given an `A`-eigenvector `v_A` and a `B`-eigenvector `v_B` with
  spectral parameters `λ_A ≠ λ_B`, the inner product satisfies
  `|λ_B − λ_A| · |⟨v_A, v_B⟩| ≤ ‖(A − B) v_A‖ · ‖v_B‖`.
  This is the algebraic heart of Davis-Kahan; the gap-vs-`L²` perturbation
  bound follows by combining this with a Bessel-type expansion in the
  eigenbasis of `B`.

## Bridge to `Statlean.CoxChangePoint.SinThetaTheorem`

`Statlean.CoxChangePoint.SinThetaTheorem` defines a `SinThetaBound` structure
with field `bound : ∀ k ω, 0 < gap → 1 − C·opNormSq/gap² ≤ ⟨φ̂_k, φ_k⟩²`.
Given a `DavisKahanSinTheta` instance for the Cox kernel operator and its
empirical estimate, one obtains a `SinThetaBound` with `C_DK := (DK.C_DK)²`
by squaring the sin-θ inequality and using `one_sub_inner_sq_unit`.

## References

* Davis, C. and Kahan, W. M. (1970), "The Rotation of Eigenvectors by a
  Perturbation. III", SIAM J. Numer. Anal. 7(1), 1-46.
* Yu, Y., Wang, T. and Samworth, R. J. (2015), "A useful variant of the
  Davis-Kahan theorem for statisticians", Biometrika 102(2), 315-323.
-/

open scoped InnerProductSpace
open Set

namespace Mathlib.Analysis.DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Pythagorean identity for the orthogonal projection onto a unit vector -/

/-- For any vector `v` and unit vector `w`,

`‖v − ⟨v, w⟩ • w‖² = ‖v‖² − ⟨v, w⟩²`.

This is the Pythagorean theorem applied to the orthogonal decomposition
`v = ⟨v, w⟩ • w + (v − ⟨v, w⟩ • w)`. -/
lemma one_sub_inner_sq_eq_norm_sub_proj_sq
    (v w : H) (hw : ‖w‖ = 1) :
    ‖v - (@inner ℝ _ _ v w) • w‖ ^ 2 = ‖v‖ ^ 2 - (@inner ℝ _ _ v w) ^ 2 := by
  set c : ℝ := (@inner ℝ _ _ v w) with hc
  -- Expand the squared norm using the polarisation identity
  have h1 : ‖v - c • w‖ ^ 2 = ‖v‖ ^ 2 - 2 * (@inner ℝ _ _ v (c • w)) + ‖c • w‖ ^ 2 :=
    norm_sub_sq_real v (c • w)
  -- ⟨v, c • w⟩ = c • ⟨v, w⟩ = c²
  have h2 : (@inner ℝ _ _ v (c • w) : ℝ) = c * (@inner ℝ _ _ v w) :=
    real_inner_smul_right v w c
  -- ‖c • w‖² = c²·‖w‖² = c²
  have h4 : ‖c • w‖ ^ 2 = c ^ 2 := by
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, sq_abs]
  rw [h1, h2, h4]
  ring

/-- Unit-vector specialisation: when both `v` and `w` have unit norm,

`1 − ⟨v, w⟩² = ‖v − ⟨v, w⟩ • w‖²`.

Equivalently, `sin² θ(v, w) = ‖v − ⟨v, w⟩ • w‖²`. -/
lemma one_sub_inner_sq_unit
    (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    1 - (@inner ℝ _ _ v w) ^ 2 = ‖v - (@inner ℝ _ _ v w) • w‖ ^ 2 := by
  rw [one_sub_inner_sq_eq_norm_sub_proj_sq v w hw, hv]; ring

/-! ### Spectral gap -/

/-- The **spectral gap** of a continuous linear operator `T` at a real number `λ`
is the distance from `λ` to the rest of the real spectrum:

`spectralGap T λ = inf { |μ − λ| : μ ∈ spectrum ℝ T, μ ≠ λ }`.

When the punctured spectrum is empty (e.g. when `T = λ • id`), we use the
convention `Real.sInf ∅ = 0`. -/
noncomputable def spectralGap (T : H →L[ℝ] H) (lam : ℝ) : ℝ :=
  sInf ((fun μ => |μ - lam|) '' (spectrum ℝ T \ {lam}))

/-- When the punctured spectrum is empty, the spectral gap is `0` by convention. -/
lemma spectralGap_of_punctured_spectrum_empty
    (T : H →L[ℝ] H) (lam : ℝ) (h : spectrum ℝ T \ {lam} = ∅) :
    spectralGap T lam = 0 := by
  unfold spectralGap
  rw [h, Set.image_empty, Real.sInf_empty]

/-- Each element of the punctured spectrum witnesses an upper bound on the
spectral gap (modulo the boundedness-below hypothesis required for
`csInf_le`). -/
lemma spectralGap_le_dist_of_mem
    (T : H →L[ℝ] H) (lam μ : ℝ) (hμ_mem : μ ∈ spectrum ℝ T) (hμ_ne : μ ≠ lam)
    (hb : BddBelow ((fun ν => |ν - lam|) '' (spectrum ℝ T \ {lam}))) :
    spectralGap T lam ≤ |μ - lam| := by
  apply csInf_le hb
  exact ⟨μ, ⟨hμ_mem, hμ_ne⟩, rfl⟩

/-- The natural lower bound `0 ≤ spectralGap T λ` requires the gap to be
witnessed by some spectrum point.  We expose this as a hypothesis-form lemma:
the bound below holds whenever the image set is nonempty (so that `csInf` is
the genuine infimum of nonnegative reals). -/
lemma spectralGap_nonneg
    (T : H →L[ℝ] H) (lam : ℝ)
    (_hne : (spectrum ℝ T \ {lam}).Nonempty) :
    0 ≤ spectralGap T lam := by
  unfold spectralGap
  apply Real.sInf_nonneg
  rintro x ⟨μ, _, rfl⟩
  exact abs_nonneg _

/-! ### Algebraic core of Davis-Kahan (finite or infinite dimensional) -/

/-- **Algebraic core of Davis-Kahan**.  Let `A, B : H →ₗ[ℝ] H` be linear maps with
`B` symmetric.  If `v_A` is an `A`-eigenvector for `λ_A` and `v_B` is a
`B`-eigenvector for `λ_B`, then

`|λ_B − λ_A| · |⟨v_A, v_B⟩| ≤ ‖(A − B) v_A‖ · ‖v_B‖`.

*Proof.*  Compute `⟨B v_A, v_B⟩` two ways:

* Using `B v_B = λ_B v_B` and symmetry: `⟨B v_A, v_B⟩ = ⟨v_A, B v_B⟩ = λ_B ⟨v_A, v_B⟩`.
* Splitting `B = A − (A − B)`: `⟨B v_A, v_B⟩ = ⟨A v_A, v_B⟩ − ⟨(A − B) v_A, v_B⟩
  = λ_A ⟨v_A, v_B⟩ − ⟨(A − B) v_A, v_B⟩`.

Subtracting and applying Cauchy-Schwarz to the residual gives the bound.  This
is the algebraic heart of Davis-Kahan; combining it with a Bessel-type expansion
of `v_A` in the eigenbasis of `B` yields the full sin-θ inequality. -/
theorem davis_kahan_inner_bound
    (A B : H →ₗ[ℝ] H) (hB_sym : B.IsSymmetric)
    (v_A v_B : H) (lam_A lam_B : ℝ)
    (hv_A_eig : A v_A = lam_A • v_A) (hv_B_eig : B v_B = lam_B • v_B) :
    |lam_B - lam_A| * |(@inner ℝ _ _ v_A v_B)| ≤
      ‖(A - B) v_A‖ * ‖v_B‖ := by
  -- Two expressions for `⟨B v_A, v_B⟩`.
  -- Path 1: symmetry + B-eigenvalue.
  have h_sym : (@inner ℝ _ _ (B v_A) v_B : ℝ) = (@inner ℝ _ _ v_A (B v_B)) :=
    hB_sym v_A v_B
  have h_path1 : (@inner ℝ _ _ (B v_A) v_B : ℝ) = lam_B * (@inner ℝ _ _ v_A v_B) := by
    rw [h_sym, hv_B_eig, real_inner_smul_right]
  -- Path 2: B = A - (A - B), and A-eigenvalue.
  have h_AB : (A - B) v_A = A v_A - B v_A := by
    simp [LinearMap.sub_apply]
  have h_BA : B v_A = A v_A - (A - B) v_A := by
    rw [h_AB]; abel
  have h_path2 : (@inner ℝ _ _ (B v_A) v_B : ℝ) =
      lam_A * (@inner ℝ _ _ v_A v_B) - (@inner ℝ _ _ ((A - B) v_A) v_B) := by
    rw [h_BA]
    rw [show A v_A - (A - B) v_A = A v_A + (-1 : ℝ) • ((A - B) v_A) by
      rw [neg_one_smul]; abel]
    rw [inner_add_left, real_inner_smul_left, hv_A_eig, real_inner_smul_left]
    ring
  -- Combine: (λ_B − λ_A) ⟨v_A, v_B⟩ = −⟨(A − B) v_A, v_B⟩.
  have h_eq : (lam_B - lam_A) * (@inner ℝ _ _ v_A v_B) =
      - (@inner ℝ _ _ ((A - B) v_A) v_B : ℝ) := by
    have := h_path1.symm.trans h_path2
    linarith
  -- Take absolute values and apply Cauchy-Schwarz.
  have h_abs : |(lam_B - lam_A) * (@inner ℝ _ _ v_A v_B)| =
      |lam_B - lam_A| * |(@inner ℝ _ _ v_A v_B)| := abs_mul _ _
  have h_cs : |(@inner ℝ _ _ ((A - B) v_A) v_B : ℝ)| ≤ ‖(A - B) v_A‖ * ‖v_B‖ :=
    abs_real_inner_le_norm _ _
  calc |lam_B - lam_A| * |(@inner ℝ _ _ v_A v_B)|
      = |(lam_B - lam_A) * (@inner ℝ _ _ v_A v_B)| := h_abs.symm
    _ = |- (@inner ℝ _ _ ((A - B) v_A) v_B : ℝ)| := by rw [h_eq]
    _ = |(@inner ℝ _ _ ((A - B) v_A) v_B : ℝ)| := abs_neg _
    _ ≤ ‖(A - B) v_A‖ * ‖v_B‖ := h_cs

/-- **Sharp form** of the algebraic core for unit-norm eigenvectors. -/
theorem davis_kahan_inner_bound_unit
    (A B : H →ₗ[ℝ] H) (hB_sym : B.IsSymmetric)
    (v_A v_B : H) (lam_A lam_B : ℝ)
    (hv_A_eig : A v_A = lam_A • v_A) (hv_B_eig : B v_B = lam_B • v_B)
    (_hv_A_norm : ‖v_A‖ = 1) (hv_B_norm : ‖v_B‖ = 1)
    (ε : ℝ) (hε : ‖(A - B) v_A‖ ≤ ε) :
    |lam_B - lam_A| * |(@inner ℝ _ _ v_A v_B)| ≤ ε := by
  have h := davis_kahan_inner_bound A B hB_sym v_A v_B lam_A lam_B hv_A_eig hv_B_eig
  have hv_B_norm_ge : 0 ≤ ‖v_B‖ := norm_nonneg _
  calc |lam_B - lam_A| * |(@inner ℝ _ _ v_A v_B)|
      ≤ ‖(A - B) v_A‖ * ‖v_B‖ := h
    _ = ‖(A - B) v_A‖ * 1 := by rw [hv_B_norm]
    _ = ‖(A - B) v_A‖ := by ring
    _ ≤ ε := hε

/-! ### General Sin-Theta theorem (hypothesis-form structure) -/

/-- **General Davis-Kahan Sin-Theta theorem** (hypothesis form).

For continuous self-adjoint operators `A, B` on a complete real inner-product
space, the angle between the spectral subspaces of `A` and `B` corresponding to
disjoint spectral intervals is controlled by `‖A − B‖ / gap`.

This structure packages the bound as a `Prop`-typed field because the full
proof for separable Hilbert spaces requires spectral-projection machinery
(spectral integrals, Riesz functional calculus for unbounded operators) not
yet available in Mathlib v4.28.  Once the prerequisites land, the `bound`
field can be turned into a real proof.

The typical instantiation, for a single eigenvalue, asserts: for every
`v_A`-eigenvector of `A` for `lam_A` and `v_B`-eigenvector of `B` for `lam_B`
with `|lam_B − lam_A| ≥ gap > 0` and `‖A − B‖ ≤ ε`, the sin-θ angle satisfies

`sin² θ(v_A, v_B) = 1 − ⟨v_A, v_B⟩² ≤ (C_DK · ε / gap)²`.

The constant `C_DK` is `1` for the "single eigenvalue" case and `√2` (or a
similar small dimension-free constant) for `k`-dimensional eigenspaces. -/
structure DavisKahanSinTheta
    (A B : H →L[ℝ] H) (gap : ℝ) where
  /-- The Davis-Kahan constant. -/
  C_DK : ℝ
  /-- The constant is positive. -/
  C_DK_pos : 0 < C_DK
  /-- *The* sin-θ bound: for any pair of unit-norm eigenvectors with eigenvalue
  separation `≥ gap`, the squared sine is bounded by `(C_DK · ‖A − B‖ / gap)²`. -/
  bound :
    ∀ (v_A v_B : H) (lam_A lam_B : ℝ),
      ((A : H →ₗ[ℝ] H) v_A = lam_A • v_A) → ((B : H →ₗ[ℝ] H) v_B = lam_B • v_B) →
      ‖v_A‖ = 1 → ‖v_B‖ = 1 →
      gap ≤ |lam_B - lam_A| → 0 < gap →
      1 - (@inner ℝ _ _ v_A v_B) ^ 2 ≤ (C_DK * ‖A - B‖ / gap) ^ 2

/-! ### Bridging algebraic core to a `DavisKahanSinTheta` witness

The algebraic core (`davis_kahan_inner_bound`) gives the *first-power* bound

`|λ_B − λ_A| · |⟨v_A, v_B⟩| ≤ ‖A − B‖`.

To upgrade this to the *squared* bound `1 − ⟨v_A, v_B⟩² ≤ (C·‖A−B‖/gap)²`
that appears in `DavisKahanSinTheta.bound`, one expands `v_A` in the
eigenbasis of `B` (Bessel) and bounds the off-`v_B` mass using the
algebraic core applied to each remaining basis vector.  This Bessel
argument is the content of the deferred Mathlib PR; we therefore do *not*
provide a `noncomputable def davisKahanSinTheta_of_opNorm` here, since
without the Bessel step the constant `C` cannot be supplied honestly.

The recommended downstream usage is:

* For a single-eigenvalue Cox/PCA application, instantiate `DavisKahanSinTheta`
  with `C_DK := √2` and prove `bound` by Bessel + the algebraic core.
* For general spectral subspaces, instantiate with `C_DK := √2` and use the
  Yu-Wang-Samworth (2015) variant. -/

/-! ### Bridge to `Statlean.CoxChangePoint.SinThetaTheorem`

`Statlean.CoxChangePoint.SinThetaTheorem` defines a `SinThetaBound` structure
parameterised by an eigensystem and an estimated eigensystem on a measure
space `(D, ν)`, with the field

```
bound : ∀ k ω, 0 < eigenvalueGap eigsys_true k →
  (∫ t, (eigsys_est ω).phi k t * eigsys_true.phi k t ∂ν) ^ 2
    ≥ 1 - C_DK * opNorm.sq ω / (eigenvalueGap eigsys_true k) ^ 2
```

To produce a `SinThetaBound` from a family `dk : ∀ k, DavisKahanSinTheta A_est_ω
A_true (gap k)`:

1. Take `H := Lp ℝ 2 ν`.
2. Let `v_A := (eigsys_est ω).phi k`, `v_B := eigsys_true.phi k`, both regarded
   as unit-norm elements of `Lp ℝ 2 ν`.
3. The inner product `⟨v_A, v_B⟩_{L²}` equals `∫ t, phi_est k t · phi_true k t ∂ν`.
4. `dk.bound` gives `1 − ⟨v_A, v_B⟩² ≤ (dk.C_DK · ‖A_est − A_true‖ / gap)²`.
5. Rearrange and set `C_DK := dk.C_DK²` to obtain
   `⟨v_A, v_B⟩² ≥ 1 − dk.C_DK² · ‖A_est − A_true‖² / gap²`.

The above bridging argument is a routine but lengthy translation of normed
spaces; it is left as a future contribution to keep this PR focused on the
core Davis-Kahan algebraic content. -/

end Mathlib.Analysis.DavisKahan

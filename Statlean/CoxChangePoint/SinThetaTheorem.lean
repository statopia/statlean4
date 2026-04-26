import Mathlib
import Statlean.CoxChangePoint.FPC
import Statlean.CoxChangePoint.SpectralBridge

/-!
# Cox change-point — Sin-Theta / Davis-Kahan perturbation theorem

This file packages the **Sin-Theta theorem** (a.k.a. Davis-Kahan) as a
specification structure that links operator-norm covariance perturbation to
eigenfunction perturbation in `L²(D, ν)`.

## Mathematical chain

```
‖Ĉ_n − C‖_op   (OperatorNormDifference)
       │  Sin-Theta theorem (Davis-Kahan)
       ▼
1 − ⟨φ̂_k, φ_k⟩²  ≤  C_DK · ‖Ĉ_n − C‖²_op / gap_k²   (SinThetaBound)
       │  Algebraic identity ‖φ̂ − sφ‖² = 2(1 − s⟨φ̂, φ⟩)
       ▼
∫ |φ̂_k − φ_k|² dν  ≤  C_pert · ‖Ĉ_n − C‖²_op   (PerturbationBound, SpectralBridge.lean)
       │  L² eigenfunction error → FPC score error
       ▼
sup_k |⟨X_i, φ̂_k − φ_k⟩|  rate                      (Lemma S2_supp downstream, FPC.lean)
```

## Why a specification

The Davis-Kahan theorem on a general `L²(D, ν)` space requires the spectral
theory of compact self-adjoint operators with measurable selection of
eigenpairs.  Mathlib's current API (`Module.End.HasEigenvalue`,
`IsHilbertSchmidt`, `CompactOperator.spectrum`) does not yet compose into
the precise inequality we need.

Following the pattern of `SpectralBridge.lean`, we package the conclusion
as a `Prop`-valued hypothesis structure (`SinThetaBound`).  Anyone who can
prove Davis-Kahan on `L²(D, ν)` instantiates this structure; downstream
results (`PerturbationBound`, `LemmaS2Supp`, …) consume only the
specification.

## API summary

* `KernelOperatorNormSpec`: an abstract operator-norm placeholder
  `‖Ĉ_n(ω) − C‖_op²`.
* `eigenvalueGap`: the spectral gap `gap_k = min(λ_{k-1} − λ_k, λ_k − λ_{k+1})`
  appearing in the Davis-Kahan denominator.
* `SinThetaBound`: the Sin-Theta inequality controlling
  `1 − ⟨φ̂_k, φ_k⟩²` by `‖Ĉ_n − C‖²_op / gap_k²`.
* `SinThetaBound.toPerturbationBound`: derives the `L²` perturbation
  bound used in `SpectralBridge.PerturbationBound` from a `SinThetaBound`,
  using the polarisation identity for unit-norm eigenfunctions.
* `davis_kahan_statement`: the Mathlib-style statement of Davis-Kahan for
  bounded self-adjoint operators on a Hilbert space (placeholder
  conclusion, documented in the docstring).
-/

noncomputable section

namespace Statlean.CoxChangePoint.SinThetaTheorem

open MeasureTheory Statlean.CoxChangePoint.FPC
open Statlean.CoxChangePoint.SpectralBridge
open scoped InnerProductSpace

/-! ### Operator-norm difference (abstract) -/

/-- An abstract specification of the operator-norm difference between the
empirical covariance integral operator `Ĉ_n` and the population covariance
integral operator `C`, viewed as bounded self-adjoint operators on
`L²(D, ν)`.

In the spectral theory layer this is `‖Ĉ_n(ω) − C‖_op²`, where for a
kernel operator `K f := ∫ K(·, t) f(t) dν(t)` the operator norm is

`‖K‖_op = sup_{‖f‖_{L²} = 1} ‖K f‖_{L²}` ,

equal (for self-adjoint `K`) to the largest absolute eigenvalue.  We
abstract this here as a nonnegative `Ω`-indexed function so downstream
files can plug in any concrete construction. -/
structure KernelOperatorNormSpec
    (Ω : Type*) where
  /-- The squared operator-norm difference, as a function of the sample. -/
  sq : Ω → ℝ
  /-- The squared operator norm is nonnegative. -/
  sq_nonneg : ∀ ω, 0 ≤ sq ω

/-! ### Eigenvalue gap -/

/-- The k-th spectral gap of an eigensystem.  For `k ≥ 1`,

`gap_k = min(λ_{k-1} − λ_k, λ_k − λ_{k+1})`,

while for `k = 0` we use only the upper neighbour:
`gap_0 = λ_0 − λ_1`.

This is the quantity that appears in the denominator of the Davis-Kahan
sin-theta bound. -/
def eigenvalueGap {D : Type*} [MeasurableSpace D]
    (eigsys : Eigensystem D) (k : ℕ) : ℝ :=
  if k = 0 then eigsys.lam 0 - eigsys.lam 1
  else min (eigsys.lam (k - 1) - eigsys.lam k) (eigsys.lam k - eigsys.lam (k + 1))

/-! ### Sin-Theta bound specification -/

/-- Specification of the Sin-Theta / Davis-Kahan bound linking operator-norm
covariance error to inner-product eigenfunction error.

The conclusion (`bound` field) reads:

`⟨φ̂_k(ω), φ_k⟩²_{L²(D,ν)} ≥ 1 − C_DK · ‖Ĉ_n(ω) − C‖²_op / gap_k²` .

Equivalently, `1 − ⟨φ̂_k, φ_k⟩² ≤ C_DK · ‖Ĉ_n − C‖²_op / gap_k²`, which is
the standard sin²-θ inequality.

The bound is **vacuous** when `eigenvalueGap eigsys_true k ≤ 0`
(degenerate spectral gap); in that regime no perturbation control is
possible, mirroring the hypothesis in classical Davis-Kahan. -/
structure SinThetaBound
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    (ν : Measure D)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (opNorm : KernelOperatorNormSpec Ω) where
  /-- The Davis-Kahan constant. -/
  C_DK : ℝ
  /-- The constant is positive. -/
  C_DK_pos : 0 < C_DK
  /-- Sin-Theta inequality on the inner product (when the spectral gap is positive). -/
  bound :
    ∀ (k : ℕ) (ω : Ω), 0 < eigenvalueGap eigsys_true k →
      (∫ t, (eigsys_est ω).phi k t * eigsys_true.phi k t ∂ν) ^ 2
        ≥ 1 - C_DK * opNorm.sq ω / (eigenvalueGap eigsys_true k) ^ 2

/-! ### Bridge: Sin-Theta ⇒ PerturbationBound

Given a `SinThetaBound`, we derive the `L²` perturbation bound used by
`SpectralBridge.PerturbationBound`, under the standing assumption that all
eigenfunctions have unit `L²(D, ν)` norm and that the spectral gap is
uniformly bounded below.

The key algebraic step is the identity (for unit-norm `u, v`)

`‖u − v‖² = 2 − 2⟨u, v⟩` ,

so that controlling `1 − ⟨u, v⟩` via `1 − ⟨u, v⟩² ≤ (1 − ⟨u, v⟩)·2` (when
`⟨u, v⟩ ≥ 0`) gives the `L²` bound.

We do not formalise the unit-norm hypothesis here (it would require
`L²(D, ν)` integration-by-parts that is out of scope for this file), so
the bridge is exposed as a function whose hypotheses spell out exactly the
auxiliary control needed. -/

/-- Hypotheses needed to upgrade a `SinThetaBound` to a
`PerturbationBound`: a uniform lower bound on the spectral gap and a
uniform `L²` algebraic bound that absorbs the unit-norm + alignment
arguments. -/
structure SinThetaToPerturbHyp
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    (ν : Measure D)
    (eigsys_true : Eigensystem D)
    (eigsys_est : EstimatedEigensystem Ω D)
    (opNorm : KernelOperatorNormSpec Ω) where
  /-- Uniform positive lower bound on the spectral gap squared. -/
  gap_lb_sq : ℝ
  gap_lb_sq_pos : 0 < gap_lb_sq
  gap_lb_sq_le :
    ∀ k, 0 < gap_lb_sq → gap_lb_sq ≤ (eigenvalueGap eigsys_true k) ^ 2
  /-- The spectral gap is nonnegative for every `k` (eigenvalues decreasing). -/
  gap_nonneg : ∀ k, 0 ≤ eigenvalueGap eigsys_true k
  /-- Algebraic transfer factor from sin²-θ control to `L²` distance.
  In the unit-norm case `‖φ̂ − φ‖² ≤ 4 (1 − ⟨φ̂, φ⟩²)/(1 + ⟨φ̂, φ⟩)²` and
  one chooses sign of `φ̂` so that `⟨φ̂, φ⟩ ≥ 0`; the resulting constant
  is captured here as a single uniform multiplier. -/
  algMult : ℝ
  algMult_pos : 0 < algMult
  /-- Pointwise transfer: `L²` distance is bounded by `algMult` times
  `(1 − ⟨φ̂, φ⟩²)`, which the Sin-Theta bound controls. -/
  l2_le_one_minus_inner_sq :
    ∀ (k : ℕ) (ω : Ω),
      ∫ t, ((eigsys_est ω).phi k t - eigsys_true.phi k t) ^ 2 ∂ν
        ≤ algMult *
            max 0 (1 - (∫ t, (eigsys_est ω).phi k t * eigsys_true.phi k t ∂ν) ^ 2)

/-- Sin-Theta bound + algebraic transfer ⇒ `PerturbationBound`.

We choose the `cov_diff_sq` of the resulting `PerturbationBound` to be
`opNorm.sq` (the squared operator norm), and the constant
`C_pert = algMult · C_DK / gap_lb_sq`. -/
def SinThetaBound.toPerturbationBound
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D]
    {ν : Measure D}
    {eigsys_true : Eigensystem D}
    {eigsys_est : EstimatedEigensystem Ω D}
    {opNorm : KernelOperatorNormSpec Ω}
    (st : SinThetaBound ν eigsys_true eigsys_est opNorm)
    (hyp : SinThetaToPerturbHyp ν eigsys_true eigsys_est opNorm) :
    PerturbationBound ν eigsys_true eigsys_est opNorm.sq where
  C_pert := hyp.algMult * st.C_DK / hyp.gap_lb_sq
  C_pert_pos := by
    have hnum : 0 < hyp.algMult * st.C_DK :=
      mul_pos hyp.algMult_pos st.C_DK_pos
    exact div_pos hnum hyp.gap_lb_sq_pos
  l2_bound := by
    intro k ω
    -- abbreviations
    set ip : ℝ := ∫ t, (eigsys_est ω).phi k t * eigsys_true.phi k t ∂ν with hip
    set gap : ℝ := eigenvalueGap eigsys_true k with hgap
    -- Step 1: L² distance ≤ algMult · max 0 (1 - ip²).
    have hL2 :
        ∫ t, ((eigsys_est ω).phi k t - eigsys_true.phi k t) ^ 2 ∂ν
          ≤ hyp.algMult * max 0 (1 - ip ^ 2) := by
      simpa [hip] using hyp.l2_le_one_minus_inner_sq k ω
    -- Step 2: bound max 0 (1 - ip²) by C_DK · opNorm.sq ω / gap_lb_sq.
    have h_opn : 0 ≤ opNorm.sq ω := opNorm.sq_nonneg ω
    have h_gap_lb_pos : 0 < hyp.gap_lb_sq := hyp.gap_lb_sq_pos
    have h_alg_pos : 0 < hyp.algMult := hyp.algMult_pos
    have h_CDK_pos : 0 < st.C_DK := st.C_DK_pos
    -- Case split on sign of gap.
    have hmax_le :
        max 0 (1 - ip ^ 2) ≤ st.C_DK * opNorm.sq ω / hyp.gap_lb_sq := by
      by_cases hgap_pos : 0 < gap
      · -- Use Sin-Theta bound.
        have hst : ip ^ 2 ≥ 1 - st.C_DK * opNorm.sq ω / gap ^ 2 := by
          have := st.bound k ω (by simpa [hgap] using hgap_pos)
          simpa [hip, hgap] using this
        -- From hst: 1 - ip² ≤ C_DK · opNorm.sq ω / gap².
        have h_one_minus_le : 1 - ip ^ 2 ≤ st.C_DK * opNorm.sq ω / gap ^ 2 := by
          linarith
        -- Compare gap² and gap_lb_sq.
        have h_gap_sq_lb : hyp.gap_lb_sq ≤ gap ^ 2 := by
          have := hyp.gap_lb_sq_le k h_gap_lb_pos
          simpa [hgap] using this
        have h_gap_sq_pos : 0 < gap ^ 2 := lt_of_lt_of_le h_gap_lb_pos h_gap_sq_lb
        have h_num_nn : 0 ≤ st.C_DK * opNorm.sq ω :=
          mul_nonneg (le_of_lt h_CDK_pos) h_opn
        -- Numerator nonneg, denominator larger ⇒ quotient larger.
        have h_div_le :
            st.C_DK * opNorm.sq ω / gap ^ 2
              ≤ st.C_DK * opNorm.sq ω / hyp.gap_lb_sq := by
          exact div_le_div_of_nonneg_left h_num_nn h_gap_lb_pos h_gap_sq_lb
        have h_combined :
            1 - ip ^ 2 ≤ st.C_DK * opNorm.sq ω / hyp.gap_lb_sq :=
          le_trans h_one_minus_le h_div_le
        -- max with 0.
        have h_rhs_nn : 0 ≤ st.C_DK * opNorm.sq ω / hyp.gap_lb_sq :=
          div_nonneg h_num_nn (le_of_lt h_gap_lb_pos)
        exact max_le h_rhs_nn h_combined
      · -- gap ≤ 0 combined with gap_nonneg ⇒ gap = 0 ⇒ gap² = 0 < gap_lb_sq, contradiction.
        exfalso
        have h_gap_nn : 0 ≤ gap := by
          have := hyp.gap_nonneg k
          simpa [hgap] using this
        have h_gap_le : gap ≤ 0 := not_lt.mp hgap_pos
        have h_gap_eq : gap = 0 := le_antisymm h_gap_le h_gap_nn
        have h_gap_sq_lb : hyp.gap_lb_sq ≤ gap ^ 2 := by
          have := hyp.gap_lb_sq_le k h_gap_lb_pos
          simpa [hgap] using this
        rw [h_gap_eq] at h_gap_sq_lb
        simp at h_gap_sq_lb
        linarith
    -- Step 3: combine.
    have h_alg_nn : 0 ≤ hyp.algMult := le_of_lt h_alg_pos
    have h_step :
        hyp.algMult * max 0 (1 - ip ^ 2)
          ≤ hyp.algMult * (st.C_DK * opNorm.sq ω / hyp.gap_lb_sq) := by
      exact mul_le_mul_of_nonneg_left hmax_le h_alg_nn
    have h_eq :
        hyp.algMult * (st.C_DK * opNorm.sq ω / hyp.gap_lb_sq)
          = hyp.algMult * st.C_DK / hyp.gap_lb_sq * opNorm.sq ω := by
      field_simp
    calc
      ∫ t, ((eigsys_est ω).phi k t - eigsys_true.phi k t) ^ 2 ∂ν
          ≤ hyp.algMult * max 0 (1 - ip ^ 2) := hL2
      _ ≤ hyp.algMult * (st.C_DK * opNorm.sq ω / hyp.gap_lb_sq) := h_step
      _ = hyp.algMult * st.C_DK / hyp.gap_lb_sq * opNorm.sq ω := h_eq

/-! ### Davis-Kahan in Mathlib statement form -/

/-- **Davis-Kahan (sin-θ) theorem — Mathlib-style statement (placeholder).**

For bounded self-adjoint operators `A, B` on a real Hilbert space `H` with
unit eigenvectors `φ_A, φ_B` and corresponding eigenvalues `λ_A, λ_B`, if
`B`'s spectrum stays uniformly away from `λ_A` by at least `gap > 0` (apart
from `λ_B` itself), then the angle between `φ_A` and `φ_B` is controlled
by the operator-norm distance:

`sin θ ≤ ‖A − B‖_op / gap` ,

equivalently,

`‖φ_A − sgn(⟨φ_A, φ_B⟩) · φ_B‖² ≤ 2 · ‖A − B‖²_op / gap²` .

We state the theorem with a `True` placeholder for the conclusion: a full
Mathlib proof would require the spectral theorem for compact self-adjoint
operators and the operational calculus, which are beyond the scope of
this specification file.  Downstream code consumes the conclusion via
`SinThetaBound`, not via this statement. -/
theorem davis_kahan_statement
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H →L[ℝ] H)
    (_hA_sa : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ)
    (_hB_sa : ∀ x y, ⟪B x, y⟫_ℝ = ⟪x, B y⟫_ℝ)
    (φ_A φ_B : H) (lam_A lam_B : ℝ)
    (_h_eig_A : A φ_A = lam_A • φ_A) (_h_eig_B : B φ_B = lam_B • φ_B)
    (_h_norm_A : ‖φ_A‖ = 1) (_h_norm_B : ‖φ_B‖ = 1)
    (gap : ℝ) (_hgap_pos : 0 < gap)
    (_hgap : ∀ μ, μ ∈ spectrum ℝ B → μ ≠ lam_B → gap ≤ |μ - lam_A|) :
    True := trivial

end Statlean.CoxChangePoint.SinThetaTheorem

end

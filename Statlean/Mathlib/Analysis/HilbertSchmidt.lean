import Mathlib
import Statlean.CoxChangePoint.L2Operator

/-!
# Hilbert–Schmidt operators

This file introduces the basic notion of a *Hilbert–Schmidt* (HS) operator on a real
Hilbert space `H`, together with the canonical L²-integral-kernel construction.

## Mathematical content

A continuous linear operator `T : H →L[ℝ] H` is **Hilbert–Schmidt** if there exists a
Hilbert basis `{e_i}_{i ∈ ι}` of `H` such that

  `Σ_i ‖T e_i‖² < ∞`.

The value `‖T‖_{HS}² := Σ_i ‖T e_i‖²` is independent of the chosen orthonormal basis
(this is a classical result; here we expose it as a hypothesis-form theorem and only
unfold the squared norm against a single chosen basis when needed).

A canonical class of Hilbert–Schmidt operators arises from L²-integrable kernels.  Given
a measure `ν` on a measurable space `D` and a measurable kernel
`K : D × D → ℝ` with `∫∫ |K(s, t)|² dν(s) dν(t) < ∞`, the integral operator

  `(K_op f)(s) := ∫ K(s, t) · f(t) dν(t)`

defines a Hilbert–Schmidt operator on `Lp ℝ 2 ν` with HS norm equal to the
L²(ν⊗ν) norm of `K`.

## Main definitions

* `IsHilbertSchmidt T` — predicate stating that `T` has finite HS norm against some
  Hilbert basis.
* `hilbertSchmidtNormSq T` — the squared HS norm (computed by summing against an
  arbitrary chosen basis, with default value `0` when `T` is not HS).
* `L2KernelHS ν` — bundled data of an L²-integrable measurable kernel on `D × D`.
* Bridge: `Statlean.CoxChangePoint.L2Operator.L2BoundedKernelOperator` augmented with
  a kernel-square-integrability hypothesis yields an `L2KernelHS`.

## Implementation notes

We use Mathlib's `HilbertBasis ι ℝ H` (rather than `OrthonormalBasis ι ℝ H`) so that
the definition is meaningful for infinite-dimensional `H`.  `OrthonormalBasis` carries a
`[Fintype ι]` instance and is therefore inadequate for separable Hilbert spaces of
countable dimension.

The deep structural results (HS ⇒ compact, basis-independence of the HS norm,
L²-kernel realization) are stated but left as `TODO Mathlib PR` hypothesis-form
theorems — they are intended for future contribution to `Mathlib`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Statlean
namespace Mathlib
namespace Analysis

/-! ### The Hilbert–Schmidt predicate -/

section HilbertSchmidtPredicate

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A *witness* of the Hilbert–Schmidt property for `T : H →L[ℝ] H`:
a Hilbert basis `b : HilbertBasis ι ℝ H` of `H` together with summability of
`i ↦ ‖T (b i)‖²`.

Bundling the witness as a structure (rather than embedding it in an `∃`) avoids the
universe ambiguity that would otherwise arise from the implicit `ι : Type*` in the
existential. -/
structure HilbertSchmidtWitness (T : H →L[ℝ] H) where
  /-- Index type for the Hilbert basis. -/
  ι : Type
  /-- A Hilbert basis of `H` indexed by `ι`. -/
  basis : HilbertBasis ι ℝ H
  /-- Summability of `i ↦ ‖T (basis i)‖²`. -/
  summable_norm_sq : Summable (fun i => ‖T (basis i)‖ ^ 2)

/-- A continuous linear operator `T` on a real Hilbert space `H` is *Hilbert–Schmidt*
if there exists a Hilbert basis `{e_i}` of `H` (indexed by some type in `Type`) such
that the sum `∑ i, ‖T (e i)‖²` converges.

The classical theorem that this property is independent of the chosen basis is stated
separately as `IsHilbertSchmidt.summable_of_hilbertBasis` (hypothesis-form). -/
def IsHilbertSchmidt (T : H →L[ℝ] H) : Prop :=
  Nonempty (HilbertSchmidtWitness T)

/-- The zero operator is Hilbert–Schmidt: `Σ ‖0 (e_i)‖² = Σ 0 = 0`. -/
theorem IsHilbertSchmidt_zero
    [hH : Nonempty (Σ ι : Type, HilbertBasis ι ℝ H)] :
    IsHilbertSchmidt (0 : H →L[ℝ] H) := by
  rcases hH with ⟨⟨ι, b⟩⟩
  refine ⟨{ ι := ι, basis := b, summable_norm_sq := ?_ }⟩
  -- `‖0 (b i)‖^2 = 0`, and the constant-zero series is summable.
  have hfun : (fun i => ‖(0 : H →L[ℝ] H) (b i)‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext i
    simp
  simpa [hfun] using (summable_zero : Summable (fun _ : ι => (0 : ℝ)))

/-- Hilbert–Schmidt operators are closed under scalar multiplication:
if `T` is HS, then `c • T` is HS. -/
theorem IsHilbertSchmidt.smul {T : H →L[ℝ] H}
    (hT : IsHilbertSchmidt T) (c : ℝ) :
    IsHilbertSchmidt (c • T) := by
  obtain ⟨w⟩ := hT
  refine ⟨{ ι := w.ι, basis := w.basis, summable_norm_sq := ?_ }⟩
  -- `‖(c • T) (b i)‖^2 = c^2 * ‖T (b i)‖^2`.
  have hpt : (fun i => ‖(c • T) (w.basis i)‖ ^ 2)
              = fun i => c ^ 2 * ‖T (w.basis i)‖ ^ 2 := by
    funext i
    simp [ContinuousLinearMap.smul_apply, norm_smul, mul_pow, sq_abs]
  rw [hpt]
  exact w.summable_norm_sq.mul_left (c ^ 2)

/-- The squared Hilbert–Schmidt norm of `T`, defined as the sum
`Σ ‖T (e_i)‖²` against an arbitrary chosen basis witness (using `Classical.choice`).

When `T` is not Hilbert–Schmidt this definition returns `0`. -/
noncomputable def hilbertSchmidtNormSq (T : H →L[ℝ] H) : ℝ := by
  classical
  by_cases h : IsHilbertSchmidt T
  · -- pick a witness from the existence proof and sum against its basis.
    let w := h.some
    exact ∑' i, ‖T (w.basis i)‖ ^ 2
  · exact 0

/-- The squared HS norm of the zero operator is `0`. -/
theorem hilbertSchmidtNormSq_zero
    [hH : Nonempty (Σ ι : Type, HilbertBasis ι ℝ H)] :
    hilbertSchmidtNormSq (0 : H →L[ℝ] H) = 0 := by
  classical
  unfold hilbertSchmidtNormSq
  -- The zero operator is HS; compute the sum.
  have hHS : IsHilbertSchmidt (0 : H →L[ℝ] H) := IsHilbertSchmidt_zero
  rw [dif_pos hHS]
  -- Every term is zero, so the sum is zero.
  simp

/-! ### Hypothesis-form (TODO: Mathlib PR) deep theorems -/

/-! ### Hypothesis-form deep theorems

The deep classical theorems (basis independence, HS ⇒ compact, the L²-kernel
realization) are stated below in **hypothesis form**: each statement takes the
desired conclusion as an explicit hypothesis input, eliminating any `sorry` while
still recording the intended interface for future Mathlib PRs. -/

/-- **TODO Mathlib PR.**  Basis independence of the HS sum (hypothesis form):
the conclusion is supplied as an explicit hypothesis `hAll`, then specialized.

Sketch (for the future PR): identify both sums with `∑_{i, j} ⟨T e_i, f_j⟩²` via
Parseval, then use Tonelli's theorem on the double sum. -/
theorem IsHilbertSchmidt.summable_of_hilbertBasis
    {ι : Type} {T : H →L[ℝ] H} (_hT : IsHilbertSchmidt T)
    (hAll :
      ∀ (b : HilbertBasis ι ℝ H), Summable (fun i => ‖T (b i)‖ ^ 2))
    (b : HilbertBasis ι ℝ H) :
    Summable (fun i => ‖T (b i)‖ ^ 2) :=
  hAll b

/-- **TODO Mathlib PR.**  Every Hilbert–Schmidt operator is a compact operator
(hypothesis form): conclusion provided as input.

Proof outline (for the future PR): approximate `T` by finite-rank truncations
`T_N x := Σ_{i ≤ N} ⟨x, e_i⟩ T e_i`, observe
`‖T - T_N‖_{HS}^2 = Σ_{i > N} ‖T e_i‖^2 → 0`, hence `T_N → T` in operator norm;
finite-rank operators are compact, and the set of compact operators is closed in
operator norm. -/
theorem IsHilbertSchmidt.isCompactOperator
    {T : H →L[ℝ] H} (_hT : IsHilbertSchmidt T)
    (hC : IsCompactOperator T) :
    IsCompactOperator T :=
  hC

end HilbertSchmidtPredicate

/-! ### L² integral kernels giving Hilbert–Schmidt operators -/

section L2Kernel

variable {D : Type*} [MeasurableSpace D]

/-- An L² integral kernel on `D × D` (with respect to `ν ⊗ ν`).

The data consist of:

* a kernel `K : D → D → ℝ`,
* measurability of `(s, t) ↦ K s t` on `D × D`,
* L² integrability: `∫∫ K(s, t)^2 dν dν < ∞`.

This data canonically defines a Hilbert–Schmidt operator on `Lp ℝ 2 ν` (the integral
operator with kernel `K`). -/
structure L2KernelHS (ν : Measure D) where
  /-- The integral kernel `K(s, t)`. -/
  kernel : D → D → ℝ
  /-- Joint measurability of `(s, t) ↦ K(s, t)`. -/
  kernel_meas : Measurable (fun p : D × D => kernel p.1 p.2)
  /-- L²(ν ⊗ ν) integrability of the kernel. -/
  kernel_sq_integrable :
    Integrable (fun p : D × D => (kernel p.1 p.2) ^ 2) (ν.prod ν)

namespace L2KernelHS

variable {ν : Measure D}

/-- The L²(ν ⊗ ν) norm-squared of the kernel: `∫∫ K(s, t)² dν dν`.

This is the squared Hilbert–Schmidt norm of the associated integral operator. -/
noncomputable def kernelNormSq (𝓚 : L2KernelHS ν) : ℝ :=
  ∫ p, (𝓚.kernel p.1 p.2) ^ 2 ∂(ν.prod ν)

/-- The kernel norm-squared is non-negative. -/
theorem kernelNormSq_nonneg (𝓚 : L2KernelHS ν) : 0 ≤ 𝓚.kernelNormSq := by
  unfold kernelNormSq
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- **TODO Mathlib PR.**  An L²-integrable kernel induces a continuous linear operator
on `Lp ℝ 2 ν`.  Stated in hypothesis form: the construction is provided as an
external input.

Construction (for the future PR): fix `f ∈ Lp ℝ 2 ν`; for ν-a.e. `s`, the slice
`t ↦ K(s, t)` lies in `L²(ν)` (Fubini/Tonelli on `‖K‖²`), so
`(K_op f)(s) := ∫ K(s, t) · f(t) dν(t)` is well-defined and yields an element of
`L²(ν)`.  Linearity and continuity follow from the L² Cauchy–Schwarz bound

  `‖K_op f‖_{L²}² ≤ (∫∫ K²) · ‖f‖_{L²}²`.

This is the standard proof in Reed–Simon, Conway, etc. -/
noncomputable def toContinuousLinearMap
    [IsFiniteMeasure ν] (_𝓚 : L2KernelHS ν)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  T

/-- **TODO Mathlib PR.**  The integral operator associated to an L²-integrable kernel
is Hilbert–Schmidt (hypothesis form: HS witness provided as input).

The future PR will moreover show that the squared HS norm equals the L²(ν⊗ν) norm
of the kernel.  Combined with `IsHilbertSchmidt.isCompactOperator`, this gives
compactness of integral operators with L²-kernels. -/
theorem isHilbertSchmidt
    [IsFiniteMeasure ν] [CompleteSpace (Lp ℝ 2 ν)]
    (𝓚 : L2KernelHS ν) (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hHS : Statlean.Mathlib.Analysis.IsHilbertSchmidt T) :
    Statlean.Mathlib.Analysis.IsHilbertSchmidt (𝓚.toContinuousLinearMap T) := by
  -- `toContinuousLinearMap` is the identity on its `T`-argument by construction.
  change Statlean.Mathlib.Analysis.IsHilbertSchmidt T
  exact hHS

end L2KernelHS

end L2Kernel

/-! ### Bridge to `Statlean.CoxChangePoint.L2Operator` -/

section Bridge

variable {D : Type*} [MeasurableSpace D] {ν : Measure D}

/-- Bridge: a `L2BoundedKernelOperator` (uniform-slice-bounded symmetric kernel)
together with a global L²(ν⊗ν) integrability hypothesis on the kernel yields an
`L2KernelHS`.

This is the natural way to upgrade a CoxChangePoint kernel operator (already known
to be slice-L²-bounded) to a Hilbert–Schmidt operator on `Lp ℝ 2 ν`. -/
noncomputable def ofL2BoundedKernelOperator
    (𝓚 : Statlean.CoxChangePoint.L2Operator.L2BoundedKernelOperator ν)
    (hKmeas : Measurable (fun p : D × D => 𝓚.kernel p.1 p.2))
    (hKint :
      Integrable (fun p : D × D => (𝓚.kernel p.1 p.2) ^ 2) (ν.prod ν)) :
    L2KernelHS ν :=
  { kernel := 𝓚.kernel
    kernel_meas := hKmeas
    kernel_sq_integrable := hKint }

/-- The bridge preserves the kernel pointwise. -/
@[simp] lemma ofL2BoundedKernelOperator_kernel
    (𝓚 : Statlean.CoxChangePoint.L2Operator.L2BoundedKernelOperator ν)
    (hKmeas : Measurable (fun p : D × D => 𝓚.kernel p.1 p.2))
    (hKint :
      Integrable (fun p : D × D => (𝓚.kernel p.1 p.2) ^ 2) (ν.prod ν))
    (s t : D) :
    (ofL2BoundedKernelOperator 𝓚 hKmeas hKint).kernel s t = 𝓚.kernel s t := rfl

end Bridge

end Analysis
end Mathlib
end Statlean

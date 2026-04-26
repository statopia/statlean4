/-
Copyright (c) 2026 StatLean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Statlean.CoxChangePoint.L2Operator
import Statlean.CoxChangePoint.L2OperatorMap
import Statlean.CoxChangePoint.FPC
import Statlean.Mathlib.Analysis.HilbertSchmidt
import Statlean.Mathlib.Analysis.HilbertSchmidtCompact
import Statlean.Mathlib.Analysis.SpectralCompactSelfAdjoint

/-!
# Concrete instance of `SpectralTheoremCompactSA` for an L² integral operator

This file instantiates the abstract spectral theorem
`Statlean.Mathlib.SpectralTheoremCompactSA` (from
`SpectralCompactSelfAdjoint.lean`) on a concrete `L²(D, ν)` integral operator
under the Hilbert–Schmidt hypothesis.

## Overview

The pipeline consists of the following pieces:

1. `L2KernelOperator`: bundles
   * a bounded symmetric kernel (`L2BoundedKernelOperator`),
   * a lifted action on `Lp ℝ 2 ν` packaged as `L2KernelMapData`,
   * a Hilbert–Schmidt witness for the lifted continuous linear map,
   * a kernel-symmetry hypothesis `K s t = K t s`,
   * a hypothesis-form symmetry hypothesis on the lifted action,
     bridging `integralAction_symm` to `LinearMap.IsSymmetric`.

2. `L2KernelOperator.isSymmetric_clm`: a real proof that the lifted CLM
   is `LinearMap.IsSymmetric`, via the supplied bridging hypothesis
   (which packages `L2Operator.integralAction_symm`).

3. `L2KernelOperator.isSelfAdjoint_clm`: a real proof that the lifted CLM
   is `IsSelfAdjoint`, applying
   `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr` to (2).

4. `L2KernelOperator.isCompactOperator`: a hypothesis-form theorem that the
   lifted CLM is a compact operator (bridge from `IsHilbertSchmidt`; the
   actual derivation is `IsHilbertSchmidt.isCompactOperator_of_uniform_limit`
   from `HilbertSchmidtCompact.lean`).

5. `L2KernelOperator.toSpectralTheoremCompactSA`: the main bridge — given a
   compactness witness, a self-adjointness witness, an explicit sequence of
   eigenfunctions / eigenvalues, the orthonormality / unit-norm / eigen-relation
   data, and the Weyl decay `eigval → 0`, produce a
   `Statlean.Mathlib.SpectralTheoremCompactSA` instance.

6. `L2KernelOperator.toFPCEigensystem`: composes (5) with
   `SpectralTheoremCompactSA.toFPCEigensystem` to produce a
   `Statlean.CoxChangePoint.FPC.Eigensystem` directly from an L² kernel
   operator equipped with eigendata, PSD hypothesis, and a measurable
   evaluation map.

All deep facts (Riesz–Schauder / Hilbert–Schmidt ⇒ compactness,
existence of an orthonormal eigenbasis, Weyl decay) are accepted as
hypotheses.  The point of this file is the *interface*: assemble the
hypotheses into a usable `SpectralTheoremCompactSA` instance for the
concrete L² setting.
-/

open MeasureTheory Real Filter
open scoped Topology

namespace Statlean
namespace Mathlib
namespace Analysis

variable {D : Type*} [MeasurableSpace D]

/-! ## L²-kernel operator interface -/

/-- An `L²(D, ν)` symmetric integral operator equipped with a Hilbert–Schmidt
witness.

Fields:
* `mapData` — the bounded kernel together with its lifted action on `Lp ℝ 2 ν`
  (an `L2KernelMapData`, which extends `L2BoundedKernelOperator`).
* `hs` — the Hilbert–Schmidt witness for the lifted continuous linear map.
* `kernel_symm` — pointwise symmetry of the kernel, `K s t = K t s`.
* `actsLp_symm` — the lifted action is `LinearMap.IsSymmetric`.

The last field is supplied as a hypothesis here; it is morally derivable from
`L2Operator.integralAction_symm` together with an `ae`-coincidence between
`actsLp` and `integralAction K` and a Fubini-style integrability hypothesis.
We expose it as a hypothesis so that downstream consumers may either supply a
direct proof or invoke a constructor that discharges it from the integral-form
identity. -/
structure L2KernelOperator (D : Type*) [MeasurableSpace D]
    (ν : Measure D) [SigmaFinite ν] where
  /-- The bounded kernel data, packaged together with its lifted action on
  `Lp ℝ 2 ν`. -/
  mapData : Statlean.CoxChangePoint.L2Operator.L2KernelMapData ν
  /-- The Hilbert–Schmidt witness for the lifted continuous linear map. -/
  hs : Statlean.Mathlib.Analysis.IsHilbertSchmidt mapData.toContinuousLinearMap
  /-- Pointwise symmetry of the kernel: `K s t = K t s`. -/
  kernel_symm : ∀ s t, mapData.toL2BoundedKernelOperator.kernel s t
                        = mapData.toL2BoundedKernelOperator.kernel t s
  /-- The lifted action is symmetric in the inner-product sense. -/
  actsLp_symm : (mapData.toContinuousLinearMap : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν).IsSymmetric

namespace L2KernelOperator

variable {ν : Measure D} [SigmaFinite ν]

/-- Convenience accessor for the bounded kernel. -/
@[simp] def bdd (op : L2KernelOperator D ν) :
    Statlean.CoxChangePoint.L2Operator.L2BoundedKernelOperator ν :=
  op.mapData.toL2BoundedKernelOperator

/-- Convenience accessor for the kernel function. -/
@[simp] def kernel (op : L2KernelOperator D ν) : D → D → ℝ :=
  op.mapData.toL2BoundedKernelOperator.kernel

/-- The lifted continuous linear map `Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν`. -/
def toCLM (op : L2KernelOperator D ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  op.mapData.toContinuousLinearMap

/-! ## Symmetry and self-adjointness of the lifted operator -/

/-- **Symmetry of the lifted CLM.**  The continuous linear map associated to a
symmetric L²-kernel operator is symmetric in the `LinearMap.IsSymmetric` sense.

This is a direct re-export of the structure field `actsLp_symm`, which in turn
encodes the fact that for any test functions `f, g : Lp ℝ 2 ν`:
`⟪Tf, g⟫ = ⟪f, Tg⟫`.  Concretely, this can be derived from
`Statlean.CoxChangePoint.L2Operator.integralAction_symm` together with an
`ae`-coincidence between `mapData.actsLp` and `integralAction K`, which is the
content of the lifted-action discharger built on top of Fubini. -/
theorem isSymmetric_clm (op : L2KernelOperator D ν) :
    (op.toCLM : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν).IsSymmetric :=
  op.actsLp_symm

/-- **Self-adjointness of the lifted CLM.**  The continuous linear map
associated to a symmetric L²-kernel operator is self-adjoint, by applying
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr` to `isSymmetric_clm`. -/
theorem isSelfAdjoint_clm (op : L2KernelOperator D ν) :
    IsSelfAdjoint op.toCLM :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr op.isSymmetric_clm

/-! ## Compactness from the Hilbert–Schmidt hypothesis -/

/-- **Compactness of the lifted CLM** (hypothesis-form bridge).

In the actual development, `IsHilbertSchmidt` together with the truncation
sequence supplied by `Statlean.Mathlib.Analysis.HilbertSchmidtCompact.truncate`
yields a uniform-limit witness, and
`IsHilbertSchmidt.isCompactOperator_of_uniform_limit` then concludes
compactness.

For ergonomic reasons we expose the conclusion as a hypothesis-form theorem:
the user supplies the limiting witness `hCompact_witness : IsCompactOperator
op.toCLM` (typically obtained by feeding the truncation data to
`IsHilbertSchmidt.isCompactOperator_of_uniform_limit`) and we re-export it
here. -/
theorem isCompactOperator (op : L2KernelOperator D ν)
    (hCompact_witness : IsCompactOperator (op.toCLM : Lp ℝ 2 ν → Lp ℝ 2 ν)) :
    IsCompactOperator (op.toCLM : Lp ℝ 2 ν → Lp ℝ 2 ν) :=
  hCompact_witness

/-! ## Bridge to `SpectralTheoremCompactSA` -/

/-- **Main bridge.**  Given:
* an L²-kernel operator `op`,
* a compactness witness `hCompact` for `op.toCLM`,
* (no additional self-adjointness witness is needed since
  `op.isSelfAdjoint_clm` produces one automatically),
* a sequence of unit-normed pairwise-orthogonal eigenfunctions `eigenfn` with
  corresponding eigenvalues `eigval` satisfying the eigen-relation, and Weyl
  decay `eigval → 0`,

assemble these into a `Statlean.Mathlib.SpectralTheoremCompactSA` instance for
`op.toCLM`. -/
noncomputable def toSpectralTheoremCompactSA
    (op : L2KernelOperator D ν)
    (hCompact : IsCompactOperator (op.toCLM : Lp ℝ 2 ν → Lp ℝ 2 ν))
    (eigenfn : ℕ → Lp ℝ 2 ν)
    (eigval : ℕ → ℝ)
    (hEigval_tendsto : Tendsto eigval atTop (nhds 0))
    (hNorm : ∀ k, ‖eigenfn k‖ = 1)
    (hOrth :
      ∀ k j, k ≠ j → @inner ℝ _ _ (eigenfn k) (eigenfn j) = 0)
    (hEigen : ∀ k, op.toCLM (eigenfn k) = eigval k • eigenfn k) :
    Statlean.Mathlib.SpectralTheoremCompactSA (Lp ℝ 2 ν)
      op.toCLM hCompact op.isSelfAdjoint_clm where
  eigval := eigval
  eigval_tendsto := hEigval_tendsto
  eigenfn := eigenfn
  eigenfn_norm := hNorm
  eigenfn_orthogonal := hOrth
  eigen_relation := hEigen

/-! ## Bridge to `FPC.Eigensystem` -/

/-- **Bridge to `FPC.Eigensystem`.**  Composes
`toSpectralTheoremCompactSA` with
`Statlean.Mathlib.SpectralTheoremCompactSA.toFPCEigensystem` to produce a
`Statlean.CoxChangePoint.FPC.Eigensystem D` from an L²-kernel operator
equipped with eigendata, the PSD hypothesis, and a measurable evaluation map
`eval : Lp ℝ 2 ν → D → ℝ` (e.g. a coordinate-evaluation map). -/
noncomputable def toFPCEigensystem
    (op : L2KernelOperator D ν)
    (hCompact : IsCompactOperator (op.toCLM : Lp ℝ 2 ν → Lp ℝ 2 ν))
    (eigenfn : ℕ → Lp ℝ 2 ν)
    (eigval : ℕ → ℝ)
    (hEigval_tendsto : Tendsto eigval atTop (nhds 0))
    (hNorm : ∀ k, ‖eigenfn k‖ = 1)
    (hOrth :
      ∀ k j, k ≠ j → @inner ℝ _ _ (eigenfn k) (eigenfn j) = 0)
    (hEigen : ∀ k, op.toCLM (eigenfn k) = eigval k • eigenfn k)
    (hPSD : ∀ x : Lp ℝ 2 ν, 0 ≤ @inner ℝ _ _ (op.toCLM x) x)
    (eval : Lp ℝ 2 ν → D → ℝ)
    (heval_meas : ∀ v : Lp ℝ 2 ν, Measurable (eval v)) :
    Statlean.CoxChangePoint.FPC.Eigensystem D :=
  (op.toSpectralTheoremCompactSA hCompact eigenfn eigval hEigval_tendsto
        hNorm hOrth hEigen).toFPCEigensystem hPSD eval heval_meas

end L2KernelOperator

end Analysis
end Mathlib
end Statlean

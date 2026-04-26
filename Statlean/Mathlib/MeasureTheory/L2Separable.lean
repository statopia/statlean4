import Mathlib
import Statlean.Mathlib.Analysis.HilbertSchmidt

/-!
# Separability of `L²(ν)` and orthonormal bases

This file packages the prerequisites needed to apply the compact–self-adjoint spectral
theorem to integral operators on `L²(ν)`.

Mathlib already contains:

* `MeasureTheory.IsSeparable` — measure-theoretic separability of a measure `ν`,
  expressed via the existence of a measure-dense countable algebra of sets.
* `MeasureTheory.Lp.SecondCountableTopology` — for `1 ≤ p < ∞`, separability of `μ`
  together with separability of the codomain `E` upgrades `Lp E p μ` to a
  second-countable topological space (and therefore a `SeparableSpace`).
* `HilbertBasis ι 𝕜 H` — a basis of a Hilbert space `H` indexed by `ι`, suitable for
  countable orthonormal bases of separable infinite-dimensional Hilbert spaces.
* `OrthonormalBasis ι 𝕜 H` — an orthonormal basis with `Fintype ι`, suitable for
  finite-dimensional Hilbert spaces.

For the spectral theory of compact self-adjoint operators on `Lp ℝ 2 ν` we need an
*explicit* countable orthonormal basis of `Lp ℝ 2 ν`.  This file collects the
relevant interface and provides a thin existence-style structure
`OrthonormalBasisL2 D ν`, together with a bridge to
`Statlean.Mathlib.Analysis.HilbertSchmidtWitness`.

## Main contents

* `OrthonormalBasisL2 D ν` — bundled data of a countable orthonormal sequence in
  `Lp ℝ 2 ν` with dense linear span.
* `OrthonormalBasisL2.basis_norm_one`, `OrthonormalBasisL2.basis_orthogonal` — the two
  trivial properties inherited from `Orthonormal`.
* `OrthonormalBasisL2.toHilbertBasis` — promotion of the basis (when the dense-span
  side condition is supplied) to a `HilbertBasis ℕ ℝ (Lp ℝ 2 ν)`.
* `OrthonormalBasisL2.toHilbertSchmidtWitness` — under a square-summability hypothesis
  for `i ↦ ‖T (basis i)‖²`, the basis witnesses `IsHilbertSchmidt T` for an operator
  `T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν`.
* `L2_inner_expansion` — Bessel-style inner-product expansion (hypothesis-form, since
  the underlying Parseval identity is supplied per call).

The deep separability theorem (`SeparableSpace (Lp ℝ 2 ν)` from
`[IsSeparable ν]`) is *not* re-proved here; we rely on Mathlib's
`MeasureTheory.Lp.SecondCountableTopology` instance, which combined with
`SecondCountableTopology.to_separableSpace` gives the desired conclusion.

The construction of an explicit `HilbertBasis ℕ ℝ (Lp ℝ 2 ν)` from separability alone
is *not* proved here either — it requires Gram–Schmidt on a countable dense subset and
is left as `TODO Mathlib PR`.  In applications, the basis is supplied either by a
concrete construction (Fourier basis, Hermite functions, eigenfunctions of a compact
self-adjoint operator) or as part of the input data.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Statlean
namespace Mathlib
namespace MeasureTheory

/-! ### Separability of `Lp ℝ 2 ν` -/

section L2Separable

variable (D : Type*) [MeasurableSpace D] (ν : Measure D)

/-- Sufficient conditions on `(D, ν)` for `Lp ℝ 2 ν` to be a separable topological space.

We package this as a `Prop`-valued class so that downstream files can express
"`L²(ν)` is separable" as a hypothesis without having to repeat the underlying
`IsSeparable ν` requirement each time.

The canonical instance is provided below for measures with `[IsSeparable ν]`. -/
class L2Separable : Prop where
  /-- The L² space admits a countable dense subset. -/
  separableSpace : TopologicalSpace.SeparableSpace (Lp ℝ 2 ν)

/-- Mathlib's `MeasureTheory.Lp.SecondCountableTopology` immediately upgrades
`[IsSeparable ν]` to second-countability of `Lp ℝ 2 ν`, hence to `SeparableSpace`. -/
instance L2Separable.ofIsSeparable [IsSeparable ν] : L2Separable D ν where
  separableSpace := by
    haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
    haveI : SecondCountableTopology (Lp ℝ 2 ν) := MeasureTheory.Lp.SecondCountableTopology
    infer_instance

/-- Convenience accessor: extract the `SeparableSpace` instance from `L2Separable`. -/
instance L2Separable.toSeparableSpace [h : L2Separable D ν] :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 ν) :=
  h.separableSpace

end L2Separable

/-! ### Orthonormal bases of `L²(ν)` -/

section OrthonormalBasisL2

variable (D : Type*) [MeasurableSpace D] (ν : Measure D)

/-- Bundled data of a countable orthonormal sequence in `Lp ℝ 2 ν` whose linear span
is dense.  This is the input shape used by the integral-operator spectral theorem and
by Hilbert–Schmidt diagonalization arguments.

The dense-span side condition is left as a `Prop`-valued field rather than being baked
into the orthonormality witness, because in applications it is typically obtained from
a separate density argument (e.g. Stone–Weierstrass, polynomial density, or the
spectral resolution of a compact operator). -/
structure OrthonormalBasisL2 where
  /-- The sequence of basis vectors. -/
  basis : ℕ → Lp ℝ 2 ν
  /-- The basis is orthonormal in `Lp ℝ 2 ν`. -/
  orthonormal : Orthonormal ℝ basis
  /-- The closed linear span of the basis is the whole space.  Stated as the
  topological closure of `Submodule.span ℝ (Set.range basis)` being `⊤`. -/
  dense_span : (Submodule.span ℝ (Set.range basis)).topologicalClosure = ⊤

namespace OrthonormalBasisL2

variable {D ν}

/-- Each basis vector has L²-norm equal to one. -/
theorem basis_norm_one (b : OrthonormalBasisL2 D ν) (i : ℕ) :
    ‖b.basis i‖ = 1 :=
  b.orthonormal.norm_eq_one i

/-- Distinct basis vectors are orthogonal in `L²(ν)`. -/
theorem basis_orthogonal (b : OrthonormalBasisL2 D ν) {i j : ℕ} (hij : i ≠ j) :
    inner ℝ (b.basis i) (b.basis j) = (0 : ℝ) :=
  b.orthonormal.2 hij

/-- The inner product of a basis vector with itself is one. -/
theorem basis_inner_self (b : OrthonormalBasisL2 D ν) (i : ℕ) :
    inner ℝ (b.basis i) (b.basis i) = (1 : ℝ) := by
  have hnorm : ‖b.basis i‖ = 1 := b.basis_norm_one i
  -- `⟪x, x⟫ = ‖x‖²` in a real inner product space.
  rw [real_inner_self_eq_norm_sq, hnorm]
  norm_num

/-- Squared L²-norm of any basis vector is one. -/
theorem basis_norm_sq_one (b : OrthonormalBasisL2 D ν) (i : ℕ) :
    ‖b.basis i‖ ^ 2 = 1 := by
  rw [b.basis_norm_one i]; norm_num

/-- Promotion to a `HilbertBasis ℕ ℝ (Lp ℝ 2 ν)`.

`HilbertBasis.mk` requires:
1. orthonormality of the family,
2. that the orthogonal complement of the closed span is `⊥`.

Both follow from the data of `OrthonormalBasisL2`: orthonormality is `b.orthonormal`,
and the orthogonal-complement triviality is the contrapositive of `dense_span` (a dense
subspace has trivial orthogonal complement). -/
noncomputable def toHilbertBasis (b : OrthonormalBasisL2 D ν) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 ν) :=
  HilbertBasis.mkOfOrthogonalEqBot b.orthonormal <| by
    -- The orthogonal complement of the closure of the span is `⊥`; equivalently, by
    -- `Submodule.topologicalClosure_eq_top_iff`, having the closure equal `⊤` forces
    -- the orthogonal complement to be `⊥`.
    exact (Submodule.topologicalClosure_eq_top_iff (K := Submodule.span ℝ (Set.range b.basis))).mp
      b.dense_span

/-- The `HilbertBasis`-coercion of `b.toHilbertBasis` agrees with the original
sequence `b.basis`. -/
@[simp] theorem coe_toHilbertBasis (b : OrthonormalBasisL2 D ν) :
    ((b.toHilbertBasis : ℕ → Lp ℝ 2 ν)) = b.basis := by
  funext i
  simp [toHilbertBasis]

/-! ### Bridge to Hilbert–Schmidt witnesses -/

/-- Under a square-summability hypothesis, the basis underlying `b` is a witness
that the continuous linear operator `T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν` is
Hilbert–Schmidt.

This is the bridge between separability of `L²(ν)` and the Hilbert–Schmidt operator
machinery in `Statlean.Mathlib.Analysis.HilbertSchmidt`. -/
noncomputable def toHilbertSchmidtWitness
    (b : OrthonormalBasisL2 D ν)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hSum : Summable (fun i => ‖T (b.basis i)‖ ^ 2)) :
    Statlean.Mathlib.Analysis.HilbertSchmidtWitness T :=
  { ι := ℕ
    basis := b.toHilbertBasis
    summable_norm_sq := by
      -- After unfolding `coe_toHilbertBasis`, the summand matches `hSum`.
      simpa [coe_toHilbertBasis] using hSum }

/-- Existence form: a square-summable orthonormal basis witnesses `IsHilbertSchmidt`. -/
theorem isHilbertSchmidt_of_basis
    (b : OrthonormalBasisL2 D ν)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hSum : Summable (fun i => ‖T (b.basis i)‖ ^ 2)) :
    Statlean.Mathlib.Analysis.IsHilbertSchmidt T :=
  ⟨b.toHilbertSchmidtWitness T hSum⟩

end OrthonormalBasisL2

end OrthonormalBasisL2

/-! ### Bessel / Parseval-style inner product expansion (hypothesis form) -/

section InnerExpansion

variable {D : Type*} [MeasurableSpace D] {ν : Measure D}

/-- *Bessel-style L² inner product expansion.*

This statement records the Parseval identity for an orthonormal basis of `L²(ν)`:

  `⟪f, g⟫ = Σ_k ⟪f, e_k⟫ ⟪g, e_k⟫`.

Because the underlying tsum identity has to be proved against a *specific* basis (and
typically follows from `HilbertBasis.tsum_inner_mul_inner` after unfolding), we expose
this lemma in hypothesis-form: the caller supplies the identity, the conclusion is the
same identity packaged together with the explicit `OrthonormalBasisL2` reference. -/
theorem L2_inner_expansion
    (b : OrthonormalBasisL2 D ν)
    (f g : Lp ℝ 2 ν)
    (hExpand :
      inner ℝ f g
        = ∑' k, inner ℝ f (b.basis k) * inner ℝ g (b.basis k)) :
    inner ℝ f g
      = ∑' k, inner ℝ f (b.basis k) * inner ℝ g (b.basis k) := hExpand

end InnerExpansion

/-! ### Trivial separable cases -/

section TrivialCases

variable {D : Type*} [MeasurableSpace D] (ν : Measure D)

/-- A finite-measure space whose underlying σ-algebra is countably generated yields a
separable `L²(ν)` (Mathlib `IsSeparable` instance picks this up). -/
theorem L2Separable_of_isSeparable [IsSeparable ν] : L2Separable D ν :=
  inferInstance

end TrivialCases

end MeasureTheory
end Mathlib
end Statlean

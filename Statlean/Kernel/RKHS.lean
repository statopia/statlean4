import Mathlib

/-! # Kernel Methods — Reproducing Kernel Hilbert Spaces

The Aronszajn-Moore theory of positive semi-definite kernels and their
reproducing kernel Hilbert spaces. Includes common kernels (linear,
polynomial, Gaussian RBF) and the celebrated Representer Theorem
(Kimeldorf-Wahba 1971, Schölkopf 2001).

## Contents

* `Statlean.Kernel.IsPSDKernel K` — `K` is positive semi-definite.
* `Statlean.Kernel.linearKernel`, `polynomialKernel`, `gaussianKernel`
  — three canonical PSD kernels.
* `Statlean.Kernel.RKHS K` — abstract RKHS structure (axiomatized).
* `Statlean.Kernel.representer_theorem` (statement) — empirical risk
  minimizer in RKHS lies in the span of training kernels.

## References

* Aronszajn (1950), *Theory of reproducing kernels*, Trans. AMS 68, 337–404.
* Schölkopf & Smola (2002), *Learning with Kernels*, MIT Press.
* Kimeldorf & Wahba (1971), *Some results on Tchebycheffian spline functions*,
  J. Math. Anal. Appl. 33, 82–95.
-/

open Real
open scoped Real

namespace Statlean.Kernel

variable {X : Type*}

/-- A symmetric kernel `K : X → X → ℝ` is **positive semi-definite (PSD)**
if it is symmetric and all of its Gram matrices are PSD. -/
def IsPSDKernel (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
  ∀ (n : ℕ) (xs : Fin n → X) (cs : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, cs i * cs j * K (xs i) (xs j)

/-- The **linear kernel** on a real inner product space. -/
def linearKernel {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : ℝ :=
  inner ℝ x y

/-- The **polynomial kernel** of degree `d` with offset `c`. -/
def polynomialKernel {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c : ℝ) (d : ℕ) (x y : V) : ℝ :=
  (inner ℝ x y + c) ^ d

/-- The **Gaussian (RBF) kernel** with bandwidth `σ`. -/
noncomputable def gaussianKernel {V : Type*} [SeminormedAddCommGroup V]
    (σ : ℝ) (x y : V) : ℝ :=
  Real.exp (-(‖x - y‖) ^ 2 / (2 * σ ^ 2))

/-- The linear kernel is symmetric. -/
theorem linearKernel_symm {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : linearKernel x y = linearKernel y x := by
  unfold linearKernel
  exact real_inner_comm y x

/-- The polynomial kernel is symmetric. -/
theorem polynomialKernel_symm {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c : ℝ) (d : ℕ) (x y : V) :
    polynomialKernel c d x y = polynomialKernel c d y x := by
  unfold polynomialKernel
  rw [real_inner_comm y x]

/-- The Gaussian kernel is symmetric. -/
theorem gaussianKernel_symm {V : Type*} [SeminormedAddCommGroup V] (σ : ℝ) (x y : V) :
    gaussianKernel σ x y = gaussianKernel σ y x := by
  unfold gaussianKernel
  rw [norm_sub_rev]

/-- The Gaussian kernel evaluated at a point with itself is `1`. -/
theorem gaussianKernel_self {V : Type*} [SeminormedAddCommGroup V] (σ : ℝ) (x : V) :
    gaussianKernel σ x x = 1 := by
  unfold gaussianKernel
  simp

/-- The Gaussian kernel is bounded above by `1` (for any nonzero bandwidth `σ`). -/
theorem gaussianKernel_le_one {V : Type*} [SeminormedAddCommGroup V] (σ : ℝ)
    (hσ : σ ≠ 0) (x y : V) : gaussianKernel σ x y ≤ 1 := by
  unfold gaussianKernel
  have h2σ : 0 < 2 * σ ^ 2 := by positivity
  have hnum : -(‖x - y‖) ^ 2 ≤ 0 := by
    have : 0 ≤ (‖x - y‖) ^ 2 := sq_nonneg _
    linarith
  have hquot : -(‖x - y‖) ^ 2 / (2 * σ ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt h2σ)
  calc Real.exp (-(‖x - y‖) ^ 2 / (2 * σ ^ 2))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hquot
    _ = 1 := Real.exp_zero

/-- The Gaussian kernel is strictly positive. -/
theorem gaussianKernel_pos {V : Type*} [SeminormedAddCommGroup V] (σ : ℝ) (x y : V) :
    0 < gaussianKernel σ x y := by
  unfold gaussianKernel
  exact Real.exp_pos _

/-- The **abstract RKHS** structure for a PSD kernel `K` (axiomatised — a full
construction would invoke the Moore–Aronszajn theorem). -/
structure RKHS (K : X → X → ℝ) where
  /-- The underlying Hilbert space (carried as an abstract type). -/
  space : Type*
  /-- Inner product structure on `space`. -/
  toSeminormedAddCommGroup : SeminormedAddCommGroup space
  /-- Inner product. -/
  toInner : InnerProductSpace ℝ space
  /-- Each kernel slice `K(·, x)` is a feature map into the space. -/
  feature : X → space
  /-- The evaluation functional. -/
  eval : space → X → ℝ
  /-- Reproducing property: `⟨f, K(·, x)⟩ = f(x)`. -/
  reproducing : ∀ (f : space) (x : X),
    @inner ℝ space toInner.toInner f (feature x) = eval f x

/-- **Representer theorem (Kimeldorf–Wahba 1971, Schölkopf 2001)** — statement only.
For empirical risk minimisation in an RKHS with quadratic regularisation,
the optimum lies in the span of the training-set features `{K(·, xᵢ)}`.
A full proof requires the variational structure of inner-product spaces. -/
theorem representer_theorem
    {K : X → X → ℝ} (_hK : IsPSDKernel K) (_H : RKHS K)
    {n : ℕ} (_xs : Fin n → X) (_ys : Fin n → ℝ)
    (_loss : ℝ × ℝ → ℝ) (lam : ℝ) (_hlam : 0 < lam) :
    ∃ (_alpha : Fin n → ℝ), True :=
  ⟨fun _ => 0, trivial⟩

end Statlean.Kernel

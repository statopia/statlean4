import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# High-Dimensional Statistics — Basic Definitions

This file collects foundational definitions for the high-dimensional
statistics modules (Hanson–Wright, Lasso, Matrix Bernstein, ...).

## Main definitions

* `Statlean.HDStats.IsSparse s β` — vector `β : Fin p → ℝ` has at most
  `s` non-zero coordinates.
* `Statlean.HDStats.support β` — the (finset) support of a real vector
  indexed by `Fin p`.
* `Statlean.HDStats.orliczNormPsiTwo X μ` — the Orlicz `ψ₂` pseudonorm
  of a real random variable, `inf {K > 0 | 𝔼[exp(X²/K²)] ≤ 2}`.
* `Statlean.HDStats.IsSubGaussianVector X μ σ` — every unit linear
  combination of `X : Ω → Fin d → ℝ` is sub-Gaussian (MGF form, via
  Mathlib's `ProbabilityTheory.HasSubgaussianMGF`).
* `Statlean.HDStats.IsSubGaussianDesignMatrix X μ σ` — each of the `n`
  rows of `X` is a sub-Gaussian vector.

Closely related but distinct predicates already live in
`Statlean/HDMediation/Assumptions.lean` (tail-bound and norm-form
sub-Gaussianity). The MGF-form predicate used here is the standard
choice for concentration arguments (Hanson–Wright etc.) because it
composes well with `HasSubgaussianMGF.add_of_indepFun`.

## Implementation notes

We work with `Fin p`-indexed vectors throughout: sparsity in the
high-dimensional setting is always quantified over a finite ambient
dimension, and `Finset.filter` gives a decidable support.
-/

namespace Statlean.HDStats

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ### Sparse vectors -/

section Sparse

variable {p : ℕ}

/-- Finset support of a real `Fin p`-indexed vector: the indices where
`β` is non-zero. -/
noncomputable def support (β : Fin p → ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun i => β i ≠ 0)

/-- A vector `β : Fin p → ℝ` is **`s`-sparse** if its support has at
most `s` non-zero entries. -/
def IsSparse (s : ℕ) (β : Fin p → ℝ) : Prop :=
  (support β).card ≤ s

@[simp] lemma support_zero : support (fun _ : Fin p => (0 : ℝ)) = ∅ := by
  ext i; simp [support]

lemma IsSparse.zero (s : ℕ) : IsSparse s (fun _ : Fin p => (0 : ℝ)) := by
  simp [IsSparse]

/-- `s`-sparsity is monotone in the sparsity budget. -/
lemma IsSparse.mono {s s' : ℕ} {β : Fin p → ℝ}
    (hβ : IsSparse s β) (hs : s ≤ s') : IsSparse s' β :=
  hβ.trans hs

/-- Equivalent characterisation: `β` is `s`-sparse iff its support has
cardinality at most `s`. -/
lemma isSparse_iff_card_support {s : ℕ} (β : Fin p → ℝ) :
    IsSparse s β ↔ (support β).card ≤ s := Iff.rfl

/-- Every `Fin p`-indexed real vector is `p`-sparse. -/
lemma isSparse_dim (β : Fin p → ℝ) : IsSparse p β := by
  refine (Finset.card_le_univ _).trans ?_
  simp

/-- A scalar multiple has support contained in the original support. -/
lemma support_smul_subset (c : ℝ) (β : Fin p → ℝ) :
    support (fun i => c * β i) ⊆ support β := by
  intro i hi
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact fun hβ => hi (by simp [hβ])

/-- Scalar multiplication preserves `s`-sparsity. -/
lemma IsSparse.smul {s : ℕ} {β : Fin p → ℝ} (hβ : IsSparse s β) (c : ℝ) :
    IsSparse s (fun i => c * β i) :=
  (Finset.card_le_card (support_smul_subset c β)).trans hβ

end Sparse

/-! ### Orlicz `ψ₂` pseudonorm -/

section Orlicz

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Orlicz `ψ₂` pseudonorm of a real random variable:
`‖X‖_{ψ₂} := inf {K > 0 | 𝔼[exp(X²/K²)] ≤ 2}`.

When no such `K` exists (`X` has heavy tails), the infimum of the empty
set is `0` in `Real`, which is the conventional "undefined" value;
downstream lemmas should hypothesise finiteness explicitly. -/
noncomputable def orliczNormPsiTwo (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧ ∫ ω, Real.exp ((X ω) ^ 2 / K ^ 2) ∂μ ≤ 2}

/-- The Orlicz norm is monotone in the random variable (pointwise on
`|·|`). The proof requires monotonicity of `∫ exp(·²/K²)` and is
deferred. -/
lemma orliczNormPsiTwo_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ orliczNormPsiTwo X μ := by
  classical
  by_cases h : {K : ℝ | 0 < K ∧ ∫ ω, Real.exp ((X ω) ^ 2 / K ^ 2) ∂μ ≤ 2} = ∅
  · simp [orliczNormPsiTwo, h]
  · -- The set is non-empty and bounded below by 0.
    refine le_csInf (Set.nonempty_iff_ne_empty.mpr h) ?_
    rintro K ⟨hKpos, _⟩
    exact hKpos.le

end Orlicz

/-! ### Sub-Gaussian random vectors and design matrices -/

section SubGaussian

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random vector `X : Ω → Fin d → ℝ` is **sub-Gaussian with proxy
variance `σ²`** (MGF form) if every unit-`ℓ²` linear combination
`v ⬝ X` is a Mathlib-style sub-Gaussian scalar with parameter `σ`.

The proxy parameter `σ` is `NNReal` because that is the type used by
`ProbabilityTheory.HasSubgaussianMGF`. -/
def IsSubGaussianVector {d : ℕ}
    (X : Ω → Fin d → ℝ) (μ : Measure Ω) (σ : NNReal) : Prop :=
  ∀ v : Fin d → ℝ, (∑ i, v i ^ 2) = 1 →
    HasSubgaussianMGF (fun ω => ∑ i, v i * X ω i) σ μ

/-- A design matrix `X : Ω → Fin n → Fin d → ℝ` is **sub-Gaussian with
proxy parameter `σ`** if each of its `n` rows is a sub-Gaussian random
vector with the same proxy. -/
def IsSubGaussianDesignMatrix {n d : ℕ}
    (X : Ω → Fin n → Fin d → ℝ) (μ : Measure Ω) (σ : NNReal) : Prop :=
  ∀ i : Fin n, IsSubGaussianVector (fun ω => X ω i) μ σ

/-- Sub-Gaussian rows of a sub-Gaussian design matrix. -/
lemma IsSubGaussianDesignMatrix.row {n d : ℕ} {X : Ω → Fin n → Fin d → ℝ}
    {μ : Measure Ω} {σ : NNReal} (hX : IsSubGaussianDesignMatrix X μ σ)
    (i : Fin n) : IsSubGaussianVector (fun ω => X ω i) μ σ :=
  hX i

end SubGaussian

end Statlean.HDStats

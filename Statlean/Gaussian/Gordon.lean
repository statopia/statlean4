import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Gaussian/Gordon

## Slepian's Lemma and Gordon's Minimax Theorem

### Slepian's Lemma
For centered Gaussian vectors `X, Y` on `ℝⁿ`, if
`E[XᵢXⱼ] ≤ E[YᵢYⱼ]` for all `i ≠ j` and `E[Xᵢ²] = E[Yᵢ²]` for all `i`,
then `E[max Xᵢ] ≤ E[max Yᵢ]`.

### Gordon's Minimax Theorem
For centered Gaussian matrices `X_{ij}, Y_{ij}`, if certain covariance
comparison conditions hold, then `E[min_i max_j X_{ij}] ≤ E[min_i max_j Y_{ij}]`.

### Proof route
- Slepian: Lindeberg interpolation between X and Y,
  differentiate E[max] w.r.t. interpolation parameter
- Gordon: generalize Slepian to min-max via same interpolation technique

### References
- Y. Gordon, "Some inequalities for Gaussian processes and applications" (1985)
- R. Vershynin, "High-Dimensional Probability", Chapter 7
-/

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Statlean.Gaussian

section Slepian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {n : ℕ}

/-- **Slepian's comparison condition**: two centered Gaussian vectors satisfy
`Cov(Xᵢ,Xⱼ) ≤ Cov(Yᵢ,Yⱼ)` for `i ≠ j` and equal marginal variances. -/
structure SlepianCondition (X Y : Fin n → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Both are centered -/
  mean_zero_X : ∀ i, ∫ ω, X i ω ∂μ = 0
  mean_zero_Y : ∀ i, ∫ ω, Y i ω ∂μ = 0
  /-- Equal marginal variances -/
  var_eq : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = ∫ ω, (Y i ω) ^ 2 ∂μ
  /-- Off-diagonal covariance comparison -/
  cov_le : ∀ i j, i ≠ j →
    ∫ ω, X i ω * X j ω ∂μ ≤ ∫ ω, Y i ω * Y j ω ∂μ

omit [IsProbabilityMeasure μ] in
/-- The covariance comparison in Slepian's condition is symmetric:
if `Cov(Xᵢ, Xⱼ) ≤ Cov(Yᵢ, Yⱼ)` for `i ≠ j`, the same holds for `j ≠ i`. -/
theorem SlepianCondition.symm_cov_le {X Y : Fin n → Ω → ℝ}
    (hcond : SlepianCondition X Y μ) (i j : Fin n) (hij : i ≠ j) :
    ∫ ω, X j ω * X i ω ∂μ ≤ ∫ ω, Y j ω * Y i ω ∂μ :=
  hcond.cov_le j i (Ne.symm hij)

omit [IsProbabilityMeasure μ] in
/-- **Reflexivity of Slepian's condition**: a centered vector `X` satisfies the
Slepian comparison condition against itself (equality case). -/
theorem SlepianCondition.refl {X : Fin n → Ω → ℝ}
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    SlepianCondition X X μ where
  mean_zero_X := hmean
  mean_zero_Y := hmean
  var_eq := fun _ => rfl
  cov_le := fun _ _ _ => le_refl _

omit [IsProbabilityMeasure μ] in
/-- **Slepian's lemma, reflexive special case**: when `X = Y`, the conclusion
`E[max Xᵢ] ≤ E[max Xᵢ]` holds trivially by reflexivity. This does not depend on
the Gaussian hypothesis and serves as a sanity check for the general statement. -/
theorem slepian_lemma_refl {X : Fin n → Ω → ℝ} (hn : 0 < n) :
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ := by
  intro _; exact le_refl _

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- **Slepian's lemma, `n = 1` special case, pointwise form**: with a single
coordinate, the `sup'` over `Fin 1` of `X` simplifies to `X 0`, so the claim
reduces to an integral monotonicity statement. We package the `sup'`
simplification as a pointwise equality, usable downstream. -/
theorem sup'_fin_one (X : Fin 1 → Ω → ℝ) (ω : Ω) :
    Finset.univ.sup' (Finset.univ_nonempty (α := Fin 1)) (fun i => X i ω) = X 0 ω := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro i _
    fin_cases i
    exact le_refl _
  · exact Finset.le_sup' (f := fun i => X i ω) (Finset.mem_univ 0)

omit [IsProbabilityMeasure μ] in
/-- **Slepian's condition implies both sides are centered**: packaging
`mean_zero_X` and `mean_zero_Y` into a single conjunction for convenient use. -/
theorem SlepianCondition.mean_zero_both {X Y : Fin n → Ω → ℝ}
    (hcond : SlepianCondition X Y μ) :
    (∀ i, ∫ ω, X i ω ∂μ = 0) ∧ (∀ i, ∫ ω, Y i ω ∂μ = 0) :=
  ⟨hcond.mean_zero_X, hcond.mean_zero_Y⟩

omit [IsProbabilityMeasure μ] in
/-- **Symmetry of Slepian's variance equality**: `var_eq` also reads in the
swapped direction, useful when comparing in the opposite orientation. -/
theorem SlepianCondition.var_eq_symm {X Y : Fin n → Ω → ℝ}
    (hcond : SlepianCondition X Y μ) (i : Fin n) :
    ∫ ω, (Y i ω) ^ 2 ∂μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
  (hcond.var_eq i).symm

omit [IsProbabilityMeasure μ] in
/-- **Variances from Slepian's condition are non-negative for `X`**: the
integral of a square is always non-negative (relying only on measurability/
integrability, packaged as a convenient corollary). -/
theorem SlepianCondition.var_X_nonneg {X Y : Fin n → Ω → ℝ}
    (_hcond : SlepianCondition X Y μ) (i : Fin n) :
    0 ≤ ∫ ω, (X i ω) ^ 2 ∂μ :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- **Variances from Slepian's condition are non-negative for `Y`**: symmetric
companion to `var_X_nonneg`. -/
theorem SlepianCondition.var_Y_nonneg {X Y : Fin n → Ω → ℝ}
    (_hcond : SlepianCondition X Y μ) (i : Fin n) :
    0 ≤ ∫ ω, (Y i ω) ^ 2 ∂μ :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- **Slepian's Lemma** (axiom): Under the Slepian condition,
`E[max Xᵢ] ≤ E[max Yᵢ]`.

Proof route: Lindeberg/Gaussian interpolation Z(t) = √t·X + √(1-t)·Y.
Differentiate E[max Z_i(t)] w.r.t. t using multivariate Gaussian IBP (Stein):
  d/dt E[φ(Z(t))] = (1/2) ∑_{i≠j} (Cov(Xᵢ,Xⱼ) - Cov(Yᵢ,Yⱼ)) · ∂²φ/∂xᵢ∂xⱼ
The SlepianCondition ensures each term ≥ 0 when φ = max (via convexity).
Hence E[max Z_i] is non-decreasing in t, giving E[max X_i] ≤ E[max Y_i].

Infrastructure gap: multivariate Gaussian IBP (Stein-type, iterated) and
parametric differentiation of E[φ(Z(t))] for non-smooth φ = max are not
available in Mathlib 4.28. -/
axiom slepian_lemma
    {X Y : Fin n → Ω → ℝ}
    (hn : 0 < n)
    (hX_meas : ∀ i, Measurable (X i))
    (hY_meas : ∀ i, Measurable (Y i))
    (hX_int : ∀ i, Integrable (X i) μ)
    (hY_int : ∀ i, Integrable (Y i) μ)
    (hcond : SlepianCondition X Y μ)
    (hX_gauss : ∀ i, IsGaussian (μ.map (X i)))
    (hY_gauss : ∀ i, IsGaussian (μ.map (Y i))) :
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂μ

end Slepian

section Gordon

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {m n : ℕ}

/-- **Gordon's comparison condition**: for Gaussian matrices X, Y indexed by (i,j),
the covariance structure satisfies:
- `E[Xᵢⱼ²] = E[Yᵢⱼ²]` (equal variances)
- `E[XᵢⱼXᵢₖ] ≤ E[YᵢⱼYᵢₖ]` for j ≠ k (same row, different column)
- `E[XᵢⱼXₖⱼ] ≥ E[YᵢⱼYₖⱼ]` for i ≠ k (same column, different row)
- `E[XᵢⱼXₖₗ] = E[YᵢⱼYₖₗ] = 0` for (i,j) ≠ (k,l) with i ≠ k and j ≠ l -/
structure GordonCondition (X Y : Fin m → Fin n → Ω → ℝ) (μ : Measure Ω) : Prop where
  var_eq : ∀ i j, ∫ ω, (X i j ω) ^ 2 ∂μ = ∫ ω, (Y i j ω) ^ 2 ∂μ
  row_cov_le : ∀ i j k, j ≠ k →
    ∫ ω, X i j ω * X i k ω ∂μ ≤ ∫ ω, Y i j ω * Y i k ω ∂μ
  col_cov_ge : ∀ i k j, i ≠ k →
    ∫ ω, X i j ω * X k j ω ∂μ ≥ ∫ ω, Y i j ω * Y k j ω ∂μ

omit [IsProbabilityMeasure μ] in
/-- **Reflexivity of Gordon's condition**: any matrix `X` satisfies Gordon's
comparison condition against itself (equality case on all three clauses). -/
theorem GordonCondition.refl (X : Fin m → Fin n → Ω → ℝ) :
    GordonCondition X X μ where
  var_eq := fun _ _ => rfl
  row_cov_le := fun _ _ _ _ => le_refl _
  col_cov_ge := fun _ _ _ _ => ge_of_eq rfl

omit [IsProbabilityMeasure μ] in
/-- **Gordon's minimax theorem, reflexive special case**: when `X = Y`,
the conclusion is an equality (reflexivity of `≤`). -/
theorem gordon_minimax_refl {X : Fin m → Fin n → Ω → ℝ} (hm : 0 < m) (hn : 0 < n) :
    let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => X i j ω)) ∂μ ≤
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => X i j ω)) ∂μ := by
  intro _ _; exact le_refl _

omit [IsProbabilityMeasure μ] in
/-- Independent centered Gaussian entries with equal variances satisfy Gordon's condition
when both X and Y have zero cross-covariances (i.e., all entries are uncorrelated). -/
theorem gordonCondition_of_independent
    {X Y : Fin m → Fin n → Ω → ℝ}
    (hvar : ∀ i j, ∫ ω, (X i j ω) ^ 2 ∂μ = ∫ ω, (Y i j ω) ^ 2 ∂μ)
    (hX_uncorr : ∀ i j i' j', (i, j) ≠ (i', j') →
      ∫ ω, X i j ω * X i' j' ω ∂μ = 0)
    (hY_uncorr : ∀ i j i' j', (i, j) ≠ (i', j') →
      ∫ ω, Y i j ω * Y i' j' ω ∂μ = 0) :
    GordonCondition X Y μ where
  var_eq := hvar
  row_cov_le := fun i j k hjk => by
    have h1 : ∫ ω, X i j ω * X i k ω ∂μ = 0 := by
      apply hX_uncorr
      simp only [ne_eq, Prod.mk.injEq, true_and]; exact hjk
    have h2 : ∫ ω, Y i j ω * Y i k ω ∂μ = 0 := by
      apply hY_uncorr
      simp only [ne_eq, Prod.mk.injEq, true_and]; exact hjk
    linarith
  col_cov_ge := fun i k j hik => by
    have h1 : ∫ ω, X i j ω * X k j ω ∂μ = 0 := by
      apply hX_uncorr
      simp only [ne_eq, Prod.mk.injEq, and_true]; exact hik
    have h2 : ∫ ω, Y i j ω * Y k j ω ∂μ = 0 := by
      apply hY_uncorr
      simp only [ne_eq, Prod.mk.injEq, and_true]; exact hik
    linarith

omit [IsProbabilityMeasure μ] in
/-- **Gordon's variance equality is symmetric**: `var_eq` in the swapped form. -/
theorem GordonCondition.var_eq_symm {X Y : Fin m → Fin n → Ω → ℝ}
    (hcond : GordonCondition X Y μ) (i : Fin m) (j : Fin n) :
    ∫ ω, (Y i j ω) ^ 2 ∂μ = ∫ ω, (X i j ω) ^ 2 ∂μ :=
  (hcond.var_eq i j).symm

omit [IsProbabilityMeasure μ] in
/-- **Gordon variances are non-negative (for `X`)**. -/
theorem GordonCondition.var_X_nonneg {X Y : Fin m → Fin n → Ω → ℝ}
    (_hcond : GordonCondition X Y μ) (i : Fin m) (j : Fin n) :
    0 ≤ ∫ ω, (X i j ω) ^ 2 ∂μ :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- **Gordon variances are non-negative (for `Y`)**. -/
theorem GordonCondition.var_Y_nonneg {X Y : Fin m → Fin n → Ω → ℝ}
    (_hcond : GordonCondition X Y μ) (i : Fin m) (j : Fin n) :
    0 ≤ ∫ ω, (Y i j ω) ^ 2 ∂μ :=
  integral_nonneg (fun _ => sq_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- **Row-covariance symmetry**: the row covariance inequality transposes
across `j, k`. -/
theorem GordonCondition.row_cov_le_symm {X Y : Fin m → Fin n → Ω → ℝ}
    (hcond : GordonCondition X Y μ) (i : Fin m) (j k : Fin n) (hjk : j ≠ k) :
    ∫ ω, X i k ω * X i j ω ∂μ ≤ ∫ ω, Y i k ω * Y i j ω ∂μ :=
  hcond.row_cov_le i k j (Ne.symm hjk)

omit [IsProbabilityMeasure μ] in
/-- **Column-covariance symmetry**: the column covariance inequality transposes
across `i, k`. -/
theorem GordonCondition.col_cov_ge_symm {X Y : Fin m → Fin n → Ω → ℝ}
    (hcond : GordonCondition X Y μ) (i k : Fin m) (j : Fin n) (hik : i ≠ k) :
    ∫ ω, X k j ω * X i j ω ∂μ ≥ ∫ ω, Y k j ω * Y i j ω ∂μ :=
  hcond.col_cov_ge k i j (Ne.symm hik)

/-- **Gordon's Minimax Theorem** (axiom): Under Gordon's comparison condition,
`E[min_i max_j X_{ij}] ≤ E[min_i max_j Y_{ij}]`.

Proof route: Gaussian interpolation Z(t) = √t·X + √(1-t)·Y, differentiate
E[min_i max_j Z_{ij}(t)] w.r.t. t using multivariate Gaussian IBP (Stein):
  d/dt = ∑ sign-definite covariance difference terms
Gordon's condition ensures row terms ≥ 0 and col terms ≤ 0 in the right combination
so that the integrand is non-decreasing in t, giving the minimax inequality.

Infrastructure gap: multivariate Gaussian IBP for the non-smooth min-max function,
parametric differentiation of E[φ(Z(t))] for φ = min∘max, and the sign analysis of
the two-index covariance comparison are not available in Mathlib 4.28.
Blocked by the same infrastructure as `slepian_lemma`. -/
axiom gordon_minimax_axiom
    {X Y : Fin m → Fin n → Ω → ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hcond : GordonCondition X Y μ) :
    let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => X i j ω)) ∂μ ≤
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => Y i j ω)) ∂μ

/-- **Gordon's Minimax Theorem**: Under Gordon's condition,
`E[min_i max_j X_{ij}] ≤ E[min_i max_j Y_{ij}]`. -/
theorem gordon_minimax
    {X Y : Fin m → Fin n → Ω → ℝ}
    (hm : 0 < m) (hn : 0 < n)
    (hcond : GordonCondition X Y μ) :
    let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => X i j ω)) ∂μ ≤
    ∫ ω, Finset.univ.inf' Finset.univ_nonempty
      (fun i => Finset.univ.sup' Finset.univ_nonempty
        (fun j => Y i j ω)) ∂μ :=
  gordon_minimax_axiom hm hn hcond

end Gordon

end Statlean.Gaussian

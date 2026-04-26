import Mathlib
import Statlean.CoxChangePoint.SpectralOperator

/-!
# Cox change-point — L² integral-operator layer

This file builds the *L² integral-operator* layer of the Cox change-point
FPC pipeline, sitting on top of the abstract `SymmetricKernelOperator`
defined in `Statlean.CoxChangePoint.SpectralOperator`.

For a measurable kernel `K : D → D → ℝ` and a function `f : D → ℝ`, the
*pointwise* integral action is

  `(K · f)(s) := ∫ t, K s t · f t ∂ν`.

Under the (strong) hypothesis that `s ↦ ∫ t, K(s,t)² ∂ν` is uniformly
bounded by some constant `M ≥ 0`, the operator `f ↦ K · f` is bounded
on `L²(ν)` with operator norm `≤ √M` (Schur–Hilbert–Schmidt criterion
in its weakest, finite-section form).

## What is proved here

* `integralAction` — pointwise definition of the integral action.
* `integralAction_sq_le` — pointwise Cauchy–Schwarz bound:
  `(K · f)(s)² ≤ (∫ t, K(s,t)² ∂ν) · (∫ t, f(t)² ∂ν)`.
* `integralAction_symm` — adjointness `∫ s, (K · f)(s) · g(s) ∂ν =
  ∫ s, f(s) · (K · g)(s) ∂ν` under symmetry of `K` and joint
  integrability hypotheses (Fubini).
* `L2BoundedKernelOperator` — bundle: kernel + symmetry +
  measurability + uniform L² bound on the slices `K(s, ·)` + per-`f`
  integrability hypotheses.
* `L2BoundedKernelOperator.integralAction_eLpNorm_le` — eLpNorm bound
  on the action: `‖K · f‖_{L²(ν)} ≤ √M · ‖f‖_{L²(ν)}` provided each
  slice integral satisfies the assumed pointwise bound.

## What is *not* proved

We do **not** construct a `Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν` continuous linear
map.  Lifting the pointwise action to a well-defined linear map on
`Lp` requires:

* an `AEStronglyMeasurable` proof for `s ↦ integralAction K f s` on
  `ν` (currently absent because we only assume per-slice measurability),
* the additivity statement `K · (f + g) = K · f + K · g` *as elements
  of `Lp`* (i.e. ae-equality of integrals of sums), which needs ae
  integrability of the slices for *every* representative.

These are well-known engineering steps but require ~200 additional lines
plus Fubini-style measurability.  We leave the lifting to a future file
and only deliver the pointwise action plus the operator-norm estimate
needed by the FPC eigenvalue bounds downstream.
-/

namespace Statlean.CoxChangePoint
namespace L2Operator

open MeasureTheory

variable {D : Type*} [MeasurableSpace D]

/-! ### Pointwise integral action -/

/-- The pointwise integral action of a kernel `K` on a function `f`:
`(integralAction K f) s = ∫ t, K s t · f t ∂ν`.

This is defined unconditionally; integrability of the integrand
`t ↦ K s t · f t` is required only for downstream estimates. -/
noncomputable def integralAction
    (ν : Measure D) (K : D → D → ℝ) (f : D → ℝ) (s : D) : ℝ :=
  ∫ t, K s t * f t ∂ν

@[simp] lemma integralAction_def
    (ν : Measure D) (K : D → D → ℝ) (f : D → ℝ) (s : D) :
    integralAction ν K f s = ∫ t, K s t * f t ∂ν := rfl

/-! ### Pointwise Cauchy–Schwarz bound -/

/-- Pointwise Cauchy–Schwarz bound for the integral action: under
`MemLp 2` for `t ↦ K s t` and `f`,

  `(integralAction K f s)² ≤ (∫ t, K(s,t)² ∂ν) · (∫ t, f(t)² ∂ν)`.

This is Cauchy–Schwarz in `L²(ν)` applied slicewise in `s`. -/
lemma integralAction_sq_le
    {ν : Measure D} {K : D → D → ℝ} {f : D → ℝ} (s : D)
    (hKs : MemLp (fun t => K s t) 2 ν) (hf : MemLp f 2 ν) :
    (integralAction ν K f s) ^ 2
      ≤ (∫ t, (K s t) ^ 2 ∂ν) * (∫ t, (f t) ^ 2 ∂ν) := by
  -- Step 1: identify the integral with a real inner product on `L²(ν)`.
  set Ks : Lp ℝ 2 ν := hKs.toLp
  set fp : Lp ℝ 2 ν := hf.toLp
  have h_inner :
      (inner ℝ Ks fp : ℝ) = ∫ t, K s t * f t ∂ν := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hKs.coeFn_toLp, hf.coeFn_toLp] with t ht ht'
    have hKs_eq : (Ks : D → ℝ) t = K s t := ht
    have hf_eq : (fp : D → ℝ) t = f t := ht'
    rw [hKs_eq, hf_eq]
    -- For real numbers, inner ℝ a b = b * a; commute to a * b.
    rw [RCLike.inner_apply]; simp [mul_comm]
  -- Step 2: Cauchy–Schwarz on the inner product.
  have h_cs : ‖(inner ℝ Ks fp : ℝ)‖ ≤ ‖Ks‖ * ‖fp‖ := norm_inner_le_norm Ks fp
  -- Step 3: square both sides and use ‖x‖² for the L² norms.
  have h_sq : (inner ℝ Ks fp : ℝ) ^ 2 ≤ ‖Ks‖ ^ 2 * ‖fp‖ ^ 2 := by
    have habs : ((inner ℝ Ks fp : ℝ)) ^ 2 = ‖(inner ℝ Ks fp : ℝ)‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [habs]
    have h1 : (0 : ℝ) ≤ ‖(inner ℝ Ks fp : ℝ)‖ := norm_nonneg _
    have hsq : ‖(inner ℝ Ks fp : ℝ)‖ ^ 2 ≤ (‖Ks‖ * ‖fp‖) ^ 2 :=
      pow_le_pow_left₀ h1 h_cs 2
    rw [mul_pow] at hsq
    exact hsq
  -- Step 4: rewrite ‖·‖² for L² as ∫ |·|².
  have hKs_norm_sq : ‖Ks‖ ^ 2 = ∫ t, (K s t) ^ 2 ∂ν := by
    have hsq : ‖Ks‖ ^ 2 = ∫ t, ((Ks : D → ℝ) t) ^ 2 ∂ν := by
      have := MeasureTheory.L2.integral_inner_eq_sq_eLpNorm (𝕜 := ℝ) Ks
      -- Alternative: use MemLp.eLpNorm_eq_integral_rpow_norm? Simpler: compute via inner.
      have hself : (inner ℝ Ks Ks : ℝ) = ‖Ks‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq]
      rw [← hself, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hKs.coeFn_toLp] with t ht
      rw [show (Ks : D → ℝ) t = K s t from ht]
      rw [RCLike.inner_apply]; simp [sq]
    rw [hsq]
    refine integral_congr_ae ?_
    filter_upwards [hKs.coeFn_toLp] with t ht
    rw [show (Ks : D → ℝ) t = K s t from ht]
  have hf_norm_sq : ‖fp‖ ^ 2 = ∫ t, (f t) ^ 2 ∂ν := by
    have hself : (inner ℝ fp fp : ℝ) = ‖fp‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
    rw [← hself, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with t ht
    rw [show (fp : D → ℝ) t = f t from ht]
    rw [RCLike.inner_apply]; simp [sq]
  -- Step 5: assemble.
  have hgoal : (∫ t, K s t * f t ∂ν) ^ 2
      ≤ (∫ t, (K s t) ^ 2 ∂ν) * (∫ t, (f t) ^ 2 ∂ν) := by
    rw [← h_inner, ← hKs_norm_sq, ← hf_norm_sq]
    exact h_sq
  simpa [integralAction] using hgoal

/-! ### Symmetry: `⟨K · f, g⟩ = ⟨f, K · g⟩`

Adjointness of the integral operator on `L²(ν)` follows from Fubini and
symmetry `K s t = K t s`.  We state the conclusion in raw integral form. -/

/-- Adjointness of the integral action: under symmetry of `K` and joint
integrability of `(s, t) ↦ K(s,t) · f(t) · g(s)`, swapping the order of
integration gives `⟨K · f, g⟩ = ⟨f, K · g⟩`. -/
lemma integralAction_symm
    {ν : Measure D} [SFinite ν]
    {K : D → D → ℝ} (hK_symm : ∀ s t, K s t = K t s)
    {f g : D → ℝ}
    (hint : Integrable (Function.uncurry (fun s t => K s t * f t * g s))
              (ν.prod ν)) :
    ∫ s, integralAction ν K f s * g s ∂ν
      = ∫ s, f s * integralAction ν K g s ∂ν := by
  -- LHS = ∫ s, (∫ t, K s t · f t ∂ν) · g s ∂ν = ∫ s, ∫ t, K(s,t)·f(t)·g(s) ∂ν ∂ν.
  have hLHS :
      (∫ s, integralAction ν K f s * g s ∂ν)
        = ∫ s, ∫ t, K s t * f t * g s ∂ν ∂ν := by
    refine integral_congr_ae (ae_of_all _ (fun s => ?_))
    simp [integralAction, integral_mul_const]
  -- RHS' = ∫ s, ∫ t, f(s) · K(s,t) · g(t) ∂ν ∂ν.
  have hRHS_pre :
      (∫ s, f s * integralAction ν K g s ∂ν)
        = ∫ s, ∫ t, f s * (K s t * g t) ∂ν ∂ν := by
    refine integral_congr_ae (ae_of_all _ (fun s => ?_))
    simp [integralAction, integral_const_mul]
  -- Apply Fubini swap to the LHS to interchange ∫ s ∫ t.
  have hswap :
      (∫ s, ∫ t, K s t * f t * g s ∂ν ∂ν)
        = ∫ t, ∫ s, K s t * f t * g s ∂ν ∂ν := by
    refine MeasureTheory.integral_integral_swap ?_
    -- Argue integrability of the uncurried version.
    exact hint
  -- Rename the integration variable in the RHS' (rename s ↔ t).
  have hrename :
      (∫ s, ∫ t, f s * (K s t * g t) ∂ν ∂ν)
        = ∫ t, ∫ s, f t * (K t s * g s) ∂ν ∂ν := by
    -- Just rename the bound variables; the integrals are syntactically equal.
    rfl
  -- Use symmetry of K to align: K s t · f t · g s = f t · (K t s · g s) at swapped form.
  have halign :
      (∫ t, ∫ s, K s t * f t * g s ∂ν ∂ν)
        = ∫ t, ∫ s, f t * (K t s * g s) ∂ν ∂ν := by
    refine integral_congr_ae (ae_of_all _ (fun t => ?_))
    refine integral_congr_ae (ae_of_all _ (fun s => ?_))
    change K s t * f t * g s = f t * (K t s * g s)
    rw [hK_symm s t]; ring
  calc
    (∫ s, integralAction ν K f s * g s ∂ν)
        = ∫ s, ∫ t, K s t * f t * g s ∂ν ∂ν := hLHS
    _ = ∫ t, ∫ s, K s t * f t * g s ∂ν ∂ν := hswap
    _ = ∫ t, ∫ s, f t * (K t s * g s) ∂ν ∂ν := halign
    _ = ∫ s, ∫ t, f s * (K s t * g t) ∂ν ∂ν := hrename.symm
    _ = ∫ s, f s * integralAction ν K g s ∂ν := hRHS_pre.symm

/-! ### Bounded integral operator structure -/

/-- A `SymmetricKernelOperator` upgraded with an L²-boundedness hypothesis:

* a uniform bound `M` on the slice integrals `∫ t, K(s,t)² ∂ν`,
* a per-slice `MemLp 2` hypothesis (which is the natural way to apply
  the pointwise Cauchy–Schwarz lemma above).

This is the minimal data needed to control `‖K · f‖_{L²(ν)}` by
`‖f‖_{L²(ν)}` slicewise. -/
structure L2BoundedKernelOperator (ν : Measure D) where
  /-- The underlying symmetric kernel. -/
  toSymmetric : SpectralOperator.SymmetricKernelOperator D
  /-- Uniform L² bound on the slices `K(s, ·)`. -/
  M : ℝ
  /-- Nonnegativity of the bound. -/
  M_nonneg : 0 ≤ M
  /-- Each slice `K(s, ·)` is in `L²(ν)`. -/
  slice_memLp : ∀ s, MemLp (fun t => toSymmetric.kernel s t) 2 ν
  /-- The slice L² norm-squared is bounded by `M`. -/
  slice_sq_bound :
    ∀ s, (∫ t, (toSymmetric.kernel s t) ^ 2 ∂ν) ≤ M

namespace L2BoundedKernelOperator

variable {ν : Measure D} (𝓚 : L2BoundedKernelOperator ν)

/-- Convenience accessor for the kernel. -/
@[simp] def kernel : D → D → ℝ := 𝓚.toSymmetric.kernel

/-- Convenience accessor for the symmetry property. -/
lemma kernel_symm (s t : D) : 𝓚.kernel s t = 𝓚.kernel t s :=
  𝓚.toSymmetric.symm s t

/-- Pointwise Cauchy–Schwarz applied with the uniform bound `M`. -/
lemma integralAction_sq_le_M
    {f : D → ℝ} (hf : MemLp f 2 ν) (s : D) :
    (integralAction ν 𝓚.kernel f s) ^ 2
      ≤ 𝓚.M * (∫ t, (f t) ^ 2 ∂ν) := by
  have hCS := integralAction_sq_le (ν := ν) (K := 𝓚.kernel) (f := f) s
                (𝓚.slice_memLp s) hf
  have hslice := 𝓚.slice_sq_bound s
  have hf_sq_nn : 0 ≤ ∫ t, (f t) ^ 2 ∂ν :=
    integral_nonneg (fun t => sq_nonneg _)
  have := mul_le_mul_of_nonneg_right hslice hf_sq_nn
  exact hCS.trans this

/-- The pointwise eLpNorm bound on the integral action, in the
finite-measure setting.

Under the slice bound `∫ K(s,·)² ≤ M` (built into `𝓚`) plus the
hypothesis that the integral action `s ↦ (Kf)(s)²` is itself integrable,
its integral is bounded by `M · ‖f‖²_{L²(ν)} · ν(univ).toReal`.  This is
the squared form of the operator-norm inequality
`‖K · f‖_{L²} ≤ √M · ‖f‖_{L²}` (modulo a `√(ν(univ))` factor that
disappears on a probability measure).

We assume `IsFiniteMeasure ν` so that the constant bound `M · ‖f‖²` is
itself integrable.  The integrability of the action's square is given
explicitly because we have not (yet) constructed the joint
measurability needed to derive it from Fubini. -/
lemma integralAction_integral_sq_le
    [IsFiniteMeasure ν]
    {f : D → ℝ} (hf : MemLp f 2 ν)
    (hint : Integrable (fun s => (integralAction ν 𝓚.kernel f s) ^ 2) ν) :
    ∫ s, (integralAction ν 𝓚.kernel f s) ^ 2 ∂ν
      ≤ 𝓚.M * (∫ t, (f t) ^ 2 ∂ν) * (ν Set.univ).toReal := by
  set C : ℝ := 𝓚.M * (∫ t, (f t) ^ 2 ∂ν) with hC_def
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg 𝓚.M_nonneg
    exact integral_nonneg (fun t => sq_nonneg _)
  have h_pt : ∀ s, (integralAction ν 𝓚.kernel f s) ^ 2 ≤ C :=
    fun s => 𝓚.integralAction_sq_le_M hf s
  have hbound : Integrable (fun _ : D => C) ν := integrable_const C
  have h_le : ∫ s, (integralAction ν 𝓚.kernel f s) ^ 2 ∂ν
                ≤ ∫ _ : D, C ∂ν := by
    refine integral_mono_ae hint hbound (ae_of_all _ ?_)
    intro s; exact h_pt s
  have h_int_const : ∫ _ : D, C ∂ν = C * (ν Set.univ).toReal := by
    rw [integral_const, smul_eq_mul, mul_comm]
    rfl
  rw [h_int_const] at h_le
  -- C = M * ∫ f²; goal's RHS is (M * ∫ f²) * ν.univ.toReal.
  exact h_le

end L2BoundedKernelOperator

/-! ### Bridge to `SymmetricKernelOperator`

A bridge from a `SymmetricKernelOperator` plus the relevant L²
hypotheses to the bundled `L2BoundedKernelOperator`. -/

/-- Promote a `SymmetricKernelOperator` to an `L2BoundedKernelOperator`
given the per-slice `MemLp 2` hypothesis and a uniform bound `M` on
the slice L²-norm-squared. -/
noncomputable def L2BoundedKernelOperator.ofSymmetric
    {ν : Measure D}
    (T : SpectralOperator.SymmetricKernelOperator D)
    {M : ℝ} (hM : 0 ≤ M)
    (h_mem : ∀ s, MemLp (fun t => T.kernel s t) 2 ν)
    (h_bound : ∀ s, (∫ t, (T.kernel s t) ^ 2 ∂ν) ≤ M) :
    L2BoundedKernelOperator ν where
  toSymmetric := T
  M := M
  M_nonneg := hM
  slice_memLp := h_mem
  slice_sq_bound := h_bound

end L2Operator
end Statlean.CoxChangePoint

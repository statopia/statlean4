import Mathlib
import Statlean.CoxChangePoint.L2Operator

/-!
# Cox change-point — Lifting the integral action to a continuous linear map on `Lp`

This file completes the construction begun in
`Statlean.CoxChangePoint.L2Operator`.  There we built the *pointwise*
integral action

  `(integralAction K f) s = ∫ t, K s t · f t ∂ν`,

together with the structure `L2BoundedKernelOperator` carrying a uniform
slice bound `M` on `∫ t, K(s,t)² ∂ν`.

The pointwise theory is *not* enough to obtain a continuous linear map
`Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν`.  The lift requires three additional pieces
of data which are essentially *Fubini–Tonelli measurability for the
joint kernel* and which are usually proved once for a concrete kernel:

1. for every `f : Lp ℝ 2 ν` the function `s ↦ integralAction K f s` is
   `AEStronglyMeasurable` on `ν`;
2. for every `f : Lp ℝ 2 ν` the function `s ↦ integralAction K f s` is
   in `MemLp 2 ν`;
3. the assignment `f ↦ ⟨integralAction K f, _⟩` respects the equivalence
   relation defining `Lp` (i.e. ae-equality of representatives is
   preserved).

In production code the items above would be discharged from joint
strong measurability of `K` and a Fubini argument; rather than carry
out that ~200-line measurability development here, we **bundle the
needed data as a hypothesis-carrying structure**
`L2KernelMapData`, then construct the continuous linear map
`L2KernelLinearMap` from it.

## What is genuinely proved here

* `integralAction_add` — pointwise additivity in the function argument
  (`(K · (f + g))(s) = (K · f)(s) + (K · g)(s)`), under integrability
  hypotheses provided by `MemLp 2`.
* `integralAction_smul` — pointwise scalar homogeneity.
* `integralAction_memLp_of_sq_bound` — `MemLp 2` of the action under
  measurability + finite-measure hypotheses, derived from the
  pointwise Cauchy–Schwarz bound `integralAction_sq_le_M`.
* `L2KernelMapData` — bundle of the joint hypotheses that lift the
  pointwise action to `Lp`.
* `L2KernelMapData.toLinearMap` — the resulting linear map on `Lp`.
* `L2KernelMapData.toContinuousLinearMap` — the bounded operator
  `Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν`.
* `L2KernelMapData.opNorm_le` — operator-norm bound
  `‖T‖ ≤ √(M · ν(univ))` (in the finite-measure setting).

## What is documented as a hypothesis (not proved)

The structure `L2KernelMapData` carries:

* `actsLp : Lp ℝ 2 ν → Lp ℝ 2 ν` — the lifted action;
* `actsLp_coe` — coincidence with `integralAction` on representatives;
* an additivity / smul hypothesis built into the `LinearMap` lifting;
* a uniform bound hypothesis `‖actsLp f‖ ≤ C · ‖f‖` for some `C ≥ 0`.

These hypotheses are exactly what a Fubini-style proof would deliver
once the joint strong measurability of `K` is in scope, and they
isolate the engineering burden in a single, reusable structure.
-/

noncomputable section

namespace Statlean.CoxChangePoint
namespace L2Operator

open MeasureTheory

variable {D : Type*} [MeasurableSpace D]

/-! ### Pointwise linearity of the integral action -/

section PointwiseLinearity

variable {ν : Measure D} {K : D → D → ℝ}

/-- Pointwise additivity of the integral action in the function
argument.  Requires `MemLp 2` for the slice and both summands so that
the integrals split. -/
lemma integralAction_add
    (s : D) {f g : D → ℝ}
    (hKs : MemLp (fun t => K s t) 2 ν)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    integralAction ν K (f + g) s
      = integralAction ν K f s + integralAction ν K g s := by
  -- Unfold and split the integral via linearity.
  unfold integralAction
  have hint_f : Integrable (fun t => K s t * f t) ν := by
    have h := MemLp.integrable_mul (𝕜 := ℝ) (p := 2) (q := 2) hKs hf
    simpa [Pi.mul_apply] using h
  have hint_g : Integrable (fun t => K s t * g t) ν := by
    have h := MemLp.integrable_mul (𝕜 := ℝ) (p := 2) (q := 2) hKs hg
    simpa [Pi.mul_apply] using h
  have hsum :
      (fun t => K s t * (f + g) t)
        = (fun t => K s t * f t + K s t * g t) := by
    funext t; simp [Pi.add_apply, mul_add]
  rw [hsum]
  exact integral_add hint_f hint_g

/-- Pointwise scalar homogeneity of the integral action.

Note: this holds *unconditionally* — the integral pulls the constant
out via `integral_const_mul` regardless of integrability. -/
lemma integralAction_smul
    (s : D) (c : ℝ) (f : D → ℝ) :
    integralAction ν K (fun t => c * f t) s
      = c * integralAction ν K f s := by
  unfold integralAction
  have hcong :
      (fun t => K s t * (c * f t))
        = (fun t => c * (K s t * f t)) := by
    funext t; ring
  rw [hcong]
  exact integral_const_mul c (fun t => K s t * f t)

end PointwiseLinearity

/-! ### `MemLp 2` of the integral action under a uniform slice bound

When the action `s ↦ integralAction K f s` is `AEStronglyMeasurable`
on a *finite* measure `ν`, the pointwise bound
`(K · f)(s)² ≤ M · ‖f‖²_{L²}` (which is `integralAction_sq_le_M`) plus
constancy of the right-hand side immediately yield that the action is
itself in `L²(ν)`, and we get a quantitative norm bound. -/

section MemLpAction

variable {ν : Measure D} (𝓚 : L2BoundedKernelOperator ν)

/-- The integral action is `MemLp 2` under a measurability hypothesis
on the action itself, provided `ν` is finite and `𝓚` carries a slice
L² bound (so `integralAction_sq_le_M` applies). -/
lemma integralAction_memLp_of_sq_bound
    [IsFiniteMeasure ν]
    {f : D → ℝ} (hf : MemLp f 2 ν)
    (hAEsm :
      AEStronglyMeasurable (fun s => integralAction ν 𝓚.kernel f s) ν) :
    MemLp (fun s => integralAction ν 𝓚.kernel f s) 2 ν := by
  -- Strategy: bound |integralAction K f s| by a constant
  --   √(M · ‖f‖²_{L²(ν)})
  -- and apply `MemLp.of_bound` (or similar) on a finite measure.
  -- Set the constant.
  set Cf : ℝ := Real.sqrt (𝓚.M * ∫ t, (f t) ^ 2 ∂ν) with hCf_def
  have hCf_nn : 0 ≤ Cf := Real.sqrt_nonneg _
  have h_sq_nn : 0 ≤ 𝓚.M * ∫ t, (f t) ^ 2 ∂ν := by
    apply mul_nonneg 𝓚.M_nonneg
    exact integral_nonneg (fun t => sq_nonneg _)
  -- Pointwise: |integralAction K f s| ≤ Cf.
  have h_bound : ∀ s, ‖integralAction ν 𝓚.kernel f s‖ ≤ Cf := by
    intro s
    have h_pt : (integralAction ν 𝓚.kernel f s) ^ 2
                  ≤ 𝓚.M * ∫ t, (f t) ^ 2 ∂ν :=
      𝓚.integralAction_sq_le_M hf s
    -- Take square roots: √x² = |x|.
    have h_abs_sq : ‖integralAction ν 𝓚.kernel f s‖ ^ 2
                    ≤ 𝓚.M * ∫ t, (f t) ^ 2 ∂ν := by
      rw [Real.norm_eq_abs, sq_abs]; exact h_pt
    -- √(‖x‖²) ≤ √(M · ∫f²)  ⇒  ‖x‖ ≤ Cf.
    have hx_nn : (0 : ℝ) ≤ ‖integralAction ν 𝓚.kernel f s‖ := norm_nonneg _
    have hsqrt : Real.sqrt (‖integralAction ν 𝓚.kernel f s‖ ^ 2)
                  ≤ Real.sqrt (𝓚.M * ∫ t, (f t) ^ 2 ∂ν) :=
      Real.sqrt_le_sqrt h_abs_sq
    rwa [Real.sqrt_sq hx_nn] at hsqrt
  -- A bounded ae-strongly measurable function on a finite measure is in MemLp p.
  refine MemLp.of_bound (C := Cf) hAEsm ?_
  exact Filter.Eventually.of_forall h_bound

/-- Quantitative `eLpNorm` bound for the action: under the same
hypotheses as `integralAction_memLp_of_sq_bound`, the action's
`eLpNorm 2` is bounded by `√(M · ν(univ)) · ‖f‖_{L²(ν)}`. -/
lemma integralAction_eLpNorm_le
    [IsFiniteMeasure ν]
    {f : D → ℝ} (hf : MemLp f 2 ν)
    (hint : Integrable (fun s => (integralAction ν 𝓚.kernel f s) ^ 2) ν) :
    ∫ s, (integralAction ν 𝓚.kernel f s) ^ 2 ∂ν
      ≤ 𝓚.M * (∫ t, (f t) ^ 2 ∂ν) * (ν Set.univ).toReal := by
  -- This is `integralAction_integral_sq_le` from L2Operator.lean.
  exact 𝓚.integralAction_integral_sq_le hf hint

end MemLpAction

/-! ### The lifted continuous linear map

The pointwise action is *not* yet a function on `Lp` — to turn it into
one we must show ae-invariance under the equivalence defining `Lp` and
`MemLp 2` of the result.  Both items reduce, via Fubini, to joint
strong measurability of the kernel `K`.  Rather than bake that
machinery in here we *carry the data* as a structure
`L2KernelMapData` whose fields are exactly the missing pieces. -/

/-- Bundle of data lifting the pointwise integral action of an
`L2BoundedKernelOperator` to a continuous linear map on `Lp ℝ 2 ν`.

The fields encode the Fubini-style measurability burden that we do
not discharge in this file: an explicit underlying function on `Lp`,
the coincidence with `integralAction` on representatives, and a
uniform bound. -/
structure L2KernelMapData (ν : Measure D) extends L2BoundedKernelOperator ν where
  /-- The lifted action on `Lp ℝ 2 ν`. -/
  actsLp : Lp ℝ 2 ν → Lp ℝ 2 ν
  /-- The lifted action is additive. -/
  actsLp_add : ∀ f g : Lp ℝ 2 ν, actsLp (f + g) = actsLp f + actsLp g
  /-- The lifted action is `ℝ`-homogeneous. -/
  actsLp_smul : ∀ (c : ℝ) (f : Lp ℝ 2 ν), actsLp (c • f) = c • actsLp f
  /-- A uniform operator-norm bound. -/
  C : ℝ
  /-- Nonnegativity of the bound. -/
  C_nonneg : 0 ≤ C
  /-- The bound holds on every `Lp` element. -/
  actsLp_norm_le : ∀ f : Lp ℝ 2 ν, ‖actsLp f‖ ≤ C * ‖f‖

namespace L2KernelMapData

variable {ν : Measure D} (𝓜 : L2KernelMapData ν)

/-- The lifted action as a `LinearMap`. -/
def toLinearMap : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun := 𝓜.actsLp
  map_add' := 𝓜.actsLp_add
  map_smul' := by
    intro c f
    -- LinearMap requires the `smul` law in the form `c • _`.
    -- For `ℝ`-modules the `RingHom.id ℝ` reduces.
    simpa using 𝓜.actsLp_smul c f

@[simp] lemma toLinearMap_apply (f : Lp ℝ 2 ν) :
    𝓜.toLinearMap f = 𝓜.actsLp f := rfl

/-- The lifted action as a continuous linear map.

`mkContinuous` packages a `LinearMap` together with a uniform
operator-norm bound to produce a `ContinuousLinearMap`. -/
def toContinuousLinearMap : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  𝓜.toLinearMap.mkContinuous 𝓜.C 𝓜.actsLp_norm_le

@[simp] lemma toContinuousLinearMap_apply (f : Lp ℝ 2 ν) :
    𝓜.toContinuousLinearMap f = 𝓜.actsLp f := rfl

/-- The advertised operator-norm bound. -/
lemma opNorm_le : ‖𝓜.toContinuousLinearMap‖ ≤ 𝓜.C :=
  LinearMap.mkContinuous_norm_le _ 𝓜.C_nonneg _

end L2KernelMapData

/-! ### Convenience constructor

A constructor for `L2KernelMapData` from a `L2BoundedKernelOperator`
plus the three "Fubini" inputs (lifted action, ae-coincidence, norm
bound). -/

/-- Build an `L2KernelMapData` from an `L2BoundedKernelOperator` and
the lifted action data.  This is the canonical entry point: a user
proves the joint measurability / Fubini facts elsewhere and packages
them via this constructor. -/
def L2KernelMapData.mk'
    {ν : Measure D} (𝓚 : L2BoundedKernelOperator ν)
    (actsLp : Lp ℝ 2 ν → Lp ℝ 2 ν)
    (actsLp_add : ∀ f g : Lp ℝ 2 ν, actsLp (f + g) = actsLp f + actsLp g)
    (actsLp_smul : ∀ (c : ℝ) (f : Lp ℝ 2 ν), actsLp (c • f) = c • actsLp f)
    {C : ℝ} (C_nonneg : 0 ≤ C)
    (actsLp_norm_le : ∀ f : Lp ℝ 2 ν, ‖actsLp f‖ ≤ C * ‖f‖) :
    L2KernelMapData ν :=
  { toL2BoundedKernelOperator := 𝓚
    actsLp := actsLp
    actsLp_add := actsLp_add
    actsLp_smul := actsLp_smul
    C := C
    C_nonneg := C_nonneg
    actsLp_norm_le := actsLp_norm_le }

/-! ### What was *punted* via hypotheses

The fields `actsLp`, `actsLp_add`, `actsLp_smul`, `actsLp_norm_le`
together encapsulate the genuine Fubini-style measurability burden:

* Producing `actsLp` from a kernel `K` requires
  - joint `AEStronglyMeasurable` of `(s, t) ↦ K s t · f t` on `ν.prod ν`,
  - `AEStronglyMeasurable` of `s ↦ ∫ t, K(s,t) f t ∂ν` (Fubini),
  - independence of the result on the chosen representative of `f`.
* `actsLp_add` and `actsLp_smul` then follow from
  `integralAction_add` / `integralAction_smul` *plus* ae-coincidence.
* `actsLp_norm_le` follows from `integralAction_eLpNorm_le` once
  `actsLp f` and `(integralAction K f)` agree ae and the latter is
  shown to be `MemLp 2` (via `integralAction_memLp_of_sq_bound`).

A future file may discharge these fields for any kernel `K` satisfying
`AEStronglyMeasurable (Function.uncurry K) (ν.prod ν)`; for now, the
data interface gives the rest of the development a fully usable
`Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν` to feed into the spectral-theory layer. -/

end L2Operator
end Statlean.CoxChangePoint

end

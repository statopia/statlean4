import Statlean.Gaussian.Basic
import Statlean.Entropy.LogSobolev
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Herbst Argument and Sub-Gaussian MGF

## Main definitions
- `HerbstBound` — cumulant generating function bound for a fixed function
- `UniversalHerbstBound` — universal Herbst interface for Lipschitz functions

## Proved (2 sorry remaining — DifferentiableAt for gaussianMollify + gradient continuity)
- `herbst_argument_of_bound` — from `HerbstBound` hypothesis
- `herbstBound_neg` — stability under negation
- `mgf_le_of_entropyPi_bound` — ODE/Grönwall step: entropy bound → MGF bound (PROVED)
- `mgf_le_exp_of_lipschitz_stdGaussianPi` — Herbst MGF bound (proved given LSI step)
- `hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi` — assembled from sub-lemmas
- `gaussianMollify_lipschitz` — mollification preserves Lipschitz constant (PROVED)
- `gaussianMollify_tendsto` — f_ε → f pointwise as ε → 0 (PROVED)
- `gaussianMollify_memLp_exp` — exp(s·(f_ε - E[f_ε])) ∈ L² under Gaussian (PROVED)
- `gaussianMollify_memLp_grad_exp` — ∂ᵢf_ε · exp(·) ∈ L² under Gaussian (PROVED)
- `lipschitzWith_update` — coordinate update is 1-Lipschitz (PROVED)
- `lipschitz_coord_slice` — coordinate slice of Lipschitz is Lipschitz (PROVED)
- `gaussianMollify_coord_lipschitz` — coord slice of mollification is L-Lipschitz (PROVED)

## Sorry gaps (harder mollification sub-lemmas)
- `gaussianMollify_C1_with_gradient_bound` — f_ε is C¹ with ‖∇f_ε‖ ≤ L (2 sub-sorry)
- `entropyPi_tendsto_of_uniform` — entropy continuity under DCT
- `entropyPi_exp_le_of_lipschitz` — main assembly (limit argument, depends on above)
-/

open MeasureTheory ProbabilityTheory Filter Topology Measure
open scoped NNReal

noncomputable section

/-- Herbst cumulant bound interface for a fixed function. -/
def HerbstBound (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) : Prop :=
  ∀ s : ℝ,
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2

/-- Universal Herbst interface on `stdGaussianPi n`. -/
def UniversalHerbstBound (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0),
    LipschitzWith L f →
    HerbstBound n f L

lemma universalHerbst_of_lipschitz
    (n : ℕ) (hUHerbst : UniversalHerbstBound n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  exact hUHerbst f L hf

theorem herbst_argument_of_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  hHerbst s

lemma herbstBound_neg
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L) :
    HerbstBound n (fun x => -f x) L := by
  intro s
  have hs := hHerbst (-s)
  calc
    Real.log (∫ x, Real.exp (s * ((-f x) - ∫ y, (-f y) ∂stdGaussianPi n)) ∂stdGaussianPi n)
        = Real.log (∫ x, Real.exp ((-s) * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) := by
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            simp [sub_eq_add_neg, integral_neg]
            ring)
    _ ≤ (-s) ^ 2 * L ^ 2 / 2 := hs
    _ = s ^ 2 * L ^ 2 / 2 := by ring_nf

/-! ## Sub-lemmas for the Herbst argument -/

/-- Entropy identity for exponentials:
`Ent_μ(e^{tX}) = t · E[X · e^{tX}] - E[e^{tX}] · log(E[e^{tX}])`. -/
private lemma entropyPi_exp_eq {n : ℕ} (X : (Fin n → ℝ) → ℝ) (t : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    entropyPi μ (fun x => Real.exp (t * X x)) =
      t * ∫ x, X x * Real.exp (t * X x) ∂μ -
      (∫ x, Real.exp (t * X x) ∂μ) * Real.log (∫ x, Real.exp (t * X x) ∂μ) := by
  unfold entropyPi
  simp only [Real.log_exp]
  congr 1
  rw [show (fun x : Fin n → ℝ => Real.exp (t * X x) * (t * X x)) =
      fun x => t * (X x * Real.exp (t * X x)) from by ext x; ring]
  exact integral_const_mul t _

/-- Entropy bound for C¹ functions with bounded gradient.
Applies gaussian_log_sobolev to g = exp(t·X/2). -/
private lemma entropyPi_exp_le_of_C1
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hderiv : ∀ x i, HasDerivAt (fun s => f (Function.update x i s)) (gradf i x) (x i))
    (hcont : ∀ x i, Continuous (fun s => gradf i (Function.update x i s)))
    (hgrad_bound : ∀ x, ∑ i, (gradf i x) ^ 2 ≤ (L : ℝ) ^ 2)
    (hf_memLp : ∀ s, MemLp (fun x => Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      2 (stdGaussianPi n))
    (hgradf_memLp : ∀ i s, MemLp (fun x => gradf i x * Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      2 (stdGaussianPi n))
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    entropyPi (stdGaussianPi n) (fun x => Real.exp (t * X x)) ≤
      t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂stdGaussianPi n := by
  intro X
  set μ := stdGaussianPi n with hμ
  -- Apply gaussian_log_sobolev to g = exp(t/2 · X(x)), gradg i x = t/2 · gradf i x · g x.
  -- Then g(x)² = exp(t·X(x)), and ∑∫(gradg i)² = (t/2)²·∑∫(gradf i)²·exp(tX)
  --   ≤ (t/2)²·L²·E[exp(tX)] by hgrad_bound.
  -- LSI gives: Ent(g²) ≤ 2·(t/2)²·L²·E[exp(tX)] = t²L²/2 · E[exp(tX)].
  let g : (Fin n → ℝ) → ℝ := fun x => Real.exp (t / 2 * X x)
  let gradg : Fin n → (Fin n → ℝ) → ℝ := fun i x => t / 2 * gradf i x * g x
  -- g(x)² = exp(t · X(x))
  have hg_sq : ∀ x, g x ^ 2 = Real.exp (t * X x) := fun x => by
    simp only [g]; rw [← Real.exp_nat_mul]; congr 1; ring
  -- MemLp g 2 μ: g x = exp(t/2 · X x) = exp((t/2) · (f x - c)) = hf_memLp(t/2)
  have hg_memLp : MemLp g 2 μ := hf_memLp (t / 2)
  -- MemLp (gradg i) 2 μ from hgradf_memLp i (t/2)
  have hgradg_memLp : ∀ i, MemLp (gradg i) 2 μ := fun i => by
    have h := (hgradf_memLp i (t / 2)).const_mul (t / 2)
    convert h using 1; ext x; simp [gradg, g]; ring
  -- HasDerivAt for s ↦ g(update x i s): chain rule exp ∘ (t/2 · (f ∘ update x i - c))
  have hgradg_deriv : ∀ x i, HasDerivAt (fun s => g (Function.update x i s)) (gradg i x) (x i) := by
    intro x i
    have hscale : HasDerivAt (fun s => t / 2 * (f (Function.update x i s) - ∫ z, f z ∂μ))
        (t / 2 * gradf i x) (x i) := by
      simpa using ((hderiv x i).sub_const _).const_mul (t / 2)
    convert hscale.exp using 1; simp [gradg, g, X]; ring
  -- Continuity of s ↦ gradg i (update x i s): product of continuous functions
  have hgradg_cont : ∀ x i, Continuous (fun s => gradg i (Function.update x i s)) := by
    intro x i; simp only [gradg, g, X]
    -- s ↦ f(update x i s) is continuous from HasDerivAt for all s (by varying the basepoint)
    have hf_diff : Differentiable ℝ (fun s => f (Function.update x i s)) := fun s => by
      have h := hderiv (Function.update x i s) i
      simp only [Function.update_self] at h
      have heq : (fun t => f (Function.update (Function.update x i s) i t)) =
                 (fun t => f (Function.update x i t)) := by ext t; simp [Function.update_idem]
      rw [heq] at h; exact h.differentiableAt
    exact (continuous_const.mul (hcont x i)).mul
      (Real.continuous_exp.comp (continuous_const.mul (hf_diff.continuous.sub continuous_const)))
  -- Apply gaussian_log_sobolev to g, gradg
  have hLSI := gaussian_log_sobolev n g gradg hg_memLp hgradg_memLp hgradg_deriv hgradg_cont
  rw [show (fun x => g x ^ 2) = (fun x => Real.exp (t * X x)) from funext hg_sq] at hLSI
  -- Integrability of (gradf i x)² · exp(t · X x): from (gradf i · exp(t/2 · X))² ∈ L¹
  have hint_gradf2_exp : ∀ i, Integrable (fun x => (gradf i x) ^ 2 * Real.exp (t * X x)) μ := fun i => by
    have h := (hgradf_memLp i (t / 2)).integrable_sq
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only; rw [mul_pow, ← Real.exp_nat_mul]; ring_nf; congr 1; simp [X]; ring
  -- Integrability of exp(t · X x): from g² ∈ L¹
  have hint_exp : Integrable (fun x => Real.exp (t * X x)) μ := by
    have h := hg_memLp.integrable_sq
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only; rw [← Real.exp_nat_mul]; ring_nf
  -- ∑∫(gradf i x)² · exp(tX) ≤ L² · E[exp(tX)] by hgrad_bound
  have hsum_bound : ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 * Real.exp (t * X x) ∂μ ≤
      (L : ℝ) ^ 2 * ∫ x, Real.exp (t * X x) ∂μ := by
    have hint_sum : Integrable (fun x => (∑ i, (gradf i x) ^ 2) * Real.exp (t * X x)) μ := by
      rw [show (fun x => (∑ i, (gradf i x) ^ 2) * Real.exp (t * X x)) =
           fun x => ∑ i, ((gradf i x) ^ 2 * Real.exp (t * X x)) from by ext x; rw [Finset.sum_mul]]
      exact integrable_finset_sum _ (fun i _ => hint_gradf2_exp i)
    calc ∑ i, ∫ x, (gradf i x) ^ 2 * Real.exp (t * X x) ∂μ
        = ∫ x, ∑ i, (gradf i x) ^ 2 * Real.exp (t * X x) ∂μ :=
          (integral_finset_sum _ (fun i _ => hint_gradf2_exp i)).symm
      _ = ∫ x, (∑ i, (gradf i x) ^ 2) * Real.exp (t * X x) ∂μ := by congr 1; ext x; rw [Finset.sum_mul]
      _ ≤ ∫ x, (L : ℝ) ^ 2 * Real.exp (t * X x) ∂μ :=
          integral_mono hint_sum (hint_exp.const_mul _)
            (fun x => mul_le_mul_of_nonneg_right (hgrad_bound x) (Real.exp_pos _).le)
      _ = (L : ℝ) ^ 2 * ∫ x, Real.exp (t * X x) ∂μ := integral_const_mul _ _
  -- ∑∫(gradg i x)² = (t/2)² · ∑∫(gradf i x)² · exp(tX)
  have hstep : ∑ i : Fin n, ∫ x, (gradg i x) ^ 2 ∂μ =
      (t / 2) ^ 2 * ∑ i, ∫ x, (gradf i x) ^ 2 * Real.exp (t * X x) ∂μ := by
    have hgradg_sq : ∀ i x, (gradg i x) ^ 2 = (t / 2) ^ 2 * (gradf i x) ^ 2 * Real.exp (t * X x) :=
      fun i x => by simp only [gradg]; rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; ring_nf
    simp_rw [hgradg_sq]; rw [Finset.mul_sum]; congr 1; ext i
    rw [show (fun x => (t / 2) ^ 2 * gradf i x ^ 2 * Real.exp (t * X x)) =
         fun x => (t / 2) ^ 2 * ((gradf i x) ^ 2 * Real.exp (t * X x)) from by ext x; ring]
    exact integral_const_mul _ _
  -- Combine: 2 · ∑∫(gradg i)² ≤ t²L²/2 · E[exp(tX)]
  have hfinal : 2 * ∑ i, ∫ x, (gradg i x) ^ 2 ∂μ ≤ t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂μ := by
    rw [hstep]
    calc 2 * ((t / 2) ^ 2 * ∑ i, ∫ x, (gradf i x) ^ 2 * Real.exp (t * X x) ∂μ)
        ≤ 2 * ((t / 2) ^ 2 * ((L : ℝ) ^ 2 * ∫ x, Real.exp (t * X x) ∂μ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_bound (sq_nonneg _)) (by norm_num)
      _ = t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂μ := by ring
  linarith

/-! ### Gaussian mollification infrastructure

For `ε > 0` and `f : (Fin n → ℝ) → ℝ`, define `f_ε(x) = E[f(x + ε·Z)]` where `Z ~ γⁿ`.
This smooths `f` while preserving the Lipschitz constant. -/

/-- Gaussian mollification: `f_ε(x) = ∫ f(x + ε·y) dγⁿ(y)`. -/
private noncomputable def gaussianMollify (n : ℕ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (x + ε • y) ∂stdGaussianPi n

/-- The affine map `y ↦ x + ε • y` is Lipschitz with constant `|ε|`. -/
private lemma lipschitzWith_affine {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) :
    LipschitzWith ⟨|ε|, abs_nonneg ε⟩ (fun y : Fin n → ℝ => x + ε • y) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro a b
  simp [dist_eq_norm]
  rw [← smul_sub, norm_smul]
  simp

/-- Lipschitz f composed with affine map is integrable under Gaussian. -/
private lemma lipschitz_comp_affine_integrable (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (L : ℝ≥0) (hf : LipschitzWith L f) (x : Fin n → ℝ) (ε : ℝ) :
    Integrable (fun y => f (x + ε • y)) (stdGaussianPi n) :=
  integrable_of_lipschitz_stdGaussianPi n _ _
    (hf.comp (lipschitzWith_affine x ε))

/-- Gaussian mollification of an L-Lipschitz function is L-Lipschitz.
Proof: |f_ε(x) - f_ε(x')| = |∫(f(x+εy) - f(x'+εy))dγ| ≤ ∫|f(x+εy)-f(x'+εy)|dγ
≤ ∫ L·‖(x+εy)-(x'+εy)‖ dγ = L·‖x-x'‖ since translation doesn't change distance. -/
private lemma gaussianMollify_lipschitz (n : ℕ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (L : ℝ≥0) (hf : LipschitzWith L f) :
    LipschitzWith L (gaussianMollify n ε f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  simp only [gaussianMollify]
  have hint1 := lipschitz_comp_affine_integrable n f L hf x ε
  have hint2 := lipschitz_comp_affine_integrable n f L hf x' ε
  have htrans : ∀ y : Fin n → ℝ,
      dist (x + ε • y) (x' + ε • y) = dist x x' := by
    intro y; simp [dist_eq_norm, add_sub_add_comm]
  rw [dist_eq_norm, ← integral_sub hint1 hint2]
  calc ‖∫ y, (f (x + ε • y) - f (x' + ε • y)) ∂stdGaussianPi n‖
      ≤ ∫ y, ‖f (x + ε • y) - f (x' + ε • y)‖ ∂stdGaussianPi n :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, (L : ℝ) * dist x x' ∂stdGaussianPi n := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
          (integrable_const _) (ae_of_all _ (fun y => ?_))
        calc ‖f (x + ε • y) - f (x' + ε • y)‖
            = dist (f (x + ε • y)) (f (x' + ε • y)) :=
              (dist_eq_norm _ _).symm
          _ ≤ L * dist (x + ε • y) (x' + ε • y) :=
              hf.dist_le_mul _ _
          _ = L * dist x x' := by rw [htrans]
    _ = (L : ℝ) * dist x x' := by
        simp [integral_const]

/-- Gaussian mollification converges pointwise to `f` as `ε → 0` for Lipschitz `f`.
More precisely, `|f_ε(x) - f(x)| ≤ L · |ε| · E[‖Z‖]`. -/
private lemma gaussianMollify_tendsto (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (L : ℝ≥0) (hf : LipschitzWith L f) (x : Fin n → ℝ) :
    Tendsto (fun ε => gaussianMollify n ε f x) (𝓝 0) (𝓝 (f x)) := by
  haveI : IsProbabilityMeasure (stdGaussianPi n) := by unfold stdGaussianPi; infer_instance
  haveI : IsFiniteMeasure (stdGaussianPi n) := by
    change IsFiniteMeasure (Measure.pi (fun _ : Fin n => stdGaussian)); infer_instance
  simp only [gaussianMollify]
  conv_rhs => rw [show f x = ∫ _y : Fin n → ℝ, f x ∂stdGaussianPi n by simp [integral_const]]
  rw [← tendsto_sub_nhds_zero_iff]
  -- Bound: ‖∫f(x+εy) dγ - f(x)‖ ≤ L * |ε| * ∫‖y‖ dγ → 0
  apply squeeze_zero_norm (a := fun ε => (L : ℝ) * (|ε| * ∫ y, ‖y‖ ∂stdGaussianPi n))
  · intro ε
    show ‖∫ y, f (x + ε • y) ∂stdGaussianPi n - ∫ _y : Fin n → ℝ, f x ∂stdGaussianPi n‖ ≤
        (L : ℝ) * (|ε| * ∫ y, ‖y‖ ∂stdGaussianPi n)
    rw [(integral_sub (lipschitz_comp_affine_integrable n f L hf x ε)
      (integrable_const (f x))).symm]
    calc ‖∫ y, (f (x + ε • y) - f x) ∂stdGaussianPi n‖
        ≤ ∫ y, ‖f (x + ε • y) - f x‖ ∂stdGaussianPi n := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (L : ℝ) * (|ε| * ‖y‖) ∂stdGaussianPi n := by
            apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
            · exact (integrable_id_stdGaussianPi n).norm.const_mul _ |>.const_mul _
            · apply ae_of_all; intro y
              calc ‖f (x + ε • y) - f x‖ = dist (f (x + ε • y)) (f x) := (dist_eq_norm _ _).symm
                _ ≤ (L : ℝ) * dist (x + ε • y) x := hf.dist_le_mul _ _
                _ = (L : ℝ) * (|ε| * ‖y‖) := by
                    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ = (L : ℝ) * (|ε| * ∫ y, ‖y‖ ∂stdGaussianPi n) := by
            rw [integral_const_mul, integral_const_mul]
  · have hcont : Continuous (fun ε : ℝ => (L : ℝ) * (|ε| * ∫ y, ‖y‖ ∂stdGaussianPi n)) :=
      continuous_const.mul (continuous_abs.mul continuous_const)
    have h0 : (fun ε : ℝ => (L : ℝ) * (|ε| * ∫ y, ‖y‖ ∂stdGaussianPi n)) 0 = 0 := by simp
    have := hcont.tendsto 0; simp only [h0] at this; exact this

/-- Gaussian mollification of Lipschitz f is C¹ with bounded gradient.

For `f_ε = gaussianMollify n ε f` with `f` L-Lipschitz, there exists a gradient function
`gradf_ε` such that:
1. `HasDerivAt` along each coordinate (f_ε is differentiable)
2. `∑ᵢ (gradf_ε i x)² ≤ L²` (gradient norm bounded by Lipschitz constant)
3. Each partial derivative is continuous along its coordinate

The derivative exists because f_ε is a convolution with a smooth Gaussian kernel.
The gradient bound follows from f_ε being L-Lipschitz (smooth + Lipschitz → ‖∇f‖ ≤ L).
Continuity of partial derivatives follows from f_ε being C^∞. -/
-- The coordinate slice `s ↦ update x i s` is 1-Lipschitz.
private lemma lipschitzWith_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith 1 (fun s : ℝ => Function.update x i s) := by
  intro s t
  simp only [edist_pi_def, Function.update_apply, ENNReal.coe_one, one_mul]
  apply Finset.sup_le
  intro j _
  split_ifs with h
  · exact le_refl _
  · simp [edist_self]

-- Coordinate slice of L-Lipschitz function is L-Lipschitz.
private lemma lipschitz_coord_slice {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith L (fun s => f (Function.update x i s)) := by
  have h1 := lipschitzWith_update x i
  have h2 : LipschitzWith (L * 1) (f ∘ (fun s => Function.update x i s)) := hf.comp h1
  simpa [Function.comp] using h2

-- Coordinate slice of mollification is L-Lipschitz.
private lemma gaussianMollify_coord_lipschitz (n : ℕ) (ε : ℝ)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith L (fun s => gaussianMollify n ε f (Function.update x i s)) :=
  lipschitz_coord_slice _ L (gaussianMollify_lipschitz n ε f L hf) x i

-- Infrastructure for differentiability of Gaussian mollification.

-- The affine map y ↦ x + ε•y is QuasiMeasurePreserving from stdGaussianPi to volume.
private lemma qmp_affine_stdGaussianPi {n : ℕ}
    (x : Fin n → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    QuasiMeasurePreserving (fun y : Fin n → ℝ => x + ε • y)
      (stdGaussianPi n) volume := by
  refine ⟨measurable_const.add (measurable_const.smul measurable_id), ?_⟩
  intro S hS
  have hmeas : Measurable (fun y : Fin n → ℝ => x + ε • y) :=
    measurable_const.add (measurable_const.smul measurable_id)
  have h_smul : Measurable (fun y : Fin n → ℝ => ε • y) :=
    measurable_const.smul measurable_id
  have h_add : Measurable (fun y : Fin n → ℝ => x + y) :=
    measurable_const.add measurable_id
  -- Factor as translation ∘ scaling, both preserve abs. continuity to volume.
  have h_vol_ac : (volume : Measure (Fin n → ℝ)).map
      (fun y => x + ε • y) ≪ volume := by
    rw [show (fun y : Fin n → ℝ => x + ε • y) =
      (fun y => x + y) ∘ (fun y => ε • y) from by ext; simp,
      ← Measure.map_map h_add h_smul]
    have h_smul_ac : volume.map (fun y : Fin n → ℝ => ε • y) ≪ volume := by
      rw [show (fun y : Fin n → ℝ => ε • y) =
        (ε • LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) from by ext; simp,
        Real.map_linearMap_volume_pi_eq_smul_volume_pi (by
          simp only [LinearMap.det_smul, ne_eq, mul_eq_zero, not_or]
          exact ⟨pow_ne_zero _ hε, by simp [LinearMap.det_id]⟩)]
      exact smul_absolutelyContinuous
    have h_mp := (measurePreserving_add_left volume x).map_eq
    have h := h_smul_ac.map h_add; rw [h_mp] at h; exact h
  exact ((stdGaussianPi_absolutelyContinuous n).map hmeas |>.trans h_vol_ac) hS

-- For a.e. y ∂γⁿ, the coord slice s ↦ f(update x i s + εy) is differentiable at x i.
-- Uses Rademacher's theorem + absolute continuity transfer.
private lemma ae_differentiableAt_coord_slice {n : ℕ} {C : ℝ≥0}
    {f : (Fin n → ℝ) → ℝ} (hf : LipschitzWith C f)
    (x : Fin n → ℝ) (ε : ℝ) (hε : ε ≠ 0) (i : Fin n) :
    ∀ᵐ y ∂stdGaussianPi n,
      DifferentiableAt ℝ (fun s => f (Function.update x i s + ε • y)) (x i) := by
  -- By Rademacher: ∀ᵐ z ∂volume, LineDifferentiableAt ℝ f z (Pi.single i 1)
  have hrad := hf.ae_lineDifferentiableAt (v := Pi.single i (1 : ℝ))
    (μ := (volume : Measure (Fin n → ℝ)))
  -- Transfer via QMP: ae for y ∂stdGaussianPi
  have hae := (qmp_affine_stdGaussianPi x ε hε).ae hrad
  -- Convert LineDifferentiableAt to DifferentiableAt of coord slice
  filter_upwards [hae] with y hy
  -- hy : LineDifferentiableAt ℝ f (x+ε•y) (Pi.single i 1)
  --    = DifferentiableAt ℝ (fun t => f((x+ε•y) + t • Pi.single i 1)) 0
  -- Goal: DifferentiableAt ℝ (fun s => f(update x i s + ε•y)) (x i)
  -- Key identity: update x i s + ε•y = (x+ε•y) + (s - x i) • Pi.single i 1
  have h_eq : (fun s => f (Function.update x i s + ε • y)) =
    (fun t => f ((x + ε • y) + t • Pi.single i (1 : ℝ))) ∘ (fun s => s - x i) := by
    ext s; congr 1; ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.comp_apply]
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  rw [h_eq]
  -- Compose: g DiffAt at 0, (· - x_i) DiffAt at x_i, maps x_i to 0
  unfold LineDifferentiableAt at hy
  refine DifferentiableAt.comp (x i) ?_ (differentiableAt_id.sub (differentiableAt_const _))
  convert hy using 1; simp
-- Used to prove AEStronglyMeasurable of parametric derivative.
private lemma hasDerivAt_tendsto_seq {g : ℝ → ℝ} {g' x₀ : ℝ} (hg : HasDerivAt g g' x₀) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) * (g (x₀ + 1 / ((k : ℝ) + 1)) - g x₀))
      atTop (𝓝 g') := by
  have h_ne : ∀ k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ≠ 0 := fun k => by positivity
  have h_tendsto : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop).atTop_add tendsto_const_nhds
    rw [show (0 : ℝ) = 1 * 0 from by ring]
    exact tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp h1)
  have key : Tendsto (fun t : ℝ => t⁻¹ * (g (x₀ + t) - g x₀)) (𝓝[≠] (0 : ℝ)) (𝓝 g') :=
    hg.tendsto_slope_zero.congr (fun t => by simp [smul_eq_mul])
  have hcomp := key.comp (tendsto_nhdsWithin_iff.mpr ⟨h_tendsto, .of_forall fun k =>
      Set.mem_compl_singleton_iff.mpr (h_ne k)⟩)
  exact hcomp.congr fun k => by simp only [Function.comp]; rw [one_div, inv_inv]

-- AEStronglyMeasurable for the parametric derivative of the integrand.
-- The function y ↦ deriv_s(f(update x i s + ε•y))(x i) is AEStronglyMeasurable
-- because it is the a.e. limit of continuous difference quotients.
private lemma aestronglyMeasurable_deriv_coord {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {x : Fin n → ℝ} {ε : ℝ} {i : Fin n}
    (hae : ∀ᵐ y ∂stdGaussianPi n,
      DifferentiableAt ℝ (fun s => f (Function.update x i s + ε • y)) (x i)) :
    AEStronglyMeasurable
      (fun y => deriv (fun s => f (Function.update x i s + ε • y)) (x i))
      (stdGaussianPi n) := by
  set u : ℕ → (Fin n → ℝ) → ℝ := fun k y =>
    ((k : ℝ) + 1) * (f (Function.update x i (x i + 1 / ((k : ℝ) + 1)) + ε • y) -
      f (Function.update x i (x i) + ε • y))
  apply aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := u)
  · intro k
    exact (continuous_const.mul
      ((hf.continuous.comp (continuous_const.add (continuous_const.smul continuous_id'))).sub
       (hf.continuous.comp (continuous_const.add (continuous_const.smul continuous_id'))))).aestronglyMeasurable
  · filter_upwards [hae] with y hy
    exact hasDerivAt_tendsto_seq hy.hasDerivAt

private lemma gaussianMollify_C1_with_gradient_bound (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) :
    ∃ gradf_ε : Fin n → (Fin n → ℝ) → ℝ,
      (∀ x i, HasDerivAt (fun s => gaussianMollify n ε f (Function.update x i s))
        (gradf_ε i x) (x i)) ∧
      (∀ x, ∑ i, (gradf_ε i x) ^ 2 ≤ (L : ℝ) ^ 2) ∧
      (∀ x i, Continuous (fun s => gradf_ε i (Function.update x i s))) ∧
      (∀ i, Measurable (gradf_ε i)) := by
  -- Define gradient as the deriv of coordinate slices
  let gradf_ε : Fin n → (Fin n → ℝ) → ℝ :=
    fun i x => deriv (fun s => gaussianMollify n ε f (Function.update x i s)) (x i)
  -- First prove HasDerivAt (goal 1) so it's available in all subsequent goals.
  have hHasDeriv : ∀ x i, HasDerivAt (fun s => gaussianMollify n ε f (Function.update x i s))
      (gradf_ε i x) (x i) := by
    -- Leibniz rule + Rademacher + AC.
    intro x i
    apply DifferentiableAt.hasDerivAt
    have hae := ae_differentiableAt_coord_slice hf x ε hε.ne' i
    have h_lip : ∀ᵐ y ∂stdGaussianPi n,
        LipschitzOnWith (Real.nnabs (L : ℝ))
          (fun s => f (Function.update x i s + ε • y)) Set.univ := .of_forall fun y => by
      have hnnabs : Real.nnabs (L : ℝ) = L := by
        ext; simp [Real.nnabs, abs_of_nonneg L.coe_nonneg]
      rw [hnnabs]; apply LipschitzWith.lipschitzOnWith
      show LipschitzWith L (fun s => f (Function.update x i s + ε • y))
      have h3 := hf.comp ((isometry_add_right (ε • y)).lipschitz.comp (lipschitzWith_update x i))
      simp only [mul_one] at h3; convert h3 using 1
    have h_diff : ∀ᵐ y ∂stdGaussianPi n,
        HasDerivAt (fun s => f (Function.update x i s + ε • y))
          (deriv (fun s => f (Function.update x i s + ε • y)) (x i)) (x i) :=
      hae.mono fun y hy => hy.hasDerivAt
    obtain ⟨_, hkey⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
      (F := fun s y => f (Function.update x i s + ε • y))
      (F' := fun y => deriv (fun s => f (Function.update x i s + ε • y)) (x i))
      Filter.univ_mem
      (.of_forall fun s => (hf.continuous.comp (continuous_const.add
        (continuous_const.smul continuous_id))).aestronglyMeasurable)
      (lipschitz_comp_affine_integrable n f L hf (Function.update x i (x i)) ε)
      (aestronglyMeasurable_deriv_coord hf hae)
      h_lip (integrable_const _) h_diff
    exact hkey.differentiableAt
  -- DifferentiableAt for f_ε: follows from Gaussian convolution smoothness.
  -- The Leibniz integral theorem (hasDerivAt_integral_of_dominated_loc_of_lip) applied
  -- to ALL directions (not just coordinate) gives HasLineDerivAt for every v.
  -- Combined with hasFDerivAt_of_hasLineDerivAt_of_closure (Rademacher.lean) → HasFDerivAt.
  have hf_ε_lip := gaussianMollify_lipschitz n ε f L hf
  have hDiff : ∀ x, DifferentiableAt ℝ (gaussianMollify n ε f) x := by
    intro x
    -- Construct candidate fderiv: L v = ∑ᵢ (∂ᵢf_ε(x)) · vᵢ
    set A : (Fin n → ℝ) →L[ℝ] ℝ :=
      ∑ j : Fin n, (gradf_ε j x) • ContinuousLinearMap.proj j
    -- Use hasFDerivAt_of_hasLineDerivAt_of_closure:
    -- Need HasLineDerivAt ℝ f_ε (A v) x v for all v.
    suffices HasFDerivAt (gaussianMollify n ε f) A x from this.differentiableAt
    apply hf_ε_lip.hasFDerivAt_of_hasLineDerivAt_of_closure (s := Set.univ)
      (by simp [closure_univ] : Metric.sphere (0 : Fin n → ℝ) 1 ⊆ closure Set.univ)
    intro v _
    -- HasLineDerivAt ℝ f_ε (A v) x v = HasDerivAt (t ↦ f_ε(x+t•v)) (A v) 0
    -- A v = ∑ j, gradf_ε j x * v j
    -- Need: the directional derivative of f_ε at x in direction v equals A v.
    -- Use the Leibniz rule for direction v (same as coord proof but general direction).
    sorry -- HasLineDerivAt via Leibniz rule for general direction v
  refine ⟨gradf_ε, hHasDeriv, ?_, ?_, ?_⟩
  · -- (2) Gradient bound: ∑(∂ᵢf_ε)² ≤ L².
    -- Route: chain rule gives ∂ᵢf_ε(x) = (fderiv ℝ f_ε x)(eᵢ).
    -- Sign vector trick: ∑|aᵢ| ≤ ‖fderiv‖_{op,∞→ℝ} ≤ L.
    -- Algebra: ∑aᵢ² ≤ (∑|aᵢ|)² ≤ L².
    intro x
    set A := fderiv ℝ (gaussianMollify n ε f) x
    set a : Fin n → ℝ := fun i => A (Pi.single i 1)
    -- Each partial derivative equals fderiv applied to basis vector
    have hpartial : ∀ i, gradf_ε i x = a i := by
      intro i
      have h1 : HasFDerivAt (gaussianMollify n ε f) A (Function.update x i (x i)) := by
        rw [Function.update_eq_self]; exact (hDiff x).hasFDerivAt
      have h2 : HasDerivAt (Function.update x i : ℝ → Fin n → ℝ)
          ((Pi.single i (1 : ℝ) : Fin n → ℝ)) (x i) := by
        have h := (hasFDerivAt_update x (x i) (i := i)).hasDerivAt
        convert h using 1
        ext j; simp [ContinuousLinearMap.pi_apply, Pi.single_apply]; split_ifs <;> simp
      -- Chain rule: HasDerivAt (f_ε ∘ update x i) (A (Pi.single i 1)) (x i)
      have h3 := h1.comp_hasDerivAt (x i) h2
      simp only [Function.comp_def] at h3
      -- By uniqueness: gradf_ε i x = deriv (f_ε ∘ update x i) (x i) = A (eᵢ)
      exact (hHasDeriv x i).unique h3
    simp_rw [hpartial]
    -- ∑ aᵢ² ≤ (∑|aᵢ|)² (algebraic: cross terms are nonneg)
    have h_sq_le : ∑ i, a i ^ 2 ≤ (∑ i, |a i|) ^ 2 := by
      calc ∑ i, a i ^ 2 = ∑ i, |a i| ^ 2 := by congr 1; ext i; rw [sq_abs]
        _ ≤ (∑ i, |a i|) ^ 2 := by
            calc ∑ i, |a i| ^ 2 = ∑ i, |a i| * |a i| := by congr 1; ext; ring
              _ ≤ ∑ i, |a i| * (∑ j, |a j|) := Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_left
                    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i))
                    (abs_nonneg _)
              _ = (∑ i, |a i|) * (∑ j, |a j|) := (Finset.sum_mul ..).symm
              _ = (∑ i, |a i|) ^ 2 := (sq ..).symm
    -- ∑|aᵢ| ≤ ‖fderiv‖ (sign vector trick: v_j = sgn(a_j), ‖v‖_∞ ≤ 1)
    have h_l1_le : ∑ i, |a i| ≤ ‖A‖ := by
      set v : Fin n → ℝ := fun j => if 0 ≤ a j then 1 else -1
      have hv_norm : ‖v‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]; intro i; simp only [v]; split_ifs <;> norm_num
      have hAv : A v = ∑ j, |a j| := by
        have hdecomp : v = ∑ j : Fin n, (v j) • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
          ext k; simp [Pi.single_apply, smul_eq_mul]
        rw [hdecomp, _root_.map_sum]; congr 1; ext j
        simp only [ContinuousLinearMap.map_smul, smul_eq_mul, a, v]
        split_ifs with h
        · simp [abs_of_nonneg h]
        · push_neg at h; simp [abs_of_neg h]
      calc ∑ j, |a j| = A v := hAv.symm
        _ ≤ |A v| := le_abs_self _
        _ = ‖A v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
        _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hv_norm (norm_nonneg _)
        _ = ‖A‖ := mul_one _
    -- ‖fderiv f_ε x‖ ≤ L (from Lipschitz bound)
    have h_norm : ‖A‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hf_ε_lip
    -- Combine: ∑aᵢ² ≤ (∑|aᵢ|)² ≤ ‖A‖² ≤ L²
    calc ∑ i, a i ^ 2 ≤ (∑ i, |a i|) ^ 2 := h_sq_le
      _ ≤ (L : ℝ) ^ 2 := sq_le_sq'
          (by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (a i)])
          (by linarith)
  · -- (3) Continuity of gradient: s ↦ deriv (t ↦ f_ε(update x i t)) s is continuous.
    -- Route: deriv g s = ∫ deriv_t f(update x i t + εy)|_{t=s} dγ(y) (Leibniz, same as (1)).
    -- Continuity follows from DCT: integrand is bounded by L (Lipschitz) and a.e. continuous
    -- in s (by Rademacher on f + Lebesgue differentiation for 1D Lipschitz functions).
    -- Alternative: g = f_ε ∘ update x i is L-Lipschitz and DifferentiableAt everywhere
    -- (from hDiff), so g' is the pointwise limit of difference quotients.
    -- The difference quotients are equicontinuous (bounded by L), so Arzelà-Ascoli applies.
    sorry
  · -- (4) Measurability: gradf_ε i = pointwise limit of measurable diff quotients.
    intro i
    set f_ε := gaussianMollify n ε f
    have hf_ε_cont : Continuous f_ε := (gaussianMollify_lipschitz n ε f L hf).continuous
    -- Difference quotient approximation
    set u : ℕ → (Fin n → ℝ) → ℝ := fun k x =>
      ((k : ℝ) + 1) * (f_ε (Function.update x i (x i + 1 / ((k : ℝ) + 1))) - f_ε x)
    -- Each u k is measurable (continuous, in fact)
    have hu_meas : ∀ k, Measurable (u k) := fun k => by
      apply Continuous.measurable
      exact continuous_const.mul
        ((hf_ε_cont.comp (continuous_id.update i
          ((continuous_apply i).add continuous_const))).sub hf_ε_cont)
    -- Pointwise convergence: u k x → gradf_ε i x (by HasDerivAt)
    have hu_tendsto : Tendsto u atTop (𝓝 (gradf_ε i)) := by
      rw [tendsto_pi_nhds]; intro x
      convert hasDerivAt_tendsto_seq (hHasDeriv x i) using 3 <;> simp [one_div, Function.update_self]
    exact measurable_of_tendsto_metrizable hu_meas hu_tendsto

/-- MemLp property for exp(s · (f_ε - E[f_ε])) under Gaussian measure.
Follows from f_ε being L-Lipschitz (hence sub-Gaussian growth). -/
private lemma gaussianMollify_memLp_exp (n : ℕ) (ε : ℝ)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (s : ℝ) :
    MemLp (fun x => Real.exp (s * (gaussianMollify n ε f x -
      ∫ y, gaussianMollify n ε f y ∂stdGaussianPi n))) 2 (stdGaussianPi n) := by
  -- f_ε is L-Lipschitz, so exp(s*(f_ε(x) - E[f_ε])) ∈ L² (Gaussian sub-Gaussian tails)
  set g := gaussianMollify n ε f
  have hLip := gaussianMollify_lipschitz n ε f L hf
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (s * (g x - ∫ y, g y ∂stdGaussianPi n)))
      (stdGaussianPi n) :=
    Continuous.aestronglyMeasurable
      (Real.continuous_exp.comp (continuous_const.mul (hLip.continuous.sub continuous_const)))
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  -- ‖exp(s*(g(x)-c))‖² = exp(2s*(g(x)-c)), which is integrable by Gaussian tails
  simp_rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
  ring_nf
  convert integrable_exp_centered_of_lipschitz_stdGaussianPi n g L hLip (2 * s) using 2
  ring

/-- MemLp property for gradf_ε · exp(s · (f_ε - E[f_ε])) under Gaussian measure. -/
private lemma gaussianMollify_memLp_grad_exp (n : ℕ) (ε : ℝ)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (gradf_ε : Fin n → (Fin n → ℝ) → ℝ)
    (hgrad_bound : ∀ x, ∑ i, (gradf_ε i x) ^ 2 ≤ (L : ℝ) ^ 2)
    (hgrad_meas : ∀ i, Measurable (gradf_ε i))
    (i : Fin n) (s : ℝ) :
    MemLp (fun x => gradf_ε i x * Real.exp (s * (gaussianMollify n ε f x -
      ∫ y, gaussianMollify n ε f y ∂stdGaussianPi n))) 2 (stdGaussianPi n) := by
  -- |gradf_ε i x| ≤ L (bounded) → gradf_ε i ∈ L^∞
  -- exp factor ∈ L² (Lipschitz sub-Gaussian growth)
  -- Product: L^∞ × L² → L² via MemLp.mul
  set g := gaussianMollify n ε f
  have hLip := gaussianMollify_lipschitz n ε f L hf
  have hexp_memLp : MemLp (fun x => Real.exp (s * (g x - ∫ y, g y ∂stdGaussianPi n))) 2
      (stdGaussianPi n) := by
    have hmeas : AEStronglyMeasurable (fun x => Real.exp (s * (g x - ∫ y, g y ∂stdGaussianPi n)))
        (stdGaussianPi n) :=
      Continuous.aestronglyMeasurable
        (Real.continuous_exp.comp (continuous_const.mul (hLip.continuous.sub continuous_const)))
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    simp_rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]; ring_nf
    convert integrable_exp_centered_of_lipschitz_stdGaussianPi n g L hLip (2 * s) using 2; ring
  -- gradf_ε i is pointwise bounded by L, hence in L^∞
  have hgradf_top : MemLp (gradf_ε i) ⊤ (stdGaussianPi n) :=
    memLp_top_of_bound (hgrad_meas i).aestronglyMeasurable (L : ℝ)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs]
        apply abs_le_of_sq_le_sq _ (NNReal.coe_nonneg L)
        exact (Finset.single_le_sum (f := fun j => (gradf_ε j x) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)).trans (hgrad_bound x)))
  -- L^∞ × L² → L² by Hölder
  exact hexp_memLp.mul hgradf_top

/-- For |x| ≤ D, we have ‖x * log x‖ ≤ D * |log D| + 1.
Uses Lean's `log |x| = log x` convention and the bound `-x log x ≤ 1` for x ∈ (0,1]. -/
private lemma norm_mul_log_le_of_abs_le {x D : ℝ} (hx : |x| ≤ D) :
    ‖x * Real.log x‖ ≤ D * |Real.log D| + 1 := by
  rw [Real.norm_eq_abs, abs_mul, ← Real.log_abs]
  set y := |x|
  have hy_nn : 0 ≤ y := abs_nonneg x
  have hyD : y ≤ D := hx
  have hD_nn : 0 ≤ D := le_trans hy_nn hyD
  by_cases hy0 : y = 0
  · simp [hy0]; positivity
  · have hy_pos : 0 < y := lt_of_le_of_ne hy_nn (Ne.symm hy0)
    by_cases hy1 : y ≤ 1
    · have hlog : Real.log y ≤ 0 := Real.log_nonpos hy_nn hy1
      rw [abs_of_nonpos hlog]
      have h1 : Real.log (1 / y) ≤ 1 / y - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt hy_pos), Real.log_one,
          _root_.zero_sub] at h1
      have h2 : y * (-Real.log y) ≤ y * (1 / y - 1) :=
        mul_le_mul_of_nonneg_left h1 hy_pos.le
      rw [mul_sub, mul_one_div_cancel (ne_of_gt hy_pos), mul_one] at h2
      linarith [mul_nonneg hD_nn (abs_nonneg (Real.log D))]
    · push_neg at hy1
      have hD1 : 1 ≤ D := by linarith
      rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hy1)),
          abs_of_nonneg (Real.log_nonneg hD1)]
      nlinarith [Real.log_le_log hy_pos hyD, Real.log_nonneg (le_of_lt hy1)]

/-- Entropy is continuous under dominated convergence of integrands.
If g_k → g pointwise with integrable dominator D (with D·|log D| also integrable),
then Ent(g_k) → Ent(g). Uses DCT twice: once for ∫g_k and once for ∫g_k·log(g_k),
plus continuity of x·log(x) for the normalizing term. -/
private lemma entropyPi_tendsto_of_uniform {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin n → ℝ) → ℝ) (g_seq : ℕ → (Fin n → ℝ) → ℝ)
    (hg_meas : ∀ k, AEStronglyMeasurable (g_seq k) μ)
    (hconv : ∀ x, Tendsto (fun k => g_seq k x) atTop (𝓝 (g x)))
    (hdom : ∃ D : (Fin n → ℝ) → ℝ, Integrable D μ ∧
      Integrable (fun x => D x * |Real.log (D x)|) μ ∧
      ∀ k x, |g_seq k x| ≤ D x ∧ |g x| ≤ D x) :
    Tendsto (fun k => entropyPi μ (g_seq k)) atTop (𝓝 (entropyPi μ g)) := by
  simp only [entropyPi]
  obtain ⟨D, hD_int, hDlog_int, hdom_bound⟩ := hdom
  -- Part 1: ∫ g_k → ∫ g by DCT
  have h_int_tendsto : Tendsto (fun k => ∫ x, g_seq k x ∂μ) atTop
      (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence D
    · exact hg_meas
    · exact hD_int
    · intro k; exact Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs]; exact (hdom_bound k a).1
    · exact Eventually.of_forall hconv
  -- Part 2: (∫ g_k) · log(∫ g_k) → (∫ g) · log(∫ g) by continuity of x * log x
  have h_mul_log_tendsto :
      Tendsto (fun k => (∫ x, g_seq k x ∂μ) * Real.log (∫ x, g_seq k x ∂μ))
        atTop (𝓝 ((∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ))) :=
    (Real.continuous_mul_log.tendsto _).comp h_int_tendsto
  -- Part 3: ∫ g_k · log g_k → ∫ g · log g by DCT with dominator D·|log D| + 1
  have h_ent_tendsto :
      Tendsto (fun k => ∫ x, g_seq k x * Real.log (g_seq k x) ∂μ)
        atTop (𝓝 (∫ x, g x * Real.log (g x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => D x * |Real.log (D x)| + 1)
    · intro k
      exact Real.continuous_mul_log.comp_aestronglyMeasurable (hg_meas k)
    · exact hDlog_int.add (integrable_const 1)
    · intro k; exact Eventually.of_forall fun a =>
        norm_mul_log_le_of_abs_le (hdom_bound k a).1
    · exact Eventually.of_forall fun a =>
        (Real.continuous_mul_log.tendsto _).comp (hconv a)
  -- Combine: (∫g_k·log g_k - (∫g_k)·log(∫g_k)) → (∫g·log g - (∫g)·log(∫g))
  exact h_ent_tendsto.sub h_mul_log_tendsto

-- Helper: y * exp(a*y) ≤ exp((a+1)*y) for a ≥ 0 (since y ≤ exp(y))
private lemma mul_exp_le_exp_succ (a y : ℝ) (ha : 0 ≤ a) :
    y * Real.exp (a * y) ≤ Real.exp ((a + 1) * y) := by
  calc y * Real.exp (a * y)
      ≤ Real.exp y * Real.exp (a * y) := by
        gcongr; linarith [Real.add_one_le_exp y]
    _ = Real.exp ((a + 1) * y) := by rw [← Real.exp_add]; ring_nf

-- Helper: exp(a*(‖x‖+c)) is integrable under stdGaussianPi when a ≥ 0
private lemma integrable_exp_norm_add_const (n : ℕ) (a c : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : Fin n → ℝ => Real.exp (a * (‖x‖ + c)))
      (stdGaussianPi n) := by
  have : (fun x : Fin n → ℝ => Real.exp (a * (‖x‖ + c))) =
      fun x => Real.exp (a * c) * Real.exp (a * ‖x‖) := by
    ext x; rw [← Real.exp_add]; congr 1; ring
  rw [this]
  exact (integrable_exp_norm_stdGaussianPi_nonneg n a ha).const_mul _

-- Helper: (‖x‖+c) * exp(a*(‖x‖+c)) is integrable (for D*|log D| bounds)
private lemma integrable_mul_exp_norm_add_const (n : ℕ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Integrable (fun x : Fin n → ℝ => (‖x‖ + c) * Real.exp (a * (‖x‖ + c)))
      (stdGaussianPi n) := by
  refine Integrable.mono' (integrable_exp_norm_add_const n (a + 1) c (by linarith)) ?_ ?_
  · exact (continuous_norm.add continuous_const).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.add continuous_const)))
      |>.aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      show ‖(‖x‖ + c) * Real.exp (a * (‖x‖ + c))‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_exp_le_exp_succ a (‖x‖ + c) ha)

/-- **Entropy bound for Lipschitz functions under Gaussian measure.**

For L-Lipschitz `f` under standard Gaussian, `Ent(exp(tX)) ≤ t²L²/2 · E[exp(tX)]`
where `X = f - E[f]`.

**Proof**: Gaussian mollification approximation.
1. Define `f_ε(x) = E[f(x + εZ)]` — smooth and L-Lipschitz
2. Apply `entropyPi_exp_le_of_C1` to each `f_ε`
3. Pass to limit `ε → 0` via DCT -/
private lemma entropyPi_exp_le_of_lipschitz
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    entropyPi (stdGaussianPi n) (fun x => Real.exp (t * X x)) ≤
      t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂stdGaussianPi n := by
  intro X
  set μ := stdGaussianPi n
  -- Strategy: approximate f by f_ε = gaussianMollify n ε f, apply C¹ bound, take limit.
  -- For each ε > 0, choose gradf_ε witnessing HasDerivAt + gradient bound.
  -- Apply entropyPi_exp_le_of_C1 to f_ε.
  -- Then pass ε → 0: f_ε → f pointwise, hence exp(t·X_ε) → exp(t·X),
  -- and the entropy bound passes to the limit.

  -- Step 1: For any ε > 0, the C¹ bound holds for f_ε
  have hC1_bound : ∀ ε : ℝ, 0 < ε →
      let f_ε := gaussianMollify n ε f
      let X_ε := fun x => f_ε x - ∫ y, f_ε y ∂μ
      entropyPi μ (fun x => Real.exp (t * X_ε x)) ≤
        t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X_ε x) ∂μ := by
    intro ε hε
    set f_ε := gaussianMollify n ε f
    set X_ε := fun x => f_ε x - ∫ y, f_ε y ∂μ
    -- Extract C¹ structure with gradient bound from combined lemma
    obtain ⟨gradf_ε, hderiv, hgrad_bound, hcont, hgrad_meas⟩ :=
      gaussianMollify_C1_with_gradient_bound n ε hε f L hf
    have hf_memLp := fun s => gaussianMollify_memLp_exp n ε f L hf s
    have hgradf_memLp := fun i s =>
      gaussianMollify_memLp_grad_exp n ε f L hf gradf_ε hgrad_bound hgrad_meas i s
    exact entropyPi_exp_le_of_C1 n f_ε L gradf_ε
      hderiv hcont hgrad_bound hf_memLp hgradf_memLp t

  -- Step 2: Define the approximation sequence ε_k = 1/(k+1) → 0
  haveI : IsProbabilityMeasure μ := by show IsProbabilityMeasure (stdGaussianPi n); unfold stdGaussianPi; infer_instance
  set c_norm := ∫ y, ‖y‖ ∂μ  -- E[‖Y‖] under Gaussian
  have hc_norm_nn : 0 ≤ c_norm := integral_nonneg (fun _ => norm_nonneg _)
  set ε_seq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε_pos : ∀ k, 0 < ε_seq k := fun k => by positivity
  have hε_tendsto : Tendsto ε_seq atTop (𝓝 0) := by
    simp_rw [ε_seq, one_div]
    exact ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds).inv_tendsto_atTop
  -- Define f_ε_k, X_ε_k, g_seq_k, g
  set f_seq : ℕ → (Fin n → ℝ) → ℝ := fun k => gaussianMollify n (ε_seq k) f
  set X_seq : ℕ → (Fin n → ℝ) → ℝ := fun k x => f_seq k x - ∫ y, f_seq k y ∂μ
  set g_seq : ℕ → (Fin n → ℝ) → ℝ := fun k x => Real.exp (t * X_seq k x)
  set g : (Fin n → ℝ) → ℝ := fun x => Real.exp (t * X x)
  -- Key: each f_{ε_k} is L-Lipschitz
  have hf_seq_lip : ∀ k, LipschitzWith L (f_seq k) :=
    fun k => gaussianMollify_lipschitz n (ε_seq k) f L hf
  -- Step 2a: Pointwise convergence f_{ε_k}(x) → f(x)
  have hf_ptwise : ∀ x, Tendsto (fun k => f_seq k x) atTop (𝓝 (f x)) := by
    intro x
    exact (gaussianMollify_tendsto n f L hf x).comp hε_tendsto
  -- Step 2b: ∫ f_{ε_k} → ∫ f by DCT (dominator: |f(0)| + L*‖x‖ + L*c_norm)
  have hf_seq_int : ∀ k, Integrable (f_seq k) μ :=
    fun k => integrable_of_lipschitz_stdGaussianPi n _ L (hf_seq_lip k)
  have hf_int : Integrable f μ := integrable_of_lipschitz_stdGaussianPi n f L hf
  have hInt_tendsto : Tendsto (fun k => ∫ y, f_seq k y ∂μ) atTop (𝓝 (∫ y, f y ∂μ)) := by
    -- f_seq k = gaussianMollify n (ε_seq k) f is L-Lipschitz, so ‖f_seq k x‖ ≤ bound(x).
    -- Dominator: D_f(x) = |f(0)| + L * ‖x‖ + L * c_norm
    -- works because |f_seq k(x)| ≤ |f_seq k(x) - f_seq k(0)| + |f_seq k(0)|
    --   ≤ L*‖x‖ + |f_seq k(0)|, and |f_seq k(0)| ≤ ∫|f(ε_k y)| ≤ |f(0)| + L*c_norm.
    set D_f := fun x : Fin n → ℝ => ‖f 0‖ + (L : ℝ) * (‖x‖ + c_norm) with hD_f_def
    have hD_f_int : Integrable D_f μ :=
      (integrable_const _).add
        ((((integrable_id_stdGaussianPi n).norm.add (integrable_const c_norm)).const_mul _))
    have hD_f_bound : ∀ k, ∀ᵐ x ∂μ, ‖f_seq k x‖ ≤ D_f x := by
      intro k; exact ae_of_all _ (fun x => by
        have hLip_k := hf_seq_lip k
        -- |f_seq k x - f_seq k 0| ≤ L * ‖x‖
        have h1 : ‖f_seq k x - f_seq k 0‖ ≤ (L : ℝ) * ‖x‖ := by
          calc ‖f_seq k x - f_seq k 0‖
              = dist (f_seq k x) (f_seq k 0) := (dist_eq_norm _ _).symm
            _ ≤ (L : ℝ) * dist x 0 := hLip_k.dist_le_mul x 0
            _ = (L : ℝ) * ‖x‖ := by rw [dist_zero_right]
        -- |f_seq k 0| ≤ |f 0| + L * c_norm (by Jensen + Lip)
        have h2 : ‖f_seq k 0‖ ≤ ‖f 0‖ + (L : ℝ) * c_norm := by
          show ‖gaussianMollify n (ε_seq k) f 0‖ ≤ _
          simp only [gaussianMollify]
          calc ‖∫ y, f (0 + ε_seq k • y) ∂μ‖
              ≤ ∫ y, ‖f (0 + ε_seq k • y)‖ ∂μ := norm_integral_le_integral_norm _
            _ ≤ ∫ y, (‖f 0‖ + (L : ℝ) * ‖y‖) ∂μ := by
                apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
                · exact (integrable_const _).add
                    ((integrable_id_stdGaussianPi n).norm.const_mul _)
                · exact ae_of_all _ (fun y => by
                    calc ‖f (0 + ε_seq k • y)‖
                        ≤ ‖f (0 + ε_seq k • y) - f 0‖ + ‖f 0‖ := by
                          linarith [norm_le_insert' (f (0 + ε_seq k • y)) (f 0)]
                      _ ≤ (L : ℝ) * ‖0 + ε_seq k • y‖ + ‖f 0‖ := by
                          gcongr
                          calc ‖f (0 + ε_seq k • y) - f 0‖
                              = dist (f (0 + ε_seq k • y)) (f 0) := (dist_eq_norm _ _).symm
                            _ ≤ (L : ℝ) * dist (0 + ε_seq k • y) 0 :=
                                hf.dist_le_mul _ _
                            _ = (L : ℝ) * ‖0 + ε_seq k • y‖ := by rw [dist_zero_right]
                      _ ≤ (L : ℝ) * ‖y‖ + ‖f 0‖ := by
                          gcongr
                          calc ‖(0 : Fin n → ℝ) + ε_seq k • y‖
                              = ‖ε_seq k • y‖ := by simp
                            _ = |ε_seq k| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
                            _ ≤ 1 * ‖y‖ := by
                                gcongr
                                rw [abs_of_pos (hε_pos k)]
                                show ε_seq k ≤ 1
                                simp only [ε_seq]
                                rw [div_le_iff₀ (by positivity : (0:ℝ) < (↑k : ℝ) + 1)]
                                linarith
                            _ = ‖y‖ := one_mul _
                      _ = ‖f 0‖ + (L : ℝ) * ‖y‖ := by ring)
            _ = ‖f 0‖ + (L : ℝ) * c_norm := by
                rw [integral_add (integrable_const _)
                  ((integrable_id_stdGaussianPi n).norm.const_mul _),
                  integral_const, integral_const_mul]
                have hm : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
                rw [hm, one_smul]
        calc ‖f_seq k x‖
            ≤ ‖f_seq k x - f_seq k 0‖ + ‖f_seq k 0‖ := by
              linarith [norm_le_insert' (f_seq k x) (f_seq k 0)]
          _ ≤ (L : ℝ) * ‖x‖ + (‖f 0‖ + (L : ℝ) * c_norm) := by linarith
          _ = ‖f 0‖ + (L : ℝ) * (‖x‖ + c_norm) := by ring)
    apply tendsto_integral_of_dominated_convergence D_f
    · exact fun k => (hf_seq_lip k).continuous.aestronglyMeasurable
    · exact hD_f_int
    · exact hD_f_bound
    · exact ae_of_all _ hf_ptwise
  -- Step 2c: X_{ε_k}(x) → X(x) pointwise
  have hX_ptwise : ∀ x, Tendsto (fun k => X_seq k x) atTop (𝓝 (X x)) :=
    fun x => (hf_ptwise x).sub hInt_tendsto
  -- Step 2d: g_k(x) = exp(t * X_{ε_k}(x)) → g(x) = exp(t * X(x)) pointwise
  have hg_ptwise : ∀ x, Tendsto (fun k => g_seq k x) atTop (𝓝 (g x)) :=
    fun x => (Real.continuous_exp.tendsto _).comp ((hX_ptwise x).const_mul t)
  -- Step 2e: Uniform dominator for |g_k(x)|.
  -- For any L-Lip h: |h(x) - ∫h| ≤ L*(‖x‖ + c_norm) (triangle + Jensen)
  -- So |g_k(x)| = exp(t*(X_{ε_k}(x))) ≤ exp(|t|*L*(‖x‖ + c_norm)) = D(x)
  set D : (Fin n → ℝ) → ℝ := fun x => Real.exp (|t| * (L : ℝ) * (‖x‖ + c_norm))
  have hD_bound : ∀ k x, |g_seq k x| ≤ D x ∧ |g x| ≤ D x := by
    intro k x
    constructor
    · -- |g_k(x)| = exp(t * X_{ε_k}(x)) ≤ exp(|t| * |X_{ε_k}(x)|)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp_of_le
      -- |X_{ε_k}(x)| ≤ L * (‖x‖ + c_norm) since f_{ε_k} is L-Lip
      have hcent : |X_seq k x| ≤ (L : ℝ) * (‖x‖ + c_norm) := by
        show |f_seq k x - ∫ y, f_seq k y ∂μ| ≤ _
        rw [show f_seq k x - ∫ y, f_seq k y ∂μ =
            ∫ y, (f_seq k x - f_seq k y) ∂μ from by
          rw [integral_sub (integrable_const _) (hf_seq_int k)]; simp [integral_const]]
        calc |∫ y, (f_seq k x - f_seq k y) ∂μ|
            ≤ ∫ y, |f_seq k x - f_seq k y| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ y, ((L : ℝ) * (‖x‖ + ‖y‖)) ∂μ := by
              apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
              · exact (integrable_const ‖x‖).add ((integrable_id_stdGaussianPi n).norm)
                  |>.const_mul _
              · exact ae_of_all _ (fun y => by
                  have := (hf_seq_lip k).dist_le_mul x y; rw [Real.dist_eq] at this
                  calc |f_seq k x - f_seq k y| ≤ (L : ℝ) * dist x y := this
                    _ = (L : ℝ) * ‖x - y‖ := by rw [dist_eq_norm]
                    _ ≤ (L : ℝ) * (‖x‖ + ‖y‖) := by gcongr; exact norm_sub_le x y)
          _ = (L : ℝ) * (‖x‖ + c_norm) := by
              simp_rw [mul_add]
              rw [integral_add (integrable_const _)
                ((integrable_id_stdGaussianPi n).norm.const_mul _),
                integral_const, integral_const_mul]
              have hm : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
              rw [hm, one_smul]
      calc t * X_seq k x ≤ |t * X_seq k x| := le_abs_self _
        _ = |t| * |X_seq k x| := abs_mul _ _
        _ ≤ |t| * ((L : ℝ) * (‖x‖ + c_norm)) :=
            mul_le_mul_of_nonneg_left hcent (abs_nonneg _)
        _ = |t| * (L : ℝ) * (‖x‖ + c_norm) := by ring
    · -- Same bound for g: |g(x)| ≤ D(x)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp_of_le
      have hcent : |X x| ≤ (L : ℝ) * (‖x‖ + c_norm) := by
        show |f x - ∫ y, f y ∂μ| ≤ _
        rw [show f x - ∫ y, f y ∂μ = ∫ y, (f x - f y) ∂μ from by
          rw [integral_sub (integrable_const _) hf_int]; simp [integral_const]]
        calc |∫ y, (f x - f y) ∂μ|
            ≤ ∫ y, |f x - f y| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ y, ((L : ℝ) * (‖x‖ + ‖y‖)) ∂μ := by
              apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
              · exact (integrable_const ‖x‖).add ((integrable_id_stdGaussianPi n).norm)
                  |>.const_mul _
              · exact ae_of_all _ (fun y => by
                  have := hf.dist_le_mul x y; rw [Real.dist_eq] at this
                  calc |f x - f y| ≤ (L : ℝ) * dist x y := this
                    _ = (L : ℝ) * ‖x - y‖ := by rw [dist_eq_norm]
                    _ ≤ (L : ℝ) * (‖x‖ + ‖y‖) := by gcongr; exact norm_sub_le x y)
          _ = (L : ℝ) * (‖x‖ + c_norm) := by
              simp_rw [mul_add]
              rw [integral_add (integrable_const _)
                ((integrable_id_stdGaussianPi n).norm.const_mul _),
                integral_const, integral_const_mul]
              have hm : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
              rw [hm, one_smul]
      calc t * X x ≤ |t * X x| := le_abs_self _
        _ = |t| * |X x| := abs_mul _ _
        _ ≤ |t| * ((L : ℝ) * (‖x‖ + c_norm)) :=
            mul_le_mul_of_nonneg_left hcent (abs_nonneg _)
        _ = |t| * (L : ℝ) * (‖x‖ + c_norm) := by ring
  -- D is integrable
  have hD_int : Integrable D μ :=
    integrable_exp_norm_add_const n (|t| * (L : ℝ)) c_norm (by positivity)
  -- D * |log D| is integrable (needed for entropyPi_tendsto_of_uniform)
  set a_dom := |t| * (L : ℝ) with ha_dom_def
  have ha_dom_nn : 0 ≤ a_dom := by positivity
  have hDlog_int : Integrable (fun x => D x * |Real.log (D x)|) μ := by
    -- D(x) = exp(a_dom * (‖x‖ + c_norm)), log D(x) = a_dom * (‖x‖ + c_norm) ≥ 0
    -- So D(x) * |log D(x)| = a_dom * (‖x‖+c_norm) * exp(a_dom*(‖x‖+c_norm))
    suffices h : Integrable (fun x : Fin n → ℝ =>
        a_dom * ((‖x‖ + c_norm) * Real.exp (a_dom * (‖x‖ + c_norm)))) μ from by
      apply h.congr (ae_of_all _ (fun x => by
        simp only [D, ha_dom_def.symm, Real.log_exp]
        rw [abs_of_nonneg (by positivity : 0 ≤ a_dom * (‖x‖ + c_norm))]
        ring))
    exact (integrable_mul_exp_norm_add_const n a_dom c_norm ha_dom_nn hc_norm_nn).const_mul _
  -- g_seq measurable
  have hg_meas : ∀ k, AEStronglyMeasurable (g_seq k) μ :=
    fun k => (Real.continuous_exp.comp (continuous_const.mul
      ((hf_seq_lip k).continuous.sub continuous_const))).aestronglyMeasurable
  -- Step 3a: ∫ g_k → ∫ g by DCT (for RHS convergence)
  have h_int_g_tendsto : Tendsto (fun k => ∫ x, g_seq k x ∂μ) atTop
      (𝓝 (∫ x, g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence D
    · exact hg_meas
    · exact hD_int
    · intro k; exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs]; exact (hD_bound k x).1)
    · exact ae_of_all _ hg_ptwise
  -- Step 3b: RHS converges: t²L²/2 * ∫ g_k → t²L²/2 * ∫ g
  have h_rhs_tendsto : Tendsto (fun k => t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, g_seq k x ∂μ)
      atTop (𝓝 (t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, g x ∂μ)) :=
    h_int_g_tendsto.const_mul (t ^ 2 * (L : ℝ) ^ 2 / 2)
  -- Step 3c: LHS converges: entropyPi μ (g_seq k) → entropyPi μ g
  have h_lhs_tendsto : Tendsto (fun k => entropyPi μ (g_seq k)) atTop
      (𝓝 (entropyPi μ g)) :=
    entropyPi_tendsto_of_uniform μ g g_seq hg_meas hg_ptwise
      ⟨D, hD_int, hDlog_int, fun k x => hD_bound k x⟩
  -- Step 4: Pass inequality to limit
  exact le_of_tendsto_of_tendsto h_lhs_tendsto h_rhs_tendsto
    (Eventually.of_forall (fun k => hC1_bound (ε_seq k) (hε_pos k)))

/-- **From entropy bound to MGF bound** (the Grönwall/ODE step):
If `Ent(e^{tX}) ≤ c·t² · E[e^{tX}]` for all t, and E[X]=0,
then `E[e^{tX}] ≤ exp(c·t²)`.

Proof sketch: Let Λ(t) = log E[e^{tX}]. The entropy bound gives
t·Λ'(t) - Λ(t) ≤ c·t², hence d/dt[Λ(t)/t] ≤ c for t > 0.
Since Λ(0)=0 and Λ'(0)=E[X]=0, we get lim Λ(t)/t = 0.
Integrating: Λ(t)/t ≤ c·t, so Λ(t) ≤ c·t².
For t < 0: same argument by symmetry (or apply to -X). -/
private lemma mgf_le_of_entropyPi_bound
    (n : ℕ) (X : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmean : ∫ x, X x ∂stdGaussianPi n = 0)
    (hint : ∀ s, Integrable (fun x => Real.exp (s * X x)) (stdGaussianPi n))
    (hent : ∀ s, entropyPi (stdGaussianPi n) (fun x => Real.exp (s * X x)) ≤
      s ^ 2 * c * ∫ x, Real.exp (s * X x) ∂stdGaussianPi n) :
    ∀ t, mgf X (stdGaussianPi n) t ≤ Real.exp (c * t ^ 2) := by
  set μ := stdGaussianPi n
  -- integrableExpSet = univ since hint gives integrability for all s
  have hExpSet : integrableExpSet X μ = Set.univ := by
    ext s; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hint s
  have hInterior : ∀ s, s ∈ interior (integrableExpSet X μ) := by
    rw [hExpSet, interior_univ]; exact fun s => Set.mem_univ s
  -- mgf is differentiable with derivative ∫ X·exp(sX)
  have hDeriv : ∀ s, HasDerivAt (mgf X μ) (∫ x, X x * Real.exp (s * X x) ∂μ) s :=
    fun s => hasDerivAt_mgf (hInterior s)
  -- mgf(0) = 1 (probability measure)
  have hMgf0 : mgf X μ 0 = 1 := by simp [mgf]
  -- mgf > 0 (exp > 0)
  have hMgfPos : ∀ s, 0 < mgf X μ s := fun s => mgf_pos (hint s)
  -- deriv(mgf)(0) = E[X] = 0
  have hDeriv0 : deriv (mgf X μ) 0 = 0 := by
    rw [deriv_mgf (hInterior 0)]; simp only
    simp_rw [zero_mul, Real.exp_zero, mul_one]; exact hmean
  -- Step 1: The key ODE inequality.
  -- Entropy identity + bound → s·Λ'(s) - Λ(s) ≤ s²c
  have hODE : ∀ s, s * deriv (fun t => Real.log (mgf X μ t)) s -
      Real.log (mgf X μ s) ≤ s ^ 2 * c := by
    intro s
    have hent_s := hent s
    rw [entropyPi_exp_eq X s μ] at hent_s
    -- Λ'(s) = M'(s)/M(s) = (∫X·exp(sX))/(mgf s)
    have hlog_deriv : HasDerivAt (fun t => Real.log (mgf X μ t))
        ((mgf X μ s)⁻¹ * ∫ x, X x * Real.exp (s * X x) ∂μ) s :=
      (Real.hasDerivAt_log (ne_of_gt (hMgfPos s))).comp s (hDeriv s)
    rw [hlog_deriv.deriv]
    -- Goal: s * (M⁻¹ * I) - log M ≤ s²c
    -- This equals (s*I - M*log M)/M, and we need ≤ s²c.
    -- Equivalently: s*I - M*log M ≤ s²c*M, which is hent_s.
    have hM_pos' := hMgfPos s
    have hM_ne : (mgf X μ s) ≠ 0 := ne_of_gt hM_pos'
    -- Rewrite LHS as (s*I - M*log M) / M
    have h_eq : s * ((mgf X μ s)⁻¹ * ∫ x, X x * Real.exp (s * X x) ∂μ) -
        Real.log (mgf X μ s) =
        (s * (∫ x, X x * Real.exp (s * X x) ∂μ) -
         mgf X μ s * Real.log (mgf X μ s)) / mgf X μ s := by
      field_simp
    rw [h_eq]
    exact (div_le_iff₀ hM_pos').mpr hent_s
  -- Step 2: Λ = log ∘ mgf
  let Λ : ℝ → ℝ := fun s => Real.log (mgf X μ s)
  have hΛ_zero : Λ 0 = 0 := by simp [Λ, hMgf0]
  have hΛderiv : ∀ s, HasDerivAt Λ ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) s :=
    fun s => (hDeriv s).log (hMgfPos s).ne'
  have hΛderiv_zero : HasDerivAt Λ 0 0 := by
    convert hΛderiv 0 using 1; simp [hMgf0, hmean]
  -- Λ'(s) = deriv Λ s
  have hΛderiv_eq : ∀ s, deriv (fun t => Real.log (mgf X μ t)) s =
      (∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s :=
    fun s => (hΛderiv s).deriv
  -- Restate hODE in terms of Λ
  have hODE' : ∀ s, s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s ≤ s ^ 2 * c := by
    intro s; rw [← hΛderiv_eq]; exact hODE s
  -- k(s) = Λ(s)/s - c*s is antitone on Ioi 0 and Iio 0
  let k : ℝ → ℝ := fun s => Λ s / s - c * s
  have hkDeriv : ∀ s ≠ 0, HasDerivAt k
      ((s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s) / s ^ 2 - c) s := by
    intro s hs
    have hdiv : HasDerivAt (fun s => Λ s / s)
        ((s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s) / s ^ 2) s := by
      have h := (hΛderiv s).div (hasDerivAt_id s) hs
      simp only [id] at h; convert h using 1; field_simp
    have hlin : HasDerivAt (fun s => c * s) c s := by simpa using (hasDerivAt_id s).const_mul c
    simpa using hdiv.sub hlin
  have hk_deriv_le : ∀ s ≠ 0, deriv k s ≤ 0 := fun s hs => by
    rw [(hkDeriv s hs).deriv]
    linarith [(div_le_iff₀ (pow_two_pos_of_ne_zero hs)).mpr
      (by linarith [hODE' s, mul_comm c (s ^ 2)] :
        s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s ≤ c * s ^ 2)]
  have hk_cont : ∀ (S : Set ℝ), (∀ s ∈ S, s ≠ 0) → ContinuousOn k S := fun S hS => by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · apply ContinuousOn.comp Real.continuousOn_log
        · exact (continuous_mgf hint).continuousOn
        · intro s _; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (hMgfPos s).ne'
      · exact continuousOn_id
      · exact fun s hs => hS s hs
    · exact (continuous_const.mul continuous_id).continuousOn
  have hk_anti_Ioi : AntitoneOn k (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (hk_cont _ (fun s hs => (Set.mem_Ioi.mp hs).ne'))
    · rw [interior_Ioi]
      intro s hs
      exact (hkDeriv s hs.ne').differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; exact fun s hs => hk_deriv_le s hs.ne'
  have hk_anti_Iio : AntitoneOn k (Set.Iio 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iio 0)
      (hk_cont _ (fun s hs => (Set.mem_Iio.mp hs).ne))
    · rw [interior_Iio]
      intro s hs
      exact (hkDeriv s hs.ne).differentiableAt.differentiableWithinAt
    · rw [interior_Iio]; exact fun s hs => hk_deriv_le s hs.ne
  -- Limit of k at 0+ and 0-
  have hΛdiv_lim_Ioi : Tendsto (fun s => Λ s / s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hf := hΛderiv_zero.hasDerivAtFilter (L := nhdsWithin 0 (Set.Ioi 0))
    rw [hasDerivAtFilter_iff_tendsto] at hf; simp [hΛ_zero] at hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hf nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    simp [Real.norm_eq_abs, abs_of_pos hs, div_eq_mul_inv, mul_comm]
  have hΛdiv_lim_Iio : Tendsto (fun s => Λ s / s) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    have hf := hΛderiv_zero.hasDerivAtFilter (L := nhdsWithin 0 (Set.Iio 0))
    rw [hasDerivAtFilter_iff_tendsto] at hf; simp [hΛ_zero] at hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hf nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Iio] at hs
    simp only [Real.norm_eq_abs]; rw [abs_of_neg hs, abs_div, abs_of_neg hs]; ring
  have hcs_lim : ∀ (S : Set ℝ), Tendsto (fun s => c * s) (nhdsWithin 0 S) (nhds 0) := fun S => by
    have h : Tendsto (fun s => c * s) (nhds (0 : ℝ)) (nhds (c * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simp at h; exact h.mono_left nhdsWithin_le_nhds
  have hk_lim_Ioi : Tendsto k (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by simpa using hΛdiv_lim_Ioi.sub (hcs_lim _)
  have hk_lim_Iio : Tendsto k (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    by simpa using hΛdiv_lim_Iio.sub (hcs_lim _)
  -- Antitone + limit 0 helper for Ioi
  have anti_Ioi : ∀ {f : ℝ → ℝ}, AntitoneOn f (Set.Ioi 0) →
      Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) → ∀ t > 0, f t ≤ 0 := by
    intro f h_anti h_lim t ht
    by_contra hft; push_neg at hft
    have h1 : {x | f x < f t} ∈ nhdsWithin 0 (Set.Ioi 0) := h_lim.eventually (Iio_mem_nhds hft)
    rw [mem_nhdsWithin] at h1
    obtain ⟨s, hs_open, hs0, hs_sub⟩ := h1; rw [Metric.isOpen_iff] at hs_open
    obtain ⟨r, hr, hr_sub⟩ := hs_open 0 hs0; set ε := min (r / 2) t
    have hε_pos : 0 < ε := lt_min (by linarith) ht
    have hε_in_ball : ε ∈ Metric.ball 0 r := by
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε_pos]
      linarith [min_le_left (r / 2) t]
    have hfε_lt : f ε < f t := hs_sub ⟨hr_sub hε_in_ball, Set.mem_Ioi.mpr hε_pos⟩
    have hfε_ge : f t ≤ f ε := h_anti (Set.mem_Ioi.mpr hε_pos) (Set.mem_Ioi.mpr ht) (min_le_right _ _)
    linarith
  -- Antitone + limit 0 helper for Iio
  have anti_Iio : ∀ {f : ℝ → ℝ}, AntitoneOn f (Set.Iio 0) →
      Tendsto f (nhdsWithin 0 (Set.Iio 0)) (nhds 0) → ∀ t < 0, 0 ≤ f t := by
    intro f h_anti h_lim t ht
    by_contra hft; push_neg at hft
    have h1 : {x | f t < f x} ∈ nhdsWithin 0 (Set.Iio 0) := h_lim.eventually (Ioi_mem_nhds hft)
    rw [mem_nhdsWithin] at h1
    obtain ⟨s, hs_open, hs0, hs_sub⟩ := h1; rw [Metric.isOpen_iff] at hs_open
    obtain ⟨r, hr, hr_sub⟩ := hs_open 0 hs0; set ε := max (-(r / 2)) t
    have hε_neg : ε < 0 := max_lt (by linarith) ht
    have hε_in_ball : ε ∈ Metric.ball 0 r := by
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_neg hε_neg]
      linarith [le_max_left (-(r / 2)) t]
    have hfε_gt : f t < f ε := hs_sub ⟨hr_sub hε_in_ball, Set.mem_Iio.mpr hε_neg⟩
    have hfε_le : f ε ≤ f t := h_anti (Set.mem_Iio.mpr ht) (Set.mem_Iio.mpr hε_neg) (le_max_right _ _)
    linarith
  -- Conclude for all t
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- t < 0: k(t) ≥ 0 → Λ(t) ≤ c*t²
    have hkt : 0 ≤ k t := anti_Iio hk_anti_Iio hk_lim_Iio t ht
    have hΛt : Λ t ≤ c * t ^ 2 := by
      simp only [k] at hkt
      calc Λ t = Λ t / t * t := by rw [div_mul_cancel₀]; exact ht.ne
        _ ≤ c * t * t := by nlinarith [ht]
        _ = c * t ^ 2 := by ring
    exact (Real.log_le_iff_le_exp (hMgfPos t)).mp hΛt
  · subst ht; simp [hMgf0]
  · -- t > 0: k(t) ≤ 0 → Λ(t) ≤ c*t²
    have hkt : k t ≤ 0 := anti_Ioi hk_anti_Ioi hk_lim_Ioi t ht
    have hΛt : Λ t ≤ c * t ^ 2 := by
      simp only [k] at hkt
      calc Λ t = Λ t / t * t := by rw [div_mul_cancel₀]; exact ht.ne'
        _ ≤ c * t * t := by nlinarith
        _ = c * t ^ 2 := by ring
    exact (Real.log_le_iff_le_exp (hMgfPos t)).mp hΛt

/-- **Herbst MGF bound**: For centered L-Lipschitz functions of Gaussian vectors,
the MGF satisfies `E[exp(s·X)] ≤ exp(L²·s²/2)`. -/
private lemma mgf_le_exp_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    mgf X (stdGaussianPi n) t ≤ Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
  intro X
  -- Combine entropy bound + ODE step
  have hint := integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf
  have hent := entropyPi_exp_le_of_lipschitz n f L hf
  have hmean : ∫ x, X x ∂stdGaussianPi n = 0 := by
    simp only [X]
    rw [integral_sub (integrable_of_lipschitz_stdGaussianPi n f L hf)
        (integrable_const _)]
    simp [integral_const, sub_self]
  have hmgf := mgf_le_of_entropyPi_bound n X ((L : ℝ) ^ 2 / 2) (by positivity) hmean hint
    (fun s => by convert hent s using 1; ring)
  calc mgf X (stdGaussianPi n) t
      ≤ Real.exp ((L : ℝ) ^ 2 / 2 * t ^ 2) := hmgf t
    _ = Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
        congr 1; push_cast [NNReal.coe_pow]; ring

/-! ## Sorry-bearing declarations -/

private lemma hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂stdGaussianPi n)
      (L ^ 2)
      (stdGaussianPi n) :=
  ⟨fun t => integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf t,
   fun t => mgf_le_exp_of_lipschitz_stdGaussianPi n f L hf t⟩

theorem herbst_argument_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  intro s
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂stdGaussianPi n
  have hSubG := hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi n f L hf
  have hcgf := hSubG.cgf_le s
  simp only [cgf, mgf] at hcgf
  calc Real.log (∫ x, Real.exp (s * X x) ∂stdGaussianPi n)
      ≤ ↑(L ^ 2) * s ^ 2 / 2 := hcgf
    _ = s ^ 2 * ↑L ^ 2 / 2 := by
        push_cast [NNReal.coe_pow]
        ring

theorem herbst_argument
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  herbst_argument_core n f L hf s

end

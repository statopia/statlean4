import Statlean.Gaussian.Basic
import Statlean.Entropy.LogSobolev
import Mathlib.Probability.Moments.SubGaussian

/-! # Herbst Argument and Sub-Gaussian MGF

## Main definitions
- `HerbstBound` — cumulant generating function bound for a fixed function
- `UniversalHerbstBound` — universal Herbst interface for Lipschitz functions

## Proved (3 sorry remaining — harder mollification steps)
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
- `gaussianMollify_C1_with_gradient_bound` — f_ε is C¹ with ‖∇f_ε‖ ≤ L (4 sub-sorry)
- `entropyPi_tendsto_of_uniform` — entropy continuity under DCT
- `entropyPi_exp_le_of_lipschitz` — main assembly (limit argument, depends on above)
-/

open MeasureTheory ProbabilityTheory Filter Topology
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
  refine ⟨gradf_ε, ?_, ?_, ?_, ?_⟩
  · -- (1) HasDerivAt: coordinate slice of f_ε is differentiable.
    -- Route: Convert to Lebesgue integral with Gaussian density kernel,
    -- differentiate the KERNEL (smooth) not f, via Leibniz rule.
    -- Key APIs: integral_gaussianReal_eq_integral_smul, hasDerivAt_integral_of_dominated_loc_of_deriv_le
    -- The derivative of gaussianPDFReal w.r.t. mean: ∂/∂μ[φ(μ,σ,x)] = φ·(x-μ)/σ²
    -- gradf_ε i x = (1/ε) ∫ f(x+εy)·yᵢ dγ(y) (Stein's identity for Gaussian convolution)
    intro x i
    -- The coord slice s ↦ gaussianMollify n ε f (update x i s)
    -- = ∫ f(fun j => if j=i then s+ε*yⱼ else xⱼ+ε*yⱼ) dγ(y)
    -- is L-Lipschitz (gaussianMollify_coord_lipschitz) hence differentiable a.e. (Rademacher).
    -- For the HasDerivAt at the SPECIFIC point x i:
    -- Use hasFDerivAt_integral_of_dominated_loc_of_lip with F(s,y) Lipschitz in s.
    -- The condition "HasFDerivAt for a.e. y" follows from:
    --   For each y, s ↦ F(s,y) is L-Lipschitz, hence diff a.e. in s (Rademacher).
    --   By Fubini on the product space (s,y): for a.e. s, diff for a.e. y.
    --   (This uses that the non-diff set is measurable and has product measure 0.)
    -- Since we need this at a SPECIFIC s₀ = x i, this is a subtle point.
    -- For GAUSSIAN convolution specifically, the function IS smooth at ALL points
    -- (convolution with Schwartz function), but proving this requires kernel differentiation.
    -- Route: Rademacher + diffeomorphism preimage + Leibniz.
    -- (a) By Rademacher: f diff at a.e. point (wrt volume). Let S = non-diff set, |S|=0.
    -- (b) For each y: F_y(s) = f(update (x+εy) i (s+εyᵢ)) is L-Lip in s.
    --     F_y diff at s₀ ↔ f diff at update(x+εy) i (s₀+εyᵢ) wrt coord i.
    -- (c) The map y ↦ update(x+εy) i (s₀+εyᵢ) is a diffeomorphism (ε≠0).
    --     Preimage of S under this diffeo has volume 0. stdGaussianPi ≪ volume.
    --     So F_y diff at s₀ for a.e. y (stdGaussianPi).
    -- (d) hasFDerivAt_integral_of_dominated_loc_of_lip gives HasFDerivAt for ∫F_y dγ.
    -- (e) Extract HasDerivAt from HasFDerivAt (1D case).
    sorry
  · -- (2) Gradient bound: ∑ᵢ (∂ᵢf_ε)² ≤ L².
    -- From (1), gradf_ε i x = deriv of coord slice at x i.
    -- By `norm_fderiv_le_of_lipschitz` on the full f_ε (L-Lipschitz, sup norm):
    --   ‖fderiv ℝ f_ε x‖_op ≤ L
    -- For linear functional on (Fin n → ℝ) with sup norm:
    --   ‖ℓ‖_op = ∑ᵢ |ℓ(eᵢ)| = ∑ᵢ |∂ᵢf_ε|
    -- So ∑ |∂ᵢf_ε| ≤ L, hence ∑ (∂ᵢf_ε)² ≤ (∑ |∂ᵢf_ε|)² ≤ L².
    -- BLOCKER: needs Differentiable from (1) + fderiv ↔ partial deriv bridge.
    sorry
  · -- (3) Continuity: s ↦ gradf_ε i (update x i s) is continuous.
    -- f_ε is C^∞ (convolution with Gaussian), so its derivative is continuous.
    -- BLOCKER: same as (1), needs smoothness of mollification.
    sorry
  · -- (4) Measurability: gradf_ε i is measurable.
    -- Follows from gradf_ε being continuous (which follows from f_ε being C^∞).
    -- Alternatively: deriv of a Lipschitz function is measurable (Rademacher).
    -- BLOCKER: same as (1)/(3).
    sorry

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

/-- Entropy is continuous under uniform convergence of non-negative integrands.
If g_k → g uniformly, g_k ≥ 0, and there is an integrable dominator,
then Ent(g_k) → Ent(g). -/
private lemma entropyPi_tendsto_of_uniform {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin n → ℝ) → ℝ) (g_seq : ℕ → (Fin n → ℝ) → ℝ)
    (hconv : ∀ x, Tendsto (fun k => g_seq k x) atTop (𝓝 (g x)))
    (hdom : ∃ D : (Fin n → ℝ) → ℝ, Integrable D μ ∧
      Integrable (fun x => D x * |Real.log (D x)|) μ ∧
      ∀ k x, |g_seq k x| ≤ D x ∧ |g x| ≤ D x)
    (hbound : ∀ k, entropyPi μ (g_seq k) ≤
      entropyPi μ g + 1) :  -- technical: entropy sequence is bounded
    Tendsto (fun k => entropyPi μ (g_seq k)) atTop (𝓝 (entropyPi μ g)) := by
  -- Uses DCT twice: ∫ g_k log g_k → ∫ g log g and ∫ g_k → ∫ g
  sorry

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

  -- Step 2: f_ε → f pointwise as ε → 0, hence X_ε → X and exp(t·X_ε) → exp(t·X)
  -- Step 3: By DCT, both sides of the inequality converge, preserving ≤
  -- This uses gaussianMollify_tendsto for pointwise convergence
  -- and Lipschitz growth control for domination.
  sorry

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

import Statlean.Variance.EfronStein
import Statlean.Gaussian.Hermite
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Gaussian Poincaré Inequality

## Proved
- `gaussian_poincare_1d_core` — 1D Poincaré via Hermite Parseval
- `gaussian_poincare_coord_bound_core` — per-coordinate bound via condVar + tower law
- `gaussian_poincare` — multi-dimensional Poincaré via Efron-Stein + coordinate bound
- `gaussian_poincare_of_integral_bound` — wrapper
- `gaussian_poincare_of_efron_stein` — via Efron-Stein + coordinate bound
- `gaussian_poincare_of_condVar_sum` — via conditional variance sum

## Sorry gaps (1 sorry)
- `memLp_four_of_W12_gaussian` — `f ∈ W^{1,2}(γ) → f ∈ L⁴(γ)`, blocked by Hermite
  product linearization.

## Proved (was sorry)
- `condExp_eq_fiberAvg_pi` — disintegration identity via `ae_eq_condExp_of_forall_setIntegral_eq`,
  Fubini (`setIntegral_prod_swap`), and `sigmaAlgExcept ≤ comap (removeNth i) pi`.
- `ae_memLp_fiber` — Fubini for `f²` via `measurePreserving_piFinSuccAbove` + product decomposition.
- `condVar_le_condExp_gradf_sq_ae` — proved via disintegration + `gaussian_poincare_1d_core`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real NNReal
open scoped ENNReal

noncomputable section

/-! ## Clean wrappers (zero sorry) -/

theorem gaussian_poincare_of_integral_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hGP :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hGP

theorem gaussian_poincare_of_efron_stein
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n))
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hSum :
      (∑ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n))
        ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hCoord i
  exact le_trans hES hSum

theorem gaussian_poincare_of_condVar_sum
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hCondVar :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          (stdGaussianPi n)[Var[f; stdGaussianPi n |
            sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]])
    (hCoord :
      ∀ i : Fin n,
        ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
          ∂(stdGaussianPi n)
          ≤
        ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  have hES :
      Var[f; stdGaussianPi n] ≤
        ∑ i : Fin n,
          ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
            ∂(stdGaussianPi n) :=
    efron_stein_of_condVar_sum_bound (μ := fun _ : Fin n => stdGaussian) f hf hCondVar
  exact gaussian_poincare_of_efron_stein n f gradf hES hCoord

/-! ## Helpers for 1D Poincaré -/

/-- f · hermiteNorm is integrable when f ∈ L²(γ). -/
private lemma integrable_f_mul_hermiteNorm' (k : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x * hermiteNorm k x) stdGaussian := by
  unfold hermiteNorm
  have : (fun x => f x * (hermiteEval k x / Real.sqrt ↑k.factorial)) =
      (fun x => (1 / Real.sqrt ↑k.factorial) * (f x * hermiteEval k x)) := by
    ext x; ring
  rw [this]
  exact (integrable_f_mul_hermiteEval k hf).const_mul _

/-- Hermite coefficient: `aₖ(f) = ∫ f · eₖ dγ`. -/
private def hermiteCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ x, f x * hermiteNorm k x ∂stdGaussian

/-- `a₀(f) = ∫ f dγ` (since e₀ = 1). -/
private lemma hermiteCoeff_zero (f : ℝ → ℝ) :
    hermiteCoeff f 0 = ∫ x, f x ∂stdGaussian := by
  simp [hermiteCoeff, hermiteNorm, hermiteEval, Polynomial.hermite_zero, Polynomial.aeval_one,
    Nat.factorial, Real.sqrt_one]

/-- The Hermite projection: ∑_{k < N} aₖ · eₖ(x). -/
private def hermiteProj (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, hermiteCoeff f k * hermiteNorm k x

/-- hermiteNorm k is in L²(γ). -/
private lemma memLp_hermiteNorm (k : ℕ) : MemLp (hermiteNorm k) 2 stdGaussian := by
  change MemLp (fun x => hermiteNorm k x) 2 stdGaussian
  have : (fun x => hermiteNorm k x) = (fun x => (1 / Real.sqrt ↑k.factorial) *
      Polynomial.aeval x (Polynomial.hermite k)) := by
    ext x; simp [hermiteNorm, hermiteEval]; ring
  rw [this]
  exact (memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num)).const_mul' _

/-- The Hermite projection is in L²(γ). -/
private lemma memLp_hermiteProj (f : ℝ → ℝ) (N : ℕ) :
    MemLp (hermiteProj f N) 2 stdGaussian := by
  apply memLp_finset_sum
  intro k _
  exact (memLp_hermiteNorm k).const_mul' _

/-- Product of hermiteNorm j and hermiteNorm k is integrable under Gaussian. -/
private lemma integrable_hermiteNorm_mul_hermiteNorm (j k : ℕ) :
    Integrable (fun x => hermiteNorm j x * hermiteNorm k x) stdGaussian := by
  have h := (memLp_hermiteNorm j).integrable_mul (memLp_hermiteNorm k) (𝕜 := ℝ)
  exact h.congr (Filter.Eventually.of_forall fun x => rfl)

/-- Inner product ∫ (hermiteProj) · eₖ using orthonormality. -/
private lemma integral_hermiteProj_mul_hermiteNorm (f : ℝ → ℝ)
    (_hf : MemLp f 2 stdGaussian) (N k : ℕ) :
    ∫ x, hermiteProj f N x * hermiteNorm k x ∂stdGaussian =
    if k < N then hermiteCoeff f k else 0 := by
  simp only [hermiteProj, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => by
    exact (integrable_hermiteNorm_mul_hermiteNorm j k).const_mul _
      |>.congr (Filter.Eventually.of_forall fun x => by ring))]
  simp_rw [show ∀ j, (fun x => hermiteCoeff f j * hermiteNorm j x * hermiteNorm k x) =
      (fun x => hermiteCoeff f j * (hermiteNorm j x * hermiteNorm k x)) from
      fun j => by ext x; ring]
  simp_rw [integral_const_mul, hermiteNorm_inner]
  split_ifs with hmem
  · have : ∀ j ∈ Finset.range N, hermiteCoeff f j * (if j = k then 1 else 0) =
        if j = k then hermiteCoeff f k else 0 := by
      intro j _; split_ifs with h <;> simp [h]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [hmem]
  · apply Finset.sum_eq_zero
    intro j hj; simp only [Finset.mem_range] at hj
    have hne : j ≠ k := by omega
    simp [hne]

/-- ∫ f · S = ∑ aₖ² where S = hermiteProj. -/
private lemma integral_f_mul_hermiteProj (f : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian) (N : ℕ) :
    ∫ x, f x * hermiteProj f N x ∂stdGaussian =
    ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 := by
  simp only [hermiteProj]
  rw [show (fun x => f x * ∑ k ∈ Finset.range N, hermiteCoeff f k * hermiteNorm k x) =
      (fun x => ∑ k ∈ Finset.range N, hermiteCoeff f k * (f x * hermiteNorm k x)) from by
    ext x; rw [Finset.mul_sum]; congr 1; ext k; ring]
  rw [integral_finset_sum _ (fun k _ =>
    (integrable_f_mul_hermiteNorm' k hf).const_mul _)]
  simp_rw [integral_const_mul]
  congr 1; ext k; rw [sq, hermiteCoeff]

/-- ∫ S² = ∑ aₖ² where S = hermiteProj. -/
private lemma integral_sq_hermiteProj (f : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian) (N : ℕ) :
    ∫ x, hermiteProj f N x ^ 2 ∂stdGaussian =
    ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 := by
  -- Write S² = (∑ aₖ eₖ) · S = ∑ aₖ (eₖ · S)
  -- ∫ S² = ∑ aₖ ∫(eₖ · S) = ∑ aₖ · aₖ = ∑ aₖ²
  rw [show (fun x => hermiteProj f N x ^ 2) =
      (fun x => ∑ k ∈ Finset.range N,
        hermiteCoeff f k * (hermiteProj f N x * hermiteNorm k x)) from by
    ext x; simp only [sq, hermiteProj]; rw [Finset.sum_mul]; congr 1; ext k; ring]
  rw [integral_finset_sum _ (fun k _ =>
    ((integrable_f_mul_hermiteNorm' k (memLp_hermiteProj f N)).const_mul _)
      |>.congr (Filter.Eventually.of_forall fun x => by ring))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (fun x => hermiteCoeff f k * (hermiteProj f N x * hermiteNorm k x)) =
      (fun x => hermiteCoeff f k * (hermiteProj f N x * hermiteNorm k x)) from rfl]
  rw [integral_const_mul, integral_hermiteProj_mul_hermiteNorm f hf N k,
      if_pos (Finset.mem_range.mp hk), sq]

/-- Concrete finite Bessel inequality for Hermite system:
`∑_{k < N} (∫ f · eₖ)² ≤ ∫ f²`. -/
private lemma hermite_bessel_finite (f : ℝ → ℝ) (hf : MemLp f 2 stdGaussian)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 ≤
      ∫ x, f x ^ 2 ∂stdGaussian := by
  -- From 0 ≤ ∫ (f - S)² = ∫ f² - 2∫fS + ∫S² = ∫ f² - 2∑aₖ² + ∑aₖ² = ∫ f² - ∑aₖ²
  have hnn : 0 ≤ ∫ x, (f x - hermiteProj f N x) ^ 2 ∂stdGaussian :=
    integral_nonneg (fun x => sq_nonneg _)
  -- Expand ∫ (f-S)²
  have hfS_int : Integrable (fun x => f x * hermiteProj f N x) stdGaussian :=
    hf.integrable_mul (memLp_hermiteProj f N) (𝕜 := ℝ)
  have hf2_int : Integrable (fun x => f x ^ 2) stdGaussian := hf.integrable_sq
  have hS2_int : Integrable (fun x => hermiteProj f N x ^ 2) stdGaussian :=
    (memLp_hermiteProj f N).integrable_sq
  -- ∫ (f-S)² = ∫ f² - 2∫ fS + ∫ S² = ∫ f² - ∑ aₖ²
  have hfS_int' : Integrable (fun x => 2 * (f x * hermiteProj f N x)) stdGaussian :=
    hfS_int.const_mul 2
  -- ∫ (f-S)² = ∫ f² - ∑ aₖ² via bilinearity + orthonormality
  have hresid : ∫ x, (f x - hermiteProj f N x) ^ 2 ∂stdGaussian =
      ∫ x, f x ^ 2 ∂stdGaussian -
      ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 := by
    -- Rewrite integrand as sum of three parts
    have h1 : ∀ x, (f x - hermiteProj f N x) ^ 2 =
        f x ^ 2 - 2 * (f x * hermiteProj f N x) + hermiteProj f N x ^ 2 := by
      intro x; ring
    -- Compute each integral separately
    have I_fS : ∫ x, f x * hermiteProj f N x ∂stdGaussian =
        ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 :=
      integral_f_mul_hermiteProj f hf N
    have I_S2 : ∫ x, hermiteProj f N x ^ 2 ∂stdGaussian =
        ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 :=
      integral_sq_hermiteProj f hf N
    -- Now compute ∫ (f-S)²
    -- = ∫ f² - 2·∫ fS + ∫ S² = ∫ f² - 2·∑aₖ² + ∑aₖ² = ∫ f² - ∑aₖ²
    -- We use: ∫ (f-S)² = ∫ f² + ∫ S² - 2·∫ fS
    -- Proof: ∫ (f-S)² = ∫ f² + ∫ S² - 2∫ fS by inner product expansion
    -- Since ∫ S² = ∑aₖ² and ∫ fS = ∑aₖ², this is ∫ f² + ∑ - 2∑ = ∫ f² - ∑
    -- For the integral split, use a direct `have` chain
    -- Step A: ∫(f-S)² where the integrand is rewritten
    -- We prove using: ∫ (f-S)² = ∫ f² + ∫ S² - 2∫ fS
    -- via the decomposition (f-S)² = f² + S² - 2fS
    -- Split: a-b+c = (a+c) + (-b), then use integral_add
    have h2a : ∫ x, (f x ^ 2 + hermiteProj f N x ^ 2) ∂stdGaussian =
        ∫ x, f x ^ 2 ∂stdGaussian + ∫ x, hermiteProj f N x ^ 2 ∂stdGaussian :=
      integral_add hf2_int hS2_int
    have h2b : ∫ x, -(2 * (f x * hermiteProj f N x)) ∂stdGaussian =
        -(2 * ∫ x, f x * hermiteProj f N x ∂stdGaussian) := by
      rw [integral_neg, integral_const_mul]
    have h2c : ∫ x, (f x - hermiteProj f N x) ^ 2 ∂stdGaussian =
        ∫ x, (f x ^ 2 + hermiteProj f N x ^ 2) ∂stdGaussian +
        ∫ x, -(2 * (f x * hermiteProj f N x)) ∂stdGaussian := by
      have : (fun x => (f x - hermiteProj f N x) ^ 2) =
          (fun x => (f x ^ 2 + hermiteProj f N x ^ 2) +
            -(2 * (f x * hermiteProj f N x))) := by ext x; ring
      rw [this]; exact integral_add (hf2_int.add hS2_int) hfS_int'.neg
    rw [h2c, h2a, h2b, I_fS, I_S2]; ring
  linarith [hresid, hnn]

/-- Summability of Hermite coefficient squares from Bessel. -/
private lemma summable_hermiteCoeff_sq (f : ℝ → ℝ) (hf : MemLp f 2 stdGaussian) :
    Summable (fun k => hermiteCoeff f k ^ 2) := by
  apply summable_of_sum_le (fun k => sq_nonneg _) (c := ∫ x, f x ^ 2 ∂stdGaussian)
  intro u
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range u
  calc ∑ x ∈ u, hermiteCoeff f x ^ 2
      ≤ ∑ x ∈ Finset.range N, hermiteCoeff f x ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => sq_nonneg _)
    _ ≤ ∫ x, f x ^ 2 ∂stdGaussian := hermite_bessel_finite f hf N

/-- For ℝ, inner product is multiplication. -/
private lemma real_inner_eq_mul (a b : ℝ) : @inner ℝ ℝ _ a b = a * b := by
  rw [RCLike.inner_apply]; simp [mul_comm]

/-- Hermite normalized functions embedded in L²(γ). -/
private noncomputable def hermiteNormLp (k : ℕ) : Lp ℝ 2 stdGaussian :=
  (memLp_hermiteNorm k).toLp (hermiteNorm k)

/-- The Hermite normalized functions form an orthonormal system in L²(γ). -/
private lemma orthonormal_hermiteNormLp : Orthonormal ℝ hermiteNormLp := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [hermiteNormLp]
  rw [L2.inner_def]
  -- Need: ∫ ⟪(toLp eᵢ)(x), (toLp eⱼ)(x)⟫ dγ = δᵢⱼ
  have := hermiteNorm_inner i j
  convert this using 1
  apply integral_congr_ae
  filter_upwards [(memLp_hermiteNorm i).coeFn_toLp, (memLp_hermiteNorm j).coeFn_toLp]
    with x hi hj
  rw [hi, hj, real_inner_eq_mul]

/-- The orthogonal complement of the Hermite span is trivial in L²(γ). -/
private lemma hermiteNormLp_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range hermiteNormLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hg_inner : ∀ k : ℕ,
      ∫ x, hermiteNorm k x * (↑↑g : ℝ → ℝ) x ∂stdGaussian = 0 := by
    intro k
    have h := hg (hermiteNormLp k) (Submodule.subset_span ⟨k, rfl⟩)
    rw [L2.inner_def] at h
    have hae : (fun x => @inner ℝ ℝ _
        ((↑↑(hermiteNormLp k) : ℝ → ℝ) x) ((↑↑g : ℝ → ℝ) x)) =ᵐ[stdGaussian]
      (fun x => hermiteNorm k x * (↑↑g : ℝ → ℝ) x) := by
      simp only [hermiteNormLp]
      filter_upwards [(memLp_hermiteNorm k).coeFn_toLp] with x hx
      rw [hx, real_inner_eq_mul]
    rwa [integral_congr_ae hae] at h
  have hg_eval : ∀ n : ℕ, ∫ x, hermiteEval n x * (↑↑g : ℝ → ℝ) x ∂stdGaussian = 0 := by
    intro n
    have := hg_inner n
    simp only [hermiteNorm] at this
    have hfact : (0 : ℝ) < Real.sqrt ↑n.factorial :=
      Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos n))
    have heq : (fun x => hermiteEval n x / Real.sqrt ↑n.factorial * (↑↑g : ℝ → ℝ) x) =
        (fun x => (1 / Real.sqrt ↑n.factorial) * (hermiteEval n x * (↑↑g : ℝ → ℝ) x)) := by
      ext x; ring
    rw [heq, integral_const_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; linarith [div_pos one_pos hfact]
    · exact h
  have hg_memLp : MemLp (↑↑g : ℝ → ℝ) 2 stdGaussian := Lp.memLp g
  have hg_ae := hermite_span_dense_L2 _ hg_memLp hg_eval
  exact Lp.ext (hg_ae.trans (Lp.coeFn_zero ℝ 2 stdGaussian).symm)

/-- The Hermite functions form a Hilbert basis of L²(γ). -/
private noncomputable def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 stdGaussian) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_hermiteNormLp hermiteNormLp_orthogonal_eq_bot

/-- Parseval identity for Hermite functions: `∑' k, aₖ² = ∫ f²`.
The proof constructs the Hermite `HilbertBasis` in `Lp ℝ 2 stdGaussian` via
`hermiteNorm_inner` → Orthonormal → orthogonal complement ⊥ →
`HilbertBasis.mkOfOrthogonalEqBot` → `hasSum_inner_mul_inner` (Parseval). -/
private lemma hermite_parseval (f : ℝ → ℝ) (hf : MemLp f 2 stdGaussian) :
    HasSum (fun k => hermiteCoeff f k ^ 2) (∫ x, f x ^ 2 ∂stdGaussian) := by
  set F := hf.toLp f
  -- Coefficients: ⟪bₖ, F⟫ = aₖ
  have hcoeff : ∀ k, @inner ℝ _ _ (hermiteBasis k) F = hermiteCoeff f k := by
    intro k
    rw [L2.inner_def]
    simp only [hermiteBasis, HilbertBasis.coe_mkOfOrthogonalEqBot, hermiteNormLp, hermiteCoeff]
    apply integral_congr_ae
    filter_upwards [(memLp_hermiteNorm k).coeFn_toLp, hf.coeFn_toLp] with x hek hfx
    rw [hek, hfx, real_inner_eq_mul, mul_comm]
  -- Parseval: HasSum (fun i => ⟪F, bᵢ⟫ * ⟪bᵢ, F⟫) ⟪F, F⟫
  have hp := hermiteBasis.hasSum_inner_mul_inner F F
  -- Convert ⟪F, bₖ⟫ * ⟪bₖ, F⟫ = aₖ²
  have h1 : (fun i => @inner ℝ _ _ F (hermiteBasis i) * @inner ℝ _ _ (hermiteBasis i) F) =
      (fun k => hermiteCoeff f k ^ 2) := by
    ext k
    rw [show @inner ℝ _ _ F (hermiteBasis k) = @inner ℝ _ _ (hermiteBasis k) F from
      (real_inner_comm F (hermiteBasis k)).symm, hcoeff k]; ring
  rw [h1] at hp
  -- Convert ⟪F, F⟫ = ∫ f²
  have h2 : @inner ℝ _ _ F F = ∫ x, f x ^ 2 ∂stdGaussian := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hfx
    rw [hfx, real_inner_eq_mul]; ring
  rwa [h2] at hp

/-- Hermite Parseval identity for the tail:
for any ε > 0, the Hermite expansion eventually captures all of ‖f‖². -/
private lemma hermite_parseval_tail (f : ℝ → ℝ) (hf : MemLp f 2 stdGaussian) :
    ∀ ε > 0, ∃ N : ℕ,
    ∫ x, f x ^ 2 ∂stdGaussian -
      ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 < ε := by
  intro ε hε
  -- Convert HasSum to Tendsto along Finset.range
  have hp := hermite_parseval f hf
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg _)] at hp
  -- hp : Tendsto (fun n => ∑ i ∈ Finset.range n, aᵢ²) atTop (nhds (∫ f²))
  rw [Metric.tendsto_atTop] at hp
  obtain ⟨N, hN⟩ := hp ε hε
  exact ⟨N, by
    have h1 := hN N le_rfl
    rw [Real.dist_eq] at h1
    have h2 : ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 ≤ ∫ x, f x ^ 2 ∂stdGaussian :=
      hermite_bessel_finite f hf N
    linarith [abs_lt.mp h1]⟩

/-- **Coefficient bound for f'**: `∑_{k=1}^{N} aₖ² ≤ ∫ f'²`.
Uses Bessel for f' and the coefficient relation. -/
private lemma hermite_coeff_f'_bound (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian) (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (N : ℕ) :
    ∑ k ∈ Finset.range N, hermiteCoeff f (k + 1) ^ 2 ≤
      ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- From Bessel for f': ∑_{k < N} (∫ f'·eₖ)² ≤ ∫ f'²
  have hbessel := hermite_bessel_finite f' hf' N
  -- From coefficient relation: ∫ f'·eₖ = √(k+1) · aₖ₊₁
  -- So (∫ f'·eₖ)² = (k+1) · aₖ₊₁²
  -- Thus ∑_{k < N} (k+1)·aₖ₊₁² ≤ ∫ f'², and since k+1 ≥ 1: ∑ aₖ₊₁² ≤ ∫ f'²
  -- We need: ∑_{k < N} aₖ₊₁² ≤ ∑_{k < N} (∫ f'·eₖ)²
  suffices h : ∀ k, hermiteCoeff f (k + 1) ^ 2 ≤ hermiteCoeff f' k ^ 2 by
    exact le_trans (Finset.sum_le_sum fun k _ => h k) hbessel
  intro k
  -- hermiteCoeff f' k = ∫ f'·eₖ = √(k+1) · hermiteCoeff f (k+1)
  have hrel := integral_deriv_mul_hermiteNorm f f' k hf hf' hderiv
  -- hrel : ∫ f'·eₖ = √(k+1) · ∫ f·eₖ₊₁
  -- i.e. hermiteCoeff f' k = √(k+1) · hermiteCoeff f (k+1)
  have hcoeff : hermiteCoeff f' k = Real.sqrt (↑(k + 1)) * hermiteCoeff f (k + 1) := by
    exact hrel
  rw [hcoeff]
  have hsq : (Real.sqrt (↑(k + 1)) * hermiteCoeff f (k + 1)) ^ 2 =
      (↑(k + 1)) * hermiteCoeff f (k + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq]
  have hk1 : (1 : ℝ) ≤ ↑(k + 1) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  nlinarith [sq_nonneg (hermiteCoeff f (k + 1))]

/-! ## Infrastructure for Measure.pi fiber decomposition -/

/-- `Function.update x i t = Fin.insertNth i t (Fin.removeNth i x)`:
expressing `update` as `insertNth ∘ removeNth`, which connects
`Function.update` to the `piFinSuccAbove` decomposition. -/
private lemma update_eq_insertNth {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) (t : ℝ) :
    Function.update x i t = Fin.insertNth i t (Fin.removeNth i x) := by
  ext j
  by_cases h : j = i
  · subst h; simp [Fin.insertNth_apply_same, Function.update_self]
  · rw [Function.update_of_ne h]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    rw [← hk, Fin.insertNth_apply_succAbove]; simp [Fin.removeNth]

/-! ## Sorry-dependent declarations -/

/-- **1D Gaussian Poincaré core**: `Var(f) ≤ ∫ f'² dγ`.

Proof via Hermite expansion:
- Var(f) = ∫ f² - (∫ f)² = ∫ f² - a₀²
- For each N: Var(f) = δₙ + ∑_{k=1}^N aₖ² where δₙ = ∫ f² - ∑_{k=0}^N aₖ²
- By Bessel for f' + coefficient relation: ∑_{k=1}^N aₖ² ≤ ∫ f'²
- By Parseval tail (from density): δₙ → 0
- Conclusion: Var(f) ≤ ∫ f'² + ε for all ε > 0 -/
theorem gaussian_poincare_1d_core
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian := by
  -- Step 1: Var(f) = ∫ f² - (∫ f)²
  haveI : IsProbabilityMeasure stdGaussian := inferInstance
  have hvar : Var[f; stdGaussian] = ∫ x, f x ^ 2 ∂stdGaussian - (∫ x, f x ∂stdGaussian) ^ 2 := by
    rw [variance_eq_sub hf]
    simp [Pi.pow_apply]
  -- Step 2: (∫ f)² = a₀²
  have ha0 : (∫ x, f x ∂stdGaussian) = hermiteCoeff f 0 := (hermiteCoeff_zero f).symm
  -- Step 3: It suffices to show ∀ε > 0, Var ≤ ∫ f'² + ε
  suffices h : ∀ ε > (0 : ℝ), Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian + ε by
    by_contra hlt
    push_neg at hlt
    have hε : (0 : ℝ) < (Var[f; stdGaussian] - ∫ x, f' x ^ 2 ∂stdGaussian) / 2 := by linarith
    have := h _ hε
    linarith
  intro ε hε
  -- Step 4: Get N from Parseval tail
  obtain ⟨N, hN⟩ := hermite_parseval_tail f hf ε hε
  -- Step 5: Decompose Var(f)
  rw [hvar, ha0]
  -- Var(f) = (∫ f² - ∑_{k=0}^{N+1} aₖ²) + (∑_{k=0}^{N+1} aₖ² - a₀²)
  --        = δ_{N+1} + ∑_{k=1}^{N+1} aₖ²
  -- Choose N large enough via Parseval tail
  have hδ : ∫ x, f x ^ 2 ∂stdGaussian -
      ∑ k ∈ Finset.range (N + 1), hermiteCoeff f k ^ 2 < ε := by
    have hle : ∑ k ∈ Finset.range N, hermiteCoeff f k ^ 2 ≤
        ∑ k ∈ Finset.range (N + 1), hermiteCoeff f k ^ 2 := by
      rw [Finset.sum_range_succ]
      linarith [sq_nonneg (hermiteCoeff f N)]
    linarith
  -- Split the sum: ∑_{k < N+1} = a₀² + ∑_{k=1}^{N}
  have hsum_split : ∑ k ∈ Finset.range (N + 1), hermiteCoeff f k ^ 2 =
      hermiteCoeff f 0 ^ 2 + ∑ k ∈ Finset.range N, hermiteCoeff f (k + 1) ^ 2 := by
    rw [Finset.sum_range_succ']; ring
  -- Bound ∑_{k=1}^N aₖ₊₁² ≤ ∫ f'²
  have hcoeff_bound := hermite_coeff_f'_bound f f' hf hf' hderiv N
  -- Combine
  linarith [hδ, hsum_split, hcoeff_bound]

theorem gaussian_poincare_1d
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    Var[f; stdGaussian] ≤ ∫ x, f' x ^ 2 ∂stdGaussian :=
  gaussian_poincare_1d_core f f' hf hf' hderiv

/-! ## Gaussian hypercontractivity: W^{1,2}(γ) → L⁴(γ)

The Nelson hypercontractivity theorem (1973) states that if `f ∈ W^{1,2}(γ)`
(i.e., `f, f' ∈ L²(γ)` with `HasDerivAt`), then `f ∈ L⁴(γ)`.

### Proof architecture

1. **Hermite partial sums converge in L²**: By Parseval (`hermite_parseval`),
   `S_N f = ∑_{k<N} aₖ eₖ → f` in L²(γ).
2. **Uniform L⁴ bound for partial sums**: The Hermite product linearization
   formula gives `‖S_N f‖₄⁴ ≤ C · (‖f‖₂² + ‖f'‖₂²)²` uniformly in N.
3. **Fatou's lemma**: Extract an a.e. convergent subsequence from the L²
   convergence, then apply Fatou's lemma with the uniform L⁴ bound.

### Status
The theorem is sorry-ed, blocked by the Hermite product linearization formula
`Hₘ · Hₙ = ∑_{k} C(m,k) · C(n,k) · k! · H_{m+n-2k}` which requires ~150
lines of algebraic formalization not present in Mathlib v4.28. -/

/-- **Gaussian hypercontractivity (W^{1,2}(γ) → L⁴(γ))**: If `f ∈ L²(γ)` and `f' ∈ L²(γ)`
with `HasDerivAt`, then `f ∈ L⁴(γ)`.

This is the 1D case of the Nelson hypercontractivity theorem (1973).

**Blocker**: Requires the Hermite product linearization formula, which gives a
uniform L⁴ bound for the Hermite partial sums `S_N f`. The reduction via
Fatou's lemma (L² convergence → a.e. subsequence → Fatou → MemLp) then
gives the result.

**Estimated effort**: ~200 lines (Hermite linearization + L⁴ bound + Fatou). -/
theorem memLp_four_of_W12_gaussian
    (f f' : ℝ → ℝ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    MemLp f 4 stdGaussian := by
  sorry

/-- The fiber average: integrate f over coordinate i, keeping other coordinates fixed. -/
private noncomputable def fiberAvg (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ t, f (Function.update x i t) ∂stdGaussian

/-- L² minimality of conditional expectation: `∫ (f - E[f|G])² ≤ ∫ (f - g)²`
for any `G`-measurable `g ∈ L²`. Proved via orthogonality in L². -/
private lemma integral_sq_sub_condExp_le_integral_sq_sub
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : @Measure Ω m0}
    [@IsProbabilityMeasure Ω m0 μ]
    (hm : m ≤ m0) (f g : Ω → ℝ)
    (hf : MemLp f 2 μ)
    (hg_meas : StronglyMeasurable[m] g)
    (hg_lp : MemLp g 2 μ) :
    ∫ x, (f x - (μ[f | m]) x) ^ 2 ∂μ ≤ ∫ x, (f x - g x) ^ 2 ∂μ := by
  set E_f := (μ[f | m]) with hEf_def
  have hEf_lp : MemLp E_f 2 μ := hf.condExp
  have hf_sub_Ef : MemLp (f - E_f) 2 μ := hf.sub hEf_lp
  have hEf_sub_g : MemLp (E_f - g) 2 μ := hEf_lp.sub hg_lp
  -- Key: ∫ (f - E_f) * (E_f - g) = 0 (orthogonality)
  have hcross : ∫ x, (f x - E_f x) * (E_f x - g x) ∂μ = 0 := by
    have hEf_g_meas : AEStronglyMeasurable[m] (E_f - g) μ :=
      (stronglyMeasurable_condExp.sub hg_meas).aestronglyMeasurable
    have h1 : ∫ x, (f x - E_f x) * (E_f x - g x) ∂μ =
        ∫ x, f x * (E_f x - g x) ∂μ - ∫ x, E_f x * (E_f x - g x) ∂μ := by
      have hint_a : Integrable (fun x => f x * (E_f x - g x)) μ :=
        hf.integrable_mul hEf_sub_g (𝕜 := ℝ)
      have hint_b : Integrable (fun x => E_f x * (E_f x - g x)) μ :=
        hEf_lp.integrable_mul hEf_sub_g (𝕜 := ℝ)
      have heq : ∀ x, (f x - E_f x) * (E_f x - g x) =
          f x * (E_f x - g x) - E_f x * (E_f x - g x) := by intro x; ring
      rw [show (fun x => (f x - E_f x) * (E_f x - g x)) =
          fun x => f x * (E_f x - g x) - E_f x * (E_f x - g x)
          from funext heq]
      exact integral_sub hint_a hint_b
    have h2 : ∫ x, f x * (E_f x - g x) ∂μ =
        ∫ x, E_f x * (E_f x - g x) ∂μ := by
      -- Pull-out: μ[f * h | m] =ᵐ μ[f|m] * h where h = E_f - g is m-measurable
      set h := E_f - g
      have hfh_int : Integrable (f * h) μ :=
        (hf.integrable_mul hEf_sub_g (𝕜 := ℝ)).congr (ae_of_all _ fun x => rfl)
      have hf_int : Integrable f μ := hf.integrable one_le_two
      have hpull := condExp_mul_of_aestronglyMeasurable_right hEf_g_meas hfh_int hf_int
      -- hpull : μ[f * h | m] =ᵐ μ[f|m] * h = E_f * h
      -- Taking integrals of both sides:
      -- ∫ μ[f*h|m] = ∫ f*h (tower property)
      -- ∫ E_f*h = ∫ μ[f|m]*h (by definition)
      have htower : ∫ x, (μ[f * h | m]) x ∂μ = ∫ x, (f * h) x ∂μ :=
        integral_condExp hm
      have hrhs : ∫ x, (μ[f * h | m]) x ∂μ = ∫ x, E_f x * h x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hpull] with x hx
        simp only [Pi.mul_apply] at hx
        exact hx
      -- Now: ∫ f*h = ∫ E_f*h
      have hkey : ∫ x, (f * h) x ∂μ = ∫ x, E_f x * h x ∂μ := by
        rw [← htower, hrhs]
      -- Convert from f * h to f x * (E_f x - g x)
      convert hkey using 1 <;> (congr 1; ext x; simp [h, Pi.mul_apply, Pi.sub_apply])
    linarith [h1, h2]
  -- ∫(f-g)² ≥ ∫(f-Ef)² via: (f-g) = (f-Ef) + (Ef-g), cross term = 0
  -- Direct approach: ∫(f-g)² = ∫(f-Ef)² + ∫(Ef-g)² (Pythagorean)
  have hfg_eq : ∀ x, (f x - g x) ^ 2 = (f x - E_f x) ^ 2 + (E_f x - g x) ^ 2 +
      2 * ((f x - E_f x) * (E_f x - g x)) := by intro x; ring
  have hfg_eq2 : ∀ x, (f x - g x) ^ 2 = ((f x - E_f x) ^ 2 + (E_f x - g x) ^ 2) +
      2 * ((f x - E_f x) * (E_f x - g x)) := by intro x; ring
  have hint1 : Integrable (fun x => (f x - E_f x) ^ 2 + (E_f x - g x) ^ 2) μ :=
    hf_sub_Ef.integrable_sq.add hEf_sub_g.integrable_sq
  have hint2 : Integrable (fun x => 2 * ((f x - E_f x) * (E_f x - g x))) μ :=
    (hf_sub_Ef.integrable_mul hEf_sub_g (𝕜 := ℝ)).const_mul 2
  have h_expand : ∫ x, (f x - g x) ^ 2 ∂μ =
      (∫ x, (f x - E_f x) ^ 2 ∂μ + ∫ x, (E_f x - g x) ^ 2 ∂μ) +
      2 * ∫ x, (f x - E_f x) * (E_f x - g x) ∂μ := by
    calc ∫ x, (f x - g x) ^ 2 ∂μ
        = ∫ x, ((f x - E_f x) ^ 2 + (E_f x - g x) ^ 2) +
            2 * ((f x - E_f x) * (E_f x - g x)) ∂μ :=
          integral_congr_ae (ae_of_all _ hfg_eq2)
      _ = ∫ x, ((f x - E_f x) ^ 2 + (E_f x - g x) ^ 2) ∂μ +
            ∫ x, 2 * ((f x - E_f x) * (E_f x - g x)) ∂μ :=
          integral_add hint1 hint2
      _ = (∫ x, (f x - E_f x) ^ 2 ∂μ + ∫ x, (E_f x - g x) ^ 2 ∂μ) +
            2 * ∫ x, (f x - E_f x) * (E_f x - g x) ∂μ := by
          congr 1
          · exact integral_add hf_sub_Ef.integrable_sq hEf_sub_g.integrable_sq
          · exact integral_const_mul 2 _
  rw [h_expand, hcross, mul_zero, add_zero]
  have : 0 ≤ ∫ x, (E_f x - g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  linarith

/-- Variance of the 1D fiber is bounded by derivative L²-norm, for each fixed
value of the other coordinates. This is `gaussian_poincare_1d_core` applied
to `t ↦ f(update x i t)` with derivative `t ↦ gradf i (update x i t)`. -/
private lemma fiber_variance_le_fiber_grad_sq
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {gradf : Fin n → (Fin n → ℝ) → ℝ}
    {i : Fin n} (x : Fin n → ℝ)
    (hf_fiber : MemLp (fun t => f (Function.update x i t)) 2 stdGaussian)
    (hg_fiber : MemLp (fun t => gradf i (Function.update x i t)) 2 stdGaussian)
    (hderiv : ∀ t, HasDerivAt (fun s => f (Function.update x i s)) (gradf i (Function.update x i t)) t) :
    ∫ t, (f (Function.update x i t) - ∫ s, f (Function.update x i s) ∂stdGaussian) ^ 2
      ∂stdGaussian ≤
    ∫ t, (gradf i (Function.update x i t)) ^ 2 ∂stdGaussian := by
  -- The LHS is Var_γ[φ] where φ(t) = f(update x i t)
  -- Apply gaussian_poincare_1d_core
  set φ := fun t => f (Function.update x i t)
  set φ' := fun t => gradf i (Function.update x i t)
  have hpoincare := gaussian_poincare_1d_core φ φ' hf_fiber hg_fiber (by
    intro t
    exact hderiv t)
  -- hpoincare : Var[φ; stdGaussian] ≤ ∫ (φ')² dγ
  -- Need to convert Var[φ; γ] to ∫ (φ - E[φ])² dγ
  have hVar : Var[φ; stdGaussian] = ∫ t, (φ t - ∫ s, φ s ∂stdGaussian) ^ 2 ∂stdGaussian := by
    rw [variance_eq_integral hf_fiber.aemeasurable]
  linarith [hVar, hpoincare]

/-- **Disintegration identity for Measure.pi**.

For the standard Gaussian product measure and coordinate `i`, the conditional
expectation of `g` given all other coordinates equals the fiber average:

  `E[g | G_i](x) =ᵃᵉ ∫ g(update x i t) dγ(t)`

The proof uses `ae_eq_condExp_of_forall_setIntegral_eq` with three conditions:
(1) Integrability of the fiber average (via Fubini on the product decomposition).
(2) Set integral equality: both sides equal `∫_S h dμ_rest` via `setIntegral_map`
    (LHS) and `setIntegral_preimage_emb` + `setIntegral_prod_swap` (RHS), using
    `sigmaAlgExcept i ≤ comap (removeNth i) pi` to extract the base set `S`.
(3) `AEStronglyMeasurable[sigmaAlgExcept i]`: the fiber average factors as
    `h ∘ removeNth i` where `removeNth i` is `sigmaAlgExcept`-measurable. -/
private lemma condExp_eq_fiberAvg_pi
    {m : ℕ} (i : Fin (m + 1))
    (g : (Fin (m + 1) → ℝ) → ℝ)
    (hg : Integrable g (stdGaussianPi (m + 1))) :
    (stdGaussianPi (m + 1))[g | sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i]
      =ᵐ[stdGaussianPi (m + 1)]
    fun x => ∫ t, g (Function.update x i t) ∂stdGaussian := by
  set mu_pi := stdGaussianPi (m + 1)
  set gamma := stdGaussian
  set mu_rest := Measure.pi (fun _ : Fin m => stdGaussian)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hmp : MeasurePreserving e mu_pi (gamma.prod mu_rest) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => stdGaussian) i
  have hm_le := sigmaAlgExcept_le (X := fun _ : Fin (m + 1) => ℝ) i
  haveI : IsProbabilityMeasure mu_pi := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin (m + 1) => stdGaussian))
    exact Measure.pi.instIsProbabilityMeasure _
  haveI : SigmaFinite (mu_pi.trim hm_le) := by
    have : IsFiniteMeasure (mu_pi.trim hm_le) := by
      constructor; rw [trim_measurableSet_eq hm_le MeasurableSet.univ]
      exact measure_lt_top _ _
    exact this.toSigmaFinite
  -- g o e.symm integrable on the product space
  have hg_prod : Integrable (fun p : ℝ × (Fin m → ℝ) => g (e.symm p))
      (gamma.prod mu_rest) := by
    rw [show (fun p => g (e.symm p)) = g ∘ e.symm from rfl]
    exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hg
  -- h(rest) = ∫ g(e.symm(t,rest)) dγ(t), integrable on mu_rest via Fubini
  set h : (Fin m → ℝ) → ℝ :=
    fun rest => ∫ t, g (e.symm (t, rest)) ∂gamma with hh_def
  have hh_int : Integrable h mu_rest := hg_prod.swap.integral_prod_left
  -- fAvg(x) = h(removeNth i x)
  have hfAvg_eq : ∀ x, (∫ t, g (Function.update x i t) ∂gamma) = h (Fin.removeNth i x) := by
    intro x; show _ = ∫ t, g (e.symm (t, Fin.removeNth i x)) ∂gamma
    congr 1; ext t
    simp [e, Fin.insertNthEquiv, MeasurableEquiv.piFinSuccAbove]
  -- removeNth i is measurable from sigmaAlgExcept to MeasurableSpace.pi
  have hremove_meas : @Measurable _ _
      (sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i) MeasurableSpace.pi
      (Fin.removeNth i : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) := by
    refine @measurable_pi_iff _ _ _
      (sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i) _ _ |>.mpr ?_
    intro k
    show @Measurable _ _
      (sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i) _
      (fun x : Fin (m + 1) → ℝ => x (i.succAbove k))
    exact Measurable.of_comap_le
      (le_iSup₂_of_le (i.succAbove k) (by simp [Fin.succAbove_ne i k]) le_rfl)
  -- removeNth i is also measurable in the full sigma algebra (pi -> pi)
  have hremove_meas_full : Measurable (Fin.removeNth i : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) :=
    measurable_pi_iff.mpr (fun k => measurable_pi_apply (i.succAbove k))
  -- map (removeNth i) mu_pi = mu_rest (via product decomposition + marginalization)
  have hmap_remove : Measure.map (Fin.removeNth i) mu_pi = mu_rest := by
    have h1 : Fin.removeNth i = Prod.snd ∘ e := by
      ext x; simp [e, Fin.removeNth, MeasurableEquiv.piFinSuccAbove]
    rw [h1, ← Measure.map_map measurable_snd e.measurable, hmp.map_eq]
    exact Measure.snd_prod
  -- fAvg = h ∘ removeNth i is integrable on mu_pi
  have hfAvg_int : Integrable (fun x => ∫ t, g (Function.update x i t) ∂gamma)
      mu_pi := by
    have : Integrable (h ∘ Fin.removeNth i) mu_pi :=
      (hmap_remove ▸ hh_int).comp_measurable hremove_meas_full
    exact this.congr (Eventually.of_forall fun x => (hfAvg_eq x).symm)
  -- Use ae_eq_condExp_of_forall_setIntegral_eq
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm_le hg ?_ ?_ ?_).symm
  -- (1) IntegrableOn fAvg for finite-measure sigmaAlgExcept-measurable sets
  · intro s _hs _hmu
    exact hfAvg_int.integrableOn
  -- (2) Set integral equality: ∫_s fAvg dπ = ∫_s g dπ
  · intro s hs _hmu
    -- sigmaAlgExcept i ≤ comap (removeNth i) pi
    have hle_comap : sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i ≤
        MeasurableSpace.comap (Fin.removeNth i) MeasurableSpace.pi := by
      unfold sigmaAlgExcept
      refine iSup₂_le ?_
      intro j hj; simp at hj
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
      rw [← hk, show (fun x : Fin (m + 1) → ℝ => x (i.succAbove k)) =
          (fun y : Fin m → ℝ => y k) ∘ (Fin.removeNth i) from by
          ext x; simp [Fin.removeNth],
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (le_iSup (fun a => MeasurableSpace.comap
        (fun (b : Fin m → ℝ) => b a) Real.measurableSpace) k)
    -- Extract S with s = removeNth i ⁻¹' S
    have hms : @MeasurableSet _
        (MeasurableSpace.comap (Fin.removeNth i) MeasurableSpace.pi) s :=
      hle_comap s hs
    rw [MeasurableSpace.measurableSet_comap] at hms
    obtain ⟨S, hS_meas, hS_eq⟩ := hms
    -- (e x).2 = removeNth i x
    have hsnd : ∀ x, (e x).2 = Fin.removeNth i x := fun x => by
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    -- Both sides = ∫ rest in S, h rest dmu_rest
    -- LHS via setIntegral_map
    have hlhs : ∫ x in s, (fun x => ∫ t, g (Function.update x i t) ∂gamma) x ∂mu_pi =
        ∫ rest in S, h rest ∂mu_rest := by
      simp only []
      simp_rw [hfAvg_eq]
      rw [← hS_eq, ← hmap_remove]
      exact (setIntegral_map hS_meas
        (hmap_remove ▸ hh_int.aestronglyMeasurable)
        hremove_meas_full.aemeasurable).symm
    -- RHS via Fubini on product decomposition
    have he_preimage : e ⁻¹' (Set.univ ×ˢ S) = Fin.removeNth i ⁻¹' S := by
      ext x; simp [Set.mem_preimage, Set.mem_prod, hsnd]
    have hrhs : ∫ x in s, g x ∂mu_pi = ∫ rest in S, h rest ∂mu_rest := by
      rw [← hS_eq, ← he_preimage]
      -- Step 1: change of variables via e
      have step1 := hmp.setIntegral_preimage_emb e.measurableEmbedding
        (fun p : ℝ × (Fin m → ℝ) => g (e.symm p)) (Set.univ ×ˢ S)
      simp only [MeasurableEquiv.symm_apply_apply] at step1
      -- Step 2: Fubini via swap + setIntegral_prod
      rw [step1, ← setIntegral_prod_swap]
      have key := setIntegral_prod
        (fun z : (Fin m → ℝ) × ℝ => g (e.symm z.swap))
        ((hg_prod.integrableOn (s := Set.univ ×ˢ S)).swap)
      simp only [setIntegral_univ, Prod.swap_prod_mk] at key
      exact key
    rw [hlhs, hrhs]
  -- (3) AEStronglyMeasurable w.r.t. sigmaAlgExcept
  · -- fAvg(x) = h(removeNth i x), h AESM on mu_rest, removeNth i sigmaAlgExcept-meas
    -- Construct: mk of h is StronglyMeasurable, compose with removeNth to get SM[sigmaAlgExcept]
    have hh_aesm : AEStronglyMeasurable h mu_rest := hh_int.aestronglyMeasurable
    -- g' = mk of h, StronglyMeasurable[pi] and h =ᵃᵉ g'
    set g' := hh_aesm.mk h with hg'_def
    have hg'_sm : StronglyMeasurable g' := hh_aesm.stronglyMeasurable_mk
    have hg'_ae : h =ᵐ[mu_rest] g' := hh_aesm.ae_eq_mk
    -- g' ∘ removeNth is StronglyMeasurable[sigmaAlgExcept]
    have hg'_comp_sm : @StronglyMeasurable _ _ _
        (sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i) (g' ∘ Fin.removeNth i) :=
      hg'_sm.comp_measurable hremove_meas
    -- fAvg =ᵃᵉ g' ∘ removeNth (pull back h =ᵃᵉ g' via QMP)
    have hqmp_remove : Measure.QuasiMeasurePreserving (Fin.removeNth i) mu_pi mu_rest := by
      constructor
      · exact hremove_meas_full
      · rw [hmap_remove]
    have hpull_ae : ∀ᵐ x ∂mu_pi, h (Fin.removeNth i x) = g' (Fin.removeNth i x) :=
      hqmp_remove.ae hg'_ae
    refine ⟨g' ∘ Fin.removeNth i, hg'_comp_sm, ?_⟩
    filter_upwards [hpull_ae] with x hx
    rw [hfAvg_eq x, Function.comp_apply, hx]

/-- `f ∈ L²(π)` implies the 1D fiber `t ↦ f(update x i t)` is in `L²(γ)` for a.e. `x`.
This is a Fubini consequence: `f² ∈ L¹(π)` and the product decomposition via
`measurePreserving_piFinSuccAbove` give `∫ f(update x i t)² dγ(t) < ∞` a.e.,
combined with `AEStronglyMeasurable` from the product structure. -/
private lemma ae_memLp_fiber
    {m : ℕ} (i : Fin (m + 1)) (f : (Fin (m + 1) → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi (m + 1))) :
    ∀ᵐ x ∂(stdGaussianPi (m + 1)),
      MemLp (fun t => f (Function.update x i t)) 2 stdGaussian := by
  set mu_pi := stdGaussianPi (m + 1)
  set gamma := stdGaussian
  set mu_rest := Measure.pi (fun _ : Fin m => stdGaussian)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i
  have hmp : MeasurePreserving e mu_pi (gamma.prod mu_rest) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => stdGaussian) i
  -- Key equation: e.symm(t, (e x).2) = update x i t
  have heq : ∀ x t, (e.symm (t, (e x).2) : Fin (m+1) → ℝ) = Function.update x i t := by
    intro x t; simp [e, Fin.insertNthEquiv, MeasurableEquiv.piFinSuccAbove]
  -- AEStronglyMeasurable of f o e.symm on the product space
  have hf_aesm_prod : AEStronglyMeasurable
      (fun p : ℝ × (Fin m → ℝ) => f (e.symm p)) (gamma.prod mu_rest) := by
    have h1 : AEStronglyMeasurable (f ∘ (e.symm ∘ e)) mu_pi := by
      simp only [MeasurableEquiv.symm_comp_self]; exact hf.aestronglyMeasurable
    rw [show (f ∘ (e.symm ∘ e)) = ((f ∘ e.symm) ∘ e) from by
      ext; simp [Function.comp]] at h1
    exact (hmp.aestronglyMeasurable_comp_iff e.measurableEmbedding).mp h1
  -- Fiber AEStronglyMeasurable: for a.e. rest, the slice is AESM
  have hfiber_aesm : ∀ᵐ rest ∂mu_rest,
      AEStronglyMeasurable (fun t => f (e.symm (t, rest))) gamma :=
    hf_aesm_prod.prodMk_right
  -- Transfer f^2 integrability to product space
  have hf2_prod : Integrable
      (fun p : ℝ × (Fin m → ℝ) => f (e.symm p) ^ 2) (gamma.prod mu_rest) := by
    rw [show (fun p : ℝ × (Fin m → ℝ) => f (e.symm p) ^ 2) =
        (fun x => f x ^ 2) ∘ e.symm from by ext p; simp [Function.comp]]
    exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf.integrable_sq
  -- Fiber norm-squared integrability via Fubini
  have hfiber_sq : ∀ᵐ rest ∂mu_rest,
      Integrable (fun t => ‖f (e.symm (t, rest))‖ ^ 2) gamma :=
    (show Integrable (fun p : ℝ × (Fin m → ℝ) => ‖f (e.symm p)‖ ^ 2)
        (gamma.prod mu_rest) from by
      convert hf2_prod using 1; ext p; simp [sq_abs]).prod_left_ae
  -- Combine AESM + norm-sq integrability to get MemLp 2 for a.e. rest
  have hfiber_memLp : ∀ᵐ rest ∂mu_rest,
      MemLp (fun t => f (e.symm (t, rest))) 2 gamma := by
    filter_upwards [hfiber_aesm, hfiber_sq] with rest haesm hint
    exact (memLp_two_iff_integrable_sq_norm haesm).mpr hint
  -- Pull back from mu_rest to mu_pi via Prod.snd o e
  have hqmp : Measure.QuasiMeasurePreserving (Prod.snd ∘ e) mu_pi mu_rest :=
    Measure.quasiMeasurePreserving_snd.comp hmp.quasiMeasurePreserving
  have hpull : ∀ᵐ x ∂mu_pi,
      MemLp (fun t => f (e.symm (t, (e x).2))) 2 gamma := hqmp.ae hfiber_memLp
  -- Convert: f(e.symm(t, (e x).2)) = f(update x i t)
  filter_upwards [hpull] with x hx
  exact hx.ae_eq (Eventually.of_forall fun t => by rw [heq])

/-- Fiberwise Poincaré bound for `n = m+1`. Uses:
1. Disintegration: `condExp[g|G_i] =ᵃᵉ fiberAvg` to convert condVar/condExp to fiber integrals
2. `condVar = E[f²|G] - E[f|G]²` (Mathlib's `condVar_ae_eq_condExp_sq_sub_sq_condExp`)
3. 1D Gaussian Poincaré (`gaussian_poincare_1d_core`) applied to each fiber -/
private lemma condVar_le_condExp_gradf_sq_ae_succ
    {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ)
    (gradf : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi (m + 1)))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi (m + 1)))
    (hderiv : ∀ x i,
      HasDerivAt (fun t => f (Function.update x i t))
        (gradf i x) (x i))
    (i : Fin (m + 1)) :
    Var[f; stdGaussianPi (m + 1) |
      sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i]
      ≤ᵐ[stdGaussianPi (m + 1)]
    (stdGaussianPi (m + 1))[(fun x => (gradf i x) ^ 2) |
      sigmaAlgExcept (X := fun _ : Fin (m + 1) => ℝ) i] := by
  haveI : IsFiniteMeasure (stdGaussianPi (m + 1)) := by
    unfold stdGaussianPi; infer_instance
  haveI : IsProbabilityMeasure (stdGaussianPi (m + 1)) := by
    unfold stdGaussianPi; exact Measure.pi.instIsProbabilityMeasure _
  have hm_le := sigmaAlgExcept_le (X := fun _ : Fin (m + 1) => ℝ) i
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm_le hf,
    condExp_eq_fiberAvg_pi i f (hf.integrable one_le_two),
    condExp_eq_fiberAvg_pi i (f ^ 2) (hf.integrable_sq),
    condExp_eq_fiberAvg_pi i (fun x => (gradf i x) ^ 2)
      ((hgradf i).integrable_sq),
    ae_memLp_fiber i f hf,
    ae_memLp_fiber i (gradf i) (hgradf i)]
    with x hcv_x hef_x hef2_x heg_x hf_fib hg_fib
  simp only [Pi.sub_apply, Pi.pow_apply] at hcv_x ⊢
  rw [hcv_x, hef2_x, heg_x, hef_x]; simp only [Pi.pow_apply]
  -- Goal: ∫ f(update x i t)² dγ - (∫ f(update x i t) dγ)² ≤ ∫ (gradf i (update x i t))² dγ
  -- This is Var_γ[φ] ≤ ∫ (φ')² dγ, which is 1D Gaussian Poincaré.
  have hderiv_fiber : ∀ t,
      HasDerivAt (fun s => f (Function.update x i s))
        (gradf i (Function.update x i t)) t := by
    intro t; have h := hderiv (Function.update x i t) i
    have h1 : (fun s => f (Function.update (Function.update x i t) i s)) =
        (fun s => f (Function.update x i s)) := by
      ext s; congr 1; ext j
      by_cases hj : j = i <;> simp [Function.update, hj]
    rw [h1, Function.update_self i t x] at h; exact h
  have hvar := variance_eq_sub hf_fib
  simp only [Pi.pow_apply] at hvar
  linarith [hvar, gaussian_poincare_1d_core _ _ hf_fib hg_fib hderiv_fiber]

/-- **Fiberwise Poincaré bound for conditional variance**.

For the standard Gaussian product measure `π = γ^n` on `Fin n → ℝ`, and coordinate `i`,
the conditional variance of `f` given all other coordinates is bounded a.e. by the
conditional expectation of `(∂ᵢf)²`:

  `condVar[f; π | G_i] ≤ᵃᵉ π[(∂ᵢf)² | G_i]`

where `G_i = sigmaAlgExcept i`.

**Proof**: For `n = 0`, vacuous (no coordinates). For `n = m+1`, uses:
1. Disintegration identity (`condExp_eq_fiberAvg_pi`): converts abstract
   `condVar`/`condExp` to concrete fiber integrals via `Function.update x i ·`
2. Fiber MemLp (`ae_memLp_fiber`): `f ∈ L²(π)` implies fiber `∈ L²(γ)` a.e.
3. `condVar = E[f²|G] - E[f|G]²` (Mathlib)
4. 1D Gaussian Poincaré (`gaussian_poincare_1d_core`) on each fiber -/
private lemma condVar_le_condExp_gradf_sq_ae
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i,
      HasDerivAt (fun t => f (Function.update x i t))
        (gradf i x) (x i))
    (i : Fin n) :
    Var[f; stdGaussianPi n |
      sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]
      ≤ᵐ[stdGaussianPi n]
    (stdGaussianPi n)[(fun x => (gradf i x) ^ 2) |
      sigmaAlgExcept (X := fun _ : Fin n => ℝ) i] := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m => exact condVar_le_condExp_gradf_sq_ae_succ f gradf hf hgradf hderiv i

/-- **Per-coordinate Poincaré bound core**.

For each coordinate `i`, `∫ (f - E[f|G_i])² dπ ≤ ∫ (∂ᵢf)² dπ`.

Proof:
1. Rewrite LHS as `E[condVar[f|G_i]]` via `efron_stein_term_eq_integral_condVar_exceptCoord`
2. Apply `condVar ≤ᵃ·ₑ condExp[(∂ᵢf)²|G_i]` (see `condVar_le_condExp_gradf_sq_ae`)
3. Integrate both sides via `integral_mono_ae`
4. Simplify RHS via tower law: `∫ E[(∂ᵢf)²|G_i] = ∫ (∂ᵢf)²` (`integral_condExp`) -/
theorem gaussian_poincare_coord_bound_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i,
      HasDerivAt (fun t => f (Function.update x i t))
        (gradf i x) (x i)) :
    ∀ i : Fin n,
      ∫ x, (f x - condExpExceptCoord
        (fun _ : Fin n => stdGaussian) i f x) ^ 2
        ∂(stdGaussianPi n)
        ≤
      ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  intro i
  haveI : IsFiniteMeasure (stdGaussianPi n) := by
    unfold stdGaussianPi; infer_instance
  have hm : sigmaAlgExcept (X := fun _ : Fin n => ℝ) i ≤
      (inferInstance : MeasurableSpace (Fin n → ℝ)) :=
    sigmaAlgExcept_le _
  -- Step 1: Rewrite LHS as E[condVar[f|G_i]]
  have hstep1 := efron_stein_term_eq_integral_condVar_exceptCoord
    (μ := fun _ : Fin n => stdGaussian) i f hf
  simp only [stdGaussianPi] at hstep1 ⊢
  rw [hstep1]
  -- Step 2: a.e. bound condVar ≤ condExp[(gradf i)²|G_i]
  have hbound := condVar_le_condExp_gradf_sq_ae f gradf hf hgradf hderiv i
  simp only [stdGaussianPi] at hbound
  -- Step 3: Integrate + tower law
  calc ∫ x, (Var[f; Measure.pi fun _ : Fin n => stdGaussian |
        sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]) x
        ∂(Measure.pi fun _ : Fin n => stdGaussian)
      ≤ ∫ x, ((Measure.pi fun _ : Fin n => stdGaussian)[
        (fun x => (gradf i x) ^ 2) |
        sigmaAlgExcept (X := fun _ : Fin n => ℝ) i]) x
        ∂(Measure.pi fun _ : Fin n => stdGaussian) :=
        integral_mono_ae integrable_condExp integrable_condExp hbound
    _ = ∫ x, (gradf i x) ^ 2
        ∂(Measure.pi fun _ : Fin n => stdGaussian) :=
        integral_condExp hm

/-- **Multi-dimensional Gaussian Poincaré inequality** (Corollary 3.2). -/
theorem gaussian_poincare
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    Var[f; stdGaussianPi n] ≤
      ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) :=
  gaussian_poincare_of_efron_stein n f gradf
    (efron_stein (μ := fun _ : Fin n => stdGaussian) f hf)
    (gaussian_poincare_coord_bound_core n f gradf hf hgradf hderiv)

end

import Statlean.Variance.EfronStein
import Statlean.Gaussian.Hermite
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Gaussian Poincaré Inequality

## Proved (zero sorry)
- `gaussian_poincare_of_integral_bound` — wrapper
- `gaussian_poincare_of_efron_stein` — via Efron-Stein + coordinate bound
- `gaussian_poincare_of_condVar_sum` — via conditional variance sum

## Sorry gaps
- `gaussian_poincare_1d_core` — needs Hermite coefficient relation + Parseval
- `gaussian_poincare_coord_bound_core` — needs Fubini + 1D Poincaré
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

/-- **Per-coordinate Poincaré bound core** (sorry — needs Fubini + 1D Poincaré). -/
theorem gaussian_poincare_coord_bound_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hderiv : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    ∀ i : Fin n,
      ∫ x, (f x - condExpExceptCoord (fun _ : Fin n => stdGaussian) i f x) ^ 2
        ∂(stdGaussianPi n)
        ≤
      ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  sorry

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

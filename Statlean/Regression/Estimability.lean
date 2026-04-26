import Statlean.Sufficiency.LehmannScheffe
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Estimability in Linear Models

## Main results

Definitions and properties of estimable linear functions `c'β` in the
linear model `Y = Xβ + ε`.  A linear function `c'β` is estimable if
`c` lies in the row space of `X` (equivalently, the column space of `Xᵀ`).

- `IsEstimable`: `c` is estimable iff `∃ a, Xᵀ *ᵥ a = c`
- `linear_estimator_unbiased`: `Xᵀ *ᵥ a = c → a ⬝ᵥ (X *ᵥ β) = c ⬝ᵥ β`
- `estimable_wellDefined`: estimable implies `c ⬝ᵥ β` well-defined on col(X)
- `isEstimable_row`: each row of X is estimable
- `blue_min_dotProduct_sq`: BLUE minimizes `‖a‖²` (variance-optimality)
- `blue_is_umvue`: BLUE is UMVUE given complete sufficient statistic

## References

- Jun Shao, *Mathematical Statistics*, 2nd ed., §3.6 (Prop 3.6) and §3.7 (Thm 3.7)
-/

open Matrix

variable {n p : ℕ}

/-! ## Estimability definition -/

/-- A linear function `c'β` is **estimable** in the linear model with design matrix `X`
if `c` is in the column space of `Xᵀ`, i.e., there exists a coefficient vector `a`
such that `Xᵀ *ᵥ a = c`.  Equivalently, `c'β` gives the same value for all `β`
satisfying the same normal equations. -/
def IsEstimable (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ) : Prop :=
  ∃ a : Fin n → ℝ, Xᵀ *ᵥ a = c

/-! ## Linear estimator algebra -/

/-- Unbiasedness of linear estimators:
if `Xᵀ *ᵥ a = c` then `a ⬝ᵥ (X *ᵥ β) = c ⬝ᵥ β` for all `β`.
In the linear model `Y = Xβ + ε` with `E[ε] = 0`, this gives `E[a'Y] = c'β`. -/
theorem linear_estimator_unbiased (X : Matrix (Fin n) (Fin p) ℝ)
    (a : Fin n → ℝ) (c : Fin p → ℝ) (β : Fin p → ℝ)
    (ha : Xᵀ *ᵥ a = c) :
    a ⬝ᵥ X *ᵥ β = c ⬝ᵥ β := by
  rw [dotProduct_mulVec, ← mulVec_transpose, ha]

/-- Estimable linear functions are well-defined on the column space:
if `Xβ₁ = Xβ₂` and `c` is estimable, then `c ⬝ᵥ β₁ = c ⬝ᵥ β₂`. -/
theorem estimable_wellDefined {X : Matrix (Fin n) (Fin p) ℝ} {c : Fin p → ℝ}
    (hc : IsEstimable X c) {β₁ β₂ : Fin p → ℝ}
    (hXβ : X *ᵥ β₁ = X *ᵥ β₂) :
    c ⬝ᵥ β₁ = c ⬝ᵥ β₂ := by
  obtain ⟨a, ha⟩ := hc
  rw [← linear_estimator_unbiased X a c β₁ ha,
      ← linear_estimator_unbiased X a c β₂ ha, hXβ]

/-- Each row of `X` is estimable. -/
theorem isEstimable_row (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) :
    IsEstimable X (X i) :=
  ⟨Pi.single i 1, by ext j; simp [mulVec, dotProduct_single]⟩

/-! ## BLUE optimality -/

/-- **BLUE optimality**: among all `a` with `Xᵀ *ᵥ a = c`, the one in the column
space of `X` minimizes `a ⬝ᵥ a` (= `‖a‖²` = `Var(a'Y)/σ²` in the linear model).

If `a₀ = X *ᵥ z` and `Xᵀ *ᵥ a₀ = c`, then `a₀ ⬝ᵥ a₀ ≤ a ⬝ᵥ a`
for all `a` with `Xᵀ *ᵥ a = c`. -/
theorem blue_min_dotProduct_sq (X : Matrix (Fin n) (Fin p) ℝ)
    (c : Fin p → ℝ) (a₀ a : Fin n → ℝ) (z : Fin p → ℝ)
    (ha₀_col : X *ᵥ z = a₀)
    (ha₀_unb : Xᵀ *ᵥ a₀ = c)
    (ha_unb : Xᵀ *ᵥ a = c) :
    a₀ ⬝ᵥ a₀ ≤ a ⬝ᵥ a := by
  -- Let d = a - a₀ (the component in ker(Xᵀ))
  set d := a - a₀ with hd_def
  -- d is in kernel of Xᵀ
  have hd_ker : Xᵀ *ᵥ d = 0 := by
    rw [hd_def, mulVec_sub, ha_unb, ha₀_unb, sub_self]
  -- Orthogonality: a₀ ∈ col(X), d ∈ ker(Xᵀ) = col(X)⊥
  have h_orth : a₀ ⬝ᵥ d = 0 := by
    rw [← ha₀_col, dotProduct_comm (X *ᵥ z) d, dotProduct_mulVec,
        ← mulVec_transpose, hd_ker, zero_dotProduct]
  -- a = a₀ + d
  have ha_eq : a = a₀ + d := by ext i; simp [hd_def]
  -- Pythagorean theorem: a ⬝ᵥ a = a₀ ⬝ᵥ a₀ + d ⬝ᵥ d
  have h_expand : a ⬝ᵥ a = a₀ ⬝ᵥ a₀ + d ⬝ᵥ d := by
    conv_lhs => rw [ha_eq]
    rw [add_dotProduct, dotProduct_add, dotProduct_add]
    have : d ⬝ᵥ a₀ = 0 := by rw [dotProduct_comm]; exact h_orth
    linarith
  -- d ⬝ᵥ d ≥ 0
  have h_nonneg : 0 ≤ d ⬝ᵥ d := by
    change 0 ≤ ∑ i : Fin n, d i * d i
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

/-! ## UMVUE bridge -/

section UMVUE

open MeasureTheory ProbabilityTheory

variable {Θ Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
variable [Nonempty α] [StandardBorelSpace α] [Nonempty Θ]

omit [Nonempty α] [StandardBorelSpace α] in
/-- **BLUE is UMVUE** (Lehmann-Scheffe bridge): given a complete sufficient statistic `T`,
any unbiased estimator yields the unique UMVUE via `E[δ|T]`.

This is a direct application of the Lehmann-Scheffe theorem to the linear model context.
The connection to BLUE: set `δ(ω) = a₀ ⬝ᵥ Y(ω)` where `a₀` satisfies `Xᵀ *ᵥ a₀ = c`
and use `linear_estimator_unbiased` to verify unbiasedness. -/
theorem blue_is_umvue
    (P : ParametricFamily Θ Ω) (T : Ω → α)
    (hT_suff : IsSufficient' P T) (hT_comp : IsComplete' P T)
    (δ : Ω → ℝ) (g : Θ → ℝ)
    (hδ_unb : IsUnbiased P δ g)
    (hδ_int : ∀ θ, Integrable δ (P.measure θ))
    (hδ'_int : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable δ' (P.measure θ))
    (hδ'_sq : ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
      ∀ θ, Integrable (fun ω => (δ' ω - g θ) ^ 2) (P.measure θ)) :
    ∃ h : α → ℝ, Measurable h ∧
      IsUnbiased P (h ∘ T) g ∧
      ∀ (δ' : Ω → ℝ), IsUnbiased P δ' g →
        ∀ θ, ∫ ω, ((h ∘ T) ω - g θ) ^ 2 ∂(P.measure θ) ≤
             ∫ ω, (δ' ω - g θ) ^ 2 ∂(P.measure θ) :=
  Statlean.Sufficiency.LehmannScheffe.lehmann_scheffe P T δ g
    hT_suff hT_comp hδ_unb hδ_int hδ'_int hδ'_sq

end UMVUE

/-! ## Theorem 3.6 (Shao, *Mathematical Statistics* §3.6)

Pipeline: `Statlean/Web/jobmofvoxwsav8y` (canonical_name `estimability_thm36`).

Existing infrastructure already covers part **(ii)** of Shao Thm 3.6:
* `linear_estimator_unbiased` ⇒ `E[a ⬝ᵥ X *ᵥ β] = c ⬝ᵥ β` for any `a` with `Zᵀa = c`
* `estimable_wellDefined` ⇒ uniqueness of `c ⬝ᵥ β` across LSE choices

The skeletons below capture the genuinely new content of Theorem 3.6:
* part **(i)** — the equivalence `R(Z) = R(Zᵀ Z)` and the rank-decomposition
  characterization `l = Qᵀ c` for `Z = Z_* Q`
* part **(iii)** — the converse under Gaussian Assumption A1: if `l ∉ R(Z)`,
  then no unbiased estimator of `lᵀ β` exists. -/

/-! ## Private infrastructure for Shao Thm 3.6 (i) -/

private lemma eucl_inner_eq_dp {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    @inner ℝ _ _ x y = dotProduct (EuclideanSpace.equiv (Fin m) ℝ x)
                                   (EuclideanSpace.equiv (Fin m) ℝ y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]; simp only [star_trivial]
  rw [show x.ofLp = (EuclideanSpace.equiv (Fin m) ℝ) x from rfl,
      show y.ofLp = (EuclideanSpace.equiv (Fin m) ℝ) y from rfl]
  rw [dotProduct_comm]

private noncomputable def Zmev {n p : ℕ} (Z : Matrix (Fin n) (Fin p) ℝ) :
    EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap.comp
    (Z.mulVecLin.comp (EuclideanSpace.equiv (Fin p) ℝ).toLinearMap)

private lemma Zmev_equiv {n p : ℕ} (Z : Matrix (Fin n) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace.equiv (Fin n) ℝ (Zmev Z v) = Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ v := by
  simp [Zmev, mulVecLin]; rfl

private lemma Zmev_adj {n p : ℕ} (Z : Matrix (Fin n) (Fin p) ℝ) :
    LinearMap.adjoint (Zmev Z) = Zmev Zᵀ := by
  symm; rw [(LinearMap.eq_adjoint_iff (Zmev Zᵀ) (Zmev Z))]
  intro v a
  rw [eucl_inner_eq_dp, eucl_inner_eq_dp, Zmev_equiv, Zmev_equiv]
  rw [mulVec_transpose, dotProduct_mulVec]

private lemma Zmev_gram_ker_eq {n p : ℕ} (Z : Matrix (Fin n) (Fin p) ℝ) :
    (Zmev (Zᵀ * Z)).ker = (Zmev Z).ker := by
  ext w; simp only [LinearMap.mem_ker]
  constructor
  · intro hw
    have hZtZ : (Zᵀ * Z) *ᵥ EuclideanSpace.equiv (Fin p) ℝ w = 0 := by
      have := congr_arg (EuclideanSpace.equiv (Fin p) ℝ) hw; rw [map_zero] at this
      rw [← this, Zmev_equiv]
    have hZ : Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w = 0 := by
      have step : dotProduct (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w)
                             (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w) = 0 := by
        have key : dotProduct (EuclideanSpace.equiv (Fin p) ℝ w)
                              ((Zᵀ * Z) *ᵥ EuclideanSpace.equiv (Fin p) ℝ w) =
                   dotProduct (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w)
                              (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w) := by
          rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
        rw [hZtZ, dotProduct_zero] at key; exact key.symm
      funext i; simp only [Pi.zero_apply]
      have hnn : ∀ j ∈ Finset.univ,
          0 ≤ (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w) j *
              (Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w) j :=
        fun j _ => mul_self_nonneg _
      exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp
        (by simp [dotProduct] at step; exact step) i (Finset.mem_univ i))
    apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    rw [Zmev_equiv, hZ, map_zero]
  · intro hw
    have hZ : Z *ᵥ EuclideanSpace.equiv (Fin p) ℝ w = 0 := by
      have := congr_arg (EuclideanSpace.equiv (Fin n) ℝ) hw; rw [map_zero] at this
      rw [← this, Zmev_equiv]
    apply (EuclideanSpace.equiv (Fin p) ℝ).injective
    rw [Zmev_equiv, ← mulVec_mulVec, hZ, mulVec_zero, map_zero]

private lemma range_orthogonal_eq_adjoint_ker_eucl
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (f : E →ₗ[𝕜] F) :
    (f.range)ᗮ = (LinearMap.adjoint f).ker := by
  ext x
  simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · intro h
    have hinn : ∀ z : E, @inner 𝕜 _ _ z ((LinearMap.adjoint f) x) = 0 := fun z => by
      rw [LinearMap.adjoint_inner_right]; exact h (f z) ⟨z, rfl⟩
    exact inner_self_eq_zero.mp (inner_eq_zero_symm.mp (hinn _))
  · intro hax y ⟨z, hz⟩
    rw [← hz, ← LinearMap.adjoint_inner_right, hax]; simp [inner_zero_right]

private lemma range_Ztrans_perp_eq_range_gram_perp {n p : ℕ}
    (Z : Matrix (Fin n) (Fin p) ℝ) :
    (Zmev Zᵀ).rangeᗮ = (Zmev (Zᵀ * Z)).rangeᗮ := by
  have h1 : (Zmev Zᵀ).rangeᗮ = (Zmev Z).ker := by
    rw [range_orthogonal_eq_adjoint_ker_eucl, Zmev_adj Zᵀ]
    simp [transpose_transpose]
  have h2 : (Zmev (Zᵀ * Z)).rangeᗮ = (Zmev Z).ker := by
    rw [range_orthogonal_eq_adjoint_ker_eucl, Zmev_adj (Zᵀ * Z)]
    rw [show (Zᵀ * Z)ᵀ = Zᵀ * Z from by rw [transpose_mul, transpose_transpose]]
    exact Zmev_gram_ker_eq Z
  rw [h1, h2]

private lemma range_Ztrans_eq_range_gram {n p : ℕ} (Z : Matrix (Fin n) (Fin p) ℝ) :
    (Zmev Zᵀ).range = (Zmev (Zᵀ * Z)).range := by
  rw [← (Zmev Zᵀ).range.orthogonal_orthogonal,
      range_Ztrans_perp_eq_range_gram_perp,
      (Zmev (Zᵀ * Z)).range.orthogonal_orthogonal]

section Shao36

/-- **Shao Thm 3.6 (i), normal-equation form**: `R(Z) = R(Zᵀ Z)`.

A linear functional `l` is in the row space of `Z` (i.e. `IsEstimable Z l`)
iff `l` is in the row space of the Gram matrix `Zᵀ Z`. -/
theorem isEstimable_iff_in_range_normal {n p : ℕ}
    (Z : Matrix (Fin n) (Fin p) ℝ) (l : Fin p → ℝ) :
    IsEstimable Z l ↔ ∃ v : Fin p → ℝ, (Zᵀ * Z) *ᵥ v = l := by
  simp only [IsEstimable]
  constructor
  · rintro ⟨a, ha⟩
    -- Transfer l to EuclideanSpace: e_p.symm l ∈ range(Zmev Zᵀ)
    have hl_in : (EuclideanSpace.equiv (Fin p) ℝ).symm l ∈ (Zmev Zᵀ).range := by
      rw [LinearMap.mem_range]
      exact ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm a, by
        apply (EuclideanSpace.equiv (Fin p) ℝ).injective
        rw [Zmev_equiv, (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply, ha]
        exact (ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin p) ℝ) l).symm⟩
    -- By range equality, e_p.symm l ∈ range(Zmev(ZᵀZ))
    rw [range_Ztrans_eq_range_gram] at hl_in
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hl_in
    -- Recover v = e_p w, and (ZᵀZ) *ᵥ v = l
    use (EuclideanSpace.equiv (Fin p) ℝ) w
    have hval := congr_arg (EuclideanSpace.equiv (Fin p) ℝ) hw
    rw [Zmev_equiv, ContinuousLinearEquiv.apply_symm_apply] at hval
    exact hval
  · rintro ⟨v, hv⟩
    -- Witness a = Z *ᵥ v: Zᵀ *ᵥ (Z *ᵥ v) = (ZᵀZ) *ᵥ v = l
    exact ⟨Z *ᵥ v, by rw [mulVec_mulVec, hv]⟩

/-- **Shao Thm 3.6 (i), Q-framing**: rank-decomposition `Z = Z_* * Q`
(with `Z_* : Matrix (Fin n) (Fin r) ℝ` of full column rank, i.e. `Z_*ᵀ Z_*`
invertible) yields the equivalence `(∃ c : Fin r → ℝ, l = Qᵀ *ᵥ c) ↔
IsEstimable Z l`.

The full-rank hypothesis is encoded as the existence of an inverse `Sinv`
of `Z_*ᵀ Z_*`. -/
theorem isEstimable_iff_in_range_Q {n p r : ℕ}
    (Z : Matrix (Fin n) (Fin p) ℝ)
    (Z_star : Matrix (Fin n) (Fin r) ℝ)
    (Q : Matrix (Fin r) (Fin p) ℝ)
    (Sinv : Matrix (Fin r) (Fin r) ℝ)
    (hZ : Z = Z_star * Q)
    (hSinv : (Z_starᵀ * Z_star) * Sinv = 1)
    (l : Fin p → ℝ) :
    (∃ c : Fin r → ℝ, l = Qᵀ *ᵥ c) ↔ IsEstimable Z l := by
  constructor
  · rintro ⟨c, hl⟩
    -- Witness: a = Z_star *ᵥ (Sinv *ᵥ c)
    -- Zᵀ *ᵥ (Z_star *ᵥ (Sinv *ᵥ c)) = Qᵀ *ᵥ c = l
    use Z_star *ᵥ (Sinv *ᵥ c)
    have key : Z_starᵀ *ᵥ (Z_star *ᵥ (Sinv *ᵥ c)) = c := by
      rw [mulVec_mulVec, mulVec_mulVec, hSinv, one_mulVec]
    rw [hl, hZ, transpose_mul]
    calc (Qᵀ * Z_starᵀ) *ᵥ (Z_star *ᵥ (Sinv *ᵥ c))
        = Qᵀ *ᵥ (Z_starᵀ *ᵥ (Z_star *ᵥ (Sinv *ᵥ c))) := by
            rw [mulVec_mulVec (Z_star *ᵥ (Sinv *ᵥ c)) Qᵀ Z_starᵀ]
      _ = Qᵀ *ᵥ c := by rw [key]
  · rintro ⟨ζ, hζ⟩
    -- Witness: c = Z_starᵀ *ᵥ ζ
    -- Zᵀ *ᵥ ζ = (Z_star * Q)ᵀ *ᵥ ζ = Qᵀ *ᵥ (Z_starᵀ *ᵥ ζ)
    use Z_starᵀ *ᵥ ζ
    rw [← hζ, hZ, transpose_mul, mulVec_mulVec ζ Qᵀ Z_starᵀ]

/-- **Shao Thm 3.6 (iii)**: under Gaussian Assumption A1, non-estimability
of `l` precludes any unbiased estimator.

Setup: `μ β` is the multivariate-Gaussian distribution of `X = Zβ + ε` with
`ε ~ N_n(0, σ² I_n)`, encoded as the iid product `(gaussianReal 0 σ²)^⊗n`
shifted by `Zβ`. If `l ∉ R(Z)` (= `¬ IsEstimable Z l`), then there is no
measurable `h : (Fin n → ℝ) → ℝ` integrable for every `μ β` and satisfying
the unbiasedness identity `∫ h dμ_β = l ⬝ᵥ β` for all `β`.

Proof idea (Shao p.200): differentiate the unbiasedness integral identity
w.r.t. `β`, apply the Lebesgue differentiation under the integral
(Theorem 2.1 in Shao), and read off `l = Zᵀ ζ` for some `ζ`, which is
exactly `IsEstimable Z l` and contradicts the hypothesis. -/
theorem not_estimable_under_gaussian {n p : ℕ}
    (Z : Matrix (Fin n) (Fin p) ℝ) (l : Fin p → ℝ)
    (σ : NNReal) (hσ : 0 < σ)
    (μ : (Fin p → ℝ) → MeasureTheory.Measure (Fin n → ℝ))
    (hμ : ∀ β, μ β =
      (MeasureTheory.Measure.pi
        (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 (σ * σ))).map
      (fun y i => y i + (Z *ᵥ β) i))
    (h_not : ¬ IsEstimable Z l) :
    ¬ ∃ h : (Fin n → ℝ) → ℝ,
      (∀ β, MeasureTheory.Integrable h (μ β)) ∧
      (∀ β, ∫ x, h x ∂(μ β) = l ⬝ᵥ β) := by
  intro ⟨h, h_int, h_unb⟩
  apply h_not
  -- Reduce to: ∀ v, Z *ᵥ v = 0 → l ⬝ᵥ v = 0
  -- then use linear algebra to conclude IsEstimable Z l.
  -- Step 1: rewrite unbiasedness via integral_map to a base-measure form.
  have h_red : ∀ β, ∫ y : Fin n → ℝ, h (fun i => y i + (Z *ᵥ β) i) ∂
      (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 (σ * σ)))
      = l ⬝ᵥ β := by
    intro β
    rw [← h_unb β, hμ β, MeasureTheory.integral_map]
    · exact (Measurable.aemeasurable
        (measurable_pi_lambda _ fun i => (measurable_pi_apply i).add measurable_const))
    · rw [← hμ β]; exact (h_int β).aestronglyMeasurable
  -- Step 2: for v ∈ ker Z, l ⬝ᵥ v = 0.
  have hann : ∀ v : Fin p → ℝ, Z *ᵥ v = 0 → l ⬝ᵥ v = 0 := by
    intro v hv
    -- At β = v: integrand simplifies (Z *ᵥ v = 0 ⇒ shift is 0)
    have hv_eq : ∫ y : Fin n → ℝ, h (fun i => y i + (Z *ᵥ v) i) ∂
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 (σ * σ))) =
        ∫ y : Fin n → ℝ, h y ∂
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 (σ * σ))) := by
      congr 1; ext y; simp [hv]
    -- At β = 0: l ⬝ᵥ 0 = 0
    have h0 : ∫ y : Fin n → ℝ, h y ∂
        (MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 (σ * σ)))
        = 0 := by
      have := h_red 0; simp [Matrix.mulVec_zero] at this; exact this
    -- h_red v : ∫ h(y + Zv) ∂π = l ⬝ᵥ v
    -- hv_eq : ∫ h(y + Zv) ∂π = ∫ h y ∂π
    -- h0 : ∫ h y ∂π = 0
    rw [← h_red v, hv_eq, h0]
  -- Step 3: l annihilates ker Z ⇒ l ∈ range Zᵀ (= IsEstimable Z l).
  simp only [IsEstimable]
  set l_e := (EuclideanSpace.equiv (Fin p) ℝ).symm l
  -- l_e ∈ (ker (Zmev Z))ᗮ
  have hl_perp : l_e ∈ (LinearMap.ker (Zmev Z))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hZu : Z *ᵥ (EuclideanSpace.equiv (Fin p) ℝ u) = 0 := by
      have := congr_arg (EuclideanSpace.equiv (Fin n) ℝ) hu
      rwa [Zmev_equiv, map_zero] at this
    rw [eucl_inner_eq_dp, (EuclideanSpace.equiv (Fin p) ℝ).apply_symm_apply,
        dotProduct_comm]
    exact hann _ hZu
  -- (ker (Zmev Z))ᗮ = range (Zmev Zᵀ):
  -- range_orthogonal_eq_adjoint_ker_eucl (Zmev Zᵀ) gives (Zmev Zᵀ).rangeᗮ = (adjoint (Zmev Zᵀ)).ker
  -- Zmev_adj Zᵀ gives adjoint(Zmev Zᵀ) = Zmev Zᵀᵀ = Zmev Z
  have hker_perp : (LinearMap.ker (Zmev Z))ᗮ = (Zmev Zᵀ).range := by
    rw [← Submodule.orthogonal_orthogonal (Zmev Zᵀ).range]
    congr 1
    have h1 : (Zmev Zᵀ).rangeᗮ = (Zmev Z).ker := by
      rw [range_orthogonal_eq_adjoint_ker_eucl, Zmev_adj Zᵀ]
      simp [Matrix.transpose_transpose]
    exact h1.symm
  -- Extract witness from range (Zmev Zᵀ)
  rw [hker_perp] at hl_perp
  obtain ⟨a_e, ha_e⟩ := LinearMap.mem_range.mp hl_perp
  -- ha_e : Zmev Zᵀ a_e = l_e; extract Zᵀ *ᵥ (e_n a_e) = l
  refine ⟨EuclideanSpace.equiv (Fin n) ℝ a_e, ?_⟩
  have hval := congr_arg (EuclideanSpace.equiv (Fin p) ℝ) ha_e
  rw [Zmev_equiv] at hval
  simp only [l_e, ContinuousLinearEquiv.apply_symm_apply] at hval
  exact hval

end Shao36

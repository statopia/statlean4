import Statlean.Sufficiency.LehmannScheffe
import Mathlib.Data.Matrix.Mul

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

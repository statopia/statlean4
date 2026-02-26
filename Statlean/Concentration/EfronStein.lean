import Statlean.Concentration.EfronSteinProved

/-! # Efron-Stein Inequality — sorry-bearing declarations

This file contains the sorry-bearing declarations for the Efron-Stein inequality.
All fully proved (sorry-free) declarations live in
`Statlean.Concentration.EfronSteinProved`.

## Remaining sorry gaps
- `efron_stein_condVar_le_of_condExp` — Jensen comparison for conditional variance
- `efron_stein_core_gen` / `hg_bound` — IH + Jensen comparison
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Finset

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i))

/-- **Jensen comparison for Efron-Stein** (sorry):
For `g = condExpExceptCoord μ i₀ f` (`sigmaAlgExcept i₀`-measurable) and `j ≠ i₀`:
  `(Measure.pi μ)[Var[g | G_j^except]] ≤ (Measure.pi μ)[Var[f | G_j^except]]`

**Proof sketch** (product Fubini for condExp, not yet in Mathlib):
For product measures, the key identity holds a.e.:
  `g(x) - E[g | G_j^e](x) = E[f(·) - E[f | G_j^e](·) | G_{i₀}^e](x)`
By conditional Jensen `(E[φ|G])² ≤ E[φ²|G]` and Fubini, integrating gives the bound. -/
private lemma efron_stein_condVar_le_of_condExp
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ) (hf : MemLp f 2 (Measure.pi μ))
    (i₀ j : ι) (hij : j ≠ i₀) :
    (Measure.pi μ)[Var[condExpExceptCoord μ i₀ f; Measure.pi μ | sigmaAlgExcept j]] ≤
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] := by
  sorry

/-- Internal induction for `efron_stein_core` on `n = Fintype.card ι`. -/
private theorem efron_stein_core_gen (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι]
      {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (∀ j, X j) → ℝ),
      Fintype.card ι = n →
      MemLp f 2 (Measure.pi μ) →
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  induction n with
  | zero =>
    intro ι _ X _ μ _ f hn hf
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp [variance_pi_of_isEmpty μ f]
  | succ n ih =>
    intro ι _ X _ μ _ f hn hf
    classical
    have hpos : 0 < Fintype.card ι := hn ▸ Nat.succ_pos n
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp hpos
    -- g = E[f | G_{i₀}^except], the marginal of f averaging out coordinate i₀
    set g := condExpExceptCoord μ i₀ f with hg_def
    have hg : MemLp g 2 (Measure.pi μ) := hf.condExp
    -- Law of Total Variance for coordinate i₀:
    --   E[Var[f | G_{i₀}^e]] + Var[g] = Var[f]
    have hltv : (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i₀]] +
        Var[g; Measure.pi μ] = Var[f; Measure.pi μ] :=
      integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i₀)
        (μ := Measure.pi μ) hf
    -- g is G_{i₀}^e-measurable, so E[g | G_{i₀}^e] = g pointwise
    have hcondExp_g : (Measure.pi μ)[g | sigmaAlgExcept i₀] = g :=
      condExp_of_stronglyMeasurable (sigmaAlgExcept_le (X := X) i₀)
        stronglyMeasurable_condExp (hg.integrable (by norm_num))
    -- Hence E[Var[g | G_{i₀}^e]] = 0 by LTV for g
    have hltv_g : (Measure.pi μ)[Var[g; Measure.pi μ | sigmaAlgExcept i₀]] = 0 := by
      have hltv2 := integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i₀)
        (μ := Measure.pi μ) hg
      simp only [hcondExp_g] at hltv2
      linarith [variance_nonneg g (Measure.pi μ)]
    -- Sum decomposition: Σᵢ = E[Var[f|G_{i₀}^e]] + Σ_{j≠i₀}
    have hsum_f :
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] =
        (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i₀]] +
        ∑ j ∈ Finset.univ.erase i₀,
          (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i₀)).symm.trans (add_comm _ _)
    -- Key bound: Var[g] ≤ Σ_{j≠i₀} E[Var[f | G_j^e]]
    -- (sorry: requires IH on ι' = {j // j ≠ i₀} via product measure transport
    --  + Jensen comparison from efron_stein_condVar_le_of_condExp)
    have hg_bound : Var[g; Measure.pi μ] ≤
        ∑ j ∈ Finset.univ.erase i₀,
          (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept j]] := by
      sorry
    -- Conclude: Var[f] = E[Var[f|G_{i₀}^e]] + Var[g]
    --                  ≤ E[Var[f|G_{i₀}^e]] + Σ_{j≠i₀} E[Var[f|G_j^e]]
    --                  = Σᵢ E[Var[f|G_i^e]]
    linarith [hltv, hg_bound, hsum_f.ge]

/-- **Efron-Stein core** (Theorem 3.1):
For independent random variables X₁,...,Xₙ on a product probability space
and a square-integrable function f, variance is bounded by the sum of conditional variances:
  `Var[f] ≤ Σᵢ (Measure.pi μ)[Var[f | G_i^except]]`

**Proof**: By induction on `n = Fintype.card ι` (see `efron_stein_core_gen`).
- Base n = 0: Trivial (ι empty, f constant, variance = 0).
- Step n → n+1: Fix i₀. LTV gives Var[f] = E[Var[f|G_{i₀}^e]] + Var[g].
  Apply key bound Var[g] ≤ Σ_{j≠i₀} E[Var[f|G_j^e]] (sorry: IH + Jensen comparison).
  Sum decomposition gives the result.

Remaining sorry: `hg_bound` in `efron_stein_core_gen`, which needs:
1. IH transport: applying the (n-1)-dim IH to g via the product measure decomposition.
2. Jensen comparison: `efron_stein_condVar_le_of_condExp` (also sorry).
Both require product-measure Fubini for conditional expectations (not in Mathlib). -/
theorem efron_stein_core
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] :=
  efron_stein_core_gen (Fintype.card ι) μ f rfl hf

/-- **ANOVA key inequality** (consequence of Efron-Stein):
For the product probability measure `Measure.pi μ` with n = `Fintype.card ι` coordinates,
the sum of variances of marginal conditional expectations satisfies:
  `∑ᵢ Var[E[f|G_i^except]] ≤ (n-1) · Var[f]`

**Proof**: Follows from Efron-Stein (`efron_stein_core`) plus the law of total variance.
By LTV: `E[Var[f|Gᵢ]] + Var[E[f|Gᵢ]] = Var[f]`, so summing over all i:
  `∑ᵢ E[Var[f|Gᵢ]] + ∑ᵢ Var[E[f|Gᵢ]] = n · Var[f]`
By Efron-Stein: `Var[f] ≤ ∑ᵢ E[Var[f|Gᵢ]]`
Therefore: `∑ᵢ Var[E[f|Gᵢ]] = n · Var[f] - ∑ᵢ E[Var[f|Gᵢ]] ≤ n · Var[f] - Var[f] = (n-1) · Var[f]`
-/
lemma efron_stein_anova_key
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∑ i : ι,
      Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ] ≤
    ((Fintype.card ι : ℝ) - 1) * Var[f; Measure.pi μ] := by
  -- Law of total variance for each coordinate i:
  --   E[Var[f|Gᵢ]] + Var[E[f|Gᵢ]] = Var[f]
  have hltv : ∀ i : ι,
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] +
        Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ] = Var[f; Measure.pi μ] :=
    fun i => integral_condVar_add_variance_condExp (sigmaAlgExcept_le (X := X) i)
              (μ := Measure.pi μ) hf
  -- Sum over all i: ∑ E[Var[f|Gᵢ]] + ∑ Var[E[f|Gᵢ]] = n · Var[f]
  have hsum :
      (∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) +
        (∑ i : ι, Var[(Measure.pi μ)[f | sigmaAlgExcept i]; Measure.pi μ]) =
        (Fintype.card ι : ℝ) * Var[f; Measure.pi μ] := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hltv]
    simp [Finset.sum_const, nsmul_eq_mul]
  -- By Efron-Stein: Var[f] ≤ ∑ E[Var[f|Gᵢ]]
  have hES := efron_stein_core (μ := μ) f hf
  -- Arithmetic: (A + B = n·V) and (V ≤ A) implies B ≤ (n-1)·V
  linarith

/-- **Efron-Stein Inequality** (Theorem 3.1):
For independent random variables X₁,...,Xₙ and a square-integrable function f:
  `Var[f(X)] ≤ Σᵢ E[(f(X) - E^{(i)}[f(X)])²]`
where `E^{(i)}` is the conditional expectation averaging out coordinate i.

This version requires no external hypothesis: the core inequality is
established via `efron_stein_core` (sorry, martingale telescoping argument). -/
theorem efron_stein
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) :=
  efron_stein_of_condVar_sum_bound (μ := μ) f hf (efron_stein_core (μ := μ) f hf)

end

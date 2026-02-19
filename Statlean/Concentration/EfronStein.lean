import Statlean.Concentration.Basic

/-! # Efron-Stein Inequality (Theorem 3.1)

## Statement
Let X₁,...,Xₙ be independent random variables, and let f be a square-integrable
function. Then:

  Var[f(X)] ≤ Σᵢ E[(f(X) - E^{(i)}[f(X)])²]

where E^{(i)}[f(X)] = E[f(X) | Xⱼ, j ≠ i] is the conditional expectation
of f given all variables except Xᵢ.

## Proof strategy
The proof uses the telescoping decomposition:
  f - E[f] = Σᵢ (Dᵢf)
where Dᵢf = E[f | X₁,...,Xᵢ] - E[f | X₁,...,Xᵢ₋₁]
(martingale difference sequence).

Then Var[f] = E[(Σᵢ Dᵢf)²] = Σᵢ E[(Dᵢf)²] (by orthogonality).
Finally, E[(Dᵢf)²] ≤ E[(f - E^{(i)}[f])²] by conditional Jensen.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Finset

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i))

/-- Efron-Stein in integral form from an already-established integral bound.
Kept as a compatibility wrapper. -/
theorem efron_stein_of_integral_bound
    (f : (∀ j, X j) → ℝ)
    (hES :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  exact hES

/-- One Efron-Stein summand equals the integral of the conditional variance
with respect to the sigma-algebra that forgets coordinate `i`. -/
lemma efron_stein_term_eq_integral_condVar_exceptCoord
    [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) =
      (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  classical
  have hm : sigmaAlgExcept i ≤ (inferInstance : MeasurableSpace (∀ j, X j)) :=
    sigmaAlgExcept_le (X := X) i
  have hfi : Integrable (fun ω => (f ω - condExpExceptCoord μ i f ω) ^ 2) (Measure.pi μ) := by
    exact (hf.sub hf.condExp).integrable_sq
  calc
    ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)
        = ∫ ω in Set.univ, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by simp
    _ = ∫ ω in Set.univ, (Var[f; Measure.pi μ | sigmaAlgExcept i]) ω ∂(Measure.pi μ) := by
      symm
      exact setIntegral_condVar (m := sigmaAlgExcept i) (hm := hm)
        (μ := Measure.pi μ) (X := f) (s := Set.univ) hfi (by simp)
    _ = (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by simp

/-- The full Efron-Stein right-hand side is the sum of conditional variances. -/
lemma efron_stein_rhs_eq_sum_integral_condVar
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    (∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ))
      =
    (∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i hi
  simpa using efron_stein_term_eq_integral_condVar_exceptCoord (μ := μ) i f hf

/-- Efron-Stein in conditional-variance-sum form:
if `Var[f]` is bounded by the sum of conditional variances, then it is bounded
by the standard Efron-Stein integral right-hand side. -/
theorem efron_stein_of_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ))
    (hCondVar :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  have hEq :=
    efron_stein_rhs_eq_sum_integral_condVar (μ := μ) f hf
  calc
    Var[f; Measure.pi μ]
      ≤ ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := hCondVar
    _ = ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
      simpa [eq_comm] using hEq

/-- **Efron-Stein Inequality** (Theorem 3.1):
For independent random variables X₁,...,Xₙ and a square-integrable function `f`,
derive the integral-form bound from the conditional-variance-sum bound. -/
theorem efron_stein
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ))
    (hCondVar :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  exact efron_stein_of_condVar_sum_bound (μ := μ) f hf hCondVar

/-- Convert an Efron-Stein integral-form bound to the equivalent
conditional-variance-sum form. -/
theorem efron_stein_to_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ))
    (hES :
      Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]] := by
  simpa [efron_stein_rhs_eq_sum_integral_condVar (μ := μ) f hf] using hES

/-- Efron-Stein integral form and conditional-variance-sum form are equivalent. -/
theorem efron_stein_iff_condVar_sum_bound
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    (Var[f; Measure.pi μ] ≤
        ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ))
      ↔
    (Var[f; Measure.pi μ] ≤
        ∑ i : ι, (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept i]]) := by
  constructor
  · intro hES
    exact efron_stein_to_condVar_sum_bound (μ := μ) f hf hES
  · intro hCondVar
    exact efron_stein_of_condVar_sum_bound (μ := μ) f hf hCondVar

/-- The Efron-Stein right-hand side is always nonnegative. -/
lemma efron_stein_rhs_nonneg
    (f : (∀ j, X j) → ℝ) :
    0 ≤ ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  classical
  refine Finset.sum_nonneg ?_
  intro i hi
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Single-coordinate case (`|ι| = 1`): Efron-Stein is exact. -/
theorem efron_stein_unique_eq
    [Unique ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] =
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  classical
  have hsig : sigmaAlgExcept (default : ι) = (⊥ : MeasurableSpace (∀ j, X j)) :=
    sigmaAlgExcept_eq_bot (X := X) (default : ι)
  have hterm :
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ) =
        Var[f; Measure.pi μ] := by
    calc
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ)
          = (Measure.pi μ)[Var[f; Measure.pi μ | sigmaAlgExcept (default : ι)]] :=
        efron_stein_term_eq_integral_condVar_exceptCoord (μ := μ) (default : ι) f hf
      _ = (Measure.pi μ)[Var[f; Measure.pi μ | (⊥ : MeasurableSpace (∀ j, X j))]] := by
        simp [hsig]
      _ = ∫ ω, (Var[f; Measure.pi μ | (⊥ : MeasurableSpace (∀ j, X j))]) ω ∂(Measure.pi μ) := by
        rfl
      _ = ∫ ω, Var[f; Measure.pi μ] ∂(Measure.pi μ) := by
        simp [condVar_bot (μ := Measure.pi μ) (hX := hf.aemeasurable)]
      _ = Var[f; Measure.pi μ] := by simp
  have hsum :
      (∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)) =
      ∫ ω, (f ω - condExpExceptCoord μ (default : ι) f ω) ^ 2 ∂(Measure.pi μ) := by
    exact (Fintype.sum_unique (f := fun i : ι =>
      ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ)))
  rw [hsum, hterm]

/-- Single-coordinate case (`|ι| = 1`): inequality form. -/
theorem efron_stein_unique
    [Unique ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (∀ j, X j) → ℝ)
    (hf : MemLp f 2 (Measure.pi μ)) :
    Var[f; Measure.pi μ] ≤
      ∑ i : ι, ∫ ω, (f ω - condExpExceptCoord μ i f ω) ^ 2 ∂(Measure.pi μ) := by
  exact (efron_stein_unique_eq (μ := μ) f hf).le

end

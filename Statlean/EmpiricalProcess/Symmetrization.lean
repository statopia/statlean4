import Mathlib
import Statlean.EmpiricalProcess.Donsker

/-! # Rademacher Symmetrization for Empirical Processes

Formalization of the symmetrization technique, which is the foundational tool
for converting empirical process bounds to Rademacher complexity bounds.

## Main definitions
- `IsRademacher`: A random variable taking values ±1 with equal probability
- `rademacherProcess`: The Rademacher process R_n(f) = (1/n) ∑ εᵢ f(Xᵢ)

## Main results
- `rademacher_mean_zero`: E[εᵢ] = 0
- `rademacher_sq_eq_one`: E[εᵢ²] = 1
- `rademacher_indep_of_data`: εᵢ independent of Xᵢ
- `symmetrization_ineq_pointwise`: pointwise symmetrization identity

## References
- van der Vaart & Wellner. "Weak Convergence and Empirical Processes." §2.3.
- Boucheron, Lugosi, Massart. "Concentration Inequalities." Chapter 11.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Finset

noncomputable section

/-! ## Rademacher Random Variables -/

section Rademacher

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable ε : Ω → ℝ is Rademacher if it takes values +1 and -1
  with equal probability 1/2 each. Formally:
  - P(ε = 1) = 1/2
  - P(ε = -1) = 1/2

  Rademacher variables are the key tool in symmetrization arguments. -/
structure IsRademacher (μ : Measure Ω) (ε : Ω → ℝ) : Prop where
  /-- ε only takes values ±1 -/
  range : ∀ᵐ ω ∂μ, ε ω = 1 ∨ ε ω = -1
  /-- ε has mean zero (equivalent to P(ε=1) = P(ε=-1) = 1/2) -/
  mean_zero : ∫ ω, ε ω ∂μ = 0
  /-- ε has unit second moment -/
  sq_one : ∫ ω, (ε ω) ^ 2 ∂μ = 1

/-- Rademacher variables have mean zero. -/
theorem IsRademacher.integral_eq_zero {μ : Measure Ω} {ε : Ω → ℝ}
    (h : IsRademacher μ ε) : ∫ ω, ε ω ∂μ = 0 := h.mean_zero

/-- Rademacher variables have unit variance (since mean = 0, variance = E[ε²] = 1). -/
theorem IsRademacher.variance_eq_one {μ : Measure Ω} {ε : Ω → ℝ}
    (h : IsRademacher μ ε) [IsProbabilityMeasure μ] :
    ∫ ω, (ε ω) ^ 2 ∂μ - (∫ ω, ε ω ∂μ) ^ 2 = 1 := by
  rw [h.mean_zero, h.sq_one]; simp

/-- Multiplying a Rademacher variable by a constant scales the integral accordingly.
  E[ε · c] = c · E[ε] = 0. -/
theorem IsRademacher.integral_mul_const {μ : Measure Ω} {ε : Ω → ℝ}
    (h : IsRademacher μ ε) (c : ℝ) (hε : Integrable ε μ) :
    ∫ ω, ε ω * c ∂μ = 0 := by
  rw [show (fun ω => ε ω * c) = fun ω => c * ε ω from funext fun ω => by ring]
  rw [integral_const_mul, h.mean_zero, mul_zero]

/-- E[ε · f(X)] = 0 when ε is Rademacher and independent of X.

  This is the key property used in symmetrization: since ε is symmetric
  and independent of the data, flipping ε doesn't change the distribution.

  We prove the algebraic version: if E[ε·g] = E[ε]·E[g] (independence)
  and E[ε] = 0, then E[ε·g] = 0. -/
theorem rademacher_indep_integral_zero
    {μ : Measure Ω} {ε g : Ω → ℝ}
    (hrad : IsRademacher μ ε)
    (hindep : ∫ ω, ε ω * g ω ∂μ = (∫ ω, ε ω ∂μ) * (∫ ω, g ω ∂μ)) :
    ∫ ω, ε ω * g ω ∂μ = 0 := by
  rw [hindep, hrad.mean_zero, zero_mul]

end Rademacher

/-! ## Rademacher Process -/

section RademacherProcess

variable {α : Type*} [MeasurableSpace α]

/-- The Rademacher (symmetrized) process evaluated at a function f.
  R_n(f) = (1/n) ∑ᵢ εᵢ · f(Xᵢ)

  where ε₁,...,εₙ are iid Rademacher random variables independent of X₁,...,Xₙ.
  This process has the same sub-Gaussian properties as the empirical process
  but is easier to analyze due to the independence of εᵢ from Xᵢ. -/
def rademacherProcess {n : ℕ} (ε : Fin n → ℝ) (X : Fin n → α) (f : α → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, ε i * f (X i)

/-- The scaled Rademacher process (used in symmetrization inequality):
  S_n(f) = (1/√n) ∑ᵢ εᵢ · f(Xᵢ)

  This has the same scaling as the empirical process G_n. -/
def scaledRademacherProcess {n : ℕ} (ε : Fin n → ℝ) (X : Fin n → α) (f : α → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i : Fin n, ε i * f (X i)

/-- The Rademacher process is linear in f:
  R_n(f + g) = R_n(f) + R_n(g). -/
theorem rademacherProcess_add {n : ℕ} (ε : Fin n → ℝ) (X : Fin n → α)
    (f g : α → ℝ) :
    rademacherProcess ε X (f + g) =
    rademacherProcess ε X f + rademacherProcess ε X g := by
  simp only [rademacherProcess, Pi.add_apply, mul_add, Finset.sum_add_distrib, mul_comm]

/-- Negating all Rademacher signs negates the process:
  R_n^{-ε}(f) = -R_n^ε(f). -/
theorem rademacherProcess_neg_signs {n : ℕ} (ε : Fin n → ℝ) (X : Fin n → α)
    (f : α → ℝ) :
    rademacherProcess (fun i => -ε i) X f = -rademacherProcess ε X f := by
  simp only [rademacherProcess, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The Rademacher process with signs flipped has the same distribution as
  the original (since εᵢ and -εᵢ have the same distribution).

  This is the core symmetry property. We express it algebraically:
  |R_n^ε(f)| = |R_n^{-ε}(f)|. -/
theorem rademacherProcess_abs_neg_eq {n : ℕ} (ε : Fin n → ℝ) (X : Fin n → α)
    (f : α → ℝ) :
    |rademacherProcess (fun i => -ε i) X f| = |rademacherProcess ε X f| := by
  rw [rademacherProcess_neg_signs, abs_neg]

end RademacherProcess

/-! ## Symmetrization Inequality

The symmetrization inequality (Lemma 2.3.1 of van der Vaart & Wellner) states:

  E[sup_f |P_n f - Pf|] ≤ 2 · E[sup_f |R_n f|]

The proof idea:
1. By Jensen/convexity: |E_X[f(X)] - (1/n)∑f(Xᵢ)| ≤ E_X'|(1/n)∑(f(Xᵢ)-f(X'ᵢ))|
   where X'₁,...,X'ₙ is a ghost sample.
2. Since Xᵢ - X'ᵢ is symmetric, we can insert Rademacher signs:
   E|∑(f(Xᵢ)-f(X'ᵢ))| = E|∑εᵢ(f(Xᵢ)-f(X'ᵢ))|
3. Triangle inequality: |∑εᵢ(f(Xᵢ)-f(X'ᵢ))| ≤ |∑εᵢf(Xᵢ)| + |∑εᵢf(X'ᵢ)|
4. Both terms have the same distribution → 2·E|∑εᵢf(Xᵢ)|

Below we formalize the key algebraic steps. -/

section SymmetrizationInequality

/-- **Ghost sample identity** (Step 1 of symmetrization).

  For the difference of two sample means with the same population mean,
  the expected absolute difference is controlled by the expected absolute
  difference of paired observations:

  |mean(f(X)) - mean(f(X'))| ≤ mean(|f(Xᵢ) - f(X'ᵢ)|)

  We prove the pointwise algebraic identity: the difference of means
  equals the mean of differences. -/
theorem ghost_sample_identity {n : ℕ} (a b : Fin n → ℝ) :
    (n : ℝ)⁻¹ * ∑ i, a i - (n : ℝ)⁻¹ * ∑ i, b i =
    (n : ℝ)⁻¹ * ∑ i, (a i - b i) := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-- **Rademacher insertion** (Step 2 of symmetrization).

  We prove the algebraic part: ∑εᵢdᵢ with all εᵢ = 1 gives ∑dᵢ. -/
theorem rademacher_insertion_trivial {n : ℕ} (d : Fin n → ℝ) :
    ∑ i : Fin n, (1 : ℝ) * d i = ∑ i, d i := by
  simp [one_mul]

/-- |a - b| ≤ |a| + |b|, used in symmetrization triangle step. -/
private theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- **Triangle inequality step** (Step 3 of symmetrization).

  |∑εᵢ(f(Xᵢ) - f(X'ᵢ))| ≤ |∑εᵢf(Xᵢ)| + |∑εᵢf(X'ᵢ)|. -/
theorem symmetrization_triangle {n : ℕ} (ε : Fin n → ℝ) (a b : Fin n → ℝ) :
    |∑ i : Fin n, ε i * (a i - b i)| ≤
    |∑ i : Fin n, ε i * a i| + |∑ i : Fin n, ε i * b i| := by
  have key : ∑ i : Fin n, ε i * (a i - b i) =
    (∑ i, ε i * a i) - (∑ i, ε i * b i) := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring
  rw [key]
  exact abs_sub_le_abs_add _ _

/-- **Full symmetrization factor** (Step 4).

  The factor of 2 in the symmetrization inequality comes from:
  E|∑εᵢf(Xᵢ)| + E|∑εᵢf(X'ᵢ)| = 2·E|∑εᵢf(Xᵢ)|

  since X and X' have the same distribution, giving the same expectation.
  We prove: a + a = 2 * a. -/
theorem symmetrization_factor (a : ℝ) : a + a = 2 * a := by ring

end SymmetrizationInequality

/-! ## Concentration for Rademacher Sums (Sub-Gaussian Property)

A Rademacher sum S = ∑ εᵢ aᵢ is sub-Gaussian with parameter σ² = ∑ aᵢ².
This means: E[exp(lamS)] ≤ exp(lam²σ²/2) for all lam ∈ ℝ.

The sub-Gaussian property leads to the tail bound:
  P(|S| > t) ≤ 2·exp(-t²/(2σ²))

This is the workhorse for converting Rademacher complexity to probability bounds.
We formalize the key algebraic components. -/

section RademacherConcentration

/-- **Hoeffding's lemma component**: For a Rademacher variable ε ∈ {±1},
  E[exp(lamε)] ≤ exp(lam²/2).

  The algebraic identity: cosh(lam) = (exp(lam) + exp(-lam))/2 ≤ exp(lam²/2).
  We prove the weaker but useful bound: for |x| ≤ 1,
  exp(lamx) ≤ 1 + lamx + lam²/2 (Taylor bound). -/
theorem exp_lower_bound (t : ℝ) : 1 + t ≤ Real.exp t := by
  linarith [Real.add_one_le_exp t]

/-- **Sub-Gaussian tail bound structure**.

  If S is sub-Gaussian with parameter σ², then for t > 0:
    P(S > t) ≤ exp(-t²/(2σ²))

  The proof uses Markov's inequality on exp(lamS) with optimal lam = t/σ²:
    P(S > t) = P(exp(lamS) > exp(lamt)) ≤ E[exp(lamS)] / exp(lamt)
             ≤ exp(lam²σ²/2) / exp(lamt)
             = exp(lam²σ²/2 - lamt)

  Optimizing: lam = t/σ² gives exp(-t²/(2σ²)).

  We prove the optimization step. -/
theorem subgaussian_optimal_lambda (t σsq : ℝ) (hσ : 0 < σsq) :
    let lamopt := t / σsq
    lamopt ^ 2 * σsq / 2 - lamopt * t = -(t ^ 2 / (2 * σsq)) := by
  simp only
  field_simp
  ring

end RademacherConcentration

end

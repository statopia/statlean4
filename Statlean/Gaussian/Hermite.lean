import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Statlean.Gaussian.Stein

/-! # Hermite Polynomial Orthogonality under Gaussian Measure

## Main results
1. `derivative_hermite`: `H'_{n+1} = (n+1) · Hₙ`
2. `integral_aeval_hermite_eq_zero`: `E_γ[Hₖ] = 0` for `k ≥ 1`
3. `hermite_inner_succ`: `E_γ[Hₘ · H_{n+1}] = m · E_γ[H_{m-1} · Hₙ]`
4. `hermite_orthogonality`: `E_γ[Hₘ · Hₙ] = n! · δ_{mn}`
-/

open Polynomial MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace Polynomial

theorem derivative_hermite (n : ℕ) :
    Polynomial.derivative (hermite (n + 1)) = (↑(n + 1) : ℤ[X]) * hermite n := by
  induction n with
  | zero =>
    simp [hermite_zero]
  | succ n ih =>
    rw [hermite_succ]
    rw [derivative_sub, derivative_mul]
    rw [derivative_X, one_mul, ih]
    rw [derivative_natCast_mul]
    have key : X * hermite n = hermite (n + 1) + derivative (hermite n) := by
      rw [hermite_succ]; ring
    conv_lhs => rw [show X * (↑(n + 1) * hermite n) = ↑(n + 1) * (X * hermite n) from by ring]
    rw [key]
    push_cast
    ring

end Polynomial

/-! ## MemLp infrastructure for ℤ[X] polynomials under Gaussian -/

lemma memLp_aeval_intPolynomial_gaussianReal (p : ℤ[X]) (q : ℝ≥0∞) (hq : q ≠ ⊤) :
    MemLp (fun x : ℝ => Polynomial.aeval x p) q stdGaussian := by
  have heq : (fun x : ℝ => Polynomial.aeval x p) =
      (fun x : ℝ => Polynomial.aeval x (p.map (algebraMap ℤ ℝ))) := by
    ext x
    rw [Polynomial.aeval_map_algebraMap]
  rw [heq]
  exact memLp_polynomial_gaussianReal _ q hq

lemma integrable_aeval_intPolynomial_gaussianReal (p : ℤ[X]) :
    Integrable (fun x : ℝ => Polynomial.aeval x p) stdGaussian :=
  (memLp_aeval_intPolynomial_gaussianReal p 1 ENNReal.one_ne_top).integrable le_rfl

/-! ## HasDerivAt infrastructure for Hermite products -/

abbrev hermiteEval (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)

lemma hasDerivAt_hermiteEval (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteEval n)
      (Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n))) x :=
  (Polynomial.hermite n).hasDerivAt_aeval x

lemma hasDerivAt_hermiteEval_mul (m n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => hermiteEval m x * hermiteEval n x)
      (Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite m)) * hermiteEval n x +
       hermiteEval m x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n))) x :=
  (hasDerivAt_hermiteEval m x).mul (hasDerivAt_hermiteEval n x)

lemma memLp_hermiteEval_mul (m n : ℕ) :
    MemLp (fun x => hermiteEval m x * hermiteEval n x) 2 stdGaussian := by
  have : (fun x => hermiteEval m x * hermiteEval n x) =
      (fun x => Polynomial.aeval x (Polynomial.hermite m * Polynomial.hermite n)) := by
    ext x; simp [Polynomial.aeval_mul]
  rw [this]
  exact memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num)

lemma memLp_deriv_hermiteEval_mul (m n : ℕ) :
    MemLp (fun x =>
      Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite m)) * hermiteEval n x +
      hermiteEval m x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)))
      2 stdGaussian := by
  apply MemLp.add
  · have : (fun x => Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite m)) *
        hermiteEval n x) =
        (fun x => Polynomial.aeval x
          (Polynomial.derivative (Polynomial.hermite m) * Polynomial.hermite n)) := by
      ext x; simp [Polynomial.aeval_mul]
    rw [this]
    exact memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num)
  · have : (fun x => hermiteEval m x *
        Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n))) =
        (fun x => Polynomial.aeval x
          (Polynomial.hermite m * Polynomial.derivative (Polynomial.hermite n))) := by
      ext x; simp [Polynomial.aeval_mul]
    rw [this]
    exact memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num)

/-! ## Hermite mean zero -/

theorem integral_aeval_hermite_eq_zero (k : ℕ) (hk : 0 < k) :
    ∫ x, hermiteEval k x ∂stdGaussian = 0 := by
  induction k with
  | zero => omega
  | succ n ih =>
    have hstein := stein_identity (hermiteEval n)
      (fun x => Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)))
      (memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num))
      (memLp_aeval_intPolynomial_gaussianReal _ 2 (by norm_num))
      (fun x => hasDerivAt_hermiteEval n x)
    have hsucc : ∀ x : ℝ, hermiteEval (n + 1) x =
        x * hermiteEval n x -
        Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)) := by
      intro x
      simp only [hermiteEval, Polynomial.hermite_succ, map_sub, Polynomial.aeval_mul,
        Polynomial.aeval_X]
    simp_rw [hsucc]
    rw [integral_sub
      (integrable_aeval_intPolynomial_gaussianReal (Polynomial.X * Polynomial.hermite n) |>.congr
        (Filter.Eventually.of_forall fun x => by
          simp [Polynomial.aeval_mul, Polynomial.aeval_X]))
      (integrable_aeval_intPolynomial_gaussianReal (Polynomial.derivative (Polynomial.hermite n)))]
    linarith

/-! ## Hermite inner product recurrence -/

theorem hermite_inner_succ (m n : ℕ) :
    ∫ x, hermiteEval m x * hermiteEval (n + 1) x ∂stdGaussian =
    ↑m * ∫ x, hermiteEval (m - 1) x * hermiteEval n x ∂stdGaussian := by
  have hsucc : ∀ x : ℝ, hermiteEval (n + 1) x =
      x * hermiteEval n x -
      Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)) := by
    intro x
    simp only [hermiteEval, Polynomial.hermite_succ, map_sub, Polynomial.aeval_mul,
      Polynomial.aeval_X]
  simp_rw [hsucc, mul_sub]
  rw [integral_sub
    (integrable_aeval_intPolynomial_gaussianReal
      (Polynomial.hermite m * (Polynomial.X * Polynomial.hermite n)) |>.congr
      (Filter.Eventually.of_forall fun x => by
        simp [Polynomial.aeval_mul, Polynomial.aeval_X]))
    (integrable_aeval_intPolynomial_gaussianReal
      (Polynomial.hermite m * Polynomial.derivative (Polynomial.hermite n)) |>.congr
      (Filter.Eventually.of_forall fun x => by
        simp [Polynomial.aeval_mul]))]
  have hrearrange : ∫ x, hermiteEval m x * (x * hermiteEval n x) ∂stdGaussian =
      ∫ x, x * (hermiteEval m x * hermiteEval n x) ∂stdGaussian := by
    congr 1; ext x; ring
  rw [hrearrange]
  rw [stein_identity (fun x => hermiteEval m x * hermiteEval n x)
    (fun x => Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite m)) *
       hermiteEval n x +
     hermiteEval m x *
       Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite n)))
    (memLp_hermiteEval_mul m n)
    (memLp_deriv_hermiteEval_mul m n)
    (fun x => hasDerivAt_hermiteEval_mul m n x)]
  rw [integral_add
    (integrable_aeval_intPolynomial_gaussianReal
      (Polynomial.derivative (Polynomial.hermite m) * Polynomial.hermite n) |>.congr
      (Filter.Eventually.of_forall fun x => by simp [Polynomial.aeval_mul]))
    (integrable_aeval_intPolynomial_gaussianReal
      (Polynomial.hermite m * Polynomial.derivative (Polynomial.hermite n)) |>.congr
      (Filter.Eventually.of_forall fun x => by simp [Polynomial.aeval_mul]))]
  ring_nf
  match m with
  | 0 =>
    simp [Polynomial.hermite_zero, Polynomial.derivative_one, map_zero, zero_mul, integral_zero]
  | m + 1 =>
    simp only [Nat.add_sub_cancel]
    have hderiv_eq : ∀ x : ℝ,
        Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite (m + 1))) =
        (↑(m + 1) : ℝ) * hermiteEval m x := by
      intro x
      simp only [Polynomial.derivative_hermite, map_mul, map_natCast]
    simp_rw [hderiv_eq, mul_assoc]
    rw [integral_const_mul]

/-! ## Full orthogonality -/

theorem hermite_orthogonality (m n : ℕ) :
    ∫ x, hermiteEval m x * hermiteEval n x ∂stdGaussian =
    if m = n then (n.factorial : ℝ) else 0 := by
  suffices aux : ∀ k : ℕ, ∀ m n : ℕ, m + n = k →
      ∫ x, hermiteEval m x * hermiteEval n x ∂stdGaussian =
      if m = n then (n.factorial : ℝ) else 0 from
    aux (m + n) m n rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro m n hmn
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · subst hm
      simp [hermiteEval, Polynomial.hermite_zero, map_one, integral_const]
    · simp only [hm, ↓reduceIte]
      simp only [hermiteEval, Polynomial.hermite_zero, map_one, mul_one]
      exact integral_aeval_hermite_eq_zero m (Nat.pos_of_ne_zero hm)
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hermite_inner_succ m n']
    by_cases hm : m = 0
    · subst hm; simp
    · have hlt : (m - 1) + n' < k := by omega
      rw [ih _ hlt _ _ rfl]
      by_cases heq : m = n' + 1
      · subst heq
        simp only [Nat.add_sub_cancel, ↓reduceIte]
        push_cast [Nat.factorial_succ]
        ring
      · have hneq : m - 1 ≠ n' := by omega
        simp [hneq, heq]

end

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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

/-! ## Normalized Hermite functions and IBP coefficient relation -/

/-- Normalized Hermite function: `eₙ(x) = Hₙ(x) / √(n!)`.
These form an orthonormal system in L²(γ). -/
noncomputable def hermiteNorm (n : ℕ) (x : ℝ) : ℝ :=
  hermiteEval n x / Real.sqrt (n.factorial : ℝ)

lemma hermiteNorm_eq (n : ℕ) (x : ℝ) :
    hermiteNorm n x = hermiteEval n x / Real.sqrt (n.factorial : ℝ) := rfl

/-- Inner product of normalized Hermite functions = Kronecker delta. -/
theorem hermiteNorm_inner (m n : ℕ) :
    ∫ x, hermiteNorm m x * hermiteNorm n x ∂stdGaussian = if m = n then 1 else 0 := by
  simp only [hermiteNorm]
  have hsqrt_m : Real.sqrt (↑m.factorial) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hsqrt_n : Real.sqrt (↑n.factorial) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have heq : (fun x => hermiteEval m x / Real.sqrt ↑m.factorial *
      (hermiteEval n x / Real.sqrt ↑n.factorial)) =
      (fun x => hermiteEval m x * hermiteEval n x /
        (Real.sqrt ↑m.factorial * Real.sqrt ↑n.factorial)) := by
    ext x; field_simp
  rw [heq, show (fun x => hermiteEval m x * hermiteEval n x /
      (Real.sqrt ↑m.factorial * Real.sqrt ↑n.factorial)) =
      (fun x => (1 / (Real.sqrt ↑m.factorial * Real.sqrt ↑n.factorial)) *
        (hermiteEval m x * hermiteEval n x)) from by ext x; ring]
  rw [integral_const_mul, hermite_orthogonality]
  split_ifs with h
  · subst h
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) _)]
  · simp

/-- The three-term recurrence for normalized Hermite:
`x · eₙ(x) = √(n+1) · e_{n+1}(x) + √n · e_{n-1}(x)`. -/
theorem hermite_recurrence_norm (n : ℕ) (x : ℝ) :
    x * hermiteNorm n x =
    Real.sqrt (↑(n + 1)) * hermiteNorm (n + 1) x +
    Real.sqrt (↑n) * hermiteNorm (n - 1) x := by
  match n with
  | 0 =>
    -- n - 1 = 0 in ℕ, √0 = 0, so last term vanishes; reduces to x * H₀/1 = √1 * H₁/1
    simp [hermiteNorm, hermiteEval, Polynomial.hermite_zero, Nat.factorial, Real.sqrt_zero]
  | m + 1 =>
    simp only [Nat.add_sub_cancel, hermiteNorm_eq]
    -- Key recurrence: x * H_{m+1}(x) = H_{m+2}(x) + (m+1) * H_m(x)
    -- From hermite_succ: H_{m+2} = X * H_{m+1} - H'_{m+1}, i.e. x * H_{m+1} = H_{m+2} + H'_{m+1}
    -- From derivative_hermite: H'_{m+1} = (m+1) * H_m
    have hrec : x * hermiteEval (m + 1) x =
        hermiteEval (m + 2) x + (↑(m + 1) : ℝ) * hermiteEval m x := by
      have hstep1 : x * hermiteEval (m + 1) x = hermiteEval (m + 2) x +
          Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite (m + 1))) := by
        simp only [hermiteEval, Polynomial.hermite_succ, map_sub, Polynomial.aeval_mul,
          Polynomial.aeval_X]
        ring
      simp only [hstep1, Polynomial.derivative_hermite, map_mul, map_natCast]
    -- Factorial sqrt splitting: √((n+1)!) = √(n+1) * √(n!)
    have h1 : Real.sqrt (↑(m + 2).factorial) =
        Real.sqrt ↑(m + 2) * Real.sqrt ↑(m + 1).factorial := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    have h2 : Real.sqrt (↑(m + 1).factorial) = Real.sqrt ↑(m + 1) * Real.sqrt ↑m.factorial := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    have hsq1_sq : Real.sqrt (↑(m + 1)) ^ 2 = (↑(m + 1) : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    -- Rewrite n + 1 + 1 to m + 2 so patterns match
    rw [show (m + 1 + 1) = m + 2 from rfl]
    -- Pull multiplication inside the division
    rw [show x * (hermiteEval (m + 1) x / Real.sqrt (↑(m + 1).factorial)) =
        (x * hermiteEval (m + 1) x) / Real.sqrt (↑(m + 1).factorial) from by ring]
    -- Substitute the recurrence and factorial splits, then close by algebra
    rw [hrec, h1, h2]
    field_simp
    rw [hsq1_sq]
    push_cast; ring

/-- f·p is integrable (L¹) under Gaussian when f ∈ L²(γ) and p is a ℤ-polynomial.
Uses Hölder: L² · L² → L¹. -/
lemma integrable_f_mul_poly_gaussian {f : ℝ → ℝ} (p : ℤ[X])
    (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x * Polynomial.aeval x p) stdGaussian := by
  have hp : MemLp (fun x => Polynomial.aeval x p) 2 stdGaussian :=
    memLp_aeval_intPolynomial_gaussianReal p 2 (by norm_num)
  have h := hf.integrable_mul hp (𝕜 := ℝ)
  exact h.congr (Filter.Eventually.of_forall fun x => by simp)

/-- f·p is integrable (L¹) under Gaussian when f ∈ L²(γ) and p is a ℝ-polynomial.
Uses Hölder: L² · L² → L¹. -/
lemma integrable_f_mul_realPoly_gaussian {f : ℝ → ℝ} (p : ℝ[X])
    (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x * Polynomial.eval x p) stdGaussian := by
  have hp : MemLp (fun x => Polynomial.eval x p) 2 stdGaussian :=
    memLp_polynomial_gaussianReal p 2 (by norm_num)
  have h := hf.integrable_mul hp (𝕜 := ℝ)
  exact h.congr (Filter.Eventually.of_forall fun x => by simp)

/-- f·Hₖ is integrable under Gaussian when f ∈ L²(γ). -/
lemma integrable_f_mul_hermiteEval (k : ℕ) {f : ℝ → ℝ} (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x * hermiteEval k x) stdGaussian :=
  integrable_f_mul_poly_gaussian _ hf

/-- f·p ∈ L²(γ) when f ∈ L²(γ) and p is a polynomial (Gaussian-specific).
Under Gaussian measure, the super-exponential tail decay compensates polynomial growth.

Sorry gap: needs either Gaussian hypercontractivity or a density argument
(approximate f by smooth compactly supported, which are in all Lᵖ). -/
lemma memLp_f_mul_poly_gaussian {f : ℝ → ℝ} (p : ℤ[X])
    (hf : MemLp f 2 stdGaussian) :
    MemLp (fun x => f x * Polynomial.aeval x p) 2 stdGaussian := by
  sorry

/-- **Hermite coefficient of derivative** (unnormalized):
`∫ f'·Hₖ dγ = ∫ f·H_{k+1} dγ`.

Proof sketch: Apply Stein to h = f·Hₖ, h' = f'·Hₖ + f·H'ₖ.
Stein: ∫ x·(f·Hₖ) dγ = ∫ (f'·Hₖ + f·H'ₖ) dγ.
Recurrence: x·Hₖ = H_{k+1} + H'ₖ gives ∫ f·(x·Hₖ) = ∫ f·H_{k+1} + ∫ f·H'ₖ.
Cancel ∫ f·H'ₖ from both sides.
Depends on `memLp_f_mul_poly_gaussian` (sorry). -/
theorem integral_deriv_mul_hermiteEval
    (f f' : ℝ → ℝ) (k : ℕ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    ∫ x, f' x * hermiteEval k x ∂stdGaussian =
    ∫ x, f x * hermiteEval (k + 1) x ∂stdGaussian := by
  -- L² membership for products (via sorry gap memLp_f_mul_poly_gaussian)
  have hfHk_L2 : MemLp (fun x => f x * hermiteEval k x) 2 stdGaussian :=
    memLp_f_mul_poly_gaussian _ hf
  have hfHk_deriv_L2 : MemLp (fun x => f' x * hermiteEval k x +
      f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k)))
      2 stdGaussian :=
    (memLp_f_mul_poly_gaussian _ hf').add (memLp_f_mul_poly_gaussian _ hf)
  -- Apply Stein to h = f·Hₖ
  have hstein := stein_identity
    (fun x => f x * hermiteEval k x)
    (fun x => f' x * hermiteEval k x +
     f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k)))
    hfHk_L2 hfHk_deriv_L2
    (fun x => (hderiv x).mul (hasDerivAt_hermiteEval k x))
  -- hstein: ∫ x·(f·Hₖ) = ∫ (f'·Hₖ + f·H'ₖ)
  -- Rearrange LHS: ∫ x·(f·Hₖ) = ∫ f·(x·Hₖ)
  have hrearrange : ∫ x, x * (f x * hermiteEval k x) ∂stdGaussian =
      ∫ x, f x * (x * hermiteEval k x) ∂stdGaussian := by
    congr 1; ext x; ring
  -- Recurrence: x·Hₖ(x) = H_{k+1}(x) + H'ₖ(x)
  have hrecurrence : ∀ x : ℝ,
      x * hermiteEval k x = hermiteEval (k + 1) x +
        Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k)) := by
    intro x
    simp only [hermiteEval, Polynomial.hermite_succ, map_sub, Polynomial.aeval_mul,
      Polynomial.aeval_X]
    ring
  -- Substitute recurrence into LHS
  have hLHS : ∫ x, f x * (x * hermiteEval k x) ∂stdGaussian =
      ∫ x, f x * hermiteEval (k + 1) x ∂stdGaussian +
      ∫ x, f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k))
        ∂stdGaussian := by
    have heq : (fun x => f x * (x * hermiteEval k x)) =
        (fun x => f x * hermiteEval (k + 1) x +
         f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k))) := by
      ext x; rw [hrecurrence x, mul_add]
    rw [heq]
    exact integral_add (integrable_f_mul_hermiteEval (k + 1) hf)
      (integrable_f_mul_poly_gaussian _ hf)
  -- Expand RHS: ∫ (f'·Hₖ + f·H'ₖ) = ∫ f'·Hₖ + ∫ f·H'ₖ
  have hRHS : ∫ x, (f' x * hermiteEval k x +
      f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k)))
      ∂stdGaussian =
      ∫ x, f' x * hermiteEval k x ∂stdGaussian +
      ∫ x, f x * Polynomial.aeval x (Polynomial.derivative (Polynomial.hermite k))
        ∂stdGaussian := by
    exact integral_add (integrable_f_mul_hermiteEval k hf')
      (integrable_f_mul_poly_gaussian _ hf)
  -- Chain: LHS = ∫ f·H_{k+1} + ∫ f·H'ₖ = ∫ x·(f·Hₖ) = ∫ (f'·Hₖ + f·H'ₖ) = ∫ f'·Hₖ + ∫ f·H'ₖ
  -- Cancel ∫ f·H'ₖ
  linarith [hrearrange, hstein, hLHS, hRHS]

/-- **Hermite coefficient of derivative** (normalized):
`∫ f'·eₖ dγ = √(k+1) · ∫ f·e_{k+1} dγ`. -/
theorem integral_deriv_mul_hermiteNorm
    (f f' : ℝ → ℝ) (k : ℕ)
    (hf : MemLp f 2 stdGaussian)
    (hf' : MemLp f' 2 stdGaussian)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) :
    ∫ x, f' x * hermiteNorm k x ∂stdGaussian =
    Real.sqrt (↑(k + 1)) * ∫ x, f x * hermiteNorm (k + 1) x ∂stdGaussian := by
  -- Unfold normalization and use the unnormalized version
  simp only [hermiteNorm]
  rw [show (fun x => f' x * (hermiteEval k x / Real.sqrt ↑k.factorial)) =
      (fun x => (1 / Real.sqrt ↑k.factorial) * (f' x * hermiteEval k x)) from by
    ext x; ring]
  rw [show (fun x => f x * (hermiteEval (k + 1) x / Real.sqrt ↑(k + 1).factorial)) =
      (fun x => (1 / Real.sqrt ↑(k + 1).factorial) * (f x * hermiteEval (k + 1) x)) from by
    ext x; ring]
  rw [integral_const_mul, integral_const_mul]
  rw [integral_deriv_mul_hermiteEval f f' k hf hf' hderiv]
  -- Now: (1/√(k!)) · ∫f·H_{k+1} = √(k+1) · (1/√((k+1)!)) · ∫f·H_{k+1}
  -- i.e., 1/√(k!) = √(k+1)/√((k+1)!)
  have hsqrt_fact : Real.sqrt ↑(k + 1).factorial =
      Real.sqrt ↑(k + 1) * Real.sqrt ↑k.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
  rw [hsqrt_fact]
  have hsk : Real.sqrt ↑k.factorial ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hsk1 : Real.sqrt ↑(k + 1) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp

/-! ## Polynomial density in L²(γ) -/

/-- Integral of a real polynomial times g vanishes when all monomial moments vanish. -/
lemma integral_polynomial_mul_g_eq_zero
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, (x ^ n) * g x ∂stdGaussian = 0)
    (p : Polynomial ℝ) :
    ∫ x, Polynomial.eval x p * g x ∂stdGaussian = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.eval_add, add_mul]
    rw [integral_add
      ((integrable_f_mul_realPoly_gaussian p hg).congr
        (Filter.Eventually.of_forall fun x => by ring))
      ((integrable_f_mul_realPoly_gaussian q hg).congr
        (Filter.Eventually.of_forall fun x => by ring))]
    rw [ihp, ihq, add_zero]
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    rw [show (fun x => a * x ^ n * g x) = (fun x => a * ((x ^ n) * g x)) from by ext; ring]
    rw [integral_const_mul, hg_orth n, mul_zero]

/-- The integral ∫ exp(t*x*I) * g(x) dγ = 0 for all t ∈ ℝ, when all monomial moments vanish.
This is the key step: the "Fourier transform of g·dγ" vanishes everywhere.

Proof: exp(itx) = Σ (itx)ⁿ/n! and each term integrates to zero against g.
The interchange of sum and integral uses dominated convergence with the dominating
function exp(|t|·|x|)·|g(x)|, which is integrable by Cauchy-Schwarz. -/
lemma integral_cexp_mul_g_eq_zero
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, (x ^ n) * g x ∂stdGaussian = 0)
    (t : ℝ) :
    ∫ x, Complex.exp (↑t * ↑x * Complex.I) * ↑(g x) ∂stdGaussian = 0 := by
  have hg_int : Integrable g stdGaussian := hg.integrable one_le_two
  -- Define partial sums F N x = (Σ_{k<N} (itx)^k/k!) * g(x)
  let F : ℕ → ℝ → ℂ := fun N x =>
    (∑ k ∈ Finset.range N, (↑t * ↑x * Complex.I) ^ k / ↑(k.factorial)) * ↑(g x)
  -- Each summand rewrites to const * ofReal(x^k * g x)
  have heq_k : ∀ k, (fun (x : ℝ) => (↑t * ↑x * Complex.I) ^ k / ↑(k.factorial) * ↑(g x)) =
      (fun (x : ℝ) => ((↑t * Complex.I) ^ k / ↑(k.factorial)) *
        (↑(x ^ k * g x) : ℂ)) := by
    intro k; ext x; push_cast; ring
  have hR : ∀ k, Integrable (fun x => x ^ k * g x) stdGaussian := fun k =>
    (integrable_f_mul_poly_gaussian (Polynomial.X ^ k) hg).congr
      (Filter.Eventually.of_forall fun x => by simp [Polynomial.aeval_X_pow, mul_comm])
  -- Each partial sum integrates to 0
  have hF_zero : ∀ N, ∫ x, F N x ∂stdGaussian = 0 := by
    intro N
    simp only [F, Finset.sum_mul]
    have hint : ∀ k ∈ Finset.range N,
        Integrable (fun (x : ℝ) => (↑t * ↑x * Complex.I) ^ k / ↑(k.factorial) * ↑(g x))
          stdGaussian := by
      intro k _
      rw [heq_k]
      exact (hR k).ofReal.const_mul _
    rw [integral_finset_sum _ hint]
    apply Finset.sum_eq_zero
    intro k _
    rw [heq_k, integral_const_mul]
    rw [integral_complex_ofReal, hg_orth k, Complex.ofReal_zero, mul_zero]
  -- Pointwise limit: F N x → exp(itx) * g(x)
  have hF_lim : ∀ᵐ x ∂stdGaussian, Filter.Tendsto (fun N => F N x) Filter.atTop
      (nhds (Complex.exp (↑t * ↑x * Complex.I) * ↑(g x))) := by
    apply Filter.Eventually.of_forall
    intro x
    have hexp : HasSum (fun n => (↑t * ↑x * Complex.I) ^ n / ↑(n.factorial))
        (Complex.exp (↑t * ↑x * Complex.I)) :=
      Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp _
    exact hexp.tendsto_sum_nat.mul_const _
  -- Domination: ‖F N x‖ ≤ exp(|t|·|x|)·|g x|
  have hF_bound : ∀ N, ∀ᵐ x ∂stdGaussian,
      ‖F N x‖ ≤ Real.exp (|t| * |x|) * |g x| := by
    intro N
    apply Filter.Eventually.of_forall
    intro x
    simp only [F, Complex.norm_mul, Complex.norm_real]
    rw [Real.norm_eq_abs]
    gcongr
    calc ‖∑ k ∈ Finset.range N,
            (↑t * ↑x * Complex.I) ^ k / ↑(k.factorial)‖
        ≤ ∑ k ∈ Finset.range N,
            ‖(↑t * ↑x * Complex.I) ^ k / ↑(k.factorial)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (|t| * |x|) ^ k / (k.factorial) := by
          gcongr with k _
          rw [norm_div, Complex.norm_pow, Complex.norm_natCast]
          gcongr
          simp [Complex.norm_mul, Complex.norm_real, Complex.norm_I]
      _ ≤ Real.exp (|t| * |x|) :=
          Real.sum_le_exp_of_nonneg (by positivity) N
  -- The bound is integrable (Hölder: exp(c|x|) ∈ L²(γ), g ∈ L²(γ))
  have hbound_int : Integrable (fun x => Real.exp (|t| * |x|) * |g x|) stdGaussian := by
    have hexp_L2 : MemLp (fun x => Real.exp (|t| * |x|)) 2 stdGaussian := by
      rw [MeasureTheory.memLp_two_iff_integrable_sq
        (Measurable.aestronglyMeasurable (by fun_prop))]
      have := integrable_exp_abs_stdGaussian (2 * |t|)
      convert this using 1; ext x
      rw [← Real.exp_nat_mul, show ↑(2 : ℕ) * (|t| * |x|) = 2 * |t| * |x| from by
        push_cast; ring]
    exact (hexp_L2.integrable_mul hg.norm).congr
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
  -- AEStronglyMeasurable for F N (follows from integrability of each term)
  have hF_meas : ∀ N, AEStronglyMeasurable (fun x => F N x) stdGaussian := by
    intro N
    simp only [F, Finset.sum_mul]
    exact (integrable_finset_sum _ fun k _ =>
      (heq_k k ▸ (hR k).ofReal.const_mul _)).aestronglyMeasurable
  -- Apply dominated convergence (argument order: bound, meas, integrable_bound, norm_bound, lim)
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (|t| * |x|) * |g x|)
    hF_meas hbound_int hF_bound hF_lim
  simp only [hF_zero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- Polynomials are dense in L²(stdGaussian): if g ∈ L²(γ) satisfies
∫ p·g dγ = 0 for every polynomial p, then g = 0 a.e.

Proof: Show ∫ e^{itx} g(x) dγ = 0 for all t, then use charFun uniqueness:
define μ₊ = γ.withDensity(g⁺) and μ₋ = γ.withDensity(g⁻). Since their
characteristic functions agree, μ₊ = μ₋, hence g = g⁺ - g⁻ = 0 a.e. -/
theorem polynomial_dense_L2_gaussian
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, (x ^ n) * g x ∂stdGaussian = 0) :
    g =ᵐ[stdGaussian] 0 := by
  have hg_int : Integrable g stdGaussian := hg.integrable one_le_two
  -- Step 1: Define positive and negative part measures
  set gp := fun x => (g x ⊔ 0 : ℝ) with hgp_def
  set gn := fun x => ((-g x) ⊔ 0 : ℝ) with hgn_def
  set μp := stdGaussian.withDensity (fun x => ENNReal.ofReal (gp x)) with hμp_def
  set μn := stdGaussian.withDensity (fun x => ENNReal.ofReal (gn x)) with hμn_def
  -- Step 2: Both are finite measures
  have hgp_int : Integrable gp stdGaussian := hg_int.sup (integrable_const 0)
  have hgn_int : Integrable gn stdGaussian := hg_int.neg.sup (integrable_const 0)
  haveI : IsFiniteMeasure μp := by
    apply isFiniteMeasure_withDensity
    exact ne_top_of_le_ne_top hgp_int.hasFiniteIntegral.ne
      (lintegral_mono fun x => Real.ofReal_le_enorm (gp x))
  haveI : IsFiniteMeasure μn := by
    apply isFiniteMeasure_withDensity
    exact ne_top_of_le_ne_top hgn_int.hasFiniteIntegral.ne
      (lintegral_mono fun x => Real.ofReal_le_enorm (gn x))
  -- Step 3: charFun μp = charFun μn
  -- Key: ∫ exp(itx) dμp = ∫ exp(itx) dμn ← ∫ g · exp(itx) dγ = 0
  have hcharFun_eq : charFun μp = charFun μn := by
    ext t
    simp only [charFun_apply_real]
    -- Both integrals can be rewritten via integral_withDensity
    have hmeas_gp : AEMeasurable (fun x => ENNReal.ofReal (gp x)) stdGaussian :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (hgp_int.aestronglyMeasurable.aemeasurable)
    have hmeas_gn : AEMeasurable (fun x => ENNReal.ofReal (gn x)) stdGaussian :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (hgn_int.aestronglyMeasurable.aemeasurable)
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas_gp
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas_gn
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have hgp_nn : ∀ x, 0 ≤ gp x := fun x => le_sup_right
    have hgn_nn : ∀ x, 0 ≤ gn x := fun x => le_sup_right
    simp_rw [ENNReal.toReal_ofReal (hgp_nn _), ENNReal.toReal_ofReal (hgn_nn _)]
    -- Convert smul to ℂ multiplication
    simp_rw [Complex.real_smul]
    -- Now: ∫ ↑(gp x) * exp(itx) dγ = ∫ ↑(gn x) * exp(itx) dγ
    -- This follows from ∫ ↑(g x) * exp(itx) dγ = 0 since g = gp - gn
    have key := integral_cexp_mul_g_eq_zero g hg hg_orth t
    rw [show (fun (x : ℝ) => Complex.exp (↑t * ↑x * Complex.I) * ↑(g x)) =
        (fun (x : ℝ) => ↑(g x) * Complex.exp (↑t * ↑x * Complex.I)) from by ext; ring] at key
    have hg_eq_real : ∀ x, g x = gp x - gn x := by
      intro x; simp [gp, gn, max_def]; split_ifs with h1 h2 <;> linarith
    have hg_eq : ∀ x, (g x : ℂ) = ↑(gp x) - ↑(gn x) := by
      intro x; rw [hg_eq_real]; push_cast; ring
    -- key now: ∫ ((↑(gp x) - ↑(gn x)) * exp(itx)) dγ = 0
    -- But we haven't split the integral yet, so key is:
    -- ∫ (↑(gp x) - ↑(gn x)) * exp(itx) dγ = 0
    -- Rewrite as ∫ (↑(gp x) * exp(itx) - ↑(gn x) * exp(itx)) dγ = 0
    -- Then use integral_sub to split
    -- Integrability: gp, gn are integrable, exp is bounded on ℂ with norm 1...
    -- Actually exp(itx) has ‖exp(itx·I)‖ = 1 if the argument is purely imaginary
    -- For real t and real x, ‖exp(t*x*I)‖ = 1
    -- So ↑(gp x) * exp(itx) is integrable since gp is integrable
    -- Integrability: ‖↑(f x) * exp(itx)‖ = |f x| since ‖exp(itx)‖ = 1
    have hint_mul : ∀ {f : ℝ → ℝ}, Integrable f stdGaussian →
        Integrable (fun x => (↑(f x) : ℂ) * Complex.exp (↑t * ↑x * Complex.I))
          stdGaussian := by
      intro f hf
      exact Integrable.mono hf (by fun_prop) (ae_of_all _ fun x => by
        rw [Complex.norm_mul, Complex.norm_real]
        have : ↑t * ↑x * Complex.I = ↑(t * x) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I, mul_one])
    -- Rewrite g = gp - gn inside key, then split integral
    simp_rw [hg_eq] at key
    rw [show (fun (x : ℝ) => (↑(gp x) - ↑(gn x)) * Complex.exp (↑t * ↑x * Complex.I)) =
        (fun (x : ℝ) => ↑(gp x) * Complex.exp (↑t * ↑x * Complex.I) -
         ↑(gn x) * Complex.exp (↑t * ↑x * Complex.I)) from by ext; ring] at key
    rw [integral_sub (hint_mul hgp_int) (hint_mul hgn_int)] at key
    exact sub_eq_zero.mp key
  -- Step 4: μp = μn by charFun injectivity
  have hμ_eq : μp = μn := Measure.ext_of_charFun hcharFun_eq
  -- Step 5: Conclude g = 0 a.e.
  -- g = gp - gn, and μp = μn means gp =ᵐ gn, so g =ᵐ 0
  apply hg_int.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  -- Decompose: ∫_s g = ∫_s gp - ∫_s gn
  have hdecomp : ∀ᵐ x ∂stdGaussian, g x = gp x - gn x := by
    filter_upwards with x
    simp [gp, gn, max_def]; split_ifs with h <;> linarith
  rw [setIntegral_congr_ae hs (hdecomp.mono fun x hx _ => hx)]
  rw [integral_sub hgp_int.integrableOn hgn_int.integrableOn]
  -- ∫_s gp = ∫_s gn because μp(s) = μn(s)
  -- Connect: ∫_s gp dγ = (∫⁻_s ofReal(gp) dγ).toReal = (μp s).toReal
  have h_eq_s : (μp s).toReal = (μn s).toReal := by rw [hμ_eq]
  have hgp_nonneg : 0 ≤ᵐ[stdGaussian.restrict s] gp := by
    filter_upwards with x; exact le_max_right _ _
  have hgn_nonneg : 0 ≤ᵐ[stdGaussian.restrict s] gn := by
    filter_upwards with x; exact le_max_right _ _
  have hp_eq : ∫ x in s, gp x ∂stdGaussian = (μp s).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hgp_nonneg
      hgp_int.aestronglyMeasurable.restrict]
    congr 1
    rw [← withDensity_apply _ hs]
  have hn_eq : ∫ x in s, gn x ∂stdGaussian = (μn s).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hgn_nonneg
      hgn_int.aestronglyMeasurable.restrict]
    congr 1
    rw [← withDensity_apply _ hs]
  rw [hp_eq, hn_eq, h_eq_s, sub_self]

/-- Helper: integral of a bounded-degree polynomial times g vanishes
when all monomial moments up to that degree vanish. -/
private lemma integral_poly_mul_g_of_moments_below
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (d : ℕ) (hmoments : ∀ k < d, ∫ x, (x ^ k) * g x ∂stdGaussian = 0)
    (p : ℝ[X]) (hp : p.natDegree < d) :
    ∫ x, Polynomial.eval x p * g x ∂stdGaussian = 0 := by
  -- Expand p as Σ_{i < natDeg+1} coeff(i) * x^i
  simp_rw [Polynomial.eval_eq_sum_range (p := p), Finset.sum_mul]
  have hint_summand : ∀ i ∈ Finset.range (p.natDegree + 1),
      Integrable (fun x => p.coeff i * x ^ i * g x) stdGaussian := by
    intro i _
    have : Integrable (fun x => x ^ i * g x) stdGaussian :=
      (integrable_f_mul_poly_gaussian (Polynomial.X ^ i) hg).congr
        (Filter.Eventually.of_forall fun x => by simp [Polynomial.aeval_X_pow, mul_comm])
    exact (this.const_mul _).congr (Filter.Eventually.of_forall fun x => by ring)
  rw [integral_finset_sum _ hint_summand]
  apply Finset.sum_eq_zero; intro i hi
  rw [show (fun x => p.coeff i * x ^ i * g x) = (fun x => p.coeff i * (x ^ i * g x)) from
    by ext; ring]
  rw [integral_const_mul, hmoments i (lt_of_lt_of_le (Finset.mem_range.mp hi) hp), mul_zero]

/-- Hermite polynomials span is dense in L²(γ): if g ∈ L²(γ) satisfies
∫ Hₙ·g dγ = 0 for all n, then g = 0 a.e. -/
theorem hermite_span_dense_L2
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, hermiteEval n x * g x ∂stdGaussian = 0) :
    g =ᵐ[stdGaussian] 0 := by
  -- Step 1: Prove all monomial moments vanish by strong induction
  have hmoments : ∀ n : ℕ, ∫ x, (x ^ n) * g x ∂stdGaussian = 0 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
    -- remainder r = X^n - hermite n has degree < n (both monic of degree n)
    set r : ℤ[X] := Polynomial.X ^ n - Polynomial.hermite n with hr_def
    -- Integrability (note: integrable_f_mul_* gives f*poly order, need .congr for poly*f)
    have hint_H : Integrable (fun x => hermiteEval n x * g x) stdGaussian :=
      (integrable_f_mul_hermiteEval n hg).congr
        (Filter.Eventually.of_forall fun x => by ring)
    have hint_r : Integrable (fun x => Polynomial.aeval x r * g x) stdGaussian :=
      (integrable_f_mul_poly_gaussian r hg).congr
        (Filter.Eventually.of_forall fun x => by ring)
    -- Decompose: ∫ x^n g = ∫ Hₙ g + ∫ r g
    have hdecomp : ∫ x, x ^ n * g x ∂stdGaussian =
        ∫ x, hermiteEval n x * g x ∂stdGaussian +
        ∫ x, Polynomial.aeval x r * g x ∂stdGaussian := by
      rw [← integral_add hint_H hint_r]
      congr 1; ext x
      simp only [hermiteEval, hr_def, map_sub, map_pow, Polynomial.aeval_X, sub_mul]
      ring
    rw [hdecomp, hg_orth n, zero_add]
    -- Convert aeval to eval via map
    set rm := r.map (algebraMap ℤ ℝ) with hrm_def
    have haeval_eq : ∀ x, Polynomial.aeval x r = Polynomial.eval x rm := by
      intro x; rw [hrm_def]; exact (Polynomial.eval_map_algebraMap r x).symm
    simp_rw [haeval_eq]
    -- If r.map = 0, integral is trivially 0
    by_cases hrm_zero : rm = 0
    · simp [hrm_zero]
    · -- r.map has degree < n (X^n and hermite n are monic of degree n, leading terms cancel)
      have hr_deg : rm.degree < (n : WithBot ℕ) := by
        rw [hrm_def, hr_def, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
        have hdeg_xn : (Polynomial.X ^ n : ℝ[X]).degree = (n : WithBot ℕ) := by
          rw [Polynomial.degree_pow, Polynomial.degree_X, nsmul_eq_mul, mul_one]
        have hdeg_herm : (Polynomial.map (algebraMap ℤ ℝ) (Polynomial.hermite n)).degree =
            (n : WithBot ℕ) := by
          rw [Polynomial.degree_map_eq_of_injective (algebraMap ℤ ℝ).injective_int,
            Polynomial.degree_hermite]
        calc (Polynomial.X ^ n - Polynomial.map (algebraMap ℤ ℝ) (Polynomial.hermite n)).degree
            < (Polynomial.X ^ n : ℝ[X]).degree := by
              apply Polynomial.degree_sub_lt
              · rw [hdeg_xn, hdeg_herm]
              · exact pow_ne_zero _ Polynomial.X_ne_zero
              · rw [Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X, one_pow]
                rw [Polynomial.leadingCoeff_map_of_injective (algebraMap ℤ ℝ).injective_int]
                simp [(Polynomial.hermite_monic n).leadingCoeff]
          _ = ↑n := hdeg_xn
      have hr_natdeg : rm.natDegree < n :=
        (Polynomial.natDegree_lt_iff_degree_lt hrm_zero).mpr hr_deg
      exact integral_poly_mul_g_of_moments_below g hg n ih _ hr_natdeg
  -- Step 2: Apply polynomial density
  exact polynomial_dense_L2_gaussian g hg hmoments

end

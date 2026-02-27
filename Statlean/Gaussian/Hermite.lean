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

/-- f·p is integrable (L¹) under Gaussian when f ∈ L²(γ) and p is a polynomial.
Uses Hölder: L² · L² → L¹. -/
lemma integrable_f_mul_poly_gaussian {f : ℝ → ℝ} (p : ℤ[X])
    (hf : MemLp f 2 stdGaussian) :
    Integrable (fun x => f x * Polynomial.aeval x p) stdGaussian := by
  have hp : MemLp (fun x => Polynomial.aeval x p) 2 stdGaussian :=
    memLp_aeval_intPolynomial_gaussianReal p 2 (by norm_num)
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

/-- Polynomials are dense in L²(stdGaussian): if g ∈ L²(γ) satisfies
∫ p·g dγ = 0 for every polynomial p, then g = 0 a.e.

Proof sketch: The function F(t) = E_γ[e^{tX}·g(X)] is entire and
F(t) = Σ tⁿ/n! · E[Xⁿg] = 0. So the Fourier transform of g·φ vanishes,
giving g = 0 a.e. by Fourier injectivity. -/
theorem polynomial_dense_L2_gaussian
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, (x ^ n) * g x ∂stdGaussian = 0) :
    g =ᵐ[stdGaussian] 0 := by
  sorry

/-- Hermite polynomials span is dense in L²(γ): if g ∈ L²(γ) satisfies
∫ Hₙ·g dγ = 0 for all n, then g = 0 a.e. -/
theorem hermite_span_dense_L2
    (g : ℝ → ℝ) (hg : MemLp g 2 stdGaussian)
    (hg_orth : ∀ n : ℕ, ∫ x, hermiteEval n x * g x ∂stdGaussian = 0) :
    g =ᵐ[stdGaussian] 0 := by
  -- Hermite polynomials span all polynomials, so ∫ p·g = 0 for all p.
  -- Apply polynomial_dense_L2_gaussian.
  sorry

end

import Statlean.EmpiricalProcess.Chaining
open MeasureTheory Real Set BigOperators

/-! # Hoeffding's Lemma (Gap C)

For bounded centered random variables: E[exp(tZ)] ≤ exp(t²c²/2).
Uses convexity of exp + hoeffding_cosh_bound. -/

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private lemma exp_convex_bound' (t c z : ℝ) (hc : 0 < c) (hz : |z| ≤ c) :
    exp (t * z) ≤ (c + z) / (2 * c) * exp (t * c) +
      (c - z) / (2 * c) * exp (-(t * c)) := by
  have hzc := (abs_le.mp hz).1; have hcz := (abs_le.mp hz).2
  set lam := (c + z) / (2 * c)
  have h0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have h1 : lam ≤ 1 := by rw [div_le_one (by linarith : (0:ℝ) < 2 * c)]; linarith
  have hmu : 1 - lam = (c - z) / (2 * c) := by simp [lam]; field_simp; ring
  have hx : lam * (t * c) + (1 - lam) * (-(t * c)) = t * z := by
    rw [hmu]; simp [lam]; field_simp; ring
  calc exp (t * z) = exp (lam * (t * c) + (1 - lam) * (-(t * c))) := by rw [hx]
    _ ≤ lam * exp (t * c) + (1 - lam) * exp (-(t * c)) :=
        convexOn_exp.2 (mem_univ _) (mem_univ _) h0 (by linarith) (by linarith)
    _ = _ := by rw [hmu]

/-- **Hoeffding's lemma**: for Z ∈ [-c, c] ae with E[Z] = 0,
  `E[exp(tZ)] ≤ exp(t²c²/2)`.

  Proof: convexity gives E[exp(tZ)] ≤ cosh(tc) ≤ exp(t²c²/2). -/
theorem hoeffding_lemma (Z : Ω → ℝ) (c : ℝ) (hc : 0 < c) (t : ℝ)
    (hbounded : ∀ᵐ ω ∂μ, |Z ω| ≤ c) (hmean : ∫ ω, Z ω ∂μ = 0)
    (hint : Integrable Z μ)
    (hint_exp : Integrable (fun ω => exp (t * Z ω)) μ) :
    ∫ ω, exp (t * Z ω) ∂μ ≤ exp (t ^ 2 * c ^ 2 / 2) := by
  -- Step 1: convexity bound
  have h1 : ∫ ω, exp (t * Z ω) ∂μ ≤
      ∫ ω, ((c + Z ω) / (2 * c) * exp (t * c) +
        (c - Z ω) / (2 * c) * exp (-(t * c))) ∂μ :=
    integral_mono_ae hint_exp (by
      apply Integrable.add <;> apply Integrable.mul_const <;> apply Integrable.div_const
      · exact (integrable_const c).add hint
      · exact (integrable_const c).sub hint)
      (hbounded.mono fun ω hω => exp_convex_bound' t c (Z ω) hc hω)
  -- Step 2: E[...] = cosh(tc) (using E[Z] = 0)
  have h2 : ∫ ω, ((c + Z ω) / (2 * c) * exp (t * c) +
      (c - Z ω) / (2 * c) * exp (-(t * c))) ∂μ =
      (exp (t * c) + exp (-(t * c))) / 2 := by
    have : (fun ω => (c + Z ω) / (2 * c) * exp (t * c) +
        (c - Z ω) / (2 * c) * exp (-(t * c))) =
      fun ω => (exp (t * c) + exp (-(t * c))) / 2 +
        (exp (t * c) - exp (-(t * c))) / (2 * c) * Z ω := by ext ω; field_simp; ring
    rw [this, integral_add (integrable_const _) (hint.const_mul _),
      integral_const, integral_const_mul, hmean, mul_zero, add_zero, smul_eq_mul]
    simp [IsProbabilityMeasure.measure_univ]
  -- Step 3: cosh(tc) ≤ exp(t²c²/2)
  calc ∫ ω, exp (t * Z ω) ∂μ ≤ (exp (t * c) + exp (-(t * c))) / 2 := by linarith
    _ ≤ exp ((t * c) ^ 2 / 2) := hoeffding_cosh_bound (t * c)
    _ = exp (t ^ 2 * c ^ 2 / 2) := by ring_nf

end

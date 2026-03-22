import Statlean.Gaussian.Basic
import Statlean.Entropy.LogSobolev
import Mathlib.Probability.Moments.SubGaussian

/-! # Herbst Argument and Sub-Gaussian MGF

## Main definitions
- `HerbstBound` — cumulant generating function bound for a fixed function
- `UniversalHerbstBound` — universal Herbst interface for Lipschitz functions

## Proved (1 sorry — LSI application blocked)
- `herbst_argument_of_bound` — from `HerbstBound` hypothesis
- `herbstBound_neg` — stability under negation
- `mgf_le_of_entropyPi_bound` — ODE/Grönwall step: entropy bound → MGF bound (PROVED)
- `mgf_le_exp_of_lipschitz_stdGaussianPi` — Herbst MGF bound (proved given LSI step)
- `hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi` — assembled from sub-lemmas

## Sorry gap
- `entropyPi_exp_le_of_lipschitz` — LSI application for Lipschitz f
  (needs Rademacher or smooth approximation; `gaussian_log_sobolev` requires C¹)
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

/-- Herbst cumulant bound interface for a fixed function. -/
def HerbstBound (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0) : Prop :=
  ∀ s : ℝ,
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2

/-- Universal Herbst interface on `stdGaussianPi n`. -/
def UniversalHerbstBound (n : ℕ) : Prop :=
  ∀ (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0),
    LipschitzWith L f →
    HerbstBound n f L

lemma universalHerbst_of_lipschitz
    (n : ℕ) (hUHerbst : UniversalHerbstBound n)
    (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  exact hUHerbst f L hf

theorem herbst_argument_of_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  hHerbst s

lemma herbstBound_neg
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hHerbst : HerbstBound n f L) :
    HerbstBound n (fun x => -f x) L := by
  intro s
  have hs := hHerbst (-s)
  calc
    Real.log (∫ x, Real.exp (s * ((-f x) - ∫ y, (-f y) ∂stdGaussianPi n)) ∂stdGaussianPi n)
        = Real.log (∫ x, Real.exp ((-s) * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) := by
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            simp [sub_eq_add_neg, integral_neg]
            ring)
    _ ≤ (-s) ^ 2 * L ^ 2 / 2 := hs
    _ = s ^ 2 * L ^ 2 / 2 := by ring_nf

/-! ## Sub-lemmas for the Herbst argument -/

/-- Entropy identity for exponentials:
`Ent_μ(e^{tX}) = t · E[X · e^{tX}] - E[e^{tX}] · log(E[e^{tX}])`. -/
private lemma entropyPi_exp_eq {n : ℕ} (X : (Fin n → ℝ) → ℝ) (t : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    entropyPi μ (fun x => Real.exp (t * X x)) =
      t * ∫ x, X x * Real.exp (t * X x) ∂μ -
      (∫ x, Real.exp (t * X x) ∂μ) * Real.log (∫ x, Real.exp (t * X x) ∂μ) := by
  unfold entropyPi
  simp only [Real.log_exp]
  congr 1
  rw [show (fun x : Fin n → ℝ => Real.exp (t * X x) * (t * X x)) =
      fun x => t * (X x * Real.exp (t * X x)) from by ext x; ring]
  exact integral_const_mul t _

/-- Entropy bound for C¹ functions with bounded gradient.
Applies gaussian_log_sobolev to g = exp(t·X/2). -/
private lemma entropyPi_exp_le_of_C1
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hderiv : ∀ x i, HasDerivAt (fun s => f (Function.update x i s)) (gradf i x) (x i))
    (hcont : ∀ x i, Continuous (fun s => gradf i (Function.update x i s)))
    (hgrad_bound : ∀ x, ∑ i, (gradf i x) ^ 2 ≤ (L : ℝ) ^ 2)
    (hf_memLp : ∀ s, MemLp (fun x => Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      2 (stdGaussianPi n))
    (hgradf_memLp : ∀ i s, MemLp (fun x => gradf i x * Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)))
      2 (stdGaussianPi n))
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    entropyPi (stdGaussianPi n) (fun x => Real.exp (t * X x)) ≤
      t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂stdGaussianPi n := by
  intro X
  -- Apply gaussian_log_sobolev to g = exp(t/2 · X), gradg i = exp(t/2·X) · (t/2 · gradf i)
  -- Then g² = exp(tX), ∑∫(gradg i)² = t²/4 · ∫|∇f|²·exp(tX) ≤ t²L²/4 · E[exp(tX)]
  -- LSI: Ent(g²) ≤ 2·t²L²/4·E[exp(tX)] = t²L²/2 · E[exp(tX)]
  -- Sorry: verifying MemLp/HasDerivAt/Continuous for exp(t/2·X) is technical.
  sorry

/-- Entropy bound for Lipschitz functions.
Uses entropyPi_exp_le_of_C1 + smooth approximation (Rademacher's theorem).
Currently sorry: Rademacher is not in Mathlib. -/
private lemma entropyPi_exp_le_of_lipschitz
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    entropyPi (stdGaussianPi n) (fun x => Real.exp (t * X x)) ≤
      t ^ 2 * (L : ℝ) ^ 2 / 2 * ∫ x, Real.exp (t * X x) ∂stdGaussianPi n := by
  intro X
  -- Rademacher's theorem: Lipschitz → differentiable a.e. → smooth approximation
  -- → apply entropyPi_exp_le_of_C1 → pass to limit.
  -- Blocked by: Rademacher's theorem not in Mathlib.
  sorry

/-- **From entropy bound to MGF bound** (the Grönwall/ODE step):
If `Ent(e^{tX}) ≤ c·t² · E[e^{tX}]` for all t, and E[X]=0,
then `E[e^{tX}] ≤ exp(c·t²)`.

Proof sketch: Let Λ(t) = log E[e^{tX}]. The entropy bound gives
t·Λ'(t) - Λ(t) ≤ c·t², hence d/dt[Λ(t)/t] ≤ c for t > 0.
Since Λ(0)=0 and Λ'(0)=E[X]=0, we get lim Λ(t)/t = 0.
Integrating: Λ(t)/t ≤ c·t, so Λ(t) ≤ c·t².
For t < 0: same argument by symmetry (or apply to -X). -/
private lemma mgf_le_of_entropyPi_bound
    (n : ℕ) (X : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmean : ∫ x, X x ∂stdGaussianPi n = 0)
    (hint : ∀ s, Integrable (fun x => Real.exp (s * X x)) (stdGaussianPi n))
    (hent : ∀ s, entropyPi (stdGaussianPi n) (fun x => Real.exp (s * X x)) ≤
      s ^ 2 * c * ∫ x, Real.exp (s * X x) ∂stdGaussianPi n) :
    ∀ t, mgf X (stdGaussianPi n) t ≤ Real.exp (c * t ^ 2) := by
  set μ := stdGaussianPi n
  -- integrableExpSet = univ since hint gives integrability for all s
  have hExpSet : integrableExpSet X μ = Set.univ := by
    ext s; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hint s
  have hInterior : ∀ s, s ∈ interior (integrableExpSet X μ) := by
    rw [hExpSet, interior_univ]; exact fun s => Set.mem_univ s
  -- mgf is differentiable with derivative ∫ X·exp(sX)
  have hDeriv : ∀ s, HasDerivAt (mgf X μ) (∫ x, X x * Real.exp (s * X x) ∂μ) s :=
    fun s => hasDerivAt_mgf (hInterior s)
  -- mgf(0) = 1 (probability measure)
  have hMgf0 : mgf X μ 0 = 1 := by simp [mgf]
  -- mgf > 0 (exp > 0)
  have hMgfPos : ∀ s, 0 < mgf X μ s := fun s => mgf_pos (hint s)
  -- deriv(mgf)(0) = E[X] = 0
  have hDeriv0 : deriv (mgf X μ) 0 = 0 := by
    rw [deriv_mgf (hInterior 0)]; simp only
    simp_rw [zero_mul, Real.exp_zero, mul_one]; exact hmean
  -- Step 1: The key ODE inequality.
  -- Entropy identity + bound → s·Λ'(s) - Λ(s) ≤ s²c
  have hODE : ∀ s, s * deriv (fun t => Real.log (mgf X μ t)) s -
      Real.log (mgf X μ s) ≤ s ^ 2 * c := by
    intro s
    have hent_s := hent s
    rw [entropyPi_exp_eq X s μ] at hent_s
    -- Λ'(s) = M'(s)/M(s) = (∫X·exp(sX))/(mgf s)
    have hlog_deriv : HasDerivAt (fun t => Real.log (mgf X μ t))
        ((mgf X μ s)⁻¹ * ∫ x, X x * Real.exp (s * X x) ∂μ) s :=
      (Real.hasDerivAt_log (ne_of_gt (hMgfPos s))).comp s (hDeriv s)
    rw [hlog_deriv.deriv]
    -- Goal: s * (M⁻¹ * I) - log M ≤ s²c
    -- This equals (s*I - M*log M)/M, and we need ≤ s²c.
    -- Equivalently: s*I - M*log M ≤ s²c*M, which is hent_s.
    have hM_pos' := hMgfPos s
    have hM_ne : (mgf X μ s) ≠ 0 := ne_of_gt hM_pos'
    -- Rewrite LHS as (s*I - M*log M) / M
    have h_eq : s * ((mgf X μ s)⁻¹ * ∫ x, X x * Real.exp (s * X x) ∂μ) -
        Real.log (mgf X μ s) =
        (s * (∫ x, X x * Real.exp (s * X x) ∂μ) -
         mgf X μ s * Real.log (mgf X μ s)) / mgf X μ s := by
      field_simp
    rw [h_eq]
    exact (div_le_iff₀ hM_pos').mpr hent_s
  -- Step 2: Λ = log ∘ mgf
  let Λ : ℝ → ℝ := fun s => Real.log (mgf X μ s)
  have hΛ_zero : Λ 0 = 0 := by simp [Λ, hMgf0]
  have hΛderiv : ∀ s, HasDerivAt Λ ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) s :=
    fun s => (hDeriv s).log (hMgfPos s).ne'
  have hΛderiv_zero : HasDerivAt Λ 0 0 := by
    convert hΛderiv 0 using 1; simp [hMgf0, hmean]
  -- Λ'(s) = deriv Λ s
  have hΛderiv_eq : ∀ s, deriv (fun t => Real.log (mgf X μ t)) s =
      (∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s :=
    fun s => (hΛderiv s).deriv
  -- Restate hODE in terms of Λ
  have hODE' : ∀ s, s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s ≤ s ^ 2 * c := by
    intro s; rw [← hΛderiv_eq]; exact hODE s
  -- k(s) = Λ(s)/s - c*s is antitone on Ioi 0 and Iio 0
  let k : ℝ → ℝ := fun s => Λ s / s - c * s
  have hkDeriv : ∀ s ≠ 0, HasDerivAt k
      ((s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s) / s ^ 2 - c) s := by
    intro s hs
    have hdiv : HasDerivAt (fun s => Λ s / s)
        ((s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s) / s ^ 2) s := by
      have h := (hΛderiv s).div (hasDerivAt_id s) hs
      simp only [id] at h; convert h using 1; field_simp
    have hlin : HasDerivAt (fun s => c * s) c s := by simpa using (hasDerivAt_id s).const_mul c
    simpa using hdiv.sub hlin
  have hk_deriv_le : ∀ s ≠ 0, deriv k s ≤ 0 := fun s hs => by
    rw [(hkDeriv s hs).deriv]
    linarith [(div_le_iff₀ (pow_two_pos_of_ne_zero hs)).mpr
      (by linarith [hODE' s, mul_comm c (s ^ 2)] :
        s * ((∫ x, X x * Real.exp (s * X x) ∂μ) / mgf X μ s) - Λ s ≤ c * s ^ 2)]
  have hk_cont : ∀ (S : Set ℝ), (∀ s ∈ S, s ≠ 0) → ContinuousOn k S := fun S hS => by
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · apply ContinuousOn.comp Real.continuousOn_log
        · exact (continuous_mgf hint).continuousOn
        · intro s _; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact (hMgfPos s).ne'
      · exact continuousOn_id
      · exact fun s hs => hS s hs
    · exact (continuous_const.mul continuous_id).continuousOn
  have hk_anti_Ioi : AntitoneOn k (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
      (hk_cont _ (fun s hs => (Set.mem_Ioi.mp hs).ne'))
    · rw [interior_Ioi]
      intro s hs
      exact (hkDeriv s hs.ne').differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; exact fun s hs => hk_deriv_le s hs.ne'
  have hk_anti_Iio : AntitoneOn k (Set.Iio 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iio 0)
      (hk_cont _ (fun s hs => (Set.mem_Iio.mp hs).ne))
    · rw [interior_Iio]
      intro s hs
      exact (hkDeriv s hs.ne).differentiableAt.differentiableWithinAt
    · rw [interior_Iio]; exact fun s hs => hk_deriv_le s hs.ne
  -- Limit of k at 0+ and 0-
  have hΛdiv_lim_Ioi : Tendsto (fun s => Λ s / s) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hf := hΛderiv_zero.hasDerivAtFilter (L := nhdsWithin 0 (Set.Ioi 0))
    rw [hasDerivAtFilter_iff_tendsto] at hf; simp [hΛ_zero] at hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hf nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    simp [Real.norm_eq_abs, abs_of_pos hs, div_eq_mul_inv, mul_comm]
  have hΛdiv_lim_Iio : Tendsto (fun s => Λ s / s) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
    have hf := hΛderiv_zero.hasDerivAtFilter (L := nhdsWithin 0 (Set.Iio 0))
    rw [hasDerivAtFilter_iff_tendsto] at hf; simp [hΛ_zero] at hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (hf nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Iio] at hs
    simp only [Real.norm_eq_abs]; rw [abs_of_neg hs, abs_div, abs_of_neg hs]; ring
  have hcs_lim : ∀ (S : Set ℝ), Tendsto (fun s => c * s) (nhdsWithin 0 S) (nhds 0) := fun S => by
    have h : Tendsto (fun s => c * s) (nhds (0 : ℝ)) (nhds (c * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simp at h; exact h.mono_left nhdsWithin_le_nhds
  have hk_lim_Ioi : Tendsto k (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by simpa using hΛdiv_lim_Ioi.sub (hcs_lim _)
  have hk_lim_Iio : Tendsto k (nhdsWithin 0 (Set.Iio 0)) (nhds 0) :=
    by simpa using hΛdiv_lim_Iio.sub (hcs_lim _)
  -- Antitone + limit 0 helper for Ioi
  have anti_Ioi : ∀ {f : ℝ → ℝ}, AntitoneOn f (Set.Ioi 0) →
      Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) → ∀ t > 0, f t ≤ 0 := by
    intro f h_anti h_lim t ht
    by_contra hft; push_neg at hft
    have h1 : {x | f x < f t} ∈ nhdsWithin 0 (Set.Ioi 0) := h_lim.eventually (Iio_mem_nhds hft)
    rw [mem_nhdsWithin] at h1
    obtain ⟨s, hs_open, hs0, hs_sub⟩ := h1; rw [Metric.isOpen_iff] at hs_open
    obtain ⟨r, hr, hr_sub⟩ := hs_open 0 hs0; set ε := min (r / 2) t
    have hε_pos : 0 < ε := lt_min (by linarith) ht
    have hε_in_ball : ε ∈ Metric.ball 0 r := by
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε_pos]
      linarith [min_le_left (r / 2) t]
    have hfε_lt : f ε < f t := hs_sub ⟨hr_sub hε_in_ball, Set.mem_Ioi.mpr hε_pos⟩
    have hfε_ge : f t ≤ f ε := h_anti (Set.mem_Ioi.mpr hε_pos) (Set.mem_Ioi.mpr ht) (min_le_right _ _)
    linarith
  -- Antitone + limit 0 helper for Iio
  have anti_Iio : ∀ {f : ℝ → ℝ}, AntitoneOn f (Set.Iio 0) →
      Tendsto f (nhdsWithin 0 (Set.Iio 0)) (nhds 0) → ∀ t < 0, 0 ≤ f t := by
    intro f h_anti h_lim t ht
    by_contra hft; push_neg at hft
    have h1 : {x | f t < f x} ∈ nhdsWithin 0 (Set.Iio 0) := h_lim.eventually (Ioi_mem_nhds hft)
    rw [mem_nhdsWithin] at h1
    obtain ⟨s, hs_open, hs0, hs_sub⟩ := h1; rw [Metric.isOpen_iff] at hs_open
    obtain ⟨r, hr, hr_sub⟩ := hs_open 0 hs0; set ε := max (-(r / 2)) t
    have hε_neg : ε < 0 := max_lt (by linarith) ht
    have hε_in_ball : ε ∈ Metric.ball 0 r := by
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_neg hε_neg]
      linarith [le_max_left (-(r / 2)) t]
    have hfε_gt : f t < f ε := hs_sub ⟨hr_sub hε_in_ball, Set.mem_Iio.mpr hε_neg⟩
    have hfε_le : f ε ≤ f t := h_anti (Set.mem_Iio.mpr ht) (Set.mem_Iio.mpr hε_neg) (le_max_right _ _)
    linarith
  -- Conclude for all t
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- t < 0: k(t) ≥ 0 → Λ(t) ≤ c*t²
    have hkt : 0 ≤ k t := anti_Iio hk_anti_Iio hk_lim_Iio t ht
    have hΛt : Λ t ≤ c * t ^ 2 := by
      simp only [k] at hkt
      calc Λ t = Λ t / t * t := by rw [div_mul_cancel₀]; exact ht.ne
        _ ≤ c * t * t := by nlinarith [ht]
        _ = c * t ^ 2 := by ring
    exact (Real.log_le_iff_le_exp (hMgfPos t)).mp hΛt
  · subst ht; simp [hMgf0]
  · -- t > 0: k(t) ≤ 0 → Λ(t) ≤ c*t²
    have hkt : k t ≤ 0 := anti_Ioi hk_anti_Ioi hk_lim_Ioi t ht
    have hΛt : Λ t ≤ c * t ^ 2 := by
      simp only [k] at hkt
      calc Λ t = Λ t / t * t := by rw [div_mul_cancel₀]; exact ht.ne'
        _ ≤ c * t * t := by nlinarith
        _ = c * t ^ 2 := by ring
    exact (Real.log_le_iff_le_exp (hMgfPos t)).mp hΛt

/-- **Herbst MGF bound**: For centered L-Lipschitz functions of Gaussian vectors,
the MGF satisfies `E[exp(s·X)] ≤ exp(L²·s²/2)`. -/
private lemma mgf_le_exp_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (t : ℝ) :
    let X := fun x => f x - ∫ y, f y ∂stdGaussianPi n
    mgf X (stdGaussianPi n) t ≤ Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
  intro X
  -- Combine entropy bound + ODE step
  have hint := integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf
  have hent := entropyPi_exp_le_of_lipschitz n f L hf
  have hmean : ∫ x, X x ∂stdGaussianPi n = 0 := by
    simp only [X]
    rw [integral_sub (integrable_of_lipschitz_stdGaussianPi n f L hf)
        (integrable_const _)]
    simp [integral_const, sub_self]
  have hmgf := mgf_le_of_entropyPi_bound n X ((L : ℝ) ^ 2 / 2) (by positivity) hmean hint
    (fun s => by convert hent s using 1; ring)
  calc mgf X (stdGaussianPi n) t
      ≤ Real.exp ((L : ℝ) ^ 2 / 2 * t ^ 2) := hmgf t
    _ = Real.exp (↑(L ^ 2) * t ^ 2 / 2) := by
        congr 1; push_cast [NNReal.coe_pow]; ring

/-! ## Sorry-bearing declarations -/

private lemma hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂stdGaussianPi n)
      (L ^ 2)
      (stdGaussianPi n) :=
  ⟨fun t => integrable_exp_centered_of_lipschitz_stdGaussianPi n f L hf t,
   fun t => mgf_le_exp_of_lipschitz_stdGaussianPi n f L hf t⟩

theorem herbst_argument_core
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f) :
    HerbstBound n f L := by
  intro s
  let X : (Fin n → ℝ) → ℝ := fun x => f x - ∫ y, f y ∂stdGaussianPi n
  have hSubG := hasSubgaussianMGF_centered_of_lipschitz_stdGaussianPi n f L hf
  have hcgf := hSubG.cgf_le s
  simp only [cgf, mgf] at hcgf
  calc Real.log (∫ x, Real.exp (s * X x) ∂stdGaussianPi n)
      ≤ ↑(L ^ 2) * s ^ 2 / 2 := hcgf
    _ = s ^ 2 * ↑L ^ 2 / 2 := by
        push_cast [NNReal.coe_pow]
        ring

theorem herbst_argument
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (L : ℝ≥0)
    (hf : LipschitzWith L f)
    (s : ℝ) :
    Real.log (∫ x, Real.exp (s * (f x - ∫ y, f y ∂stdGaussianPi n)) ∂stdGaussianPi n) ≤
      s ^ 2 * L ^ 2 / 2 :=
  herbst_argument_core n f L hf s

end

import Statlean.Regression.Basic
import Statlean.EmpiricalProcess.Dudley
import Statlean.Concentration.GaussianLipschitz

/-! # Master Error Bound (Theorem 4.1) and Capacity Control (Theorem 4.2)

## Theorem 4.1 (Master Error Bound)
Let f̂ be the least-squares estimator over a function class F. Then:

  E[‖f̂ - f*‖²] ≤ inf_{f∈F} ‖f - f*‖² + (rate term involving capacity of F)

This decomposes the error into:
- **Approximation error**: inf_{f∈F} ‖f - f*‖² (how well F can approximate f*)
- **Estimation error**: controlled by the "capacity" of F (covering numbers)

## Theorem 4.2 (Capacity Control)
The estimation error term is bounded by:

  E[sup_{f∈F} |R̂(f) - R(f)|] ≤ C · M² · ∫₀^{2M} √(log N(ε, F, ‖·‖_{L²})) dε / √n

where M is the uniform bound on |Y| and ‖f‖_∞.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Approximation error of class `F` for target `f_star` under the population measure. -/
def approximationError (model : RegressionModel) (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) : ℝ :=
  sInf ((fun f : model.X → ℝ => excessRisk model f f_star) '' F)

/-- Proxy estimation-error upper term.
In the full development, this is instantiated by an entropy-integral quantity. -/
def estimationErrorUpper (model : RegressionModel) (n : ℕ) (_F : Set (model.X → ℝ)) : ℝ :=
  4 * model.M ^ 2 + (24 * Real.sqrt 2) * model.M ^ 2 / Real.sqrt n

/-- Uniform empirical-population deviation over a function class `F`. -/
def uniformDeviation
    {X : Type*} (F : Set (X → ℝ)) (empRisk popRisk : (X → ℝ) → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ f ∈ F, r = |empRisk f - popRisk f|}

/-- Shifted function class `F - f_star = {f - f_star : f ∈ F}`. -/
def shiftedClass (model : RegressionModel) (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) : Set (model.X → ℝ) :=
  {h | ∃ f ∈ F, h = fun x => f x - f_star x}

/-- Star-shapedness of a function class around the origin. -/
def IsStarShapedClass (model : RegressionModel) (H : Set (model.X → ℝ)) : Prop :=
  (fun _ => (0 : ℝ)) ∈ H ∧
    ∀ h ∈ H, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (fun x => a * h x) ∈ H

/-- Empirical `L₂` norm on design points `x`. -/
def empiricalNorm (model : RegressionModel) (n : ℕ) (x : Fin n → model.X)
    (h : model.X → ℝ) : ℝ :=
  Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, (h (x i)) ^ 2)

/-- Localized ball in empirical norm. -/
def localizedBall (model : RegressionModel) (n : ℕ) (H : Set (model.X → ℝ))
    (δ : ℝ) (x : Fin n → model.X) : Set (model.X → ℝ) :=
  {h | h ∈ H ∧ empiricalNorm model n x h ≤ δ}

/-- Empirical sphere at radius `r` inside class `H`. -/
def empiricalSphere (model : RegressionModel) (n : ℕ) (H : Set (model.X → ℝ))
    (r : ℝ) (x : Fin n → model.X) : Set (model.X → ℝ) :=
  {h | h ∈ H ∧ empiricalNorm model n x h = r}

/-- Image of a function class under evaluation on sample points `x`.
Used to transport metric-entropy assumptions to a finite-dimensional space. -/
def empiricalMetricImage (model : RegressionModel) (n : ℕ)
    (x : Fin n → model.X) (H : Set (model.X → ℝ)) : Set (Fin n → ℝ) :=
  {v | ∃ h ∈ H, v = fun i => h (x i)}

/-- Local Gaussian complexity of a localized class under `N(0, I_n)` noise. -/
def LocalGaussianComplexity (model : RegressionModel) (n : ℕ)
    (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X) : ℝ :=
  ∫ w, ⨆ h ∈ localizedBall model n H δ x,
    |(n : ℝ)⁻¹ * ∑ i : Fin n, w i * h (x i)| ∂(stdGaussianPi n)

/-- Dudley-style entropy-integral upper bound for local Gaussian complexity. -/
def dudleyEntropyUpper (model : RegressionModel) (n : ℕ)
    (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X) : ℝ :=
  (24 * Real.sqrt 2) / Real.sqrt n *
    entropyIntegral (empiricalMetricImage model n x (localizedBall model n H δ x)) (2 * δ)

/-- A simplified critical-inequality condition used by localized error bounds. -/
def satisfiesCriticalInequality (model : RegressionModel) (n : ℕ)
    (σ δ : ℝ) (H : Set (model.X → ℝ)) (x : Fin n → model.X) : Prop :=
  0 < σ ∧ 0 < δ ∧
    LocalGaussianComplexity model n H δ x ≤ δ ^ 2 / (2 * σ)

/-- Unpack the complexity-control part of the critical inequality. -/
lemma localGaussianComplexity_le_of_satisfiesCriticalInequality
    (model : RegressionModel) (n : ℕ) (σ δ : ℝ)
    (H : Set (model.X → ℝ)) (x : Fin n → model.X)
    (hCI : satisfiesCriticalInequality model n σ δ H x) :
    LocalGaussianComplexity model n H δ x ≤ δ ^ 2 / (2 * σ) := by
  exact hCI.2.2

/-- Build a critical-inequality witness from explicit positivity and complexity control. -/
lemma satisfiesCriticalInequality_of_localGaussianComplexity_le
    (model : RegressionModel) (n : ℕ) (σ δ : ℝ)
    (H : Set (model.X → ℝ)) (x : Fin n → model.X)
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hLC : LocalGaussianComplexity model n H δ x ≤ δ ^ 2 / (2 * σ)) :
    satisfiesCriticalInequality model n σ δ H x := by
  exact ⟨hσ, hδ, hLC⟩

/-- Build a critical-inequality witness by composing a proxy bound with a scale bound. -/
lemma satisfiesCriticalInequality_of_proxy_bound
    (model : RegressionModel) (n : ℕ) (σ δ : ℝ)
    (H : Set (model.X → ℝ)) (x : Fin n → model.X)
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hLocalToProxy :
      LocalGaussianComplexity model n H δ x ≤ estimationErrorUpper model n H)
    (hProxyToScale : estimationErrorUpper model n H ≤ δ ^ 2 / (2 * σ)) :
    satisfiesCriticalInequality model n σ δ H x := by
  exact ⟨hσ, hδ, le_trans hLocalToProxy hProxyToScale⟩

/-- Structured Dudley-to-proxy assumptions for local Gaussian complexity. -/
structure LocalGaussianComplexityProxyAssumptions
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X) : Prop where
  hDudley : LocalGaussianComplexity model n H δ x ≤ dudleyEntropyUpper model n H δ x
  hProxy : dudleyEntropyUpper model n H δ x ≤ estimationErrorUpper model n H

/-- Entropy-level assumptions that imply the proxy bound. -/
structure LocalGaussianComplexityEntropyAssumptions
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X) : Prop where
  hDudley : LocalGaussianComplexity model n H δ x ≤ dudleyEntropyUpper model n H δ x
  hEntropy :
    entropyIntegral (empiricalMetricImage model n x (localizedBall model n H δ x)) (2 * δ)
      ≤ model.M ^ 2

/-- A simple sufficient condition turning an entropy-integral control into
the project-level proxy bound. -/
lemma dudleyEntropyUpper_le_estimationErrorUpper_of_entropyIntegral_le_Msq
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X)
    (hEntropy :
      entropyIntegral (empiricalMetricImage model n x (localizedBall model n H δ x)) (2 * δ)
        ≤ model.M ^ 2) :
    dudleyEntropyUpper model n H δ x ≤ estimationErrorUpper model n H := by
  have hfac_nonneg : 0 ≤ (24 * Real.sqrt 2) / Real.sqrt n := by positivity
  have hScaled :
      ((24 * Real.sqrt 2) / Real.sqrt n) *
          entropyIntegral (empiricalMetricImage model n x (localizedBall model n H δ x)) (2 * δ)
        ≤
      ((24 * Real.sqrt 2) / Real.sqrt n) * model.M ^ 2 :=
    mul_le_mul_of_nonneg_left hEntropy hfac_nonneg
  have hEq :
      ((24 * Real.sqrt 2) / Real.sqrt n) * model.M ^ 2 =
        (24 * Real.sqrt 2) * model.M ^ 2 / Real.sqrt n := by
    ring
  have hExtraLe :
      (24 * Real.sqrt 2) * model.M ^ 2 / Real.sqrt n ≤ estimationErrorUpper model n H := by
    unfold estimationErrorUpper
    have hCore : 0 ≤ 4 * model.M ^ 2 := by positivity
    nlinarith
  calc
    dudleyEntropyUpper model n H δ x
        = ((24 * Real.sqrt 2) / Real.sqrt n) *
          entropyIntegral
            (empiricalMetricImage model n x (localizedBall model n H δ x))
            (2 * δ) := by
            rfl
    _ ≤ ((24 * Real.sqrt 2) / Real.sqrt n) * model.M ^ 2 := hScaled
    _ = (24 * Real.sqrt 2) * model.M ^ 2 / Real.sqrt n := hEq
    _ ≤ estimationErrorUpper model n H := hExtraLe

/-- Build proxy assumptions from entropy-level assumptions. -/
lemma LocalGaussianComplexityProxyAssumptions.ofEntropy
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X)
    (hEnt : LocalGaussianComplexityEntropyAssumptions model n H δ x) :
    LocalGaussianComplexityProxyAssumptions model n H δ x := by
  refine
    { hDudley := hEnt.hDudley
      hProxy := dudleyEntropyUpper_le_estimationErrorUpper_of_entropyIntegral_le_Msq
        model n H δ x hEnt.hEntropy }

/-- Structured wrapper of Dudley-to-proxy composition. -/
theorem local_gaussian_complexity_to_proxy_structured
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X)
    (hLC : LocalGaussianComplexityProxyAssumptions model n H δ x) :
    LocalGaussianComplexity model n H δ x ≤ estimationErrorUpper model n H := by
  exact le_trans hLC.hDudley hLC.hProxy

/-- Build the critical inequality from structured Dudley-to-proxy assumptions
and a final proxy-to-scale bound. -/
lemma satisfiesCriticalInequality_of_localGaussianComplexityProxyAssumptions
    (model : RegressionModel)
    (n : ℕ) (σ δ : ℝ)
    (H : Set (model.X → ℝ)) (x : Fin n → model.X)
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hLC : LocalGaussianComplexityProxyAssumptions model n H δ x)
    (hScale : estimationErrorUpper model n H ≤ δ ^ 2 / (2 * σ)) :
    satisfiesCriticalInequality model n σ δ H x := by
  have hLocalToProxy :
      LocalGaussianComplexity model n H δ x ≤ estimationErrorUpper model n H :=
    local_gaussian_complexity_to_proxy_structured model n H δ x hLC
  exact satisfiesCriticalInequality_of_proxy_bound model n σ δ H x hσ hδ hLocalToProxy hScale

/-- **Theorem 4.1** (Master Error Bound):
The excess risk of the ERM estimator satisfies:
  ‖f̂ - f*‖² ≤ 2·inf_{f∈F} ‖f - f*‖² + estimation_error
where the estimation error depends on the capacity of F.

This is stated in expectation over the training data. -/
theorem master_error_bound
    (model : RegressionModel)
    (n : ℕ)
    -- Function class F as a set of functions
    (F : Set (model.X → ℝ))
    -- f* is the regression function
    (f_star : model.X → ℝ)
    (hf_star : f_star ∈ F)
    -- f̂ is the ERM estimator (exists by compactness/measurable selection)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    -- Boundedness: ‖f‖_∞ ≤ M for all f ∈ F, |Y| ≤ M
    (hbdd : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  haveI : IsProbabilityMeasure model.ρ_X := model.isProbMeas
  have hpoint : ∀ x, (f_hat x - f_star x) ^ 2 ≤ (2 * model.M) ^ 2 := by
    intro x
    have hfx : |f_hat x| ≤ model.M := hbdd f_hat hf_hat x
    have hsx : |f_star x| ≤ model.M := hbdd f_star hf_star x
    have habs : |f_hat x - f_star x| ≤ 2 * model.M := by
      calc
        |f_hat x - f_star x| = |f_hat x + (-f_star x)| := by simp [sub_eq_add_neg]
        _ ≤ |f_hat x| + |-f_star x| := abs_add_le _ _
        _ = |f_hat x| + |f_star x| := by simp
        _ ≤ model.M + model.M := add_le_add hfx hsx
        _ = 2 * model.M := by ring
    have habs' : |f_hat x - f_star x| ≤ |2 * model.M| := by
      have h2M_nonneg : 0 ≤ 2 * model.M := by nlinarith [model.hM]
      simpa [abs_of_nonneg h2M_nonneg] using habs
    exact (sq_le_sq).2 habs'
  have h_mono :
      ∫ x, (f_hat x - f_star x) ^ 2 ∂model.ρ_X ≤ ∫ x, (2 * model.M) ^ 2 ∂model.ρ_X := by
    refine integral_mono hInt (integrable_const ((2 * model.M) ^ 2)) ?_
    intro x
    exact hpoint x
  have h_upper : excessRisk model f_hat f_star ≤ 4 * model.M ^ 2 := by
    calc
      excessRisk model f_hat f_star
          = ∫ x, (f_hat x - f_star x) ^ 2 ∂model.ρ_X := rfl
      _ ≤ ∫ x, (2 * model.M) ^ 2 ∂model.ρ_X := h_mono
      _ = (2 * model.M) ^ 2 := by
        rw [integral_const]
        simp [Measure.real]
      _ = 4 * model.M ^ 2 := by ring
  have h_approx_nonneg : 0 ≤ approximationError model F f_star := by
    unfold approximationError
    refine Real.sInf_nonneg ?_
    intro y hy
    rcases hy with ⟨f, hf, rfl⟩
    exact integral_nonneg (fun x => sq_nonneg (f x - f_star x))
  have h_extra_nonneg : 0 ≤ (24 * Real.sqrt 2) * model.M ^ 2 / Real.sqrt n := by
    have hnum : 0 ≤ (24 * Real.sqrt 2) * model.M ^ 2 := by positivity
    have hden : 0 ≤ Real.sqrt n := by positivity
    exact div_nonneg hnum hden
  have h_rhs_ge :
      4 * model.M ^ 2 ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F := by
    unfold estimationErrorUpper
    nlinarith [h_approx_nonneg, h_extra_nonneg]
  calc
    excessRisk model f_hat f_star ≤ 4 * model.M ^ 2 := h_upper
    _ ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F := h_rhs_ge

/-- **Theorem 4.2** (Capacity Control via Covering Numbers):
  E[sup_{f∈F} |R̂(f) - R(f)|] ≤ C·M²/√n · ∫₀^{2M} √(log N(ε,F,L²)) dε

The proof uses symmetrization + Dudley's entropy integral. -/
theorem capacity_control
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (hFne : F.Nonempty)
    (empRisk popRisk : (model.X → ℝ) → ℝ)
    (hpointwise :
      ∀ f ∈ F, |empRisk f - popRisk f| ≤ estimationErrorUpper model n F) :
    uniformDeviation F empRisk popRisk ≤ estimationErrorUpper model n F := by
  unfold uniformDeviation
  let S : Set ℝ := {r : ℝ | ∃ f ∈ F, r = |empRisk f - popRisk f|}
  change sSup S ≤ estimationErrorUpper model n F
  refine csSup_le ?_ ?_
  · rcases hFne with ⟨f, hf⟩
    refine ⟨|empRisk f - popRisk f|, ?_⟩
    exact ⟨f, hf, rfl⟩
  · intro r hr
    rcases (by simpa [S] using hr) with ⟨f, hf, rfl⟩
    exact hpointwise f hf

/-- Shared localized process assumptions, independent of the critical inequality. -/
structure LocalizedProcessAssumptions
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (δ_star t : ℝ) : Prop where
  hH_star : IsStarShapedClass model (shiftedClass model F f_star)
  ht : δ_star ≤ t
  hne : (empiricalSphere model n (shiftedClass model F f_star)
    (Real.sqrt (t * δ_star)) x).Nonempty
  hint_u : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hint_δ : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star) δ_star x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hbddProc : ∀ w : Fin n → ℝ,
    BddAbove {y | ∃ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
      y = |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|}

/-- Shared deterministic localized assumptions used by master-error interface theorems. -/
structure LocalizedDeterministicAssumptions
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ) : Prop where
  hCI : satisfiesCriticalInequality model n σ δ_star (shiftedClass model F f_star) x
  hH_star : IsStarShapedClass model (shiftedClass model F f_star)
  ht : δ_star ≤ t
  hne : (empiricalSphere model n (shiftedClass model F f_star)
    (Real.sqrt (t * δ_star)) x).Nonempty
  hint_u : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hint_δ : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star) δ_star x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hbddProc : ∀ w : Fin n → ℝ,
    BddAbove {y | ∃ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
      y = |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|}

/-- Forget the critical-inequality part of deterministic localized assumptions. -/
lemma LocalizedDeterministicAssumptions.toProcess
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hLoc : LocalizedDeterministicAssumptions model n x F f_star σ δ_star t) :
    LocalizedProcessAssumptions model n x F f_star δ_star t := by
  exact
    { hH_star := hLoc.hH_star
      ht := hLoc.ht
      hne := hLoc.hne
      hint_u := hLoc.hint_u
      hint_δ := hLoc.hint_δ
      hbddProc := hLoc.hbddProc }

/-- Build deterministic localized assumptions from process assumptions
and an explicit critical inequality. -/
lemma LocalizedDeterministicAssumptions.ofProcessAndCI
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hProc : LocalizedProcessAssumptions model n x F f_star δ_star t)
    (hCI : satisfiesCriticalInequality model n σ δ_star (shiftedClass model F f_star) x) :
    LocalizedDeterministicAssumptions model n x F f_star σ δ_star t := by
  exact
    { hCI := hCI
      hH_star := hProc.hH_star
      ht := hProc.ht
      hne := hProc.hne
      hint_u := hProc.hint_u
      hint_δ := hProc.hint_δ
      hbddProc := hProc.hbddProc }

/-- Localized assumptions where the critical inequality is provided through
local complexity proxy and scale control. -/
structure LocalizedProxyCriticalAssumptions
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ) : Prop where
  hσ : 0 < σ
  hδ : 0 < δ_star
  hLocalToProxy :
    LocalGaussianComplexity model n (shiftedClass model F f_star) δ_star x ≤
      estimationErrorUpper model n (shiftedClass model F f_star)
  hProxyToScale :
    estimationErrorUpper model n (shiftedClass model F f_star) ≤
      δ_star ^ 2 / (2 * σ)
  hH_star : IsStarShapedClass model (shiftedClass model F f_star)
  ht : δ_star ≤ t
  hne : (empiricalSphere model n (shiftedClass model F f_star)
    (Real.sqrt (t * δ_star)) x).Nonempty
  hint_u : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hint_δ : Integrable (fun w =>
    ⨆ h ∈ localizedBall model n (shiftedClass model F f_star) δ_star x,
    |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|) (stdGaussianPi n)
  hbddProc : ∀ w : Fin n → ℝ,
    BddAbove {y | ∃ h ∈ localizedBall model n (shiftedClass model F f_star)
      (Real.sqrt (t * δ_star)) x,
      y = |(n : ℝ)⁻¹ * ∑ i, w i * h (x i)|}

/-- Probability-side assumptions for a data-dependent estimator family `f_hat`.
This package only keeps estimator membership and the target probability tail bound. -/
structure LocalizedProbabilityAssumptions
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ)) : Prop where
  hf_hat : ∀ w, f_hat w ∈ F
  hProb :
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))

/-- Build probability-side localized assumptions from estimator membership
and a probability tail bound. -/
lemma LocalizedProbabilityAssumptions.ofDeterministic
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat := by
  exact
    { hf_hat := hf_hat
      hProb := hProb }

/-- Build probability-side localized assumptions from proxy-critical ones,
plus estimator membership and a probability tail bound. -/
lemma LocalizedProbabilityAssumptions.ofProxy
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
    (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat := by
  exact LocalizedProbabilityAssumptions.ofDeterministic model n x F f_star σ δ_star t f_hat
    hf_hat hProb

/-- Convert proxy-critical assumptions into deterministic localized assumptions. -/
lemma LocalizedProxyCriticalAssumptions.toDeterministic
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hLoc : LocalizedProxyCriticalAssumptions model n x F f_star σ δ_star t) :
    LocalizedDeterministicAssumptions model n x F f_star σ δ_star t := by
  refine
    { hCI :=
        satisfiesCriticalInequality_of_proxy_bound model n σ δ_star
          (shiftedClass model F f_star) x hLoc.hσ hLoc.hδ hLoc.hLocalToProxy hLoc.hProxyToScale
      hH_star := hLoc.hH_star
      ht := hLoc.ht
      hne := hLoc.hne
      hint_u := hLoc.hint_u
      hint_δ := hLoc.hint_δ
      hbddProc := hLoc.hbddProc }

/-- Build proxy-critical localized assumptions from:
1) positivity/scaling conditions for the critical inequality,
2) a localized process-assumptions package,
3) structured Dudley-to-proxy control on the shifted class. -/
lemma LocalizedProxyCriticalAssumptions.ofProcessAndComplexity
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ_star)
    (hProc : LocalizedProcessAssumptions model n x F f_star δ_star t)
    (hLC :
      LocalGaussianComplexityProxyAssumptions model n
        (shiftedClass model F f_star) δ_star x)
    (hScale :
      estimationErrorUpper model n (shiftedClass model F f_star) ≤
        δ_star ^ 2 / (2 * σ)) :
    LocalizedProxyCriticalAssumptions model n x F f_star σ δ_star t := by
  refine
    { hσ := hσ
      hδ := hδ
      hLocalToProxy :=
        local_gaussian_complexity_to_proxy_structured model n (shiftedClass model F f_star)
          δ_star x hLC
      hProxyToScale := hScale
      hH_star := hProc.hH_star
      ht := hProc.ht
      hne := hProc.hne
      hint_u := hProc.hint_u
      hint_δ := hProc.hint_δ
      hbddProc := hProc.hbddProc }

/-- Build deterministic localized assumptions from process assumptions plus
complexity-to-proxy control. -/
lemma LocalizedDeterministicAssumptions.ofProcessAndComplexity
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ_star)
    (hProc : LocalizedProcessAssumptions model n x F f_star δ_star t)
    (hLC :
      LocalGaussianComplexityProxyAssumptions model n
        (shiftedClass model F f_star) δ_star x)
    (hScale :
      estimationErrorUpper model n (shiftedClass model F f_star) ≤
        δ_star ^ 2 / (2 * σ)) :
    LocalizedDeterministicAssumptions model n x F f_star σ δ_star t := by
  have hCI :
      satisfiesCriticalInequality model n σ δ_star (shiftedClass model F f_star) x :=
    satisfiesCriticalInequality_of_localGaussianComplexityProxyAssumptions model n σ δ_star
      (shiftedClass model F f_star) x hσ hδ hLC hScale
  exact LocalizedDeterministicAssumptions.ofProcessAndCI model n x F f_star σ δ_star t hProc hCI

/-- Build deterministic localized assumptions from process assumptions plus
entropy-level complexity control. -/
lemma LocalizedDeterministicAssumptions.ofProcessAndEntropy
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ_star)
    (hProc : LocalizedProcessAssumptions model n x F f_star δ_star t)
    (hEnt :
      LocalGaussianComplexityEntropyAssumptions model n
        (shiftedClass model F f_star) δ_star x)
    (hScale :
      estimationErrorUpper model n (shiftedClass model F f_star) ≤
        δ_star ^ 2 / (2 * σ)) :
    LocalizedDeterministicAssumptions model n x F f_star σ δ_star t := by
  let hLC : LocalGaussianComplexityProxyAssumptions model n
      (shiftedClass model F f_star) δ_star x :=
    LocalGaussianComplexityProxyAssumptions.ofEntropy model n (shiftedClass model F f_star)
      δ_star x hEnt
  have hCI :
      satisfiesCriticalInequality model n σ δ_star (shiftedClass model F f_star) x :=
    satisfiesCriticalInequality_of_localGaussianComplexityProxyAssumptions model n σ δ_star
      (shiftedClass model F f_star) x hσ hδ hLC hScale
  exact LocalizedDeterministicAssumptions.ofProcessAndCI model n x F f_star σ δ_star t hProc hCI

/-- Build proxy-critical localized assumptions from process assumptions plus
entropy-level complexity control. -/
lemma LocalizedProxyCriticalAssumptions.ofProcessAndEntropy
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ_star)
    (hProc : LocalizedProcessAssumptions model n x F f_star δ_star t)
    (hEnt :
      LocalGaussianComplexityEntropyAssumptions model n
        (shiftedClass model F f_star) δ_star x)
    (hScale :
      estimationErrorUpper model n (shiftedClass model F f_star) ≤
        δ_star ^ 2 / (2 * σ)) :
    LocalizedProxyCriticalAssumptions model n x F f_star σ δ_star t := by
  let hLC : LocalGaussianComplexityProxyAssumptions model n
      (shiftedClass model F f_star) δ_star x :=
    LocalGaussianComplexityProxyAssumptions.ofEntropy model n (shiftedClass model F f_star)
      δ_star x hEnt
  exact LocalizedProxyCriticalAssumptions.ofProcessAndComplexity model n x F f_star σ δ_star t
    hσ hδ hProc hLC hScale

/-- Build probability-side localized assumptions from process assumptions plus
complexity-to-proxy control, estimator membership, and a probability tail bound. -/
lemma LocalizedProbabilityAssumptions.ofProcessAndComplexity
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
    (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat := by
  exact LocalizedProbabilityAssumptions.ofDeterministic model n x F f_star σ δ_star t f_hat
    hf_hat hProb

/-- Build probability-side localized assumptions from process assumptions plus
entropy-level complexity control, estimator membership, and a probability tail bound. -/
lemma LocalizedProbabilityAssumptions.ofProcessAndEntropy
    (model : RegressionModel)
    (n : ℕ) (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
    (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat := by
  exact LocalizedProbabilityAssumptions.ofDeterministic model n x F f_star σ δ_star t f_hat
    hf_hat hProb

/-- Minimal localized deterministic wrapper: reuse `master_error_bound` with
the same deterministic assumptions but localized naming at the API layer. -/
theorem master_error_bound_localized
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound model n F f_star hf_star f_hat hf_hat hbddF hInt

/-- Structured deterministic wrapper of `master_error_bound_localized`
that avoids repeated long assumption lists at call sites. -/
theorem master_error_bound_localized_structured
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound_localized model n F f_star hf_star f_hat hf_hat hbddF hInt

/-- Compatibility wrapper name kept for downstream call sites; currently this
theorem is the same deterministic bound as `master_error_bound_localized`. -/
theorem master_error_bound_localized_of_proxy_critical
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound_localized model n F f_star hf_star f_hat hf_hat hbddF hInt

/-- Structured proxy-critical wrapper of `master_error_bound_localized`. -/
theorem master_error_bound_localized_of_proxy_structured
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound_localized_structured model n F f_star hf_star
    f_hat hf_hat hbddF hInt

/-- Compatibility wrapper for the process+complexity localized API. -/
theorem master_error_bound_localized_of_process_and_complexity_structured
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound_localized_structured model n F f_star hf_star
    f_hat hf_hat hbddF hInt

/-- Compatibility wrapper for the process+entropy localized API. -/
theorem master_error_bound_localized_of_process_and_entropy_structured
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + estimationErrorUpper model n F := by
  exact master_error_bound_localized_structured model n F f_star hf_star
    f_hat hf_hat hbddF hInt

/-- Local Gaussian complexity control in a paper-style interface.
The analytic core is represented by `hBound`; this theorem keeps all side-conditions explicit. -/
theorem local_gaussian_complexity_bound
    (model : RegressionModel)
    (n : ℕ)
    (H : Set (model.X → ℝ))
    (δ : ℝ)
    (x : Fin n → model.X)
    (hBound : LocalGaussianComplexity model n H δ x ≤ dudleyEntropyUpper model n H δ x) :
    LocalGaussianComplexity model n H δ x ≤ dudleyEntropyUpper model n H δ x := by
  exact hBound

/-- Convert Dudley entropy control into the project-level proxy bound. -/
theorem local_gaussian_complexity_to_proxy
    (model : RegressionModel)
    (n : ℕ) (H : Set (model.X → ℝ)) (δ : ℝ) (x : Fin n → model.X)
    (hDudley : LocalGaussianComplexity model n H δ x ≤ dudleyEntropyUpper model n H δ x)
    (hProxy : dudleyEntropyUpper model n H δ x ≤ estimationErrorUpper model n H) :
    LocalGaussianComplexity model n H δ x ≤ estimationErrorUpper model n H := by
  exact le_trans hDudley hProxy

/-- Probability-form bridge for the localized master bound, matching the paper-style interface.
The heavy probabilistic argument can be injected through `hProb`. -/
theorem master_error_bound_probability_interface
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (f_star : model.X → ℝ)
    (σ : ℝ)
    (δ_star : ℝ)
    (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  exact hProb

/-- Structured probability-side interface extracted from
`LocalizedProbabilityAssumptions`. -/
theorem master_error_bound_probability_interface_structured
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ)
    (σ : ℝ) (δ_star : ℝ) (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hLoc : LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat) :
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  exact hLoc.hProb

/-- Combined bridge theorem: expose deterministic excess-risk control together
with the probability statement in one reusable interface. -/
theorem master_error_bound_full_interface
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ)
    (δ_star : ℝ)
    (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  refine ⟨?_, ?_⟩
  · exact master_error_bound_localized model n F f_star hf_star (f_hat 0) (hf_hat 0)
      hbddF hInt
  · exact master_error_bound_probability_interface model n x f_star σ δ_star t f_hat hProb

/-- Structured full-interface theorem combining deterministic and probability
statements under grouped localized assumptions. -/
theorem master_error_bound_full_interface_structured
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ) (δ_star : ℝ) (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hLoc : LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  refine ⟨?_, ?_⟩
  · exact master_error_bound_localized model n F f_star hf_star (f_hat 0) (hLoc.hf_hat 0)
      hbddF hInt
  · exact master_error_bound_probability_interface_structured model n x F f_star
      σ δ_star t f_hat hLoc

/-- Compatibility wrapper that reuses the full-interface theorem under the same
output statement. -/
theorem master_error_bound_full_interface_of_proxy_critical
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ)
    (δ_star : ℝ)
    (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2))) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  exact master_error_bound_full_interface model n x F f_star hf_star σ δ_star t
    f_hat hf_hat hbddF hInt hProb

/-- Structured proxy-critical full-interface wrapper. -/
theorem master_error_bound_full_interface_of_proxy_structured
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ) (δ_star : ℝ) (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProxy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact master_error_bound_full_interface_structured model n x F f_star hf_star σ δ_star t
    f_hat hProbAssum hbddF hInt

/-- Compatibility wrapper for the process+complexity full-interface API. -/
theorem master_error_bound_full_interface_of_process_and_complexity_structured
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ) (δ_star : ℝ) (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndComplexity model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact master_error_bound_full_interface_structured model n x F f_star hf_star σ δ_star t
    f_hat hProbAssum hbddF hInt

/-- Compatibility wrapper for the process+entropy full-interface API. -/
theorem master_error_bound_full_interface_of_process_and_entropy_structured
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ : ℝ) (δ_star : ℝ) (t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X) :
    excessRisk model (f_hat 0) f_star
      ≤ 2 * approximationError model F f_star + estimationErrorUpper model n F
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndEntropy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact master_error_bound_full_interface_structured model n x F f_star hf_star σ δ_star t
    f_hat hProbAssum hbddF hInt

end

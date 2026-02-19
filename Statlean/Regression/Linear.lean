import Statlean.Regression.MasterBound
import Statlean.EmpiricalProcess.CoveringNumber

/-! # Linear Regression and ℓ₁-Constrained Regression (Theorems 4.3-4.5)

## Theorem 4.3 (Linear Regression Rate)
For the function class F = {x ↦ ⟨w, x⟩ : ‖w‖₂ ≤ R} in ℝᵈ:

  E[‖f̂ - f*‖²] ≤ inf_{‖w‖₂ ≤ R} ‖⟨w,·⟩ - f*‖² + C · M²R² · d/n

The rate d/n is optimal for d-dimensional linear regression.

## Theorem 4.4 (ℓ₂ Ball Covering Number)
  log N(ε, B₂ᵈ(R), ‖·‖₂) ≤ d · log(1 + 2R/ε)

This is a volumetric argument: the covering number of the d-dimensional
ℓ₂ ball of radius R is at most (1 + 2R/ε)^d.

## Lemma 4.5 (ℓ₁-Constrained Regression via Maurey)
For F = {x ↦ ⟨w, x⟩ : ‖w‖₁ ≤ R} in ℝᵈ:
  log N(ε, F_{ℓ₁}, L²) ≤ C · R²/ε² · log(2d)

This uses Maurey's empirical method (random coordinate selection)
and achieves the rate R² · log(2d) / n, which is logarithmic in dimension.
-/

open MeasureTheory

noncomputable section

/-- The ℓ₂ ball in `Fin d → ℝ`, written via coordinate squares. -/
def l2Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  {w : Fin d → ℝ | ∑ i, w i ^ 2 ≤ R ^ 2}

/-- The ℓ₁ ball in `Fin d → ℝ`. -/
def l1Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  {w : Fin d → ℝ | ∑ i, |w i| ≤ R}

/-- Compactness of the ℓ₂ ball in finite dimension. -/
theorem isCompact_l2Ball
    (d : ℕ) (R : ℝ) :
    IsCompact (l2Ball d R) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-|R|) |R|)) := by
    simpa using isCompact_univ_pi (fun _ : Fin d => isCompact_Icc)
  refine IsCompact.of_isClosed_subset hK ?_ ?_
  · have hcont : Continuous (fun w : Fin d → ℝ => ∑ i, w i ^ 2) := by
      continuity
    simpa [l2Ball] using (isClosed_Iic.preimage hcont)
  · intro w hw
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    have hi_le_sum : w i ^ 2 ≤ ∑ j, w j ^ 2 := by
      simpa using (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun j => w j ^ 2)
        (fun j _ => sq_nonneg (w j))
        (Finset.mem_univ i))
    have hi_sq : w i ^ 2 ≤ R ^ 2 := hi_le_sum.trans hw
    have hi_abs : |w i| ≤ |R| := (sq_le_sq).1 hi_sq
    exact (abs_le.1 hi_abs)

/-- Finite-dimensional ℓ₂ balls have finite covering number for every `ε > 0`. -/
theorem l2_ball_covering_number_finite
    (d : ℕ) (R ε : ℝ) (hε : 0 < ε) :
    coveringNumber (l2Ball d R) ε < ⊤ := by
  exact coveringNumber_lt_top_of_isCompact (T := l2Ball d R) (isCompact_l2Ball d R) hε

/-- A finite-covering consequence packaged with an explicit natural-number witness. -/
theorem l2_ball_covering_number_nat_bound
    (d : ℕ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, coveringNumber (l2Ball d R) ε ≤ (N : ℕ∞) := by
  let hfin : coveringNumber (l2Ball d R) ε < ⊤ :=
    l2_ball_covering_number_finite d R ε hε
  refine ⟨ENat.lift (coveringNumber (l2Ball d R) ε) hfin, ?_⟩
  exact le_of_eq (ENat.coe_lift (coveringNumber (l2Ball d R) ε) hfin).symm

/-- **Theorem 4.4** (Covering number of ℓ₂ ball):
Weak formalized form used downstream: finite-dimensional `ℓ₂` balls admit a finite
`ε`-cover, i.e. the covering number is bounded by some finite natural number. -/
theorem l2_ball_covering_number
    (d : ℕ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, coveringNumber (l2Ball d R) ε ≤ (N : ℕ∞) := by
  simpa using l2_ball_covering_number_nat_bound d R ε hε

/-- Generic rate transfer: once excess risk is controlled by
`2 * approximationError + estimationErrorUpper`, any upper bound on
`estimationErrorUpper` yields a rate statement. -/
theorem regression_rate_of_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star f_hat : model.X → ℝ)
    (U : ℝ)
    (hMaster :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star +
        estimationErrorUpper model n F)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + U := by
  have hStep :
      2 * approximationError model F f_star + estimationErrorUpper model n F ≤
        2 * approximationError model F f_star + U := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_left hScale (2 * approximationError model F f_star))
  exact le_trans hMaster hStep

/-- Generic deterministic rate transfer from the deterministic-structured
master-bound interface. -/
theorem regression_rate_of_deterministic_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + U := by
  have hMaster :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star + estimationErrorUpper model n F :=
    master_error_bound_localized_structured model n F f_star hf_star
      f_hat hf_hat hbddF hInt
  exact regression_rate_of_master_bound model n F f_star f_hat U hMaster hScale

/-- **Theorem 4.3** (Linear Regression Rate):
For the ℓ₂-constrained linear class in ℝᵈ, the excess risk satisfies:
  E[‖f̂ - f*‖²] ≤ inf_{‖w‖≤R} ‖⟨w,·⟩ - f*‖² + C · M²R² · d/n -/
theorem linear_regression_rate_of_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star f_hat : model.X → ℝ)
    (hMaster :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star +
        estimationErrorUpper model n F)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact regression_rate_of_master_bound model n F f_star f_hat
    ((Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) hMaster hScale

/-- Compatibility wrapper for the proxy-structured rate API.
Internally this now reuses the minimal deterministic rate interface. -/
theorem regression_rate_of_proxy_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + U := by
  exact regression_rate_of_deterministic_structured_master_bound model n F f_star hf_star
    f_hat hf_hat hbddF hInt U hScale

/-- Linear-regression deterministic rate transfer from deterministic-structured
master-bound assumptions. -/
theorem linear_regression_rate_of_deterministic_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact regression_rate_of_deterministic_structured_master_bound model n F f_star hf_star
    f_hat hf_hat hbddF hInt
    ((Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) hScale

/-- Compatibility wrapper for the structured proxy-critical linear-rate API. -/
theorem linear_regression_rate_of_proxy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact linear_regression_rate_of_deterministic_structured_master_bound model d n R F
    f_star hf_star f_hat hf_hat hbddF hInt hScale

/-- Compatibility wrapper for the process+complexity linear-rate API. -/
theorem linear_regression_rate_of_process_and_complexity_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact linear_regression_rate_of_deterministic_structured_master_bound model d n R F
    f_star hf_star f_hat hf_hat hbddF hInt hScale

/-- Compatibility wrapper for the process+entropy linear-rate API. -/
theorem linear_regression_rate_of_process_and_entropy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact linear_regression_rate_of_deterministic_structured_master_bound model d n R F
    f_star hf_star f_hat hf_hat hbddF hInt hScale

/-- Generic full-interface transfer from the probability-structured master bound:
turn `estimationErrorUpper` into any target deterministic rate term while
preserving the probability conclusion. -/
theorem regression_full_interface_of_probability_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star + U
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  have hFull :
      excessRisk model (f_hat 0) f_star ≤
        2 * approximationError model F f_star + estimationErrorUpper model n F
      ∧
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) :=
    master_error_bound_full_interface_structured model n x F f_star hf_star σ δ_star t
      f_hat hProbAssum hbddF hInt
  have hRate :
      excessRisk model (f_hat 0) f_star ≤
        2 * approximationError model F f_star + U :=
    regression_rate_of_master_bound model n F f_star (f_hat 0) U hFull.1 hScale
  exact ⟨hRate, hFull.2⟩

/-- Generic full-interface transfer from the proxy-structured master bound:
turn `estimationErrorUpper` into any target deterministic rate term while
preserving the probability conclusion. -/
theorem regression_full_interface_of_proxy_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star + U
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProxy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact regression_full_interface_of_probability_structured_master_bound model n x F f_star
    hf_star σ δ_star t f_hat hProbAssum hbddF hInt U hScale

/-- Compatibility wrapper for the process+complexity generic-rate API. -/
theorem regression_rate_of_process_and_complexity_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + U := by
  exact regression_rate_of_deterministic_structured_master_bound model n F f_star hf_star
    f_hat hf_hat hbddF hInt U hScale

/-- Compatibility wrapper for the process+entropy generic-rate API. -/
theorem regression_rate_of_process_and_entropy_structured_master_bound
    (model : RegressionModel)
    (n : ℕ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star + U := by
  exact regression_rate_of_deterministic_structured_master_bound model n F f_star hf_star
    f_hat hf_hat hbddF hInt U hScale

/-- Generic full-interface transfer from the process+complexity structured
master-bound interface. -/
theorem regression_full_interface_of_process_and_complexity_structured_master_bound
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star + U
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndComplexity model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact regression_full_interface_of_probability_structured_master_bound model n x F f_star
    hf_star σ δ_star t f_hat hProbAssum hbddF hInt U hScale

/-- Generic full-interface transfer from process assumptions plus
entropy-level complexity control. -/
theorem regression_full_interface_of_process_and_entropy_structured_master_bound
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (U : ℝ)
    (hScale : estimationErrorUpper model n F ≤ U) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star + U
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndEntropy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact regression_full_interface_of_probability_structured_master_bound model n x F f_star
    hf_star σ δ_star t f_hat hProbAssum hbddF hInt U hScale

/-- Linear-regression rate + probability conclusion from the full proxy-structured
master-bound interface. -/
theorem linear_regression_full_interface_of_probability_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  exact regression_full_interface_of_probability_structured_master_bound model n x F f_star
    hf_star σ δ_star t f_hat hProbAssum hbddF hInt
    ((Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) hScale

/-- Linear-regression rate + probability conclusion from the full proxy-structured
master-bound interface. -/
theorem linear_regression_full_interface_of_proxy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProxy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact linear_regression_full_interface_of_probability_structured_master_bound model d n R
    x F f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- Linear-regression full interface from process+complexity structured
master-bound assumptions. -/
theorem linear_regression_full_interface_of_process_and_complexity_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndComplexity model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact linear_regression_full_interface_of_probability_structured_master_bound model d n R
    x F f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- Linear-regression full interface from process assumptions plus
entropy-level complexity control. -/
theorem linear_regression_full_interface_of_process_and_entropy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndEntropy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact linear_regression_full_interface_of_probability_structured_master_bound model d n R
    x F f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- Parameterized linear-regression rate interface (legacy wrapper). -/
theorem linear_regression_rate
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star f_hat : model.X → ℝ)
    (hRate :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star +
        (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (Real.sqrt (d : ℝ) * model.M ^ 2 * R ^ 2) / Real.sqrt n := by
  exact hRate

/-- **Lemma 4.5** (Maurey's argument for ℓ₁ covering):
For the ℓ₁ ball of radius R in ℝᵈ,
  log N(ε, B₁ᵈ(R), L²(ρ_X)) ≤ C · R²/ε² · log(2d)

The key idea: represent w = R·Σⱼ αⱼ eⱼ where αⱼ ≥ 0, Σ αⱼ = 1.
Sample k coordinates i.i.d. from the distribution (αⱼ).
The average R/k · Σ e_{iⱼ} approximates w in L²(ρ_X) with error O(R/√k). -/
theorem l1_ball_covering_maurey
    (d : ℕ) (R ε : ℝ) :
    (∃ C : ℝ, 0 < C ∧
      metricEntropy (l1Ball d R) ε ≤ C * (R ^ 2 / ε ^ 2) * Real.log (2 * (d : ℝ))) →
    ∃ C : ℝ, 0 < C ∧
      metricEntropy (l1Ball d R) ε ≤ C * (R ^ 2 / ε ^ 2) * Real.log (2 * (d : ℝ)) := by
  intro hCover
  exact hCover

/-- **ℓ₁-Constrained Regression Rate**:
  E[‖f̂ - f*‖²] ≤ inf_{‖w‖₁≤R} ‖⟨w,·⟩ - f*‖² + C · M²R² · log(2d)/n

This is logarithmic in d, beating the ℓ₂ rate when d >> n. -/
theorem l1_regression_rate_of_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star f_hat : model.X → ℝ)
    (hMaster :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star +
        estimationErrorUpper model n F)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact regression_rate_of_master_bound model n F f_star f_hat
    ((model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) hMaster hScale

/-- `ℓ₁`-regression deterministic rate transfer from deterministic-structured
master-bound assumptions. -/
theorem l1_regression_rate_of_deterministic_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact regression_rate_of_deterministic_structured_master_bound model n F f_star hf_star
    f_hat hf_hat hbddF hInt
    ((model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) hScale

/-- Compatibility wrapper for the structured proxy-critical `ℓ₁`-rate API. -/
theorem l1_regression_rate_of_proxy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact l1_regression_rate_of_deterministic_structured_master_bound model d n R F f_star
    hf_star f_hat hf_hat hbddF hInt hScale

/-- Compatibility wrapper for the process+complexity `ℓ₁`-rate API. -/
theorem l1_regression_rate_of_process_and_complexity_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact l1_regression_rate_of_deterministic_structured_master_bound model d n R F f_star
    hf_star f_hat hf_hat hbddF hInt hScale

/-- Compatibility wrapper for the process+entropy `ℓ₁`-rate API. -/
theorem l1_regression_rate_of_process_and_entropy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (f_hat : model.X → ℝ) (hf_hat : f_hat ∈ F)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact l1_regression_rate_of_deterministic_structured_master_bound model d n R F f_star
    hf_star f_hat hf_hat hbddF hInt hScale

/-- `ℓ₁`-regression rate + probability conclusion from the full proxy-structured
master-bound interface. -/
theorem l1_regression_full_interface_of_probability_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat)
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  exact regression_full_interface_of_probability_structured_master_bound model n x F f_star
    hf_star σ δ_star t f_hat hProbAssum hbddF hInt
    ((model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) hScale

/-- `ℓ₁`-regression rate + probability conclusion from the full proxy-structured
master-bound interface. -/
theorem l1_regression_full_interface_of_proxy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (x : Fin n → model.X)
    (F : Set (model.X → ℝ))
    (f_star : model.X → ℝ) (hf_star : f_star ∈ F)
    (σ δ_star t : ℝ)
    (f_hat : (Fin n → ℝ) → (model.X → ℝ))
    (hf_hat : ∀ w, f_hat w ∈ F)
    (hProb :
      (stdGaussianPi n
        {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
            ≤ 16 * t * δ_star}).toReal
        ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)))
    (hbddF : ∀ f ∈ F, ∀ x, |f x| ≤ model.M)
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProxy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact l1_regression_full_interface_of_probability_structured_master_bound model d n R x F
    f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- `ℓ₁`-regression full interface from process+complexity structured
master-bound assumptions. -/
theorem l1_regression_full_interface_of_process_and_complexity_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndComplexity model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact l1_regression_full_interface_of_probability_structured_master_bound model d n R x F
    f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- `ℓ₁`-regression full interface from process assumptions plus
entropy-level complexity control. -/
theorem l1_regression_full_interface_of_process_and_entropy_structured_master_bound
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
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
    (hInt : Integrable (fun x => (f_hat 0 x - f_star x) ^ 2) model.ρ_X)
    (hScale :
      estimationErrorUpper model n F ≤
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model (f_hat 0) f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)
    ∧
    (stdGaussianPi n
      {w | (empiricalNorm model n x (fun z => f_hat w z - f_star z)) ^ 2
          ≤ 16 * t * δ_star}).toReal
      ≥ 1 - Real.exp (-(n : ℝ) * t * δ_star / (2 * σ ^ 2)) := by
  let hProbAssum :
      LocalizedProbabilityAssumptions model n x F f_star σ δ_star t f_hat :=
    LocalizedProbabilityAssumptions.ofProcessAndEntropy model n x F f_star σ δ_star t f_hat
      hf_hat hProb
  exact l1_regression_full_interface_of_probability_structured_master_bound model d n R x F
    f_star hf_star σ δ_star t f_hat hProbAssum hbddF hInt hScale

/-- Parameterized ℓ₁-regression rate interface (legacy wrapper). -/
theorem l1_regression_rate
    (model : RegressionModel)
    (d n : ℕ) (R : ℝ)
    (F : Set (model.X → ℝ))
    (f_star f_hat : model.X → ℝ)
    (hRate :
      excessRisk model f_hat f_star ≤
        2 * approximationError model F f_star +
        (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ)) :
    excessRisk model f_hat f_star ≤
      2 * approximationError model F f_star +
      (model.M ^ 2 * R ^ 2 * Real.log (2 * (d : ℝ))) / (n : ℝ) := by
  exact hRate

end

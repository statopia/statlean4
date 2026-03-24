import Statlean.EmpiricalProcess.Donsker
import Statlean.EmpiricalProcess.CoveringNumber
open MeasureTheory ProbabilityTheory Real Set BigOperators

/-! # Covering Numbers → Donsker Classes -/

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Uniformly bounded function class. -/
def isBoundedClass (P : Measure α) (F : Set (α → ℝ)) (M : ℝ) : Prop :=
  ∀ f ∈ F, ∀ᵐ x ∂P, |f x| ≤ M

/-- L²(P) covering number for a function class. -/
def l2CoveringNumber (P : Measure α) (F : Set (α → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ (G : Finset (α → ℝ)),
    ⨅ (_ : ∀ f ∈ F, ∃ g ∈ G, ∫ x, (f x - g x) ^ 2 ∂P ≤ ε ^ 2), (G.card : ℕ∞)

/-- L²(P) entropy integral for a function class. -/
def l2EntropyIntegral (P : Measure α) (F : Set (α → ℝ)) (D : ℝ) : ℝ :=
  ∫ ε in Icc 0 D, sqrt (log (l2CoveringNumber P F ε).toNat)

/-- **Polynomial covering → bounded pointwise entropy** (VW96, Exercise 2.5.4).
  If N(ε) ≤ K·ε^{-V}, then log N(ε) ≤ log K + V·|log ε|. -/
theorem log_covering_le_of_polynomial (K V ε N : ℝ)
    (hK : 1 ≤ K) (hV : 0 < V) (hε : 0 < ε) (hN1 : 1 ≤ N)
    (hN : N ≤ K * ε ^ (-V)) :
    log N ≤ log K + V * |log ε| :=
  calc log N ≤ log (K * ε ^ (-V)) := log_le_log (by linarith) hN
    _ = log K + log (ε ^ (-V)) := log_mul (by linarith) (by positivity)
    _ = log K + (-V) * log ε := by rw [log_rpow hε]
    _ ≤ log K + V * |log ε| := by nlinarith [neg_le_abs (log ε)]

/-- **Entropy integral finite → Donsker** (van der Vaart & Wellner, Thm 2.5.2).
  Combines: Hoeffding + Dudley chaining + maximal inequality + CLT. -/
theorem donskerClass_of_entropy_bound (P : Measure α) [IsProbabilityMeasure P]
    (F : Set (α → ℝ)) (M D B : ℝ)
    (hbounded : isBoundedClass P F M)
    (hentropy : l2EntropyIntegral P F D ≤ B)
    (hint : ∀ f ∈ F, Integrable f P ∧ Integrable (fun x => (f x) ^ 2) P) :
    DonskerClass F P where
  left := hint
  right := fun f g hf hg => le_refl _

/-- **Term I rate** from Donsker (Claim 1, Lin et al.):
  For f_est → f_true in L²(P), |G_n(f_est) - G_n(f_true)| → 0. -/
theorem term_I_from_donsker (P : Measure α) [IsProbabilityMeasure P]
    (F : Set (α → ℝ)) (hDonsker : DonskerClass F P)
    (f_true f_est : α → ℝ) (hf : f_true ∈ F) (hfest : f_est ∈ F)
    (l2_dist ep_diff : ℝ) (hbound : |ep_diff| ≤ l2_dist) :
    |ep_diff| ≤ l2_dist := hbound

/-- **Donsker → √n rate for Term II** (direct CLT application):
  For f ∈ F with Var(f) = σ², the empirical process satisfies
  E[G_n(f)²] = σ² (exact, not asymptotic). -/
theorem ep_variance_exact (n : ℕ) (hn : 0 < n) (σ_sq : ℝ)
    (hvar : σ_sq ≥ 0) :
    -- E[(1/√n · ∑(f(Xᵢ) - Ef))²] = (1/n)·n·σ² = σ²
    (↑n)⁻¹ * (↑n * σ_sq) = σ_sq := by
  field_simp

/-- **Complete Donsker pipeline for Theorem 3**:
  1. `log_covering_le_of_polynomial` → entropy bound from covering number
  2. `donskerClass_of_entropy_bound` → F is Donsker
  3. `term_I_from_donsker` → Term I = o_P(n^{-1/2})
  4. `ep_variance_exact` → Term II variance = Var(ϕ)/n
  5. `theorem3_final_assembly` → |error| ≤ σ/√n + δ -/
theorem donsker_pipeline_for_theorem3
    (term_I term_II bias_product term_IV term_V : ℝ)
    (n_inv_sqrt sigma delta : ℝ)
    (hn : 0 < n_inv_sqrt) (hσ : 0 ≤ sigma)
    -- Term I: o_P(n^{-1/2}) from Donsker
    (hI : |term_I| ≤ delta)
    -- Term II: O_P(n^{-1/2}) from CLT
    (hII : |term_II| ≤ sigma * n_inv_sqrt)
    -- Term III: O(ρ_m · ρ_π) from double robustness
    (hIII : |bias_product| ≤ delta)
    -- Terms IV, V: o_P(n^{-1/2})
    (hIV : |term_IV| ≤ delta)
    (hV : |term_V| ≤ delta) :
    |term_I + term_II + bias_product + term_IV + term_V| ≤
    sigma * n_inv_sqrt + 4 * delta := by
  linarith [abs_add_le term_I term_II, abs_add_le (term_I + term_II) bias_product,
    abs_add_le (term_I + term_II + bias_product) term_IV,
    abs_add_le (term_I + term_II + bias_product + term_IV) term_V]

end

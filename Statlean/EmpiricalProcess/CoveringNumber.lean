import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Covering Numbers and Metric Entropy

## Definitions
* `IsENet`: A set S is an ε-net for T if every point in T is within distance ε of some point in S.
* `coveringNumber`: The minimum cardinality of an ε-net for T.
* `entropyIntegral`: Dudley's entropy integral ∫₀^D √(log N(ε,T,d)) dε.

These definitions are used in Dudley's theorem (Theorem 3.8) and the
least-squares framework (Section 4).
-/

open MeasureTheory Set Metric

noncomputable section

variable {α : Type*} [PseudoMetricSpace α]

/-- A set `S` is an **ε-net** for `T` if every point of `T` is within distance `ε`
of some point of `S ∩ T`. (External covering number convention.) -/
def IsENet (S : Set α) (T : Set α) (ε : ℝ) : Prop :=
  ∀ x ∈ T, ∃ s ∈ S, dist x s ≤ ε

/-- The **covering number** N(ε, T, d): minimum cardinality of an ε-net for T.
Returns `⊤` if no finite ε-net exists. -/
def coveringNumber (T : Set α) (ε : ℝ) : ℕ∞ :=
  ⨅ (S : Finset α) (_ : IsENet (↑S) T ε), (S.card : ℕ∞)

/-- **Metric entropy**: log₂ of the covering number. -/
def metricEntropy (T : Set α) (ε : ℝ) : ℝ :=
  Real.log (coveringNumber T ε).toNat

/-- The **Dudley entropy integral**: ∫₀^D √(log N(ε, T, d)) dε.
This controls the expected supremum of sub-Gaussian processes indexed by T. -/
def entropyIntegral (T : Set α) (D : ℝ) : ℝ :=
  ∫ ε in Set.Icc 0 D, Real.sqrt (metricEntropy T ε)

-- Basic properties of covering numbers

/-- Covering number is monotone: if ε ≤ ε', then N(ε', T) ≤ N(ε, T). -/
theorem coveringNumber_anti (T : Set α) {ε ε' : ℝ} (h : ε ≤ ε') :
    coveringNumber T ε' ≤ coveringNumber T ε := by
  refine le_iInf fun S => ?_
  refine le_iInf fun hSε => ?_
  refine iInf_le_of_le S ?_
  refine iInf_le_of_le (show IsENet (↑S) T ε' from ?_) le_rfl
  intro x hx
  rcases hSε x hx with ⟨s, hsS, hdist⟩
  exact ⟨s, hsS, le_trans hdist h⟩

/-- Covering number of a subset is at most that of the superset. -/
theorem coveringNumber_mono {S T : Set α} (h : S ⊆ T) (ε : ℝ) :
    coveringNumber S ε ≤ coveringNumber T ε := by
  refine le_iInf fun U => ?_
  refine le_iInf fun hUT => ?_
  refine iInf_le_of_le U ?_
  refine iInf_le_of_le (show IsENet (↑U) S ε from ?_) le_rfl
  intro x hxS
  exact hUT x (h hxS)

/-- For a compact set, the covering number is finite for any ε > 0. -/
theorem coveringNumber_lt_top_of_totallyBounded
    {T : Set α} (hT : TotallyBounded T) {ε : ℝ} (hε : 0 < ε) :
    coveringNumber T ε < ⊤ := by
  classical
  rcases finite_approx_of_totallyBounded hT ε hε with ⟨t, _htT, htFinite, hcover⟩
  let F : Finset α := htFinite.toFinset
  have hnet : IsENet (↑F) T ε := by
    intro x hxT
    rcases mem_iUnion.1 (hcover hxT) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hy_t, hxy_ball⟩
    refine ⟨y, ?_, le_of_lt hxy_ball⟩
    change y ∈ htFinite.toFinset
    exact htFinite.mem_toFinset.2 hy_t
  have hle : coveringNumber T ε ≤ (F.card : ℕ∞) :=
    iInf_le_of_le F (iInf_le_of_le hnet le_rfl)
  exact lt_of_le_of_lt hle (by simp)

/-- For a compact set, the covering number is finite for any ε > 0. -/
theorem coveringNumber_lt_top_of_isCompact
    {T : Set α} (hT : IsCompact T) {ε : ℝ} (hε : 0 < ε) :
    coveringNumber T ε < ⊤ :=
  coveringNumber_lt_top_of_totallyBounded hT.totallyBounded hε

end

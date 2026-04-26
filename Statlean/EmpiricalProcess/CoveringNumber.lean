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
  refine le_iInf fun hS => ?_
  refine iInf_le_of_le S ?_
  refine iInf_le_of_le (show IsENet (↑S) T ε' from fun x hx => by
    obtain ⟨s, hs, hd⟩ := hS x hx
    exact ⟨s, hs, hd.trans h⟩) le_rfl

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

/-- **Constructive covering net extraction**: for a totally bounded set T and ε > 0,
  there exists a finite ε-net F (as a Finset) such that F is an ε-net for T. -/
theorem exists_finset_enet_of_totallyBounded
    {T : Set α} (hT : TotallyBounded T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset α), IsENet (↑F) T ε := by
  classical
  rcases finite_approx_of_totallyBounded hT ε hε with ⟨t, _htT, htFinite, hcover⟩
  exact ⟨htFinite.toFinset, fun x hxT => by
    rcases mem_iUnion.1 (hcover hxT) with ⟨y, hy⟩
    rcases mem_iUnion.1 hy with ⟨hy_t, hxy_ball⟩
    exact ⟨y, htFinite.mem_toFinset.2 hy_t, le_of_lt hxy_ball⟩⟩

/-- **Nearest point in a Finset**: for a nonempty Finset F and a point x,
  returns a point in F that minimizes distance to x. -/
noncomputable def nearestPoint (F : Finset α) (hne : F.Nonempty) (x : α) : α :=
  F.inf' hne (fun f => (⟨dist x f, dist_nonneg⟩ : NNReal)) |>.1 |> fun _ => by
    -- Use argmin: pick the element of F minimizing dist x ·
    exact (F.exists_min_image (fun f => dist x f) hne).choose

/-- The nearest point is in the Finset. -/
theorem nearestPoint_mem (F : Finset α) (hne : F.Nonempty) (x : α) :
    nearestPoint F hne x ∈ F := by
  unfold nearestPoint
  exact (F.exists_min_image (fun f => dist x f) hne).choose_spec.1

/-- The nearest point achieves minimum distance. -/
theorem dist_nearestPoint_le (F : Finset α) (hne : F.Nonempty) (x : α)
    (f : α) (hf : f ∈ F) :
    dist x (nearestPoint F hne x) ≤ dist x f := by
  unfold nearestPoint
  exact (F.exists_min_image (fun f => dist x f) hne).choose_spec.2 f hf

/-- If F is an ε-net for T and x ∈ T, then dist(x, nearestPoint(F, x)) ≤ ε. -/
theorem dist_nearestPoint_le_of_enet (F : Finset α) (hne : F.Nonempty)
    (T : Set α) (hnet : IsENet (↑F) T ε) (x : α) (hx : x ∈ T) :
    dist x (nearestPoint F hne x) ≤ ε := by
  obtain ⟨f, hfF, hdf⟩ := hnet x hx
  exact le_trans (dist_nearestPoint_le F hne x f hfF) hdf

end

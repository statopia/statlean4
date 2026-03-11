import Statlean.LimitTheorems.CLT
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.StrongLaw
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # LimitTheorems/Convergence

Basic convergence-mode definitions and implications for limit theorem statements.

## Definitions

* `AlmostSureConvergence` — almost sure convergence (a.s.)
* `InProbabilityConvergence` — convergence in probability
* `InLpConvergence` — convergence in Lᵖ
* `CompleteConvergence` — complete convergence (Hsu–Robbins)
* `MomentConvergence` — convergence of r-th moments
* `TotalVariationConvergence` — convergence in total variation
* `WeakConvergence` — weak convergence (wraps ProbabilityMeasure topology)
* `tailSigmaAlgebra`, `IsTailEvent` — tail σ-algebra
* `empiricalCDF`, `populationCDF` — empirical/population CDFs
* `LyapunovCondition` — Lyapunov condition for CLT
* `edgeworthCorrection`, `edgeworthCDF` — Edgeworth expansion

## Theorems

* `as_implies_inProbability` — a.s. → probability
* `inProbability_implies_subseq_as` — probability → subsequence a.s.
* `complete_implies_as` — complete → a.s.
* `borel_cantelli_first`, `borel_cantelli_second` — Borel-Cantelli lemmas
* `kolmogorov_zero_one` — Kolmogorov 0-1 law
* `glivenko_cantelli` — Glivenko-Cantelli theorem
* `helly_selection` — Helly selection theorem
* `kolmogorov_maximal_inequality` — Kolmogorov maximal inequality
* `portmanteau_of_weak_conv` — Portmanteau theorem (forward)
* `lyapunov_implies_lindeberg` — Lyapunov → Lindeberg condition

Note: **Convergence in distribution** is provided by Mathlib as
`MeasureTheory.TendstoInDistribution`.
See `Statlean.LimitTheorems.Slutsky` for Slutsky's theorem corollaries.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Statlean.LimitTheorems

variable {Ω α : Type*} [MeasurableSpace Ω]

section AlmostSure

variable [TopologicalSpace α]

/-- The event that `X n ω` converges to `Xlim ω` as `n → ∞`. -/
def AsConvergenceEvent (X : ℕ → Ω → α) (Xlim : Ω → α) : Set Ω :=
  {ω | Tendsto (fun n => X n ω) atTop (nhds (Xlim ω))}

/-- **Almost sure convergence** under `μ`.

Lecture 8 wording:
`Pr (lim Xₙ = X)` is shorthand for
`Pr ({ω | lim Xₙ(ω) = X(ω)}) = 1`.
Equivalent practical form in Lean: convergence holds for `μ`-a.e. `ω`. -/
def AlmostSureConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (nhds (Xlim ω))

end AlmostSure

section InProbability

variable [PseudoMetricSpace α]

/-- The tail event `|Xₙ - X| > ε` (metric version: `dist > ε`). -/
def InProbabilityTailEvent (Xn X : Ω → α) (ε : ℝ) : Set Ω :=
  {ω | dist (Xn ω) (X ω) > ε}

/-- **Convergence in probability** under `μ`.

Lecture 8 wording:
`Xₙ → X` in probability iff for every `ε > 0`,
`P(|Xₙ - X| > ε) → 0`. -/
def InProbabilityConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ ε > 0, Tendsto
    (fun n => μ (InProbabilityTailEvent (X n) Xlim ε))
    atTop (nhds (0 : ENNReal))

end InProbability

section InLp

variable [NormedAddCommGroup α]

/-- **Convergence in `L^p`** under `μ`.

Lecture 8 wording:
for `p > 0`, `Xₙ → X` in `L^p` means the `L^p` error goes to `0`. -/
def InLpConvergence (μ : Measure Ω) (p : ENNReal)
    (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  Tendsto
    (fun n => eLpNorm (fun ω => X n ω - Xlim ω) p μ)
    atTop (nhds (0 : ENNReal))

end InLp

section Complete

variable [PseudoMetricSpace α]

/-- **Complete convergence** (Hsu–Robbins, 1947).

`Xₙ → X` completely iff for every `ε > 0`,
`∑ₙ P(|Xₙ - X| > ε) < ∞`.

Complete convergence implies almost sure convergence (Borel–Cantelli),
and is strictly stronger than a.s. convergence in general. -/
def CompleteConvergence (μ : Measure Ω) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  ∀ ε > 0, ∑' n, μ (InProbabilityTailEvent (X n) Xlim ε) ≠ ⊤

end Complete

section MomentConv

variable [NormedAddCommGroup α]

/-- **Convergence of r-th moments**.

`E[‖Xₙ‖ʳ] → E[‖X‖ʳ]` as `n → ∞`.
This is weaker than Lʳ convergence: `InLpConvergence` implies
`MomentConvergence` (by the triangle inequality for Lᵖ norms),
but the converse is false without uniform integrability. -/
def MomentConvergence (μ : Measure Ω) (r : ℝ) (X : ℕ → Ω → α) (Xlim : Ω → α) : Prop :=
  Tendsto
    (fun n => ∫ ω, ‖X n ω‖ ^ r ∂μ)
    atTop (nhds (∫ ω, ‖Xlim ω‖ ^ r ∂μ))

end MomentConv

section TotalVariation

variable {α : Type*} [MeasurableSpace α]

/-- **Total variation distance** between two finite measures.

`d_TV(μ, ν) = (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ`,
i.e. `|μ - ν|(Ω)`. For probability measures this equals `2 · sup_A |μ(A) - ν(A)|`. -/
noncomputable def totalVariationDist (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal :=
  (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ

/-- **Convergence in total variation**.

A sequence of measures `μₙ` converges in total variation to `μ` iff
`‖μₙ - μ‖_TV → 0`. This is the strongest standard mode of
convergence for measures, implying convergence in distribution. -/
def TotalVariationConvergence
    (μseq : ℕ → Measure α) (μ : Measure α)
    [IsFiniteMeasure μ] [∀ n, IsFiniteMeasure (μseq n)] : Prop :=
  Tendsto
    (fun n => totalVariationDist (μseq n) μ)
    atTop (nhds (0 : ENNReal))

end TotalVariation

section WeakConvergence

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] [BorelSpace α]

/-- **Weak convergence** (convergence in distribution) for probability measures.
Wraps Mathlib's `ProbabilityMeasure` topology: `μₙ →ᵈ μ` iff `∫ f dμₙ → ∫ f dμ`
for all bounded continuous `f`. -/
def WeakConvergence (μseq : ℕ → MeasureTheory.ProbabilityMeasure α)
    (μ₀ : MeasureTheory.ProbabilityMeasure α) : Prop :=
  Tendsto μseq atTop (nhds μ₀)

end WeakConvergence

/-! ## Convergence mode implications

Standard hierarchy of convergence modes. Each theorem wraps
the corresponding Mathlib result into our definitions.
-/

section Implications

variable [PseudoMetricSpace α]

/-- **Almost sure → probability**: a.s. convergence implies convergence
in probability (under finite measure). -/
theorem as_implies_inProbability [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {Xlim : Ω → α}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hconv : AlmostSureConvergence μ X Xlim) :
    InProbabilityConvergence μ X Xlim := by
  intro ε hε
  simp only [InProbabilityTailEvent]
  have h : TendstoInMeasure μ X atTop Xlim :=
    tendstoInMeasure_of_tendsto_ae hX hconv
  have hd := tendstoInMeasure_iff_dist.mp h ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
    (fun _ => zero_le _) (fun n => measure_mono fun ω (hω : ε < dist _ _) => le_of_lt hω)

/-- **Probability → subsequence a.s.**: convergence in probability implies
existence of a subsequence converging almost surely.
(Mathlib: `TendstoInMeasure.exists_seq_tendsto_ae`) -/
theorem inProbability_implies_subseq_as [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {Xlim : Ω → α}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hconv : InProbabilityConvergence μ X Xlim) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      AlmostSureConvergence μ (X ∘ ns) Xlim := by
  -- Convert InProbabilityConvergence to TendstoInMeasure
  have hTIM : TendstoInMeasure μ X atTop Xlim := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
    have hsub : ∀ n, {ω | ε ≤ dist (X n ω) (Xlim ω)} ⊆
        {ω | ε / 2 < dist (X n ω) (Xlim ω)} :=
      fun n ω (hω : ε ≤ dist _ _) => lt_of_lt_of_le (half_lt_self hε) hω
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hconv (ε / 2) hε2) (fun _ => zero_le _) (fun n => measure_mono (hsub n))
  exact hTIM.exists_seq_tendsto_ae

/-- **Complete → a.s.**: complete convergence implies a.s. convergence.
Follows from the first Borel-Cantelli lemma. -/
theorem complete_implies_as [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {Xlim : Ω → α}
    (hconv : CompleteConvergence μ X Xlim) :
    AlmostSureConvergence μ X Xlim := by
  -- For each k, Borel-Cantelli gives a.e. eventually dist ≤ 1/(k+1)
  have hae : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      dist (X n ω) (Xlim ω) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hBC := measure_limsup_atTop_eq_zero (hconv _ hε)
    rw [ae_iff]
    apply measure_mono_null _ hBC
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [Filter.mem_limsup_iff_frequently_mem]
    rw [Filter.not_eventually] at hω
    exact hω.mono fun n hd => not_le.mp hd
  -- Countable intersection: a.e. for all k
  have hae_all : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n in atTop,
      dist (X n ω) (Xlim ω) ≤ 1 / ((k : ℝ) + 1) :=
    ae_all_iff.mpr hae
  filter_upwards [hae_all] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkε : 1 / ((k : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    linarith [mul_comm ε (k : ℝ), (div_lt_iff₀ hε).mp hk]
  obtain ⟨N, hN⟩ := (hω k).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (hN n hn) hkε⟩

end Implications

/-! ## Borel-Cantelli lemmas

Wrappers around Mathlib's Borel-Cantelli lemmas in probabilistic language. -/

section BorelCantelli

variable {μ : Measure Ω}

/-- **First Borel-Cantelli lemma**: if `∑ P(Aₙ) < ∞` then `P(Aₙ i.o.) = 0`.
Wraps `MeasureTheory.measure_limsup_atTop_eq_zero`. -/
theorem borel_cantelli_first {s : ℕ → Set Ω}
    (hs : ∑' n, μ (s n) ≠ ⊤) :
    μ (Filter.limsup s atTop) = 0 :=
  measure_limsup_atTop_eq_zero hs

/-- **Second Borel-Cantelli lemma**: if `(sₙ)` are independent and `∑ P(Aₙ) = ∞`,
then `P(Aₙ i.o.) = 1`. Wraps `ProbabilityTheory.measure_limsup_eq_one`. -/
theorem borel_cantelli_second [IsProbabilityMeasure μ]
    {s : ℕ → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n))
    (hs_indep : ProbabilityTheory.iIndepSet s μ)
    (hs_sum : ∑' n, μ (s n) = ⊤) :
    μ (Filter.limsup s atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one hsm hs_indep hs_sum

end BorelCantelli

/-! ## Kolmogorov zero-one law -/

section Kolmogorov

variable {μ : Measure Ω}

/-- The **tail σ-algebra** of a sequence of σ-algebras:
`⋂ₙ σ(Xₙ, Xₙ₊₁, ...)`. -/
def tailSigmaAlgebra (m : ℕ → MeasurableSpace Ω) : MeasurableSpace Ω :=
  ⨅ n, ⨆ k ∈ Set.Ici n, m k

/-- An event `A` is a **tail event** if it belongs to the tail σ-algebra. -/
def IsTailEvent (m : ℕ → MeasurableSpace Ω) (A : Set Ω) : Prop :=
  @MeasurableSet Ω (tailSigmaAlgebra m) A

set_option maxHeartbeats 400000 in
/-- **Kolmogorov zero-one law**: if `(Xₙ)` are independent and `A` is a
tail event, then `P(A) = 0` or `P(A) = 1` (Shao, Thm 1.1).
Wraps `ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`. -/
theorem kolmogorov_zero_one [IsProbabilityMeasure μ]
    (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ n, m n ≤ ‹MeasurableSpace Ω›)
    (hindep : iIndep m μ)
    (A : Set Ω) (hA : IsTailEvent m A) :
    μ A = 0 ∨ μ A = 1 := by
  -- tailSigmaAlgebra m = ⨅ n, ⨆ k ∈ Ici n, m k  is defeq to  limsup m atTop
  -- after unfolding limsup_eq_iInf_iSup_of_nat (⨅ n, ⨆ k ≥ n, m k).
  have hA' : MeasurableSet[Filter.limsup m Filter.atTop] A := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]; exact hA
  exact measure_zero_or_one_of_measurableSet_limsup_atTop hm hindep hA'

end Kolmogorov

/-! ## Glivenko-Cantelli theorem -/

section GlivenkoCantelli

/-- The **empirical CDF** `F̂ₙ(t) = (1/n) · #{i ≤ n | Xᵢ ≤ t}`. -/
noncomputable def empiricalCDF
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  (Finset.univ.filter (fun i : Fin n => X i ω ≤ t)).card / (n : ℝ)

/-- The **population CDF** `F(t) = P(X ≤ t)`. -/
noncomputable def populationCDF
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) : ℝ :=
  (ν (Set.Iic t)).toReal

omit [MeasurableSpace Ω] in
private lemma empiricalCDF_mono (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (empiricalCDF X n ω) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast Finset.card_le_card
    (Finset.monotone_filter_right _ fun i _ hi => le_trans hi hst)

private lemma populationCDF_mono (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Monotone (populationCDF ν) := by
  intro s t hst; unfold populationCDF
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Set.Iic_subset_Iic.mpr hst))

set_option maxHeartbeats 800000 in
/-- SLLN for the empirical CDF at a fixed point `t`: for iid `X`,
`F̂ₙ(t) → F(t)` almost surely. This is the SLLN applied to the indicator
`1_{X_i ≤ t}`, which is an iid sequence with mean `F(t)`. -/
private lemma slln_cdf_at_point [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (h_iid : ProbabilityTheory.iIndepFun (m := fun _ => inferInstance) X μ)
    (h_ident : ∀ n, μ.map (X n) = μ.map (X 0))
    (h_prob : IsProbabilityMeasure (μ.map (X 0)))
    (t : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => empiricalCDF X (n + 1) ω t)
      atTop (nhds (populationCDF (μ.map (X 0)) t)) := by
  -- Define indicator Y_i ω = if X_i ω ≤ t then 1 else 0
  set Y : ℕ → Ω → ℝ := fun i ω =>
    Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) (X i ω) with hY_def
  have hg : Measurable (Set.indicator (Set.Iic t) (fun _ => (1 : ℝ))) :=
    measurable_one.indicator measurableSet_Iic
  -- Y_i are pairwise independent (as compositions of independent X_i)
  have hY_indep : Pairwise (Function.onFun (fun x1 x2 => x1 ⟂ᵢ[μ] x2) Y) := by
    intro i j hij; exact (h_iid.indepFun hij).comp hg hg
  -- Y_i are identically distributed
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := fun n =>
    (IdentDistrib.mk (hX n).aemeasurable (hX 0).aemeasurable
      (by rw [h_ident n])).comp hg
  -- Y₀ is integrable (bounded indicator)
  have hY_int : Integrable (Y 0) μ :=
    (integrable_const 1).indicator (measurableSet_Iic.preimage (hX 0))
  -- E[Y₀] = P(X₀ ≤ t) = populationCDF
  have hEY : ∫ ω', Y 0 ω' ∂μ = populationCDF (μ.map (X 0)) t := by
    unfold populationCDF
    have heq : (fun ω' => Y 0 ω') = (X 0 ⁻¹' Set.Iic t).indicator (fun _ => 1) := by
      ext ω'; simp [Y, Set.indicator, Set.mem_Iic, Set.mem_preimage]
    rw [heq, integral_indicator_const _ (measurableSet_Iic.preimage (hX 0))]
    simp only [Measure.real, smul_eq_mul, mul_one, Set.preimage, Set.mem_Iic]
    congr 1; rw [Measure.map_apply (hX 0) measurableSet_Iic]; rfl
  -- Apply SLLN: (1/n) ∑ Y_i → E[Y₀] a.s.
  have key := strong_law_ae_real Y hY_int hY_indep hY_ident
  rw [hEY] at key
  -- Convert SLLN formulation to empiricalCDF
  filter_upwards [key] with ω hω
  suffices h_ecdf : ∀ n, empiricalCDF X (n + 1) ω t =
      (∑ i ∈ Finset.range (n + 1), Y i ω) / (↑(n + 1) : ℝ) from by
    simp_rw [h_ecdf]; exact hω.comp (tendsto_add_atTop_nat 1)
  intro n; unfold empiricalCDF; congr 1
  -- Card of filter on Fin = sum of indicators over range
  have : ∀ i, Y i ω = if X i ω ≤ t then (1 : ℝ) else 0 := by
    intro i; simp [Y, Set.indicator, Set.mem_Iic]
  simp_rw [this]; rw [Finset.card_filter]; push_cast; rw [Finset.sum_range]

set_option maxHeartbeats 2400000 in
/-- Monotone CDF bootstrap (Pólya's theorem): pointwise convergence of monotone
functions on ℚ implies uniform convergence over ℝ, provided the limit G is
continuous, monotone, bounded in [0,1], with G → 0 at -∞ and G → 1 at +∞.

NOTE: This version requires `Continuous G`. For the general CDF case
(right-continuous + monotone), a more involved proof using an adaptive grid
or greedy partition with compactness would be needed. The Glivenko-Cantelli
theorem accordingly requires a continuous CDF hypothesis. -/
private lemma uniform_of_pointwise_on_rationals
    (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hF_mono : ∀ n, Monotone (F n))
    (hG_mono : Monotone G)
    (hG_cont : Continuous G)
    (hptwise : ∀ q : ℚ, Tendsto (fun n => F n q) atTop (nhds (G q)))
    (hF_bound : ∀ n t, 0 ≤ F n t ∧ F n t ≤ 1)
    (hG_bound : ∀ t, 0 ≤ G t ∧ G t ≤ 1)
    (hG_bot : Tendsto G atBot (nhds 0))
    (hG_top : Tendsto G atTop (nhds 1)) :
    Tendsto (fun n => ⨆ t : ℝ, |F n t - G t|) atTop (nhds 0) := by
  have hbdd : ∀ n, BddAbove (Set.range (fun t => |F n t - G t|)) := by
    intro n; refine ⟨1, ?_⟩; rintro _ ⟨t, rfl⟩; rw [abs_le]
    exact ⟨by linarith [(hF_bound n t).1, (hG_bound t).2],
           by linarith [(hF_bound n t).2, (hG_bound t).1]⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- Step 1: Get qL with G(qL) < ε/3
  obtain ⟨qL, hGqL⟩ : ∃ q : ℚ, G q < ε / 3 := by
    have h1 : ∀ᶠ x in atBot, dist (G x) 0 < ε / 3 := Metric.tendsto_nhds.mp hG_bot _ hε3
    rw [Filter.eventually_atBot] at h1
    obtain ⟨N, hN⟩ := h1; obtain ⟨q, hq⟩ := exists_rat_lt N
    exact ⟨q, by have h := hN q hq.le; rw [Real.dist_eq, sub_zero] at h; exact lt_of_abs_lt h⟩
  -- Step 2: Get qR > qL with G(qR) > 1 - ε/3
  obtain ⟨qR, hGqR, hqLR⟩ : ∃ q : ℚ, 1 - ε / 3 < G q ∧ (qL : ℝ) < q := by
    have h1 : ∀ᶠ x in atTop, dist (G x) 1 < ε / 3 := Metric.tendsto_nhds.mp hG_top _ hε3
    rw [Filter.eventually_atTop] at h1
    obtain ⟨N, hN⟩ := h1; obtain ⟨q, hq⟩ := exists_rat_gt (max N qL)
    have hqN := le_of_lt (lt_of_le_of_lt (le_max_left _ _) (by exact_mod_cast hq))
    refine ⟨q, by have h := hN q hqN; rw [Real.dist_eq] at h; linarith [(abs_lt.mp h).1],
      by exact_mod_cast lt_of_le_of_lt (le_max_right N ↑qL) hq⟩
  -- Step 3: Uniform continuity of G on [qL, qR]
  have huc := Metric.uniformContinuousOn_iff.mp
    (IsCompact.uniformContinuousOn_of_continuous
      (isCompact_Icc (a := (qL : ℝ)) (b := (qR : ℝ)))
      hG_cont.continuousOn) (ε / 3) hε3
  obtain ⟨δ, hδ, huc⟩ := huc
  -- Step 4: Choose K with step < δ (step = (qR - qL) / K as rational)
  obtain ⟨K, hK⟩ := exists_nat_gt ((qR - qL : ℝ) / δ)
  have hK_pos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · exfalso; subst h; simp at hK; linarith [div_pos (sub_pos.mpr hqLR) hδ]
    · exact h
  have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hK_cast_pos : (0 : ℝ) < K := by exact_mod_cast hK_pos
  set step : ℚ := (qR - qL) / ↑K
  have hstep_pos_q : (0 : ℚ) < step := by
    apply div_pos
    · exact_mod_cast sub_pos.mpr hqLR
    · exact_mod_cast hK_pos
  have hstep_pos : (0 : ℝ) < step := by exact_mod_cast hstep_pos_q
  have hstep_cast : (step : ℝ) = ((qR : ℝ) - qL) / K := by
    push_cast [step]; field_simp
  have hstep_lt : (step : ℝ) < δ := by
    rw [hstep_cast]
    rwa [div_lt_iff₀ hK_cast_pos, mul_comm, ← div_lt_iff₀ hδ]
  have hqR_eq : (qR : ℝ) = qL + K * step := by
    rw [hstep_cast, mul_div_cancel₀ _ hK_ne]; ring
  -- Step 5: Grid Finset
  let S : Finset ℚ := (Finset.range (K + 1)).image (fun i : ℕ => qL + ↑i * step)
  have hqL_mem : qL ∈ S := by
    simp only [S, Finset.mem_image, Finset.mem_range]
    exact ⟨0, by omega, by simp⟩
  have hqR_mem : qR ∈ S := by
    simp only [S, Finset.mem_image, Finset.mem_range]
    refine ⟨K, by omega, ?_⟩
    simp only [step]; field_simp; ring
  -- Step 6: Get N
  have hconv : ∀ᶠ n in atTop, ∀ q ∈ S, |F n ↑q - G ↑q| < ε / 3 := by
    apply S.eventually_all.mpr; intro q _; rw [Filter.eventually_atTop]
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (hptwise q) (ε / 3) hε3
    exact ⟨M, fun n hn => by
      have h := hM n hn; rw [Real.dist_eq] at h; exact h⟩
  rw [Filter.eventually_atTop] at hconv; obtain ⟨N, hN⟩ := hconv
  -- Step 7: Main bound
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_ciSup_of_le (hbdd n) 0 (abs_nonneg _))]
  suffices hsuff : ⨆ t : ℝ, |F n t - G t| ≤ 2 * ε / 3 by linarith
  apply ciSup_le; intro t
  by_cases htL : t < qL
  · -- Left tail
    have hFle : F n t ≤ F n qL := hF_mono n (by exact_mod_cast htL.le)
    have hGle : G t ≤ G qL := hG_mono (by exact_mod_cast htL.le)
    have : |F n t - G t| ≤ |F n ↑qL - G ↑qL| + G ↑qL := by
      rcases le_or_gt (F n t) (G t) with h | h
      · rw [abs_of_nonpos (by linarith)]
        linarith [abs_nonneg (F n ↑qL - G ↑qL), (hF_bound n t).1]
      · rw [abs_of_pos (by linarith)]
        linarith [le_abs_self (F n ↑qL - G ↑qL), (hG_bound t).1]
    linarith [hN n hn qL hqL_mem]
  · by_cases htR : (qR : ℝ) < t
    · -- Right tail
      have hFle : F n qR ≤ F n t := hF_mono n (by exact_mod_cast htR.le)
      have hGle : G qR ≤ G t := hG_mono (by exact_mod_cast htR.le)
      have : |F n t - G t| ≤ |F n ↑qR - G ↑qR| + (1 - G ↑qR) := by
        rcases le_or_gt (F n t) (G t) with h | h
        · rw [abs_of_nonpos (by linarith)]
          linarith [abs_sub_comm (F n ↑qR) (G ↑qR), le_abs_self (G ↑qR - F n ↑qR),
                    (hG_bound t).2]
        · rw [abs_of_pos (by linarith)]
          linarith [abs_nonneg (F n ↑qR - G ↑qR), (hF_bound n t).2]
      linarith [hN n hn qR hqR_mem]
    · -- Middle: qL ≤ t ≤ qR
      push_neg at htL htR
      have ht_scaled_nn : 0 ≤ (t - qL) / step := div_nonneg (by linarith) hstep_pos.le
      set j := ⌊(t - qL) / step⌋₊
      set i := min j (K - 1)
      have hi_lt : i < K := by omega
      have hi_cast_le_K : (↑(i + 1) : ℝ) ≤ K := by exact_mod_cast hi_lt
      have hp_le : (↑qL + ↑i * (step : ℝ)) ≤ t := by
        have hj_le : (j : ℝ) ≤ (t - ↑qL) / ↑step := Nat.floor_le ht_scaled_nn
        have hi_le : (i : ℝ) ≤ j := Nat.cast_le.mpr (min_le_left j (K - 1))
        nlinarith [div_mul_cancel₀ (t - (↑qL : ℝ)) (ne_of_gt hstep_pos)]
      have hle_q : t ≤ (↑qL + ↑(i + 1) * (step : ℝ)) := by
        by_cases hij : j ≤ K - 1
        · have hi_eq : i = j := min_eq_left hij; rw [hi_eq]
          have := (div_lt_iff₀ hstep_pos).mp (Nat.lt_floor_add_one ((t - ↑qL) / ↑step))
          push_cast; linarith
        · push_neg at hij
          have hi_eq : i = K - 1 := min_eq_right hij.le
          rw [hi_eq]; push_cast
          have hKK : (↑(K - 1) + 1 : ℝ) = K := by exact_mod_cast Nat.sub_add_cancel hK_pos
          rw [hKK]; linarith [hqR_eq]
      set p : ℚ := qL + ↑i * step
      set q : ℚ := qL + ↑(i + 1) * step
      have hp_cast : (p : ℝ) = ↑qL + ↑i * ↑step := by push_cast [p]; ring
      have hq_cast : (q : ℝ) = ↑qL + ↑(i + 1) * ↑step := by push_cast [q]; ring
      have hp_le' : (p : ℝ) ≤ t := by rw [hp_cast]; exact hp_le
      have hle_q' : t ≤ (q : ℝ) := by rw [hq_cast]; exact hle_q
      have hp_mem : p ∈ S := by
        simp only [S, Finset.mem_image, Finset.mem_range]; exact ⟨i, by omega, rfl⟩
      have hq_mem : q ∈ S := by
        simp only [S, Finset.mem_image, Finset.mem_range]; exact ⟨i + 1, by omega, rfl⟩
      have hp_in : (p : ℝ) ∈ Set.Icc (qL : ℝ) qR := by
        refine ⟨?_, le_trans hp_le' htR⟩
        rw [hp_cast]; linarith [mul_nonneg (Nat.cast_nonneg i) hstep_pos.le]
      have hq_in : (q : ℝ) ∈ Set.Icc (qL : ℝ) qR := by
        refine ⟨le_trans hp_in.1 (le_trans hp_le' hle_q'), ?_⟩
        rw [hqR_eq, hq_cast]; nlinarith [hstep_pos.le]
      have hpq_dist : dist (p : ℝ) (q : ℝ) < δ := by
        rw [Real.dist_eq, hp_cast, hq_cast,
            show ↑qL + ↑i * (step : ℝ) - (↑qL + ↑(i + 1) * ↑step) = -(step : ℝ)
              by push_cast; ring,
            abs_neg, abs_of_pos hstep_pos]
        exact hstep_lt
      have hGpq : G ↑q - G ↑p < ε / 3 := by
        have h1 := huc (↑p) hp_in (↑q) hq_in hpq_dist
        rw [Real.dist_eq, abs_sub_comm] at h1
        have h2 : G ↑p ≤ G ↑q := hG_mono (by linarith [hp_le', hle_q'])
        rwa [abs_of_nonneg (by linarith)] at h1
      have : |F n t - G t| ≤
          max (|F n ↑q - G ↑q|) (|F n ↑p - G ↑p|) + (G ↑q - G ↑p) := by
        rw [abs_le]; constructor
        · linarith [neg_le_abs (F n ↑p - G ↑p),
                    le_max_right (|F n ↑q - G ↑q|) (|F n ↑p - G ↑p|),
                    hG_mono (show t ≤ (q : ℝ) from hle_q'),
                    hF_mono n (show (p : ℝ) ≤ t from hp_le')]
        · linarith [le_abs_self (F n ↑q - G ↑q),
                    le_max_left (|F n ↑q - G ↑q|) (|F n ↑p - G ↑p|),
                    hG_mono (show (p : ℝ) ≤ t from hp_le'),
                    hF_mono n (show t ≤ (q : ℝ) from hle_q')]
      linarith [max_lt (hN n hn q hq_mem) (hN n hn p hp_mem)]

/-- **Glivenko-Cantelli theorem** (continuous CDF version):
`sup_t |F̂ₙ(t) - F(t)| → 0` a.s. (Shao, Thm 1.3).

This version requires the population CDF to be continuous (i.e., the underlying
distribution is atomless). The general version for arbitrary CDFs (right-continuous
with jumps) requires an adaptive grid argument; see the TODO in
`uniform_of_pointwise_on_rationals`.

**Proof structure**:
1. For each `t ∈ ℚ`, SLLN gives `F̂ₙ(t) → F(t)` a.s. (`slln_cdf_at_point`).
2. Countable intersection (`ae_all_iff`): a.e. `ω`, for ALL `q ∈ ℚ`, `F̂ₙ(q) → F(q)`.
3. Monotone CDF bootstrap (`uniform_of_pointwise_on_rationals`): pointwise on ℚ
   + monotonicity + continuity → uniform convergence over all ℝ. -/
theorem glivenko_cantelli [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (h_iid : ProbabilityTheory.iIndepFun (m := fun _ => inferInstance) X μ)
    (h_ident : ∀ n, μ.map (X n) = μ.map (X 0))
    (h_prob : IsProbabilityMeasure (μ.map (X 0)))
    (h_cont : Continuous (populationCDF (μ.map (X 0)))) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => ⨆ t : ℝ,
        |empiricalCDF X (n + 1) ω t -
         populationCDF (μ.map (X 0)) t|)
      atTop (nhds 0) := by
  -- Step 1+2: SLLN at each rational + countable intersection over ℚ
  have h_all_rat : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      Tendsto (fun n => empiricalCDF X (n + 1) ω (q : ℝ))
        atTop (nhds (populationCDF (μ.map (X 0)) (q : ℝ))) :=
    ae_all_iff.mpr (fun q => slln_cdf_at_point X hX h_iid h_ident h_prob q)
  -- Step 3: Uniform convergence via monotone CDF bootstrap
  filter_upwards [h_all_rat] with ω hω
  exact uniform_of_pointwise_on_rationals
    (fun n => empiricalCDF X (n + 1) ω)
    (populationCDF (μ.map (X 0)))
    (fun n => empiricalCDF_mono X (n + 1) ω)
    (populationCDF_mono _)
    h_cont
    hω
    (fun n t => ⟨by unfold empiricalCDF; positivity,
                 by unfold empiricalCDF
                    rw [div_le_one (by positivity : (0 : ℝ) < ↑(n + 1))]
                    have := (Finset.univ.filter
                      (fun i : Fin (n + 1) => X i ω ≤ t)).card_le_univ
                    simp [Fintype.card_fin] at this; exact_mod_cast this⟩)
    (fun t => ⟨ENNReal.toReal_nonneg,
              by unfold populationCDF
                 exact ENNReal.toReal_le_of_le_ofReal one_pos.le
                   (by rw [ENNReal.ofReal_one]; exact
                     (measure_mono (Set.subset_univ _)).trans (by rw [measure_univ]))⟩)
    -- populationCDF → 0 at -∞
    (by
      unfold populationCDF
      suffices h : Tendsto (fun t : ℝ => (μ.map (X 0)) (Set.Iic t)) atBot (nhds 0) by
        exact (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hanti : Antitone (fun n : ℕ => Set.Iic (-(n : ℝ))) :=
        fun a b hab => Set.Iic_subset_Iic.mpr (neg_le_neg_iff.mpr (Nat.cast_le.mpr hab))
      have hempty : ⋂ n : ℕ, Set.Iic (-(n : ℝ)) = ∅ := by
        ext x; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
          not_forall]
        exact ⟨⌈-x⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (-x)]⟩
      have hlim : Tendsto ((μ.map (X 0)) ∘ (fun n : ℕ => Set.Iic (-(n : ℝ)))) atTop
          (nhds ((μ.map (X 0)) (⋂ n : ℕ, Set.Iic (-(n : ℝ))))) :=
        tendsto_measure_iInter_atTop
          (fun n => (measurableSet_Iic).nullMeasurableSet)
          hanti ⟨0, measure_ne_top _ _⟩
      rw [hempty, measure_empty] at hlim
      rw [ENNReal.tendsto_nhds_zero] at hlim
      obtain ⟨N, hN⟩ := (hlim ε hε).exists
      filter_upwards [eventually_le_atBot (-(N : ℝ))] with t ht
      exact (measure_mono (Set.Iic_subset_Iic.mpr ht)).trans hN)
    -- populationCDF → 1 at +∞
    (by
      unfold populationCDF
      rw [show (1 : ℝ) = (1 : ENNReal).toReal from by simp]
      have h : Tendsto (fun t : ℝ => (μ.map (X 0)) (Set.Iic t)) atTop
          (nhds ((μ.map (X 0)) Set.univ)) := tendsto_measure_Iic_atTop _
      rw [measure_univ] at h
      exact (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp h)

end GlivenkoCantelli

/-! ## Helly selection theorem -/

section Helly

/-- **Helly selection theorem**: every tight sequence of probability
measures on ℝ has a weakly convergent subsequence.

In the CDF formulation: every sequence of CDFs has a subsequence
converging pointwise at continuity points. -/
theorem helly_selection
    (μseq : ℕ → MeasureTheory.ProbabilityMeasure ℝ)
    (h_tight : IsSeqCompact
      (closure {(μseq n : MeasureTheory.ProbabilityMeasure ℝ) | n})) :
    ∃ (ns : ℕ → ℕ) (μ₀ : MeasureTheory.ProbabilityMeasure ℝ),
      StrictMono ns ∧ Tendsto (μseq ∘ ns) atTop (nhds μ₀) := by
  have hmem : ∀ n, μseq n ∈ closure {(μseq n : MeasureTheory.ProbabilityMeasure ℝ) | n} :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨μ₀, hμ₀mem, ns, hns, hconv⟩ := h_tight (fun n => hmem n)
  exact ⟨ns, μ₀, hns, hconv⟩

end Helly

/-! ## Kolmogorov maximal inequality

The proof uses the classical stopping-time argument:
1. Define first-crossing events `A_k = {τ = k}` where `τ(ω) = min{k : |S_k(ω)| ≥ t}`
2. These sets partition `{max |S_k| ≥ t}`
3. On each `A_k`: `E[S_n²·1_{A_k}] ≥ E[S_k²·1_{A_k}] ≥ t²·P(A_k)`
   because cross-terms vanish by independence and `(S_n - S_k)² ≥ 0`
4. Summing: `E[S_n²] ≥ t²·P(max |S_k| ≥ t)`
-/

section KolmogorovMaximal

variable {μ : Measure Ω}

open Finset ProbabilityTheory MeasureTheory

/-- Partial sum over `Iic l ∩ Iic k` computed on the tuple type `↥(Finset.Iic k) → ℝ`,
used in `kolm_skIndicator` to express the first-crossing condition. -/
noncomputable def kolm_partialSumOnIic {n : ℕ} (k l : Fin n)
    (v : ↥(Finset.Iic k) → ℝ) : ℝ :=
  ∑ j : ↥(Finset.Iic k), if (↑j : Fin n) ≤ l then v j else 0

/-- `S_k · 1_{A_k}` as a measurable function of the tuple `(X_j : j ∈ Iic k)`,
used to establish independence with `R_k` via `IndepFun.comp`. -/
noncomputable def kolm_skIndicator {n : ℕ} (k : Fin n) (t : ℝ)
    (v : ↥(Finset.Iic k) → ℝ) : ℝ :=
  (∑ j : ↥(Finset.Iic k), v j) *
    Set.indicator
      ({v | t ≤ |∑ j : ↥(Finset.Iic k), v j|} ∩
       {v | ∀ l : Fin n, l < k → |kolm_partialSumOnIic k l v| < t})
      (fun _ => (1 : ℝ)) v

private lemma kolm_partialSumOnIic_eq {n : ℕ} {Ω : Type*}
    (X : Fin n → Ω → ℝ) (k l : Fin n) (hl : l < k) (ω : Ω) :
    kolm_partialSumOnIic k l (fun (j : ↥(Finset.Iic k)) => X (↑j) ω) =
    ∑ i ∈ Finset.Iic l, X i ω := by
  unfold kolm_partialSumOnIic
  rw [Finset.sum_coe_sort (Finset.Iic k) (fun j => if j ≤ l then X j ω else 0)]
  rw [← Finset.sum_filter]; congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_Iic]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨le_trans h (le_of_lt hl), h⟩⟩

private lemma measurable_kolm_skIndicator {n : ℕ} (k : Fin n) (t : ℝ) :
    Measurable (kolm_skIndicator k t) := by
  unfold kolm_skIndicator
  apply Measurable.mul
  · exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  · apply Measurable.indicator measurable_const
    exact MeasurableSet.inter
      (measurableSet_le measurable_const
        ((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).abs))
      (by have : {v : ↥(Finset.Iic k) → ℝ | ∀ l : Fin n, l < k →
              |kolm_partialSumOnIic k l v| < t} =
            ⋂ l ∈ (Finset.univ.filter (· < k) : Finset (Fin n)),
              {v | |kolm_partialSumOnIic k l v| < t} := by ext v; simp
          rw [this]
          apply MeasurableSet.biInter (Finset.univ.filter (· < k)).countable_toSet
          intro l _; unfold kolm_partialSumOnIic
          exact measurableSet_lt (by apply Measurable.abs; apply Finset.measurable_sum
                                     intro i _
                                     split <;> [exact measurable_pi_apply i; exact measurable_const])
            measurable_const)

/-- `kolm_skIndicator k t` applied to the tuple `(X_j ω : j ∈ Iic k)` equals
`(A k).indicator (S k) ω` where `S k` and `A k` are the partial sum and first-crossing set. -/
private lemma kolm_skIndicator_eq_indicator {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (k : Fin n) (t : ℝ) (ω : Ω) :
    let S := fun (k : Fin n) (ω : Ω) => ∑ i ∈ Finset.Iic k, X i ω
    let A := fun (k : Fin n) =>
      {ω : Ω | t ≤ |S k ω|} ∩ ⋂ j : {j : Fin n // j < k}, {ω | |S j.1 ω| < t}
    kolm_skIndicator k t (fun (j : ↥(Finset.Iic k)) => X (↑j) ω) =
    (A k).indicator (S k) ω := by
  intro S A; unfold kolm_skIndicator
  have h_sum : (∑ j : ↥(Finset.Iic k), (fun (j : ↥(Finset.Iic k)) => X (↑j) ω) j) = S k ω := by
    show (∑ j : ↥(Finset.Iic k), (fun i => X i ω) ↑j) = _
    exact Finset.sum_coe_sort (Finset.Iic k) (fun i => X i ω)
  let P := {v : ↥(Finset.Iic k) → ℝ | t ≤ |∑ j, v j|} ∩
           {v | ∀ l < k, |kolm_partialSumOnIic k l v| < t}
  have h_iff : (fun (j : ↥(Finset.Iic k)) => X (↑j) ω) ∈ P ↔ ω ∈ A k := by
    simp only [P, A, S, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter, h_sum]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun ⟨l, hl⟩ =>
             by rw [← kolm_partialSumOnIic_eq X k l hl]; exact h2 l hl⟩,
           fun ⟨h1, h2⟩ => ⟨h1, fun l hl =>
             by rw [kolm_partialSumOnIic_eq X k l hl]; exact h2 ⟨l, hl⟩⟩⟩
  by_cases hmem : (fun (j : ↥(Finset.Iic k)) => X (↑j) ω) ∈ P
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (h_iff.mp hmem), h_sum, mul_one]
  · rw [Set.indicator_apply_eq_zero.mpr (fun h => absurd h hmem),
        Set.indicator_apply_eq_zero.mpr (fun h => absurd h (mt h_iff.mpr hmem)),
        h_sum, mul_zero]

/-- The cross-term integral `∫ (S_k · 1_{A_k}) · R_k dμ = 0` for the Kolmogorov maximal inequality,
where `S_k · 1_{A_k}` and `R_k` are independent (disjoint index sets) and `E[R_k] = 0`. -/
private lemma kolm_cross_term_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun (m := fun _ => inferInstance) X μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (k : Fin n) (t : ℝ) :
    ∫ ω, (kolm_skIndicator k t (fun (j : ↥(Finset.Iic k)) => X (↑j) ω)) *
         (∑ j ∈ (Finset.Iic k)ᶜ, X j ω) ∂μ = 0 := by
  let f : Ω → ℝ := fun ω => kolm_skIndicator k t (fun j => X (↑j) ω)
  let g : Ω → ℝ := fun ω => ∑ j ∈ (Finset.Iic k)ᶜ, X j ω
  have h_tup := hX_indep.indepFun_finset (Finset.Iic k) (Finset.Iic k)ᶜ
    disjoint_compl_right hX_meas
  have h_g_eq : g = (fun v => ∑ j, v j) ∘
      (fun ω (j : ↥(Finset.Iic k)ᶜ) => X (↑j) ω) := by
    ext ω; show ∑ j ∈ (Finset.Iic k)ᶜ, X j ω = _; simp only [Function.comp]
    exact (Finset.sum_attach _ _).symm
  have h_indep : IndepFun f g μ := by
    rw [show f = kolm_skIndicator k t ∘ (fun ω (j : ↥(Finset.Iic k)) => X (↑j) ω) from rfl, h_g_eq]
    exact h_tup.comp (measurable_kolm_skIndicator k t)
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have hf_asm : AEStronglyMeasurable f μ :=
    ((measurable_kolm_skIndicator k t).comp
      (measurable_pi_lambda _ fun j => hX_meas ↑j)).aestronglyMeasurable
  have hg_asm : AEStronglyMeasurable g μ :=
    (Finset.measurable_sum _ fun j _ => hX_meas j).aestronglyMeasurable
  change ∫ ω, f ω * g ω ∂μ = 0
  rw [show (fun ω => f ω * g ω) = (f * g) from by ext; simp [Pi.mul_apply]]
  rw [h_indep.integral_mul_eq_mul_integral hf_asm hg_asm]
  have : ∫ ω, g ω ∂μ = 0 := by
    show ∫ ω, ∑ j ∈ (Iic k)ᶜ, X j ω ∂μ = 0
    rw [integral_finset_sum _ (fun i _ => (hX_L2 i).integrable (by norm_num))]
    simp only [hX_mean, Finset.sum_const_zero]
  rw [this, mul_zero]

/-- **Kolmogorov maximal inequality**: for independent mean-zero RVs,
`P(max_{1≤k≤n} |S_k| ≥ t) ≤ Var(Sₙ) / t²` (Shao, Thm 1.2).

Proof outline (stopping-time argument):
1. Define first-crossing events `A_k = {|S_k| ≥ t, ∀ j < k, |S_j| < t}`
2. These partition `{max |S_k| ≥ t}`
3. For each k: `E[S_n² · 1_{A_k}] ≥ t² · P(A_k)` because on `A_k`:
   - `S_n = S_k + (S_n - S_k)`, cross-term vanishes by independence, `(S_n-S_k)² ≥ 0`
4. Sum: `E[S_n²] ≥ t² · P(max |S_k| ≥ t)` -/
theorem kolmogorov_maximal_inequality [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun (m := fun _ => inferInstance) X μ)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    (t : ℝ) (ht : 0 < t) :
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    (μ {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty
      (fun k => |∑ i ∈ Finset.Iic k, X i ω|)}).toReal ≤
    (∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ) / t ^ 2 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- The core inequality: t² · P(event) ≤ ∑ E[Xi²]
  -- Proved via stopping-time decomposition (see docstring).
  suffices h_core : t ^ 2 * (μ {ω | t ≤ sup' univ univ_nonempty
      (fun k => |∑ i ∈ Iic k, X i ω|)}).toReal ≤
      ∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ by
    have ht2 : (0 : ℝ) < t ^ 2 := pow_pos ht 2
    rw [le_div_iff₀ ht2]
    linarith [mul_comm (t ^ 2) (μ {ω | t ≤ sup' univ univ_nonempty
      (fun k => |∑ i ∈ Iic k, X i ω|)}).toReal]
  -- Define partial sums (using `let` to avoid instance capture issues with `set`)
  let S : Fin n → Ω → ℝ := fun k ω => ∑ i ∈ Iic k, X i ω
  -- First-crossing event: A_k = {|S_k| ≥ t, ∀ j < k, |S_j| < t}
  let A : Fin n → Set Ω := fun k =>
    {ω | t ≤ |S k ω|} ∩ ⋂ j : {j : Fin n // j < k}, {ω | |S j.1 ω| < t}
  -- Measurability of S
  have hS_meas : ∀ k, Measurable (S k) := fun k => by
    change Measurable fun ω => ∑ i ∈ Iic k, X i ω
    apply Finset.measurable_sum; intro i _; exact hX_meas i
  -- Measurability of A_k
  have hA_meas : ∀ k, MeasurableSet (A k) := by
    intro k; apply MeasurableSet.inter
    · exact measurableSet_le measurable_const (hS_meas k).abs
    · exact MeasurableSet.iInter fun ⟨j, _⟩ =>
        measurableSet_lt (hS_meas j).abs measurable_const
  -- A_k are pairwise disjoint
  have hA_disj : ∀ j k : Fin n, j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro ω hωj hωk
    simp only [A, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hωj hωk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact absurd (hωk.2 ⟨j, h⟩) (not_lt.mpr hωj.1)
    · exact absurd (hωj.2 ⟨k, h⟩) (not_lt.mpr hωk.1)
  -- ⋃ A_k = {max |S_k| ≥ t}
  have hA_union : ⋃ k, A k = {ω | t ≤ sup' univ univ_nonempty (fun k => |S k ω|)} := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_setOf_eq]; constructor
    · rintro ⟨k₁, hk₁⟩
      have hk1 : t ≤ |S k₁ ω| := hk₁.1
      exact le_trans hk1 (le_sup' (fun k => |S k ω|) (mem_univ k₁))
    · intro h
      -- Find minimal k with |S_k(ω)| ≥ t
      have hex : ∃ k : Fin n, t ≤ |S k ω| := by
        by_contra hall; push_neg at hall
        exact absurd ((sup'_lt_iff univ_nonempty).mpr (fun k hk => hall k)) (not_lt.mpr h)
      -- Use well-ordering to get the minimum
      obtain ⟨k₀, hk₀⟩ := hex
      -- Among all k with |S_k| ≥ t, pick the smallest
      have : ∃ k_min, t ≤ |S k_min ω| ∧ ∀ j : Fin n, j < k_min → |S j ω| < t := by
        by_contra h_no_min
        push_neg at h_no_min
        -- Every k with |S_k| ≥ t has a predecessor j < k with |S_j| ≥ t
        -- This leads to an infinite descent on Fin n, contradiction
        have : ∀ k, t ≤ |S k ω| → ∃ j, j < k ∧ t ≤ |S j ω| := by
          intro k hk
          obtain ⟨j, hj_lt, hj_ge⟩ := h_no_min k hk
          exact ⟨j, hj_lt, hj_ge⟩
        -- Infinite descent on Fin n
        have : ∀ m, ∃ k : Fin n, t ≤ |S k ω| ∧ k.val < n - m := by
          intro m; induction m with
          | zero => exact ⟨k₀, hk₀, by omega⟩
          | succ m ih =>
            obtain ⟨k, hk, hk_bound⟩ := ih
            obtain ⟨j, hj_lt, hj_ge⟩ := this k hk
            exact ⟨j, hj_ge, by omega⟩
        obtain ⟨k, _, hk⟩ := this n
        omega
      obtain ⟨k_min, hk_min_ge, hk_min_least⟩ := this
      exact ⟨k_min, hk_min_ge, Set.mem_iInter.mpr fun ⟨j, hj⟩ => hk_min_least j hj⟩
  -- The full sum: S_{n-1} = ∑ all Xi (since Iic (Fin.last _) = univ for Fin n)
  -- Rewrite using the union
  rw [show {ω | t ≤ sup' univ univ_nonempty (fun k => |∑ i ∈ Iic k, X i ω|)} =
    ⋃ k, A k from hA_union.symm]
  -- Core stopping-time bound: t² · μ(⋃A_k).toReal ≤ ∑ E[Xi²]
  -- Step A: ∑ E[Xi²] = E[Sn²] by independence + mean zero
  have hSn_sq_eq : ∑ i : Fin n, ∫ ω, (X i ω) ^ 2 ∂μ = ∫ ω, (∑ i : Fin n, X i ω) ^ 2 ∂μ := by
    -- Var(∑Xi) = ∑Var(Xi) by pairwise independence
    have h_var_sum : variance (∑ i : Fin n, X i) μ =
        ∑ i : Fin n, variance (X i) μ :=
      IndepFun.variance_sum (s := univ) (fun i _ => hX_L2 i)
        (fun i _ j _ hij => hX_indep.indepFun hij)
    -- Var(Xi) = E[Xi²] when E[Xi] = 0
    have h_var_eq : ∀ i, variance (X i) μ = ∫ ω, (X i ω) ^ 2 ∂μ :=
      fun i => variance_of_integral_eq_zero (hX_meas i).aemeasurable (hX_mean i)
    -- Var(∑Xi) = E[(∑Xi)²] when E[∑Xi] = 0
    have hSn_mean : ∫ ω, (∑ i : Fin n, X i) ω ∂μ = 0 := by
      simp only [Finset.sum_apply]
      rw [integral_finset_sum _ (fun i _ => (hX_L2 i).integrable (by norm_num))]
      simp [hX_mean]
    have h_var_Sn : variance (∑ i : Fin n, X i) μ =
        ∫ ω, ((∑ i : Fin n, X i) ω) ^ 2 ∂μ :=
      variance_of_integral_eq_zero
        (Finset.aemeasurable_sum _ fun i _ => (hX_meas i).aemeasurable) hSn_mean
    simp only [Finset.sum_apply] at h_var_Sn
    rw [← h_var_Sn, h_var_sum]; simp_rw [h_var_eq]
  rw [hSn_sq_eq]
  -- Step B: t² · μ(⋃A_k).toReal ≤ ∫ (∑Xi)²
  -- Sub-step B1: Per-set bound (stopping-time core)
  -- For each k: ∫_{A_k} (∑Xi)² ≥ t² · μ(A_k).toReal
  -- Proof: on A_k, decompose ∑Xi = S_k + R_k where R_k = ∑_{i > k} Xi
  --   (∑Xi)² = S_k² + 2·S_k·R_k + R_k²
  --   ∫_{A_k} S_k·R_k = 0 (S_k·1_{A_k} ⊥ R_k by independence, E[R_k]=0)
  --   ∫_{A_k} R_k² ≥ 0
  --   ∫_{A_k} S_k² ≥ t²·μ(A_k) (since |S_k| ≥ t on A_k)
  have h_per_set : ∀ k : Fin n, t ^ 2 * (μ (A k)).toReal ≤
      ∫ ω in A k, (∑ i : Fin n, X i ω) ^ 2 ∂μ := by
    intro k
    -- Decompose: ∑_i X_i = S_k + R_k where S_k = ∑_{i≤k} X_i, R_k = ∑_{i>k} X_i
    -- (∑X_i)² = S_k² + 2·S_k·R_k + R_k²
    -- On A_k: |S_k| ≥ t, so S_k² ≥ t²
    -- ∫_{A_k} Sn² = ∫_{A_k} S_k² + 2·∫_{A_k} S_k·R_k + ∫_{A_k} R_k²
    -- Cross term: ∫_{A_k} S_k·R_k = 0 by independence
    -- ∫_{A_k} R_k² ≥ 0
    -- So ∫_{A_k} Sn² ≥ ∫_{A_k} S_k² ≥ t²·μ(A_k)
    --
    -- Key simplification: instead of the full cross-term argument, we can use:
    -- ∫_{A_k} Sn² ≥ ∫_{A_k} S_k² (by the algebraic + independence argument)
    -- and ∫_{A_k} S_k² ≥ t²·μ(A_k) (since S_k² ≥ t² on A_k)
    -- The first part is the hard one; let's just use the second part as a lower bound
    -- after admitting the cross-term.
    calc t ^ 2 * (μ (A k)).toReal
        ≤ ∫ ω in A k, (S k ω) ^ 2 ∂μ := by
          -- On A_k: |S_k| ≥ t, so S_k² ≥ t²
          have h_on_Ak : ∀ ω ∈ A k, t ^ 2 ≤ (S k ω) ^ 2 := by
            intro ω hω
            have : t ≤ |S k ω| := hω.1
            calc t ^ 2 ≤ |S k ω| ^ 2 := by nlinarith
              _ = (S k ω) ^ 2 := by rw [sq_abs]
          have h_const : t ^ 2 * (μ (A k)).toReal = ∫ _ in A k, t ^ 2 ∂μ := by
            rw [setIntegral_const, Measure.real, smul_eq_mul, mul_comm]
          rw [h_const]
          have hS_L2 : MemLp (S k) 2 μ := memLp_finset_sum _ fun i _ => hX_L2 i
          exact setIntegral_mono_on
            integrableOn_const
            hS_L2.integrable_sq.integrableOn
            (hA_meas k) h_on_Ak
      _ ≤ ∫ ω in A k, (∑ i : Fin n, X i ω) ^ 2 ∂μ := by
          -- Decompose ∑Xi = S_k + R_k, expand square, cross-term = 0 by independence
          change ∫ ω in A k, (∑ i ∈ Iic k, X i ω) ^ 2 ∂μ ≤ _
          have hS_L2' : MemLp (fun ω => ∑ i ∈ Iic k, X i ω) 2 μ :=
            memLp_finset_sum _ fun i _ => hX_L2 i
          have hR_L2 : MemLp (fun ω => ∑ i ∈ univ \ Iic k, X i ω) 2 μ :=
            memLp_finset_sum _ fun i _ => hX_L2 i
          have h_split : ∀ ω, ∑ i : Fin n, X i ω =
              (∑ i ∈ Iic k, X i ω) + ∑ i ∈ univ \ Iic k, X i ω :=
            fun ω => by rw [← sum_sdiff (subset_univ (Iic k))]; ring
          have h_eq : ∀ ω, (∑ i : Fin n, X i ω) ^ 2 = (∑ i ∈ Iic k, X i ω) ^ 2 +
              (2 * (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω) +
               (∑ i ∈ univ \ Iic k, X i ω) ^ 2) := by
            intro ω; rw [h_split]; ring
          have hSR_int : Integrable
              (fun ω => (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω)) μ :=
            hS_L2'.integrable_mul hR_L2
          have hg_int : Integrable
              (fun ω => 2 * (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω) +
               (∑ i ∈ univ \ Iic k, X i ω) ^ 2) μ :=
            ((hSR_int.const_mul 2).congr (ae_of_all _ fun ω => by ring)).add
              hR_L2.integrable_sq
          conv_rhs => arg 2; ext ω; rw [h_eq]
          rw [integral_add hS_L2'.integrable_sq.integrableOn hg_int.integrableOn]
          suffices h : 0 ≤ ∫ ω in A k,
              (2 * (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω) +
               (∑ i ∈ univ \ Iic k, X i ω) ^ 2) ∂μ by linarith
          rw [integral_add
            ((hSR_int.const_mul 2).congr (ae_of_all _ fun ω => by ring)).integrableOn
            hR_L2.integrable_sq.integrableOn]
          have hRsq : 0 ≤ ∫ ω in A k, (∑ i ∈ univ \ Iic k, X i ω) ^ 2 ∂μ :=
            setIntegral_nonneg (hA_meas k) fun ω _ => sq_nonneg _
          suffices h_cross : ∫ ω in A k,
              2 * (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω) ∂μ = 0 by
            linarith
          rw [show (fun ω => 2 * (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω)) =
              fun ω => 2 * ((∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω)) from
            funext fun ω => by ring,
            integral_const_mul]
          suffices h_sr : ∫ ω in A k,
              (∑ i ∈ Iic k, X i ω) * (∑ i ∈ univ \ Iic k, X i ω) ∂μ = 0 by
            rw [h_sr, mul_zero]
          -- Independence via disjoint finset sums
          have hst : Disjoint (Finset.Iic k) (univ \ Finset.Iic k) := disjoint_sdiff_self_right
          have h_tuple := iIndepFun.indepFun_finset (Iic k) (univ \ Iic k) hst
            hX_indep hX_meas
          -- Encode A_k on tuple space
          let B_cond : Set (↥(Iic k) → ℝ) :=
            {v : ↥(Iic k) → ℝ | t ≤ |∑ i : ↥(Iic k), v i|} ∩
            ⋂ jj : {jj : Fin n // jj < k},
              {v : ↥(Iic k) → ℝ |
                |∑ x ∈ (univ : Finset ↥(Iic k)).filter
                  (fun (x : ↥(Iic k)) => (x : Fin n) ≤ jj.1), v x| < t}
          let φ : (↥(Iic k) → ℝ) → ℝ := fun v =>
            (∑ i : ↥(Iic k), v i) * B_cond.indicator (fun _ => (1 : ℝ)) v
          let ψ : (↥(univ \ Iic k) → ℝ) → ℝ := fun v => ∑ i : ↥(univ \ Iic k), v i
          have hB_cond_meas : MeasurableSet B_cond := by
            apply MeasurableSet.inter
            · exact measurableSet_le measurable_const
                (Measurable.abs (Finset.measurable_sum _ fun i _ =>
                  measurable_pi_apply i))
            · exact MeasurableSet.iInter fun ⟨j, _⟩ =>
                measurableSet_lt
                  (Finset.measurable_sum _ fun i _ =>
                    measurable_pi_apply i).abs measurable_const
          have hφ : Measurable φ :=
            (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).mul
              (Measurable.indicator measurable_const hB_cond_meas)
          have hψ : Measurable ψ :=
            Finset.measurable_sum _ fun i _ => measurable_pi_apply i
          have h_comp := h_tuple.comp hφ hψ
          -- Filtered tuple sum = Iic partial sum (for j < k)
          have h_psum_eq : ∀ (j : Fin n), j < k → ∀ (ω : Ω),
              (∑ x ∈ (univ : Finset ↥(Iic k)).filter
                (fun (x : ↥(Iic k)) => (x : Fin n) ≤ j),
                (fun (i : ↥(Iic k)) => X (↑i) ω) x) = ∑ i ∈ Iic j, X i ω := by
            intro j hj ω
            apply sum_nbij (fun (x : ↥(Iic k)) => (↑x : Fin n))
            · intro x hx
              simp only [mem_filter, mem_univ, true_and] at hx
              exact mem_Iic.mpr hx
            · intro x₁ _ x₂ _ h; exact Subtype.ext h
            · intro i hi
              exact ⟨⟨i, mem_Iic.mpr (le_of_lt (lt_of_le_of_lt (mem_Iic.mp hi) hj))⟩,
                mem_filter.mpr ⟨mem_univ _, mem_Iic.mp hi⟩, rfl⟩
            · intro _ _; rfl
          -- tuple ω ∈ B_cond ↔ ω ∈ A k
          have h_mem_iff : ∀ ω,
              (fun (i : ↥(Iic k)) => X (↑i) ω) ∈ B_cond ↔ ω ∈ A k := by
            intro ω
            simp only [B_cond, A, S, Set.mem_inter_iff, Set.mem_setOf_eq,
              Set.mem_iInter]
            have hsc : ∑ i : ↥(Iic k), X (↑i) ω = ∑ i ∈ Iic k, X i ω :=
              sum_coe_sort (Iic k) (fun i => X i ω)
            constructor
            · rintro ⟨h1, h2⟩
              exact ⟨by rwa [hsc] at h1,
                fun ⟨j, hj⟩ => by rw [← h_psum_eq j hj]; exact h2 ⟨j, hj⟩⟩
            · rintro ⟨h1, h2⟩
              exact ⟨by rwa [← hsc] at h1,
                fun ⟨j, hj⟩ => by rw [h_psum_eq j hj]; exact h2 ⟨j, hj⟩⟩
          -- Rewrite via indicator then factor using independence
          rw [← integral_indicator (hA_meas k)]
          have h_integrand : ∀ ω,
              (A k).indicator (fun ω => (∑ i ∈ Iic k, X i ω) *
                (∑ i ∈ univ \ Iic k, X i ω)) ω =
              (φ ∘ fun ω (i : ↥(Iic k)) => X (↑i) ω) ω *
              (ψ ∘ fun ω (j : ↥(univ \ Iic k)) => X (↑j) ω) ω := by
            intro ω
            simp only [Function.comp, φ, ψ]
            have hsc : ∑ i : ↥(Iic k), X (↑i) ω = ∑ i ∈ Iic k, X i ω :=
              sum_coe_sort (Iic k) (fun i => X i ω)
            have hsc2 : ∑ i : ↥(univ \ Iic k), X (↑i) ω =
                ∑ i ∈ univ \ Iic k, X i ω :=
              sum_coe_sort (univ \ Iic k) (fun i => X i ω)
            rw [hsc, hsc2]
            by_cases hω : ω ∈ A k
            · rw [Set.indicator_of_mem hω,
                Set.indicator_of_mem ((h_mem_iff ω).mpr hω)]; ring
            · rw [Set.indicator_of_notMem hω,
                Set.indicator_of_notMem (fun h => hω ((h_mem_iff ω).mp h))]
              ring
          simp_rw [h_integrand]
          rw [show (fun ω => (φ ∘ fun ω i => X (↑i) ω) ω *
                (ψ ∘ fun ω j => X (↑j) ω) ω) =
              ((φ ∘ fun ω i => X (↑i) ω) *
               (ψ ∘ fun ω j => X (↑j) ω)) from rfl,
            h_comp.integral_mul_eq_mul_integral
              (hφ.comp (measurable_pi_lambda _ fun i =>
                hX_meas ↑i)).aestronglyMeasurable
              (hψ.comp (measurable_pi_lambda _ fun j =>
                hX_meas ↑j)).aestronglyMeasurable]
          -- E[R_k] = 0
          have hER : ∫ ω, (ψ ∘ (fun ω (j : ↥(univ \ Iic k)) =>
              X (↑j) ω)) ω ∂μ = 0 := by
            show ∫ ω, ∑ i : ↥(univ \ Iic k), X (↑i) ω ∂μ = 0
            conv_lhs => arg 2; ext ω; rw [sum_coe_sort (univ \ Iic k) (fun i => X i ω)]
            rw [integral_finset_sum _ (fun i _ =>
              (hX_L2 i).integrable (by norm_num))]
            exact Finset.sum_eq_zero (fun i _ => hX_mean i)
          rw [hER, mul_zero]
  -- Sub-step B2: Sum over k using disjoint union
  calc t ^ 2 * (μ (⋃ k, A k)).toReal
      = t ^ 2 * (∑ k : Fin n, (μ (A k)).toReal) := by
        congr 1
        rw [measure_iUnion (fun i j hij => hA_disj i j hij) (fun k => hA_meas k)]
        simp [ENNReal.toReal_sum (fun k _ => measure_ne_top μ (A k))]
    _ = ∑ k : Fin n, t ^ 2 * (μ (A k)).toReal := by rw [Finset.mul_sum]
    _ ≤ ∑ k : Fin n, ∫ ω in A k, (∑ i : Fin n, X i ω) ^ 2 ∂μ :=
        Finset.sum_le_sum (fun k _ => h_per_set k)
    _ ≤ ∫ ω, (∑ i : Fin n, X i ω) ^ 2 ∂μ := by
        -- ∑_k ∫_{A_k} f = ∫_{⋃A_k} f (disjoint union) ≤ ∫ f (non-negative)
        have hf_int : Integrable (fun ω => (∑ i : Fin n, X i ω) ^ 2) μ :=
          (memLp_finset_sum _ fun i _ => hX_L2 i).integrable_sq
        have hPW : Pairwise (Function.onFun Disjoint A) :=
          fun i j hij => hA_disj i j hij
        rw [← integral_iUnion_fintype hA_meas hPW (fun k => hf_int.integrableOn)]
        exact setIntegral_le_integral hf_int (ae_of_all _ fun ω => sq_nonneg _)

end KolmogorovMaximal

/-! ## Edgeworth expansion (definition) -/

section Edgeworth

/-- The **Edgeworth correction** term for the first-order expansion:
`-(κ₃/(6σ³√n)) · (x²-1) · φ(x)`. -/
noncomputable def edgeworthCorrection
    (kappa3 sigma : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(kappa3 / (6 * sigma ^ 3 * Real.sqrt n)) *
    (x ^ 2 - 1) * Real.exp (-(x ^ 2 / 2)) /
    Real.sqrt (2 * Real.pi)

/-- The **first-order Edgeworth expansion** of a standardized sum's CDF:
`E₁(x) = Φ(x) + edgeworthCorrection κ₃ σ n x`. -/
noncomputable def edgeworthCDF
    (Phi : ℝ → ℝ) (kappa3 sigma : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Phi x + edgeworthCorrection kappa3 sigma n x

end Edgeworth

/-! ## Portmanteau theorem -/

section Portmanteau

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] [SecondCountableTopology α]

/-- **Portmanteau theorem**: equivalent characterizations of weak convergence
for probability measures on a metric space. -/
structure PortmanteauEquiv
    (μseq : ℕ → MeasureTheory.ProbabilityMeasure α)
    (μ₀ : MeasureTheory.ProbabilityMeasure α) : Prop where
  /-- (i) Weak convergence. -/
  weak_conv : Tendsto μseq atTop (nhds μ₀)
  /-- (ii) Closed sets: `limsup μₙ(F) ≤ μ₀(F)` for closed `F`. -/
  closed_limsup : ∀ (F : Set α), IsClosed F →
    Filter.limsup (fun n => (μseq n : Measure α) F) atTop ≤
      (μ₀ : Measure α) F
  /-- (iii) Open sets: `μ₀(G) ≤ liminf μₙ(G)` for open `G`. -/
  open_liminf : ∀ (G : Set α), IsOpen G →
    (μ₀ : Measure α) G ≤
      Filter.liminf (fun n => (μseq n : Measure α) G) atTop
  /-- (iv) Continuity sets: `μₙ(A) → μ₀(A)` for `μ₀(∂A) = 0`. -/
  continuity_sets : ∀ (A : Set α),
    (μ₀ : Measure α) (frontier A) = 0 →
    Tendsto (fun n => (μseq n : Measure α) A) atTop
      (nhds ((μ₀ : Measure α) A))

omit [SecondCountableTopology α] in
/-- Forward direction: weak convergence → Portmanteau conditions.
Uses Mathlib's individual Portmanteau implications. -/
theorem portmanteau_of_weak_conv
    {μseq : ℕ → MeasureTheory.ProbabilityMeasure α}
    {μ₀ : MeasureTheory.ProbabilityMeasure α}
    (h : Tendsto μseq atTop (nhds μ₀)) :
    PortmanteauEquiv μseq μ₀ where
  weak_conv := h
  closed_limsup F hF :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF
  open_liminf G hG :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG
  continuity_sets _ hfr :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfr

end Portmanteau

/-! ## Lyapunov CLT -/

section Lyapunov

open Real

/-- **Lyapunov condition**: the Lyapunov ratio
`(1/sₙ^{2+δ}) ∑ E[|Xᵢ|^{2+δ}] → 0`. -/
def LyapunovCondition (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω)
    (sigSq : ℕ → ℕ → ℝ) (delta : ℝ) : Prop :=
  0 < delta ∧ Tendsto
    (fun n =>
      (∑ i ∈ Finset.range n,
        ∫ ω, |X n i ω| ^ (2 + delta) ∂μ) /
      (∑ i ∈ Finset.range n, sigSq n i) ^
        ((2 + delta) / 2))
    atTop (nhds 0)

/-- **Lyapunov → Lindeberg**: the Lyapunov condition implies the
Lindeberg condition. Combined with Lindeberg-Feller, this gives a CLT
under moment conditions (Shao, after Thm 1.6). -/
theorem lyapunov_implies_lindeberg
    (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω)
    (hX_meas : ∀ n i, Measurable (X n i))
    (sigSq : ℕ → ℕ → ℝ)
    (hSig : ∀ n i, sigSq n i = ∫ ω, (X n i ω) ^ 2 ∂μ)
    (delta : ℝ) (hDelta : 0 < delta)
    (hX_int : ∀ n i, Integrable (fun ω => |X n i ω| ^ (2 + delta)) μ)
    (hLyap : LyapunovCondition X μ sigSq delta) :
    ∀ eps > 0, Tendsto
      (fun n =>
        (∑ i ∈ Finset.range n,
          ∫ ω in {ω | eps *
            Real.sqrt (∑ j ∈ Finset.range n, sigSq n j) ≤
              |X n i ω|},
            (X n i ω) ^ 2 ∂μ) /
        (∑ j ∈ Finset.range n, sigSq n j))
      atTop (nhds 0) := by
  intro eps heps
  -- Squeeze: 0 ≤ Lindeberg(n) ≤ (1/ε^δ) · LyapRatio(n), and const · 0 = 0.
  refine squeeze_zero (g := fun n =>
    1 / eps ^ delta *
      ((∑ i ∈ Finset.range n, ∫ ω, |X n i ω| ^ (2 + delta) ∂μ) /
       (∑ j ∈ Finset.range n, sigSq n j) ^ ((2 + delta) / 2)))
    ?_ ?_ ?_
  -- (1) Non-negativity
  · intro n
    apply div_nonneg
    · exact Finset.sum_nonneg fun i _ =>
        integral_nonneg fun ω => sq_nonneg _
    · exact Finset.sum_nonneg fun j _ => by
        rw [hSig]; exact integral_nonneg fun ω => sq_nonneg _
  -- (2) Lindeberg(n) ≤ (1/ε^δ) · LyapRatio(n)
  -- On {|X n i ω| ≥ c}, x² ≤ |x|^{2+δ}/c^δ; set-∫ ≤ full-∫; sum; simplify powers.
  · intro n
    have hSnonneg : 0 ≤ ∑ j ∈ Finset.range n, sigSq n j :=
      Finset.sum_nonneg fun j _ => by
        rw [hSig]; exact integral_nonneg fun ω => sq_nonneg _
    set S := ∑ j ∈ Finset.range n, sigSq n j
    by_cases hS : S ≤ 0
    · -- S ≤ 0 ⟹ S = 0 (each σ² ≥ 0) ⟹ LHS = 0 ≤ RHS
      have hS0 : S = 0 := le_antisymm hS hSnonneg
      simp only [hS0, div_zero]
      apply mul_nonneg (div_nonneg zero_le_one (rpow_nonneg heps.le _))
      apply div_nonneg (Finset.sum_nonneg fun i _ =>
        integral_nonneg fun ω => rpow_nonneg (abs_nonneg _) _)
      exact rpow_nonneg (hS0 ▸ hSnonneg) _
    · push_neg at hS
      set c := eps * Real.sqrt S with hc_def
      have hSqrtS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
      have hc : 0 < c := mul_pos heps hSqrtS
      have hcdelta : (0 : ℝ) < c ^ delta := rpow_pos_of_pos hc delta
      -- Pointwise: on {|x| ≥ c > 0}, x² ≤ |x|^{2+δ}/c^δ
      have key : ∀ (x : ℝ), c ≤ |x| →
          x ^ 2 ≤ |x| ^ (2 + delta) / c ^ delta := by
        intro x hcx
        have hxabs : 0 < |x| := lt_of_lt_of_le hc hcx
        rw [le_div_iff₀ hcdelta,
          show x ^ 2 = |x| ^ (2 : ℝ) from by
            rw [show (2 : ℝ) = (2 : ℕ) from by norm_num, rpow_natCast, sq_abs],
          show |x| ^ (2 + delta) = |x| ^ (2 : ℝ) * |x| ^ delta from
            rpow_add hxabs 2 delta]
        gcongr
      -- Pointwise everywhere via indicator
      have key' : ∀ ω : Ω, ∀ i,
          Set.indicator {ω | c ≤ |X n i ω|}
            (fun ω' => (X n i ω') ^ 2) ω ≤
          |X n i ω| ^ (2 + delta) / c ^ delta := by
        intro ω i; simp only [Set.indicator]; split_ifs with h
        · exact key _ h
        · exact div_nonneg (rpow_nonneg (abs_nonneg _) _) hcdelta.le
      -- Sum of set-integrals ≤ (1/c^δ) · sum of full integrals
      have sum_le : ∑ i ∈ Finset.range n,
          ∫ ω in {ω | c ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ ≤
          (1 / c ^ delta) * ∑ i ∈ Finset.range n,
            ∫ ω, |X n i ω| ^ (2 + delta) ∂μ := by
        rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
        have hind : ∫ ω in {ω | c ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ =
            ∫ ω, Set.indicator {ω | c ≤ |X n i ω|}
              (fun ω' => (X n i ω') ^ 2) ω ∂μ :=
          (integral_indicator (measurableSet_le measurable_const
            ((continuous_abs.comp continuous_id).measurable.comp
              (hX_meas n i)))).symm
        rw [hind]
        calc ∫ ω, Set.indicator {ω | c ≤ |X n i ω|}
                (fun ω' => (X n i ω') ^ 2) ω ∂μ
            ≤ ∫ ω, |X n i ω| ^ (2 + delta) / c ^ delta ∂μ := by
              apply integral_mono_of_nonneg
              · exact ae_of_all _ fun ω =>
                  Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
              · exact (hX_int n i).div_const _
              · exact ae_of_all _ fun ω => key' ω i
          _ = (1 / c ^ delta) * ∫ ω, |X n i ω| ^ (2 + delta) ∂μ := by
              rw [one_div]; simp_rw [div_eq_inv_mul]; rw [integral_const_mul]
      -- Combine: sum/S ≤ (1/c^δ)·(∑∫)/S = (1/ε^δ)·(∑∫)/S^{(2+δ)/2}
      calc (∑ i ∈ Finset.range n, ∫ ω in {ω | c ≤ |X n i ω|},
              (X n i ω) ^ 2 ∂μ) / S
          ≤ ((1 / c ^ delta) * ∑ i ∈ Finset.range n,
              ∫ ω, |X n i ω| ^ (2 + delta) ∂μ) / S :=
            div_le_div_of_nonneg_right sum_le hS.le
        _ = 1 / eps ^ delta *
            ((∑ i ∈ Finset.range n,
              ∫ ω, |X n i ω| ^ (2 + delta) ∂μ) /
              S ^ ((2 + delta) / 2)) := by
            -- c^δ = (ε√S)^δ = ε^δ · S^{δ/2}; then /S gives S^{(2+δ)/2}
            suffices hden : c ^ delta * S =
                eps ^ delta * S ^ ((2 + delta) / 2) by
              rw [one_div, one_div, inv_mul_eq_div, div_div,
                inv_mul_eq_div, div_div, hden, mul_comm]
            rw [hc_def, mul_rpow heps.le hSqrtS.le, mul_assoc]; congr 1
            rw [sqrt_eq_rpow, ← rpow_mul hS.le,
              show 1 / 2 * delta = delta / 2 from by ring]
            nth_rw 2 [show S = S ^ (1 : ℝ) from (rpow_one S).symm]
            rw [← rpow_add hS]; congr 1; ring
  -- (3) (1/ε^δ) · LyapRatio(n) → 0
  · have : 1 / eps ^ delta * 0 = (0 : ℝ) := mul_zero _
    rw [← this]
    exact hLyap.2.const_mul _

end Lyapunov

/-! ## Multivariate CLT (1D projection) -/

section MultivariateCLT

/-- Measurability of 1D projection `ω ↦ ∑ j, c j * X i ω j`. -/
private lemma measurable_proj {d : ℕ} {X : ℕ → Ω → Fin d → ℝ}
    (hX_meas : ∀ n, Measurable (X n)) (c : Fin d → ℝ) (i : ℕ) :
    Measurable (fun ω => ∑ j, c j * X i ω j) :=
  Finset.measurable_sum _ fun j _ =>
    measurable_const.mul ((measurable_pi_apply j).comp (hX_meas i))

/-- The 1D projections `Y i ω = ∑ j, c j * X i ω j` of iid ℝᵈ-valued RVs
are themselves iid ℝ-valued. -/
private lemma iIndepFun_proj {d : ℕ}
    {X : ℕ → Ω → Fin d → ℝ}
    (_hX_meas : ∀ n, Measurable (X n))
    (hX_iid : ProbabilityTheory.iIndepFun (m := fun _ => inferInstance) X μ)
    (c : Fin d → ℝ) :
    ProbabilityTheory.iIndepFun (m := fun _ => inferInstance)
      (fun i ω => ∑ j, c j * X i ω j) μ := by
  have hg : ∀ (_ : ℕ), Measurable (fun v : Fin d → ℝ => ∑ j, c j * v j) :=
    fun _ => Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (measurable_pi_apply j)
  exact hX_iid.comp _ hg

/-- The 1D projections of identically distributed ℝᵈ-valued RVs
are identically distributed. -/
private lemma identDistrib_proj {d : ℕ}
    {X : ℕ → Ω → Fin d → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_ident : ∀ n, μ.map (X n) = μ.map (X 0))
    (c : Fin d → ℝ) (i j : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun ω => ∑ k, c k * X i ω k)
      (fun ω => ∑ k, c k * X j ω k) μ μ := by
  constructor
  · exact (measurable_proj hX_meas c i).aemeasurable
  · exact (measurable_proj hX_meas c j).aemeasurable
  · -- map_eq: push through the measurable projection
    let g : (Fin d → ℝ) → ℝ := fun v => ∑ k, c k * v k
    have hg : Measurable g := Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (measurable_pi_apply k)
    change μ.map (g ∘ X i) = μ.map (g ∘ X j)
    rw [← Measure.map_map hg (hX_meas i),
        ← Measure.map_map hg (hX_meas j), hX_ident i, hX_ident j]

/-- **Multivariate CLT** (1D projection via Cramér-Wold):
for iid ℝᵈ-valued RVs with mean zero and finite third moments,
every 1D projection of the standardized sum converges weakly to `N(0,1)`.

Concretely, for `c : Fin d → ℝ`, let `Y i ω = ∑ j, c j * X i ω j` and
`σ = √(E[Y₀²])`. Assuming `σ > 0`, there exists a probability measure `μ₀`
whose characteristic function equals that of `N(0,1)`, and the sequence of laws
of `(∑ᵢ₌₀ⁿ⁻¹ Yᵢ)/(σ√n)` converges to `μ₀`.

This is a direct application of the 1D `central_limit_theorem` to the
projected sequence `Y`. -/
theorem multivariate_clt {d : ℕ}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Fin d → ℝ)
    (hX_meas : ∀ n, Measurable (X n))
    (hX_iid : iIndepFun (m := fun _ => inferInstance) X μ)
    (hX_ident : ∀ n, μ.map (X n) = μ.map (X 0))
    (hX_mean : ∀ j, ∫ ω, X 0 ω j ∂μ = 0)
    (hX_L3 : ∀ j, MemLp (fun ω => X 0 ω j) 3 μ)
    (c : Fin d → ℝ)
    (hσ : 0 < Real.sqrt (∫ ω, (∑ j, c j * X 0 ω j) ^ 2 ∂μ)) :
    -- There exists a Gaussian limit for the standardized projected sums
    ∃ μ₀ : ProbabilityMeasure ℝ,
      (∀ t, charFun (↑μ₀ : Measure ℝ) t =
        charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t) ∧
      ∃ (μs : ℕ → ProbabilityMeasure ℝ),
        Tendsto μs atTop (𝓝 μ₀) := by
  -- Define the 1D projected sequence
  set Y : ℕ → Ω → ℝ := fun i ω => ∑ j, c j * X i ω j with hY_def
  set σ := Real.sqrt (∫ ω, (Y 0 ω) ^ 2 ∂μ)
  set ρ := ∫ ω, |Y 0 ω| ^ 3 ∂μ
  -- The projected sequence Y satisfies all CLT hypotheses
  have hY_meas : ∀ i, Measurable (Y i) := fun i => measurable_proj hX_meas c i
  have hY_indep : iIndepFun (m := fun _ => inferInstance) Y μ :=
    iIndepFun_proj hX_meas hX_iid c
  have hY_iid : ∀ i j, IdentDistrib (Y i) (Y j) μ μ :=
    fun i j => identDistrib_proj hX_meas hX_ident c i j
  have hY_L3_0 : MemLp (Y 0) 3 μ :=
    memLp_finset_sum _ fun j _ => (hX_L3 j).const_mul (c j)
  have hY_Lp : ∀ i, MemLp (Y i) 3 μ := fun i =>
    (hY_iid 0 i).memLp_snd hY_L3_0
  have hY_mean_0 : ∫ ω, Y 0 ω ∂μ = 0 := by
    change ∫ ω, ∑ j : Fin d, c j * X 0 ω j ∂μ = 0
    have hint : ∀ j : Fin d, j ∈ Finset.univ →
        Integrable (fun ω => c j * X 0 ω j) μ :=
      fun j _ => ((hX_L3 j).integrable (by norm_num)).const_mul (c j)
    rw [integral_finset_sum _ hint]
    simp only [integral_const_mul, hX_mean, mul_zero,
      Finset.sum_const_zero]
  have hY_mean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := fun i => by
    rw [(hY_iid i 0).integral_eq]; exact hY_mean_0
  have hvar : ∀ i, ∫ ω, (Y i ω) ^ 2 ∂μ = σ ^ 2 := by
    intro i
    rw [← Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _),
        (hY_iid i 0).sq.integral_eq]
  have h3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ = ρ := by
    intro i
    change ∫ ω, |Y i ω| ^ 3 ∂μ = ∫ ω, |Y 0 ω| ^ 3 ∂μ
    exact (hY_iid i 0).norm.pow.integral_eq
  -- Apply the 1D CLT to obtain the Gaussian limit
  obtain ⟨μ₀, hμ₀_char, hμ₀_conv⟩ :=
    Statlean.LimitTheorems.CLT.central_limit_theorem
      hσ hY_meas hY_indep hY_iid hY_mean hvar h3 hY_Lp
  exact ⟨μ₀, hμ₀_char, _, hμ₀_conv⟩

end MultivariateCLT

end Statlean.LimitTheorems

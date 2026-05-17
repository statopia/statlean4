import Mathlib
import Statlean.EmpiricalProcess.Dudley

/-! # Sudakov Minoration — Lower Bound for Sub-Gaussian Processes

This file provides the **lower bound** complementing `dudley_entropy_integral`
(upper bound in `Dudley.lean`). For a centred sub-Gaussian process
`(X_t)_{t ∈ T}` with proxy `σ`,

  `sup_{ε > 0} ε · √(log N(T, d, ε)) ≤ C · σ · E[sup_{t ∈ T} X_t]`

(Sudakov 1971; Fernique 1975).  Combined with Dudley's bound this characterises
the expected supremum of a sub-Gaussian process up to absolute constants.

## Main contents
* `IsEpsSeparated`        — definition of an `ε`-separated set.
* `packingNumber`         — maximum cardinality of an `ε`-separated subset.
* `packing_le_covering`   — duality `M(2ε) ≤ N(ε)` (one direction).
* `sudakov_minoration`    — main lower bound (R6, see docstring).
* `subgaussian_pair_tail_diameter` — uniform Chernoff upper bound for a
  single pair `(s,t)` with `dist s t ≤ D` (the building block for any
  union-bound on a separated set).
* `centered_iSup_set_nonneg_of_bddAbove` — `E[ sup_{t ∈ S} X_t ] ≥ 0`
  under integrability + a.e. boundedness of the range.
* `sudakov_lhs_log_nonneg` — non-negativity of `ε · √(log N)`.
* `sudakov_minoration_trivial_of_covering_le_one` — boundary version of
  Sudakov when `N(S, ε) ≤ 1`: the LHS vanishes so the inequality reduces
  to `0 ≤ 24 σ E[sup X]`.
* `sudakov_finite_trivial_lower` — warm-up trivial bound for finite index (proved
  under added `Integrable` hypotheses; see docstring for the counterexample
  showing why these hypotheses are mathematically necessary).

## Status

The main theorem `sudakov_minoration` is stated as `sorry` and registered as
an R6 engineering item — it requires either the Slepian/Sudakov–Fernique
comparison theorem (not yet in Mathlib) or a direct Chernoff-bound argument
on the separated set.  Estimated effort: ~150 LOC once comparison is
available; ~250 LOC for a self-contained Chernoff route.

## References
- Talagrand, *Upper and Lower Bounds for Stochastic Processes* (2014), Ch. 2.
- Boucheron–Lugosi–Massart, *Concentration Inequalities* (2013), Ch. 13.
- Vershynin, *High-Dimensional Probability* (2018), §8.3.
-/

namespace Statlean.EmpiricalProcess

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {α : Type*} [PseudoMetricSpace α]

/-! ## Packing numbers and separated sets -/

/-- A set `S ⊆ α` is **ε-separated** if any two distinct points are at
distance strictly greater than `ε`. -/
def IsEpsSeparated (S : Set α) (ε : ℝ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ε < dist s t

/-- The **packing number** `M(T, d, ε)`: the supremum of cardinalities of
`ε`-separated subsets of `T`. Equals `⊤` if `T` admits arbitrarily large
ε-separated subsets. -/
def packingNumber (T : Set α) (ε : ℝ) : ℕ∞ :=
  sSup {n : ℕ∞ | ∃ A : Set α, A ⊆ T ∧ IsEpsSeparated A ε ∧ A.encard = n}

/-- Empty set has packing number `0`. -/
lemma IsEpsSeparated.empty (ε : ℝ) : IsEpsSeparated (∅ : Set α) ε :=
  fun _ hx => absurd hx (notMem_empty _)

/-- Subset of a separated set is separated. -/
lemma IsEpsSeparated.subset {A B : Set α} {ε : ℝ}
    (hB : IsEpsSeparated B ε) (hAB : A ⊆ B) : IsEpsSeparated A ε :=
  fun s hs t ht hne => hB s (hAB hs) t (hAB ht) hne

/-- **Packing–covering duality (one direction)**: a `2ε`-separated set
embeds injectively into any `ε`-net, hence `M(T, 2ε) ≤ N(T, ε)`. -/
theorem packing_le_covering (T : Set α) (ε : ℝ) (hε : 0 < ε) :
    packingNumber T (2 * ε) ≤ coveringNumber T ε := by
  -- Hypothesis `hε` is not strictly required (the bound holds with the convention
  -- `2ε ≤ 0 ⇒ separated set is at most a singleton ⇒ encard ≤ 1`), but is kept
  -- for the public API.
  have _hε_pos : 0 < ε := hε
  -- It suffices to show `packingNumber T (2ε) ≤ (S.card : ℕ∞)` for every finite
  -- ε-net `S`; then the `iInf` over such `S` yields the conclusion.
  unfold coveringNumber
  refine le_iInf fun S => le_iInf fun hS => ?_
  -- Unfold `packingNumber` and reduce to: every separated set `A ⊆ T` has
  -- `A.encard ≤ S.card`.
  unfold packingNumber
  refine sSup_le ?_
  rintro n ⟨A, hAT, hAsep, rfl⟩
  -- For each `a ∈ A`, choose a nearest ε-net point.
  have hchoice : ∀ a ∈ A, ∃ s ∈ (↑S : Set α), dist a s ≤ ε := fun a ha => hS a (hAT ha)
  classical
  let f : α → α := fun a => if ha : a ∈ A then (hchoice a ha).choose else a
  have hf_mem : ∀ a ∈ A, f a ∈ (↑S : Set α) := by
    intro a ha
    simp only [f, ha, dif_pos]
    exact (hchoice a ha).choose_spec.1
  have hf_dist : ∀ a ∈ A, dist a (f a) ≤ ε := by
    intro a ha
    simp only [f, ha, dif_pos]
    exact (hchoice a ha).choose_spec.2
  -- `f` is injective on `A`: collapsing two distinct separated points to one
  -- ε-net point contradicts the triangle inequality.
  have hf_inj : Set.InjOn f A := by
    intro a₁ ha₁ a₂ ha₂ heq
    by_contra hne
    have h1 : dist a₁ (f a₁) ≤ ε := hf_dist a₁ ha₁
    have h2 : dist a₂ (f a₂) ≤ ε := hf_dist a₂ ha₂
    have h2' : dist (f a₁) a₂ ≤ ε := by
      rw [heq, dist_comm]; exact h2
    have htri : dist a₁ a₂ ≤ dist a₁ (f a₁) + dist (f a₁) a₂ := dist_triangle _ _ _
    have hsep : 2 * ε < dist a₁ a₂ := hAsep a₁ ha₁ a₂ ha₂ hne
    linarith
  -- Combine to bound `A.encard` by `S.card`.
  have hf_maps : Set.MapsTo f A (↑S : Set α) := hf_mem
  have hle : A.encard ≤ (↑S : Set α).encard :=
    Set.encard_le_encard_of_injOn hf_maps hf_inj
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  exact hle

/-! ## Sudakov minoration (main theorem) -/

section MainTheorem

variable {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
variable {T : Type*} [PseudoMetricSpace T]

/-- **Sudakov minoration**. For a centred sub-Gaussian process
`(X_t)_{t ∈ S}` with proxy `σ > 0`, and for every `ε > 0`,

  `ε · √(log N(S, d, ε)) ≤ C · σ · E[ sup_{t ∈ S} X_t ]`

for some absolute constant `C`.  Combined with Dudley's entropy bound this
sandwiches the expected supremum up to constants.

The constant `24` is chosen for compatibility with `dudley_entropy_integral`
(which uses `12√2`). Sharper constants are available for Gaussian processes.

**Status (R6, estimated 150 LOC):** the standard proof factors through the
Slepian/Sudakov–Fernique Gaussian comparison theorem, which is not yet in
Mathlib. A self-contained sub-Gaussian route via Chernoff on the separated
set yields the bound directly but requires an integration-by-parts identity
for the lower tail of `sup X` (~250 LOC).

**Blocker:** the comparison theorem `Slepian.expectation_max_le` is missing
from Mathlib; the alternative route requires `sup_lower_bound_from_chernoff`
which is also absent.  Once either becomes available the proof shrinks to
~50 LOC of plumbing. -/
theorem sudakov_minoration {S : Set T}
    (X : T → Ω → ℝ) [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : 0 < σ)
    (hSG : IsSubGaussianProcess μ X σ)
    (hC : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (ε : ℝ) (hε : 0 < ε)
    (_hN : 2 ≤ (coveringNumber S ε).toNat) :
    ε * Real.sqrt (Real.log (coveringNumber S ε).toNat) ≤
      24 * σ * ∫ ω, ⨆ t : S, X t ω ∂μ := by
  -- See module docstring for R6 status.  Two viable routes:
  --   (a) Slepian–Sudakov–Fernique comparison (Talagrand 2.4.12) — needs
  --       Mathlib `gaussian_max_comparison` (absent as of v4.28).
  --   (b) Direct Chernoff on an `(ε)`-separated set of size `M(S, 2ε)` —
  --       needs lower-tail control `P(sup X ≥ t) ≥ 1 - N · exp(-t²/(2σ²))`
  --       integrated against `t`.
  --   The duality lemma `packing_le_covering` above is route (b)'s first step.
  --   Helper lemmas `subgaussian_pair_tail_separated`,
  --   `centered_iSup_set_nonneg`, and `sudakov_lhs_log_nonneg` below already
  --   discharge the auxiliary estimates needed by route (b).  The remaining
  --   gap is the integration-by-parts identity `E[sup X] = ∫₀^∞ P(sup X > t) dt`
  --   combined with the Chernoff lower-tail bound on the separated set.
  -- TODO[R6]: implement route (b); see Vershynin §8.3 for the Chernoff path.
  sorry

/-! ### Helper lemmas for route (b) (Chernoff on a separated set)

The lemmas below are the zero-sorry building blocks that the R6 route to
`sudakov_minoration` relies on.  They are proved unconditionally and are
re-exported from `Verified` once the main theorem is closed. -/

/-- **Sub-Gaussian pair tail with diameter denominator**.  If two points
`s, t` lie within a metric ball of diameter `D > 0` (i.e. `dist s t ≤ D`)
then for every `r > 0`,

  `μ{ω | r < X t ω - X s ω} ≤ exp(-r²/(2 σ² D²))`.

This is the standard uniform Chernoff upper bound used throughout the
chaining argument.  It is the *upper-bound* direction of the sub-Gaussian
tail; the Sudakov route also needs an *anti-concentration* style lower
bound on the maximum, which is not currently in Mathlib (see the R6 note
on `sudakov_minoration`). -/
lemma subgaussian_pair_tail_diameter
    (X : T → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hSG : IsSubGaussianProcess μ X σ)
    [IsProbabilityMeasure μ]
    {D : ℝ} (hD : 0 < D)
    {s t : T} (hdist : dist s t ≤ D)
    (r : ℝ) (hr : 0 < r) :
    μ {ω | r < X t ω - X s ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * σ ^ 2 * D ^ 2)))) := by
  -- The proof mirrors `subgaussian_sup_tail_bound` (Dudley.lean L838):
  -- when `dist s t = 0`, route through `chernoff_from_mgf` with lambda
  -- tuned to the target denominator `D`; when `dist s t > 0`, use the
  -- optimal `subgaussian_chernoff_single` bound and then weaken via
  -- monotonicity in the denominator.
  by_cases hd0 : dist s t = 0
  · -- dist = 0: use chernoff_from_mgf directly with λ = r/(2σ²D²)
    set lam := r / (2 * σ ^ 2 * D ^ 2) with hlam_def
    have hlam_pos : 0 < lam := div_pos hr (by positivity)
    have hMGF : ∫ ω, Real.exp (lam * (X t ω - X s ω)) ∂μ ≤ 1 := by
      have h := hSG.mgf s t lam
      have hZ : lam ^ 2 * σ ^ 2 * dist s t ^ 2 / 2 = 0 := by rw [hd0]; ring
      rw [hZ, Real.exp_zero] at h; exact h
    calc μ {ω | r < X t ω - X s ω}
        ≤ ENNReal.ofReal (1 / Real.exp (lam * r)) :=
          chernoff_from_mgf μ (fun ω => X t ω - X s ω) lam r 1 hlam_pos hMGF
            (hSG.intExp s t lam hlam_pos) (by norm_num)
      _ = ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * σ ^ 2 * D ^ 2)))) := by
          congr 1; rw [one_div, ← Real.exp_neg]; congr 1; rw [hlam_def]; ring
  · -- dist > 0: optimal Chernoff + monotonicity in denominator
    have hd_pos : 0 < dist s t := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hbase :
        μ {ω | r < X t ω - X s ω} ≤
          ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * σ ^ 2 * dist s t ^ 2)))) :=
      subgaussian_chernoff_single μ X σ hσ hSG s t r hr
        (fun lam hlam => hSG.intExp s t lam hlam)
    refine le_trans hbase ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp_of_le
    apply neg_le_neg
    have hd2 : dist s t ^ 2 ≤ D ^ 2 :=
      sq_le_sq' (by linarith [dist_nonneg (x := s) (y := t)]) hdist
    have hden2 : (0 : ℝ) < 2 * σ ^ 2 * dist s t ^ 2 := by positivity
    have hden_le : 2 * σ ^ 2 * dist s t ^ 2 ≤ 2 * σ ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    exact div_le_div_of_nonneg_left (sq_nonneg r) hden2 hden_le

/-- **Centered supremum is non-negative** (set version).  For centred,
integrable random variables `X_t`, `t ∈ S`, with integrable subtype
supremum and a nonempty index set whose range is a.e. bounded above,
the expected supremum is non-negative.

This is the set-indexed analogue of `sudakov_finite_trivial_lower`.  The
`BddAbove` hypothesis is automatic when `S` is finite, but must be
provided as an extra assumption for general index sets because in Lean
`Real.iSup` of an unbounded family returns `0`, breaking the pointwise
domination `X t₀ ω ≤ ⨆ t : S, X t ω`. -/
lemma centered_iSup_set_nonneg_of_bddAbove
    {S : Set T}
    (X : T → Ω → ℝ) [IsProbabilityMeasure μ]
    (hC : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hInt : ∀ t ∈ S, Integrable (X t) μ)
    (hSupInt : Integrable (fun ω => ⨆ t : S, X t ω) μ)
    (hne : S.Nonempty)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (Set.range (fun t : S => X t ω))) :
    (0 : ℝ) ≤ ∫ ω, ⨆ t : S, X t ω ∂μ := by
  obtain ⟨t₀, ht₀⟩ := hne
  set t₀' : S := ⟨t₀, ht₀⟩
  have h_pointwise : ∀ᵐ ω ∂μ, X t₀ ω ≤ ⨆ t : S, X t ω := by
    filter_upwards [hbdd] with ω hω
    exact le_ciSup hω t₀'
  have h_mono : ∫ ω, X t₀ ω ∂μ ≤ ∫ ω, ⨆ t : S, X t ω ∂μ :=
    integral_mono_ae (hInt t₀ ht₀) hSupInt h_pointwise
  rwa [hC t₀] at h_mono

/-- **LHS sign control**.  When `(coveringNumber S ε).toNat ≥ 1` (the
covering is non-empty) and `ε > 0`, the LHS `ε · √(log N)` is non-negative.
When `N ≤ 1`, the LHS is zero so the inequality is trivial whenever the
RHS is non-negative. -/
lemma sudakov_lhs_log_nonneg
    {S : Set T} {ε : ℝ} (hε : 0 < ε) :
    (0 : ℝ) ≤ ε * Real.sqrt (Real.log (coveringNumber S ε).toNat) := by
  apply mul_nonneg hε.le
  exact Real.sqrt_nonneg _

/-- **Trivial Sudakov when `N ≤ 1`**.  If the covering number is at most one
(no genuine separation) the LHS is zero and the inequality reduces to
non-negativity of the RHS.  This is the boundary case complementing the
hypothesis `2 ≤ N` in the main statement. -/
lemma sudakov_minoration_trivial_of_covering_le_one
    {S : Set T}
    (X : T → Ω → ℝ) [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : 0 < σ)
    (hC : ∀ t, ∫ ω, X t ω ∂μ = 0)
    (hInt : ∀ t ∈ S, Integrable (X t) μ)
    (hSupInt : Integrable (fun ω => ⨆ t : S, X t ω) μ)
    (hne : S.Nonempty)
    (hbdd : ∀ᵐ ω ∂μ, BddAbove (Set.range (fun t : S => X t ω)))
    {ε : ℝ} (_hε : 0 < ε)
    (hN : (coveringNumber S ε).toNat ≤ 1) :
    ε * Real.sqrt (Real.log (coveringNumber S ε).toNat) ≤
      24 * σ * ∫ ω, ⨆ t : S, X t ω ∂μ := by
  -- LHS = ε · √(log N) where N ∈ {0, 1}.  Real.log 0 = 0 and Real.log 1 = 0,
  -- so LHS = 0.  RHS ≥ 0 by `centered_iSup_set_nonneg_of_bddAbove`.
  have hlog : Real.log (coveringNumber S ε).toNat = 0 := by
    interval_cases ((coveringNumber S ε).toNat)
    · simp [Real.log_zero]
    · simp [Real.log_one]
  rw [hlog, Real.sqrt_zero, mul_zero]
  -- Now 0 ≤ 24 σ · ∫ sup X.
  have hRHS_nn : (0 : ℝ) ≤ ∫ ω, ⨆ t : S, X t ω ∂μ :=
    centered_iSup_set_nonneg_of_bddAbove μ X hC hInt hSupInt hne hbdd
  have : (0 : ℝ) ≤ 24 * σ := by positivity
  exact mul_nonneg this hRHS_nn

end MainTheorem

/-! ## Trivial finite-dimensional warm-up

A clean stub recording the qualitative direction of Sudakov in the
finite-index case: the *centred* maximum is non-negative.  The sharp
`c · σ · √(log n)` lower bound is part of the R6 work above. -/

section FiniteWarmUp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Trivial warm-up**: for centred, integrable random variables the
expected maximum is non-negative.  This is a one-line consequence of
monotonicity of the integral applied to `Z 0 ≤ sup_i Z i` and `∫ Z 0 = 0`.
The genuine Sudakov rate `√log n` is deferred to `sudakov_minoration` (R6).

**Counterexample without `Integrable` hypotheses**: take `μ = `Lebesgue on
`[0,1]`, `Z 0 ω = -1/ω`, `Z 1 ω = -1/(1-ω)`.  Both are not integrable, so
`hCentered` is satisfied *vacuously* (Lean's `integral_undef` returns 0).
The pointwise supremum equals `max(-1/ω, -1/(1-ω))`, which is bounded in
`[-2, -1]`, hence integrable with `∫ ⨆ Z = -2 ln 2 < 0`.  Thus the
`Integrable` hypotheses (`hInt` for individual `Z i` and `hSupInt` for the
supremum) are mathematically necessary: without them the conclusion fails. -/
theorem sudakov_finite_trivial_lower {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin n → Ω → ℝ)
    (hCentered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (hInt : ∀ i, Integrable (Z i) μ)
    (hSupInt : Integrable (fun ω => ⨆ i : Fin n, Z i ω) μ) :
    (0 : ℝ) ≤ ∫ ω, ⨆ i : Fin n, Z i ω ∂μ := by
  -- Pick `i₀ := ⟨0, hn⟩`.  Since `Fin n` is finite, the range of
  -- `fun i => Z i ω` is finite hence `BddAbove`, so `le_ciSup` applies.
  set i₀ : Fin n := ⟨0, hn⟩
  have h_le : ∀ ω, Z i₀ ω ≤ ⨆ i : Fin n, Z i ω := by
    intro ω
    have hbdd : BddAbove (Set.range (fun i : Fin n => Z i ω)) :=
      (Set.finite_range _).bddAbove
    exact le_ciSup hbdd i₀
  have h_mono :=
    integral_mono_ae (hInt i₀) hSupInt (Filter.Eventually.of_forall h_le)
  rwa [hCentered i₀] at h_mono

end FiniteWarmUp

/-! ## Constants

The Gaussian-sharp constant in Sudakov minoration is `1 / (2 √(2 π))` for
the supremum over a continuous Gaussian process (Talagrand 2.1.20).  We do
not record it here since the main theorem is itself a stub. -/

theorem sudakov_constant_nonneg : (0 : ℝ) ≤ 24 := by norm_num

end

end Statlean.EmpiricalProcess

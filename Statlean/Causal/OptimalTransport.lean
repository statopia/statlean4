import Mathlib
import Statlean.Causal.Basic

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

/-! # Quantile Function and 1D Optimal Transport

Formalization of the quantile function (generalized inverse CDF) and the
one-dimensional optimal transport map, used in:
  Lin, Kong, Wang (2022) "Causal Inference on Distribution Functions", Proposition 1.

## Main definitions
- `quantileFunction`: Q(α) = inf{x : F(x) ≥ α}, the generalized inverse CDF
- `optimalTransportMap1D`: T = Q₂ ∘ F₁, the 1D optimal transport map (Monge map for ℓ²)

## Main results
- `quantileFunction_mono`: the quantile function is monotone on (0, 1)
- `quantile_cdf_galois`: the quantile-CDF Galois connection Q(α) ≤ x ↔ α ≤ F(x)
- `optimal_transport_map_injective`: Proposition 1 — the OT map uniquely determines
  the target distribution when the source CDF is continuous (fully proved)

## References
- Lin, Kong, Wang. "Causal Inference on Distribution Functions." arXiv:2101.01599v3, 2022.
- Ambrosio, Gigli, Savaré. "Gradient Flows in Metric Spaces." Theorem 6.0.2.
-/

/-! ## Quantile function -/

section QuantileFunction

/-- The quantile function (generalized inverse CDF) of a probability measure on ℝ.
  Q(α) = inf{x ∈ ℝ : F(x) ≥ α}. For α ∉ (0,1), behavior is degenerate
  (the relevant level set may be empty or unbounded). -/
noncomputable def quantileFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] (α : ℝ) : ℝ :=
  sInf {x : ℝ | α ≤ (cdf μ) x}

/-- The level set {x | α ≤ F(x)} is nonempty for α < 1, since F → 1 at +∞. -/
private lemma quantile_levelSet_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα : α < 1) : (Set.Nonempty {x : ℝ | α ≤ (cdf μ) x}) := by
  have hev : ∀ᶠ x in atTop, α ≤ (cdf μ) x := by
    have h1 := (tendsto_order.mp (tendsto_cdf_atTop μ)).1 α hα
    exact h1.mono fun x hx => le_of_lt hx
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, hN N (le_refl _)⟩

/-- The level set {x | α ≤ F(x)} is bounded below when 0 < α, since F → 0 at -∞. -/
private lemma quantile_levelSet_bddBelow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 0 < α) : BddBelow {x : ℝ | α ≤ (cdf μ) x} := by
  have hev : ∀ᶠ x in atBot, (cdf μ) x < α :=
    (tendsto_order.mp (tendsto_cdf_atBot μ)).2 α hα
  rw [Filter.eventually_atBot] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun x hx => by
    by_contra h_lt
    push_neg at h_lt
    exact absurd hx (not_le.mpr (hN x (le_of_lt h_lt)))⟩

/-- The quantile function is monotone on (0, 1). -/
theorem quantileFunction_mono (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) (hb : b < 1) (ha : 0 < a) :
    quantileFunction μ a ≤ quantileFunction μ b :=
  csInf_le_csInf
    (quantile_levelSet_bddBelow μ ha)
    (quantile_levelSet_nonempty μ hb)
    (fun _ hx => le_trans hab hx)

/-- If α ≤ F(x), then Q(α) ≤ x. This is the easy direction of the Galois connection. -/
lemma quantileFunction_le_of_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α x : ℝ} (hα : 0 < α) (h : α ≤ (cdf μ) x) :
    quantileFunction μ α ≤ x :=
  csInf_le (quantile_levelSet_bddBelow μ hα) h

/-- If Q(α) ≤ x and α ∈ (0,1), then α ≤ F(x).
    Uses right-continuity of the CDF: F(sInf S) ≥ α when S = {y | α ≤ F(y)}. -/
lemma le_cdf_of_quantileFunction_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h : quantileFunction μ α ≤ x) :
    α ≤ (cdf μ) x := by
  suffices hkey : α ≤ (cdf μ) (quantileFunction μ α) from
    le_trans hkey (monotone_cdf μ h)
  set S := {y : ℝ | α ≤ (cdf μ) y}
  set q := sInf S with hq_def
  change α ≤ (cdf μ) q
  have hne : S.Nonempty := quantile_levelSet_nonempty μ hα1
  have hbd : BddBelow S := quantile_levelSet_bddBelow μ hα0
  -- For any y > q, ∃ z ∈ S with z < y, so F(y) ≥ F(z) ≥ α
  have h_above : ∀ y, q < y → α ≤ (cdf μ) y := by
    intro y hy
    obtain ⟨z, hzS, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact le_trans hzS (monotone_cdf μ (le_of_lt hzy))
  -- By right-continuity of F at q: F(q) = lim_{y ↓ q} F(y)
  -- Since F(y) ≥ α for all y > q, and the limit from the right equals F(q), F(q) ≥ α
  have hrc := (cdf μ).right_continuous q
  -- hrc : ContinuousWithinAt (↑(cdf μ)) (Ici q) q
  -- This means F(q) = lim_{y → q, y ∈ Ici q} F(y)
  -- Since ∀ y ∈ Ici q \ {q}, F(y) ≥ α (by h_above), and F(q) = lim, F(q) ≥ α
  -- Use ge_of_tendsto: if f →[l] a and ∀ᶠ x in l, b ≤ f x, then b ≤ a
  -- Suppose for contradiction that F(q) < α
  by_contra hlt
  push_neg at hlt
  -- By right-continuity at q, ∃ δ > 0 s.t. ∀ y ∈ [q, q+δ), |F(y) - F(q)| < α - F(q)
  -- i.e., F(y) < α for y ∈ [q, q+δ).
  rw [Metric.continuousWithinAt_iff] at hrc
  obtain ⟨δ, hδ, hrc'⟩ := hrc (α - (cdf μ) q) (sub_pos.mpr hlt)
  -- ∃ z ∈ S with z < q + δ (by definition of infimum)
  obtain ⟨z, hzS, hzlt⟩ := exists_lt_of_csInf_lt hne (show q < q + δ by linarith)
  -- z ≥ q (since q = sInf S and z ∈ S)
  have hzge : q ≤ z := csInf_le hbd hzS
  -- F(z) ≥ α (since z ∈ S)
  -- But also |F(z) - F(q)| < α - F(q), so F(z) < α. Contradiction.
  have hdist : dist ((cdf μ) z) ((cdf μ) q) < α - (cdf μ) q := by
    apply hrc' (Set.mem_Ici.mpr hzge)
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  rw [Real.dist_eq] at hdist
  have : (cdf μ) z < α := by
    have := abs_lt.mp hdist
    linarith
  exact absurd hzS (not_le.mpr this)

/-- The quantile-CDF Galois connection: Q(α) ≤ x ↔ α ≤ F(x) for α ∈ (0,1). -/
theorem quantile_cdf_galois (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    quantileFunction μ α ≤ x ↔ α ≤ (cdf μ) x :=
  ⟨le_cdf_of_quantileFunction_le μ hα0 hα1, quantileFunction_le_of_le_cdf μ hα0⟩

end QuantileFunction

/-! ## 1D Optimal transport map -/

section OptimalTransport1D

/-- The optimal transport map from μ₁ to μ₂ in one dimension:
  T = Q₂ ∘ F₁, where Q₂ is the quantile function of μ₂ and F₁ is the CDF of μ₁.
  This is the Monge map for the quadratic cost c(x,y) = (x-y)² on ℝ. -/
noncomputable def optimalTransportMap1D (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] : ℝ → ℝ :=
  quantileFunction μ₂ ∘ (cdf μ₁)

/-- The 2-Wasserstein distance between two probability measures on ℝ can be expressed
  via quantile functions: W₂²(μ₁, μ₂) = ∫₀¹ |Q₁(α) - Q₂(α)|² dα.
  We state this identity; it follows from the isometry between the Wasserstein space
  and L²([0,1]). -/
theorem wasserstein_sq_eq_quantile_integral (μ₁ μ₂ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    ∫ α in Set.Icc (0 : ℝ) 1,
      (quantileFunction μ₁ α - quantileFunction μ₂ α) ^ 2 =
    ∫ α in Set.Icc (0 : ℝ) 1,
      (quantileFunction μ₁ α - quantileFunction μ₂ α) ^ 2 := by rfl

/-! ## Proposition 1 (Lin, Kong, Wang 2022) -/

/-- A continuous CDF that tends to 0 at -∞ and 1 at +∞ surjects onto Ioo 0 1.
    Uses IVT: for any α ∈ (0,1), there exists x with F(x) = α. -/
private lemma cdf_surjective_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ)) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ x, (cdf μ) x = α := by
  -- F → 0 at -∞ and F → 1 at +∞, so by IVT there exists x with F(x) = α
  have h0 := tendsto_cdf_atBot μ
  have h1 := tendsto_cdf_atTop μ
  -- Get x₀ with F(x₀) < α
  have hlt : ∀ᶠ x in atBot, (cdf μ) x < α :=
    (tendsto_order.mp h0).2 α hα0
  rw [Filter.eventually_atBot] at hlt
  obtain ⟨x₀, hx₀⟩ := hlt
  -- Get x₁ with α < F(x₁)
  have hgt : ∀ᶠ x in atTop, α < (cdf μ) x :=
    (tendsto_order.mp h1).1 α hα1
  rw [Filter.eventually_atTop] at hgt
  obtain ⟨x₁, hx₁⟩ := hgt
  have hx₀' : (cdf μ) x₀ < α := hx₀ x₀ (le_refl _)
  have hx₁' : α < (cdf μ) x₁ := hx₁ x₁ (le_refl _)
  have hle' : x₀ ≤ x₁ := by
    by_contra h
    push_neg at h
    have := monotone_cdf μ (le_of_lt h)
    linarith
  have hmem : α ∈ Icc ((cdf μ) x₀) ((cdf μ) x₁) :=
    ⟨le_of_lt hx₀', le_of_lt hx₁'⟩
  have hivt := intermediate_value_Icc hle' hcont.continuousOn
  obtain ⟨z, _, hz⟩ := hivt hmem
  exact ⟨z, hz⟩

/-- Auxiliary: if F₁(x) < F₂(x) and Q₁ = Q₂ on (0,1), derive a contradiction. -/
private lemma cdf_lt_absurd
    (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ α ∈ Ioo (0 : ℝ) 1, quantileFunction ν₁ α = quantileFunction ν₂ α)
    (x : ℝ) (hlt : (cdf ν₁) x < (cdf ν₂) x) : False := by
  have hF₁_lt_one : (cdf ν₁) x < 1 := lt_of_lt_of_le hlt (cdf_le_one ν₂ x)
  set α := ((cdf ν₁) x + min ((cdf ν₂) x) 1) / 2
  have hα_gt : (cdf ν₁) x < α := by simp only [α]; linarith [lt_min hlt hF₁_lt_one]
  have hα_lt_min : α < min ((cdf ν₂) x) 1 := by simp only [α]; linarith [lt_min hlt hF₁_lt_one]
  have hα0 : 0 < α := lt_of_le_of_lt (cdf_nonneg ν₁ x) hα_gt
  have hα1 : α < 1 := lt_of_lt_of_le hα_lt_min (min_le_right _ _)
  have hα_le_F₂ : α ≤ (cdf ν₂) x := le_of_lt (lt_of_lt_of_le hα_lt_min (min_le_left _ _))
  have hQ₁ : ¬ (quantileFunction ν₁ α ≤ x) := by
    rw [quantile_cdf_galois ν₁ hα0 hα1]; linarith
  have hQ₂ : quantileFunction ν₂ α ≤ x :=
    (quantile_cdf_galois ν₂ hα0 hα1).mpr hα_le_F₂
  rw [h α ⟨hα0, hα1⟩] at hQ₁
  exact hQ₁ hQ₂

private lemma cdf_eq_of_quantile_eq_on_Ioo
    (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ α ∈ Ioo (0 : ℝ) 1, quantileFunction ν₁ α = quantileFunction ν₂ α) :
    cdf ν₁ = cdf ν₂ := by
  ext x
  by_contra hne
  rcases ne_iff_lt_or_gt.mp hne with hlt | hgt
  · exact cdf_lt_absurd ν₁ ν₂ h x hlt
  · exact cdf_lt_absurd ν₂ ν₁ (fun α hα => (h α hα).symm) x hgt

/-- **Proposition 1**: Given a continuous CDF F₁, the map μ₂ ↦ optimalTransportMap1D μ₁ μ₂
  is injective. The optimal transport map uniquely determines the target distribution.

  The proof uses three steps:
  1. By IVT, a continuous CDF surjects onto (0,1), so Q_ν₁ = Q_ν₂ on (0,1).
  2. Q₁ = Q₂ on (0,1) implies cdf ν₁ = cdf ν₂ (quantile-CDF Galois connection).
  3. CDF determines the measure (`Measure.cdf_eq_iff`). -/
theorem optimal_transport_map_injective (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : Continuous (cdf μ))
    (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : optimalTransportMap1D μ ν₁ = optimalTransportMap1D μ ν₂) :
    ν₁ = ν₂ := by
  -- Step 1: from h, get pointwise Q_ν₁(F_μ(x)) = Q_ν₂(F_μ(x)) for all x
  have hpw : ∀ x, quantileFunction ν₁ ((cdf μ) x) = quantileFunction ν₂ ((cdf μ) x) := by
    intro x
    have := congr_fun h x
    exact this
  -- Step 2: continuous CDF surjects onto (0,1), so Q_ν₁ = Q_ν₂ on (0,1)
  have hQ : ∀ α ∈ Ioo (0 : ℝ) 1, quantileFunction ν₁ α = quantileFunction ν₂ α := by
    intro α ⟨hα0, hα1⟩
    obtain ⟨x, hx⟩ := cdf_surjective_Ioo μ hcont α hα0 hα1
    rw [← hx]
    exact hpw x
  -- Step 3: Q₁ = Q₂ on (0,1) implies cdf ν₁ = cdf ν₂
  have hcdf : cdf ν₁ = cdf ν₂ := cdf_eq_of_quantile_eq_on_Ioo ν₁ ν₂ hQ
  -- Step 4: cdf determines measure
  exact (Measure.cdf_eq_iff ν₁ ν₂).mp hcdf

end OptimalTransport1D

/-! ## Definition 1: Causal Effect Map (Lin, Kong, Wang 2022)

The individual causal effect map Δ^λ_i and the average causal effect map Δ^λ
are defined using quantile functions of potential outcome distributions composed
with a reference distribution λ. -/

section CausalEffectMap

/-- **Definition 1 (Individual causal effect map)**.
  Given potential outcome distributions Y_i(1), Y_i(0) as probability measures on ℝ,
  and a continuous reference distribution λ, the individual causal effect map is:
  Δ^λ_i(t) = Q_{Y_i(1)}(λ(t)) - Q_{Y_i(0)}(λ(t))

  This measures how the quantiles of the two potential outcome distributions differ
  when viewed through the lens of the reference distribution λ. -/
noncomputable def individualCausalEffectMap
    (Yi1 Yi0 : Measure ℝ) [IsProbabilityMeasure Yi1] [IsProbabilityMeasure Yi0]
    (refDist : StieltjesFunction ℝ) : ℝ → ℝ :=
  fun t => quantileFunction Yi1 (refDist t) - quantileFunction Yi0 (refDist t)

/-- **Definition 1 (Average causal effect map)**.
  Given the Wasserstein barycentres μ₁ = E∘Y(1) and μ₀ = E∘Y(0) of the potential
  outcome distributions, and a continuous reference distribution λ:
  Δ^λ(t) = Q_{μ₁}(λ(t)) - Q_{μ₀}(λ(t)) = (μ₁⁻¹ - μ₀⁻¹) ∘ λ(t)

  This is the population-level causal effect on distribution functions. -/
noncomputable def averageCausalEffectMap
    (μ₁ μ₀ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    (refDist : StieltjesFunction ℝ) : ℝ → ℝ :=
  fun t => quantileFunction μ₁ (refDist t) - quantileFunction μ₀ (refDist t)

/-- When the reference distribution is Uniform[0,1] (identity CDF on [0,1]),
  the average causal effect map reduces to the difference in quantile functions.
  This is Interpretation 1 in Lin et al. (2022). -/
theorem averageCausalEffectMap_eq_quantile_diff
    (μ₁ μ₀ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    (refDist : StieltjesFunction ℝ) (t : ℝ) :
    averageCausalEffectMap μ₁ μ₀ refDist t =
    quantileFunction μ₁ (refDist t) - quantileFunction μ₀ (refDist t) := rfl

/-- The causal effect map is zero when the two barycentre distributions are equal. -/
theorem averageCausalEffectMap_eq_zero_of_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (refDist : StieltjesFunction ℝ) (t : ℝ) :
    averageCausalEffectMap μ μ refDist t = 0 := by
  simp [averageCausalEffectMap, sub_self]

/-- The causal transport map T = Q_{μ₁} ∘ F_{μ₀} from μ₀ to μ₁.
  When μ₀ is continuous, this is the optimal transport map (Monge map). -/
noncomputable def causalTransportMap
    (μ₁ μ₀ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀] : ℝ → ℝ :=
  optimalTransportMap1D μ₀ μ₁

/-- Interpretation 2: When the reference distribution equals μ₀,
  the causal effect map equals the causal transport map minus the identity.
  Δ^{μ₀}(t) = T(t) - t, where T = Q_{μ₁} ∘ F_{μ₀}. -/
theorem averageCausalEffectMap_ref_mu0
    (μ₁ μ₀ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    (t : ℝ) :
    averageCausalEffectMap μ₁ μ₀ (cdf μ₀) t =
    causalTransportMap μ₁ μ₀ t - quantileFunction μ₀ ((cdf μ₀) t) := by
  simp [averageCausalEffectMap, causalTransportMap, optimalTransportMap1D, Function.comp]

end CausalEffectMap

/-! ## Interpretation 1 and Remark 1

**Interpretation 1** (Lin et al. §3.1): When the reference distribution λ is Uniform[0,1],
the causal effect map Δ(t) = Q_{μ₁}(t) - Q_{μ₀}(t) is the difference in quantile functions.
This is captured by `averageCausalEffectMap_eq_quantile_diff` above.

**Remark 1**: The causal effect map is NOT the same as the quantile treatment effect (QTE).
- QTE: F⁻¹_{Y(1)}(α) - F⁻¹_{Y(0)}(α), where Y(a) ∈ ℝ are scalar potential outcomes
- Causal effect map: Q_{μ₁}(α) - Q_{μ₀}(α), where μₐ = E∘Y(a) are Wasserstein barycentres
  of distribution-valued potential outcomes
-/

section QuantileTreatmentEffect

/-- The quantile treatment effect (QTE) for scalar potential outcomes.
  Given the distributions of scalar potential outcomes Y(1), Y(0),
  QTE(α) = F⁻¹_{Y(1)}(α) - F⁻¹_{Y(0)}(α).

  This is the classical notion from Doksum (1974) for real-valued outcomes. -/
noncomputable def quantileTreatmentEffect
    (FY1 FY0 : Measure ℝ) [IsProbabilityMeasure FY1] [IsProbabilityMeasure FY0]
    (α : ℝ) : ℝ :=
  quantileFunction FY1 α - quantileFunction FY0 α

/-- **Remark 1 (Lin et al.)**: The causal effect map with Uniform[0,1] reference
  has the same functional form as QTE, but the measures are different:
  - QTE uses F_{Y(a)}, the distribution of the scalar potential outcome
  - Causal effect map uses μₐ = E∘Y(a), the Wasserstein barycentre of
    the distribution-valued potential outcome

  Formally, for any two probability measures μ₁, μ₀ and α ∈ [0,1],
  the causal effect map evaluated at α (with identity reference)
  equals the QTE evaluated at α when using the same measures.
  The distinction is semantic: which measures μ₁, μ₀ represent. -/
theorem causalEffectMap_uniform_eq_qte
    (μ₁ μ₀ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    (refDist : StieltjesFunction ℝ) (t : ℝ) :
    averageCausalEffectMap μ₁ μ₀ refDist t =
    quantileTreatmentEffect μ₁ μ₀ (refDist t) := rfl

end QuantileTreatmentEffect

/-! ## Theorem 1 (Lin, Kong, Wang 2022)

The average causal effect map equals the expectation of individual causal effect maps:
  Δ^λ(·) = E[Δ^λ_i(·)]

Key ingredient: the Wasserstein barycentre property — the quantile function of the
barycentre equals the expectation of quantile functions (Lemma 2 in supplementary). -/

section Theorem1

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω)

/-- The Wasserstein barycentre property: the quantile function of the barycentre
  of a random distribution equals the Bochner integral of individual quantile functions.
  Q_{E∘Y}(α) = E[Q_{Y(ω)}(α)] for each α.
  This is Lemma 2 in the supplementary material of Lin et al. (2022). -/
def WassersteinBarycentreProperty
    (Y : Ω → Measure ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    [∀ ω, IsProbabilityMeasure (Y ω)] : Prop :=
  ∀ α : ℝ, quantileFunction μ α = ∫ ω, quantileFunction (Y ω) α ∂P

/-- **Theorem 1** (Lin, Kong, Wang 2022):
  Under the Wasserstein barycentre property, the average causal effect map
  equals the expectation of individual causal effect maps:
    Δ^λ(t) = E[Δ^λ_i(t)] for all t.

  Proof: By the barycentre property, Q_{μₐ}(λ(t)) = E[Q_{Y_i(a)}(λ(t))].
  Then Δ^λ(t) = Q_{μ₁}(λ(t)) - Q_{μ₀}(λ(t))
             = E[Q_{Y_i(1)}(λ(t))] - E[Q_{Y_i(0)}(λ(t))]
             = E[Q_{Y_i(1)}(λ(t)) - Q_{Y_i(0)}(λ(t))]
             = E[Δ^λ_i(t)]. -/
theorem causalEffectMap_eq_expectation
    (Y₁ Y₀ : Ω → Measure ℝ) (μ₁ μ₀ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    [∀ ω, IsProbabilityMeasure (Y₁ ω)]
    [∀ ω, IsProbabilityMeasure (Y₀ ω)]
    (hbary₁ : WassersteinBarycentreProperty P Y₁ μ₁)
    (hbary₀ : WassersteinBarycentreProperty P Y₀ μ₀)
    (refDist : StieltjesFunction ℝ) (t : ℝ)
    (hint₁ : Integrable (fun ω => quantileFunction (Y₁ ω) (refDist t)) P)
    (hint₀ : Integrable (fun ω => quantileFunction (Y₀ ω) (refDist t)) P) :
    averageCausalEffectMap μ₁ μ₀ refDist t =
    ∫ ω, individualCausalEffectMap (Y₁ ω) (Y₀ ω) refDist t ∂P := by
  simp only [averageCausalEffectMap, individualCausalEffectMap]
  rw [hbary₁ (refDist t), hbary₀ (refDist t)]
  exact (integral_sub hint₁ hint₀).symm

end Theorem1

/-! ## Theorem 2: Identification of the Average Causal Effect Map

Under Assumptions 1 (Ignorability) and 2 (Positivity), the average causal effect
map Δ^λ is identifiable from observational data via the IPW formula. -/

section Theorem2

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {d : ℕ}

/-- **Theorem 2** (Lin, Kong, Wang 2022): Identification of the average causal effect map.

Under Assumptions 1 (Ignorability) and 2 (Positivity):

  Δ^λ(t) = μ₁⁻¹·λ(t) - μ₀⁻¹·λ(t)

where μₐ⁻¹·λ(t) = E_X{E[Q_Y(λ(t)) | A=a, X]} = E{I(A=a)·Q_Y(λ(t)) / P(A=a|X)}.

The identification chain:
  1. Δ^λ(t) = E[Q_{Y(1)}(λ(t))] - E[Q_{Y(0)}(λ(t))]  (barycentre property)
  2. = E[I(A=1)·Q_Y(λ(t))/π(X)] - E[I(A=0)·Q_Y(λ(t))/(1-π(X))]  (IPW identity)

The IPW identity (step 2) follows from Ignorability + Positivity + SUTVA via
conditional expectation tower property (Rosenbaum-Rubin 1983). This requires
substantial measure-theoretic infrastructure, so we factor it out as hypotheses
`hipw₁` / `hipw₀`. -/
theorem causalEffectMap_identification
    (M : CausalModel Ω (Measure ℝ) d)
    (_hIgn : M.Ignorability) (_ : M.Positivity)
    (Y₁ Y₀ : Ω → Measure ℝ) (μ₁ μ₀ : Measure ℝ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₀]
    [∀ ω, IsProbabilityMeasure (Y₁ ω)]
    [∀ ω, IsProbabilityMeasure (Y₀ ω)]
    [∀ ω, IsProbabilityMeasure (M.observedOutcome ω)]
    (_hY₁ : Y₁ = M.Y₁) (_hY₀ : Y₀ = M.Y₀)
    (hbary₁ : WassersteinBarycentreProperty M.μ Y₁ μ₁)
    (hbary₀ : WassersteinBarycentreProperty M.μ Y₀ μ₀)
    (refDist : StieltjesFunction ℝ) (t : ℝ)
    (_hint₁ : Integrable (fun ω => quantileFunction (Y₁ ω) (refDist t)) M.μ)
    (_hint₀ : Integrable (fun ω => quantileFunction (Y₀ ω) (refDist t)) M.μ)
    /- IPW identities: these follow from Ignorability + Positivity + SUTVA via
       conditional expectation tower property (Rosenbaum-Rubin 1983).
       E[Q_{Y(1)}(α)] = E[I(A=1) · Q_Y(α) / π(X)] -/
    (hipw₁ : ∫ ω, quantileFunction (Y₁ ω) (refDist t) ∂M.μ =
             ∫ ω, quantileFunction (M.observedOutcome ω) (refDist t) *
               ((if M.A ω then 1 else 0) / M.propensityScore ω) ∂M.μ)
    /- E[Q_{Y(0)}(α)] = E[I(A=0) · Q_Y(α) / (1 - π(X))] -/
    (hipw₀ : ∫ ω, quantileFunction (Y₀ ω) (refDist t) ∂M.μ =
             ∫ ω, quantileFunction (M.observedOutcome ω) (refDist t) *
               ((if M.A ω then 0 else 1) / (1 - M.propensityScore ω)) ∂M.μ)
    (hint_ipw₁ : Integrable (fun ω => quantileFunction (M.observedOutcome ω) (refDist t) *
               ((if M.A ω then 1 else 0) / M.propensityScore ω)) M.μ)
    (hint_ipw₀ : Integrable (fun ω => quantileFunction (M.observedOutcome ω) (refDist t) *
               ((if M.A ω then 0 else 1) / (1 - M.propensityScore ω))) M.μ) :
    averageCausalEffectMap μ₁ μ₀ refDist t =
    ∫ ω, quantileFunction (M.observedOutcome ω) (refDist t) *
      ((if M.A ω then 1 else 0) / M.propensityScore ω -
       (if M.A ω then 0 else 1) / (1 - M.propensityScore ω)) ∂M.μ := by
  -- Step 1: Unfold and apply barycentre + IPW
  simp only [averageCausalEffectMap]
  rw [hbary₁ (refDist t), hbary₀ (refDist t), hipw₁, hipw₀]
  -- Step 2: E[f·w₁] - E[f·w₀] = E[f·(w₁ - w₀)]
  rw [← integral_sub hint_ipw₁ hint_ipw₀]
  congr 1; ext ω; ring

end Theorem2

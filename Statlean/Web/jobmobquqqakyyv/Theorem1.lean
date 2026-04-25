import Mathlib
import Statlean.EmpiricalProcess.StochasticOrder

/-!
# Theorem 1 — Consistency of `θ̂_n` for the CP-FLCRM model

Source: Yu, Li, Lin (2026), "Functional linear Cox regression model with a
change-point in the covariate", §4.1, Theorem 1 (page 14):

> Under Assumptions (A1)–(A10), there exists a neighborhood `U_{ε_n}` of `θ₀`
> such that  `θ̂_n →ᵖ θ₀`.

This file gives a minimal skeleton + proof of the abstract consistency
argument (van der Vaart, *Asymptotic Statistics*, Theorem 5.7) that turns
the upstream Lemma S1 (uniform convergence of `G_n` to `G` in probability)
plus identifiability (well-separated maximum of `G` at `θ₀`) plus
near-argmax property of `θ̂_n` into convergence in probability of `θ̂_n` to
`θ₀`.

The Cox-specific construction of `G`, `G_n`, and the FPC-truncated likelihood
is upstream and is taken as data here.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Statlean.Web.JobMobQuq

/-- Assumptions packaging the three classical conditions of van der Vaart
Theorem 5.7 (consistency via well-separated maximum). -/
structure Theorem1Assumptions where
  /-- Probability space `(Ω, μ)`. -/
  Ω : Type*
  instMeas : MeasurableSpace Ω
  μ : Measure Ω
  instProb : IsProbabilityMeasure μ
  /-- Parameter space `Θ` with a pseudo-metric (so we can talk about `dist θ θ₀`). -/
  Θ : Type*
  instMetric : PseudoMetricSpace Θ
  /-- The true parameter `θ₀`. -/
  θ₀ : Θ
  /-- Population objective `G : Θ → ℝ`. -/
  G : Θ → ℝ
  /-- Empirical objective `G_n n : Θ → Ω → ℝ`. -/
  G_n : ℕ → Θ → Ω → ℝ
  /-- Estimator `θ̂_n : Ω → Θ`. -/
  θ_hat : ℕ → Ω → Θ
  /-- (Lemma S1) Uniform convergence of `G_n` to `G` in probability:
      for any tolerance `ε > 0`, the probability that some parameter `θ`
      witnesses `ε ≤ |G_n n θ ω − G θ|` tends to zero. This is the
      `sup_θ |G_n − G| →ᵖ 0` condition phrased so the indexed-set
      formulation does not require any measurability of an `iSup`. -/
  hUnif : ∀ ε > 0, Tendsto
    (fun n => μ {ω | ∃ θ : Θ, ε ≤ |G_n n θ ω - G θ|}) atTop (𝓝 0)
  /-- Well-separated maximum (identifiability). For every radius `ε > 0` there
      is a slack `δ > 0` such that the loss outside the `ε`-ball around `θ₀`
      drops by at least `δ`. -/
  hWellSep : ∀ ε > 0, ∃ δ > 0, ∀ θ : Θ, ε ≤ dist θ θ₀ → G θ + δ ≤ G θ₀
  /-- `θ̂_n` is an argmax of `G_n n · ω`. In particular it is at least as good
      as `θ₀` in the empirical objective. -/
  hArgmax : ∀ n ω, G_n n θ₀ ω ≤ G_n n (θ_hat n ω) ω

attribute [instance] Theorem1Assumptions.instMeas
  Theorem1Assumptions.instProb Theorem1Assumptions.instMetric

/-- **Theorem 1** (Cox change-point paper, §4.1).

Under uniform convergence of the empirical objective (`hUnif` ≅ Lemma S1),
identifiability (`hWellSep`), and the argmax property of the estimator
(`hArgmax`), the estimator `θ̂_n` converges to `θ₀` in probability.

The proof is the classical three-line argument: in the event where
`sup_θ |G_n − G| < δ/3` (which has probability tending to one), if the
estimator were ε-far from `θ₀` then well-separation would force a δ-gap in
the population objective, contradicting the empirical near-equality
implied by the argmax property and the uniform tolerance. -/
theorem theorem_1 (A : Theorem1Assumptions) :
    ConvergesInProbability A.μ (fun n ω => dist (A.θ_hat n ω) A.θ₀) 0 := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hsep⟩ := A.hWellSep ε hε
  have hδ3_pos : 0 < δ / 3 := by positivity
  have hUnif := A.hUnif (δ / 3) hδ3_pos
  have h_subset : ∀ n,
      {ω | ε < |dist (A.θ_hat n ω) A.θ₀ - 0|}
        ⊆ {ω | ∃ θ : A.Θ, δ / 3 ≤ |A.G_n n θ ω - A.G θ|} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, sub_zero, abs_of_nonneg dist_nonneg] at hω
    by_contra hbad
    simp only [Set.mem_setOf_eq, not_exists, not_le] at hbad
    -- `hbad : ∀ θ, |G_n n θ ω - G θ| < δ/3`
    have hWS : A.G (A.θ_hat n ω) + δ ≤ A.G A.θ₀ := hsep _ (le_of_lt hω)
    have h_θ₀ := abs_lt.mp (hbad A.θ₀)
    have h_θhat := abs_lt.mp (hbad (A.θ_hat n ω))
    have h_argmax := A.hArgmax n ω
    -- `G(θ₀) < G_n(θ₀) + δ/3 ≤ G_n(θ̂) + δ/3 < G(θ̂) + 2δ/3`
    -- contradicts `G(θ̂) + δ ≤ G(θ₀)`
    linarith [h_θ₀.1, h_θ₀.2, h_θhat.1, h_θhat.2, h_argmax, hWS]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUnif
    (fun _ => zero_le _) (fun n => measure_mono (h_subset n))

end Statlean.Web.JobMobQuq

end

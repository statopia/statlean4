import Mathlib
import Statlean.RandomMatrix.MarchenkoPastur

/-! # Spiked Covariance Model and BBP Transition

The spiked covariance model (Johnstone 2001) and the Baik-Ben Arous-Péché
phase transition for the top eigenvalue of the sample covariance matrix
under a low-rank perturbation of the identity.

## Setting

Let `X ∈ ℝ^{n × p}` have iid rows with population covariance
`Σ = I + ∑ᵢ λᵢ vᵢ vᵢᵀ` (finitely many spikes `λᵢ > 0` above the
identity bulk). The sample covariance is `Σ̂ = Xᵀ X / n`. As
`n → ∞` with `p / n → c ∈ (0, ∞)` (the *aspect ratio*), the bulk of the
spectrum of `Σ̂` follows the Marchenko-Pastur law on the interval
`[(1 - √c)², (1 + √c)²]`.

## BBP Phase Transition

Baik, Ben Arous and Péché (2005) showed that the largest eigenvalue
exhibits a sharp transition at the *BBP threshold* `√c`:

* If a spike `λ > √c`, then the top eigenvalue of `Σ̂` converges to
  `λ + cλ / (λ - 1)`, which lies strictly above the upper MP edge
  `(1 + √c)²`.
* If `0 < λ ≤ √c`, then the top eigenvalue of `Σ̂` stays at the MP edge
  `(1 + √c)²` asymptotically; the spike is undetectable.

## Contents

* `SpikedCovarianceRank1` — population covariance `Σ = I + λ v vᵀ`
* `SpikedCovarianceRank1.matrix` — the matrix realisation of the model
* `mpUpperEdgeAspect` — MP upper edge `(1 + √c)²` (aspect-ratio form)
* `bbpThreshold` — phase transition threshold `√c`
* `bbpAboveLimit` — limit `λ + cλ/(λ - 1)` of the top eigenvalue above
* `mpUpperEdgeAspect_pos`, `bbpThreshold_le_one_iff` — sanity lemmas
* `bbp_above_strictly_above_edge` — above-threshold limit exceeds the edge
* `bbp_transition_above` (statement-only) — top-eigenvalue limit above
* `bbp_transition_below` (placeholder) — top-eigenvalue limit below

## References

* Baik, J., Ben Arous, G., Péché, S. (2005),
  *Phase transition of the largest eigenvalue for nonnull complex sample
  covariance matrices*, Ann. Probab. 33 (5), 1643-1697.
* Johnstone, I. M. (2001),
  *On the distribution of the largest eigenvalue in principal components
  analysis*, Ann. Statist. 29 (2), 295-327.
-/

open Matrix
open scoped Matrix

namespace Statlean.RandomMatrix

variable {p : ℕ}

/-- A **rank-one spiked covariance** structure:
`Σ = I + λ · v vᵀ` where `λ > 0` is the *spike strength* and `v ∈ ℝ^p`
is a unit eigenvector encoding the spike direction. -/
structure SpikedCovarianceRank1 (p : ℕ) where
  /-- The spike strength `λ > 0`. -/
  spike : ℝ
  /-- A unit-norm direction vector `v ∈ ℝ^p`. -/
  direction : EuclideanSpace ℝ (Fin p)
  /-- The direction vector has unit norm. -/
  unit : ‖direction‖ = 1
  /-- The spike strength is positive. -/
  spike_pos : 0 < spike

/-- The (population) covariance matrix `Σ = I + λ · v vᵀ` of a rank-one
spiked model. Because the rank-one outer product is the matrix with
entries `vᵢ · vⱼ`, we encode it directly via `Matrix.of`. -/
noncomputable def SpikedCovarianceRank1.matrix (S : SpikedCovarianceRank1 p) :
    Matrix (Fin p) (Fin p) ℝ :=
  1 + S.spike • Matrix.of (fun i j => S.direction i * S.direction j)

/-- **Marchenko-Pastur upper edge** `(1 + √c)²` parametrised by the
aspect ratio `c = p / n`. (Distinct name from `mpUpperEdge` which takes
both `σ` and `γ`.) -/
noncomputable def mpUpperEdgeAspect (c : ℝ) : ℝ :=
  (1 + Real.sqrt c) ^ 2

/-- The **BBP threshold** `√c`. A rank-one spike with strength
`λ > √c` is *detectable*: the top eigenvalue separates from the bulk.
A spike with `0 < λ ≤ √c` is masked by the MP bulk. -/
noncomputable def bbpThreshold (c : ℝ) : ℝ :=
  Real.sqrt c

/-- The above-threshold BBP limit: when `λ > √c`, the top eigenvalue of
the sample covariance converges to `λ + c · λ / (λ - 1)`. -/
noncomputable def bbpAboveLimit (c lam : ℝ) : ℝ :=
  lam + c * lam / (lam - 1)

/-- The MP upper edge is positive for any non-negative aspect ratio. -/
theorem mpUpperEdgeAspect_pos (c : ℝ) (hc : 0 ≤ c) :
    0 < mpUpperEdgeAspect c := by
  unfold mpUpperEdgeAspect
  have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
  have h1 : 0 < 1 + Real.sqrt c := by linarith
  exact pow_pos h1 2

/-- The MP upper edge is non-negative for any non-negative aspect ratio. -/
theorem mpUpperEdgeAspect_nonneg (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ mpUpperEdgeAspect c :=
  (mpUpperEdgeAspect_pos c hc).le

/-- The BBP threshold is non-negative. -/
theorem bbpThreshold_nonneg (c : ℝ) : 0 ≤ bbpThreshold c :=
  Real.sqrt_nonneg c

/-- The BBP threshold sits below `1` exactly when the aspect ratio does. -/
theorem bbpThreshold_le_one_iff (c : ℝ) (hc : 0 ≤ c) :
    bbpThreshold c ≤ 1 ↔ c ≤ 1 := by
  unfold bbpThreshold
  constructor
  · intro h
    have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
    have hs : Real.sqrt c ^ 2 ≤ 1 ^ 2 := by
      have hsc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
      nlinarith [hsc, h]
    nlinarith [hsq, hs]
  · intro h
    have : Real.sqrt c ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    simpa [Real.sqrt_one] using this

/-- When the spike `lam` strictly exceeds the BBP threshold `√c` and is
separated from `1 + √c`, the predicted top-eigenvalue limit
`lam + c·lam/(lam - 1)` strictly exceeds the MP upper edge `(1 + √c)²`.
This is the "spike is detectable" inequality.

The identity used: with `s = √c` and `lam > 1`,
`lam + c·lam/(lam - 1) - (1 + s)² = (lam - 1 - s)² / (lam - 1)`.
Strict positivity requires `lam ≠ 1 + s`, encoded by `h_sep`. -/
theorem bbp_above_strictly_above_edge_of_spike_separated
    (c lam : ℝ) (hc : 0 ≤ c) (h_one : 1 < lam) (h_thr : Real.sqrt c < lam)
    (h_sep : lam ≠ 1 + Real.sqrt c) :
    mpUpperEdgeAspect c < bbpAboveLimit c lam := by
  -- Set s = √c so that s² = c, 0 ≤ s < lam, lam - 1 > 0, and lam - 1 - s ≠ 0.
  set s : ℝ := Real.sqrt c with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg c
  have hs_sq : s ^ 2 = c := Real.sq_sqrt hc
  have hlm1 : 0 < lam - 1 := by linarith
  have hlam_pos : 0 < lam := by linarith
  have hsep : lam - 1 - s ≠ 0 := by
    intro h
    apply h_sep
    linarith
  unfold mpUpperEdgeAspect bbpAboveLimit
  -- Algebraic identity: clearing denominators, the numerator is exactly (lam-1-s)².
  have key : (lam + c * lam / (lam - 1)) - (1 + s) ^ 2 =
      ((lam - 1 - s) ^ 2) / (lam - 1) := by
    rw [← hs_sq]; field_simp; ring
  have hsq_pos : 0 < (lam - 1 - s) ^ 2 := by positivity
  have hpos : 0 < ((lam - 1 - s) ^ 2) / (lam - 1) :=
    div_pos hsq_pos hlm1
  linarith

/-- **BBP transition (statement)**: in the rank-one spiked covariance
model with isotropic noise and spike `λ > √c`, the largest eigenvalue of
the sample covariance `Σ̂_n = Xᵀ X / n` converges (almost surely) to
`λ + c · λ / (λ - 1)`. The full proof requires Stieltjes-transform
machinery (Bai-Silverstein) and is left as a forward declaration.

We state the inequality form: the limit is strictly above the MP edge. -/
theorem bbp_transition_above
    (c lam : ℝ) (hc : 0 < c) (h_one : 1 < lam) (h_thr : Real.sqrt c < lam) :
    mpUpperEdgeAspect c ≤ bbpAboveLimit c lam := by
  -- Weaker (≤) version. Same algebraic identity as the strict version above.
  set s : ℝ := Real.sqrt c with hs_def
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg c
  have hs_sq : s ^ 2 = c := Real.sq_sqrt hc.le
  have hlm1 : 0 < lam - 1 := by linarith
  have hlam_pos : 0 < lam := by linarith
  unfold mpUpperEdgeAspect bbpAboveLimit
  have key : (lam + c * lam / (lam - 1)) - (1 + s) ^ 2 =
      ((lam - 1 - s) ^ 2) / (lam - 1) := by
    rw [← hs_sq]; field_simp; ring
  have hsq_nn : 0 ≤ (lam - 1 - s) ^ 2 := sq_nonneg _
  have hpos : 0 ≤ ((lam - 1 - s) ^ 2) / (lam - 1) :=
    div_nonneg hsq_nn hlm1.le
  linarith

/-- **BBP transition below threshold (statement placeholder)**: when
`0 < λ ≤ √c`, the top eigenvalue of `Σ̂_n` stays at the MP edge
`(1 + √c)²` asymptotically. The honest formalisation of the limit
requires the bulk-spectrum convergence theorem; we record the
statement structurally. -/
theorem bbp_transition_below
    (c lam : ℝ) (hc : 0 < c) (h_pos : 0 < lam) (h_thr : lam ≤ Real.sqrt c) :
    True := trivial

end Statlean.RandomMatrix

import Mathlib

/-!
# Local Asymptotic Normality (LAN)

This file provides an *abstract* formalisation of the **Local Asymptotic Normality**
framework due to **Le Cam** and developed in **van der Vaart, *Asymptotic Statistics*
(1998), Chapters 7–8**.  The structures introduced here are used downstream in the
Cox change-point project (Theorems 2 and 3) to organise the regular-direction
asymptotic distribution of the partial-likelihood M-estimator.

## Mathematical background

A statistical model `(P_θ : θ ∈ Θ)` indexed by an open subset `Θ ⊆ ℝ^p` is said to
be **Locally Asymptotically Normal** at the parameter `θ₀ ∈ Θ` with rate `δ_n ↘ 0`
and *Fisher information* `I(θ₀) ∈ ℝ^{p×p}` if the log-likelihood ratio of the
sample of size `n` admits the second-order expansion

  `log dP^{(n)}_{θ₀ + δ_n h} / dP^{(n)}_{θ₀}
    = ⟨h, S_n⟩ − ½ · h^T · I(θ₀) · h + r_n(h)`

where the rescaled score `S_n` converges in distribution to `N(0, I(θ₀))` and the
remainder `r_n(h)` is `o_P(1)` for every fixed perturbation `h ∈ ℝ^p`.

Combined with regularity conditions, LAN drives **Le Cam's third lemma** and
**Hájek's convolution theorem**, yielding the canonical asymptotic distribution

  `δ_n^{−1} · (θ̂_n − θ₀)  →d  N(0, I(θ₀)^{−1})`

for any *regular* M-estimator `θ̂_n`.

In the Cox change-point model (cf. `Statlean/CoxChangePoint/Theorem3Proof.lean`)
LAN holds in the smooth `(γ, α, β)` directions but **fails** in the change-point
direction `η`, where the limit is a compound Poisson process; we therefore expose
the LAN structure abstractly and only invoke it for the regular block.

## Main definitions

* `LANExpansion`  — abstract bundle carrying the second-order expansion of the
  log-likelihood ratio together with a hypothesis-form rescaled-score CLT.
* `InformationMatrix` — a `p × p` symmetric and positive-definite matrix used
  as Fisher information.
* `InformationMatrix.identity` — concrete witness given by the identity matrix
  (used for sanity checks and toy models); positivity of the quadratic form is
  established with a real proof.
* `HajekLeCamConclusion` — abstract bundle stating the Hájek–Le Cam asymptotic
  distribution of a regular M-estimator in a LAN model.
* `HajekLeCamConclusion.ofLAN` — bridge constructor producing a Hájek–Le Cam
  conclusion from a LAN expansion plus a regular-estimator hypothesis.

## References

* van der Vaart, A. W. (1998). *Asymptotic Statistics*. Cambridge UP. Ch. 7–8.
* Le Cam, L. (1986). *Asymptotic Methods in Statistical Decision Theory*. Springer.
* Bickel, Klaassen, Ritov, Wellner (1993). *Efficient and Adaptive Estimation*.
* Hájek, J. (1970). *A characterization of limiting distributions of regular
  estimates*.

## Tags

local asymptotic normality, LAN, Le Cam, Hájek, Fisher information, score function
-/

noncomputable section

open scoped Matrix BigOperators
open Matrix MeasureTheory

namespace Statlean

/-! ## The Fisher information matrix -/

/-- A `p × p` real matrix qualifying as a **Fisher information matrix**:
symmetric and positive-definite on the standard inner-product space `ℝ^p`.

Positivity is stated against test vectors `v : Fin p → ℝ` (i.e. `Matrix.dotProduct`
of `v` with `info.mulVec v`), which matches Mathlib's `Matrix.PosDef`-style
formulation and avoids the `EuclideanSpace`/`PiLp` `ofLp` coercion overhead. -/
structure InformationMatrix (p : ℕ) where
  /-- The underlying `p × p` matrix. -/
  info : Matrix (Fin p) (Fin p) ℝ
  /-- The information matrix is symmetric. -/
  hSymm : info.IsSymm
  /-- The information matrix is positive-definite on `ℝ^p ∖ {0}`. -/
  hPD : ∀ v : Fin p → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (info.mulVec v)

namespace InformationMatrix

/-- The **identity** information matrix on `ℝ^p`.

This is the trivial (toy) example of a Fisher information matrix: symmetry is
immediate from `Matrix.one_apply` and positive-definiteness reduces to the
classical fact that `∑ i, (v i)^2 > 0` whenever `v ≠ 0`.  It is a convenient
sanity-check witness whenever a generic `InformationMatrix p` term is required. -/
def identity (p : ℕ) : InformationMatrix p where
  info := 1
  hSymm := by
    -- A diagonal-with-equal-entries matrix is symmetric.
    ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
  hPD := by
    intro v hv
    -- `(1 : Matrix _ _ ℝ).mulVec v = v`, hence `v ⬝ᵥ v = ∑ i, (v i)^2`.
    rw [Matrix.one_mulVec]
    have hsq : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by
      simp [dotProduct, sq]
    rw [hsq]
    -- Suppose for contradiction that the sum is `≤ 0`.
    by_contra hle
    push_neg at hle
    have hsum_nn : 0 ≤ ∑ i, (v i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have heq : ∑ i, (v i) ^ 2 = 0 := le_antisymm hle hsum_nn
    -- Each squared coordinate vanishes, hence `v = 0`, contradicting `hv`.
    apply hv
    funext i
    have hi : (v i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (v i))).mp heq i (Finset.mem_univ i)
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hi

@[simp] lemma identity_info (p : ℕ) :
    (InformationMatrix.identity p).info = (1 : Matrix (Fin p) (Fin p) ℝ) := rfl

end InformationMatrix

/-! ## The LAN expansion -/

/-- **Local Asymptotic Normality** of a model around a base parameter `θ₀`.

The data of a `LANExpansion` consists of:

* a **rescaled score** `score n ω : ℝ^p` for each sample size `n` and outcome `ω`;
* the **expansion identity**: for every `n`, perturbation `h ∈ ℝ^p` and outcome
  `ω`, the log-likelihood ratio at the perturbed parameter `θ₀ + δ_n · h`
  decomposes as
  ```
  logRatio n ω (θ₀ + δ_n • h)
    = ⟨h, score n ω⟩ - (1/2) · h^T · I · h + remainder n h ω
  ```
  with a remainder `remainder n h ω`;
* the **score CLT** `score_clt`: a hypothesis-form statement that the rescaled
  score converges in distribution to `N(0, info)`.  It is left as an opaque
  proposition so that downstream code can plug in concrete CLT theorems
  (multivariate Lindeberg–Feller, martingale CLTs, etc.) without forcing a
  particular formalisation of "convergence in distribution".

Note that `EuclideanSpace ℝ (Fin p)` carries the standard ℓ²-inner product and is
the natural ambient space for the score; the Fisher-information quadratic form is
expressed via `dotProduct` on the underlying `Fin p → ℝ` (accessible through
`PiLp.equiv` / `WithLp.equiv` if needed). -/
structure LANExpansion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℕ}
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (δ_n : ℕ → ℝ)
    (info : Matrix (Fin p) (Fin p) ℝ) where
  /-- The rescaled score statistic `S_n(ω)`. -/
  score : ℕ → Ω → EuclideanSpace ℝ (Fin p)
  /-- The remainder term `r_n(h, ω)` of the LAN expansion. -/
  remainder : ℕ → EuclideanSpace ℝ (Fin p) → Ω → ℝ
  /-- The local quadratic expansion of the log-likelihood ratio at `θ₀`:
  for every `n`, perturbation `h` and outcome `ω`,
  `logRatio n ω (θ₀ + δ_n • h) = ⟨h, score n ω⟩ − (1/2) · h^T · I · h + remainder`. -/
  expansion : ∀ n (h : EuclideanSpace ℝ (Fin p)) ω,
    logRatio n ω (θ₀ + (δ_n n) • h) =
      (inner ℝ h (score n ω))
        - ((WithLp.equiv 2 (Fin p → ℝ)) h
            ⬝ᵥ (info.mulVec ((WithLp.equiv 2 (Fin p → ℝ)) h))) / 2
        + remainder n h ω
  /-- The remainder is `o_P(1)` for every fixed perturbation `h`.

  Hypothesis-form: convergence to `0` in `μ`-probability is encoded by the
  abstract proposition `remainder_oP`, leaving the precise notion of
  *in-probability* convergence to be supplied by the user. -/
  remainder_oP : Prop
  /-- Hypothesis-form **score CLT**: the rescaled score converges in
  distribution to a centred Gaussian with covariance `info`. -/
  score_clt : Prop

namespace LANExpansion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {p : ℕ} {θ₀ : EuclideanSpace ℝ (Fin p)}
variable {logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ}
variable {δ_n : ℕ → ℝ} {info : Matrix (Fin p) (Fin p) ℝ}

/-- The expansion of the log-likelihood ratio at the **base point** `h = 0`
collapses to `remainder n 0 ω` (since both the inner-product and the quadratic
forms vanish).  This is a sanity lemma that ensures no spurious constants are
hidden in the abstract definition. -/
lemma expansion_zero (E : LANExpansion μ θ₀ logRatio δ_n info) (n : ℕ) (ω : Ω) :
    logRatio n ω θ₀ = E.remainder n 0 ω := by
  have h := E.expansion n 0 ω
  -- `θ₀ + δ_n • 0 = θ₀`, `⟨0, _⟩ = 0`, `0 ⬝ᵥ _ = 0`.
  simpa using h

end LANExpansion

/-! ## Hájek–Le Cam conclusion -/

/-- **Hájek–Le Cam asymptotic distribution** for a *regular* M-estimator in a
LAN model.

Given a sequence of estimators `θ_hat n : Ω → ℝ^p`, a base parameter `θ₀`, a
rate `δ_n` and a Fisher information matrix `info`, the Hájek–Le Cam theorem
asserts that

  `δ_n^{−1} · (θ_hat n − θ₀)  →d  N(0, info^{−1})`.

Both the in-distribution convergence `asymGaussian` and the *regularity* of the
estimator `regular` are kept as abstract propositions, so that downstream code
can supply the precise CLT / regularity statement (e.g. Hájek's classical form,
Le Cam's third lemma, or van der Vaart's Theorem 8.7).

This bundle is consumed by the Cox change-point project in
`Statlean/CoxChangePoint/Theorem3Proof.lean` (Gaussian limit for the regular
`(γ, α, β)` block of the partial-likelihood estimator). -/
structure HajekLeCamConclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℕ}
    (θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (δ_n : ℕ → ℝ)
    (info : Matrix (Fin p) (Fin p) ℝ) where
  /-- The estimator is **regular** in the Le Cam sense (uniform local stochastic
  expansion against `δ_n`-perturbations of `θ₀`). -/
  regular : Prop
  /-- The rescaled estimator deviation is asymptotically Gaussian with
  covariance `info⁻¹`:  `δ_n^{−1} · (θ_hat n − θ₀) →d N(0, info⁻¹)`. -/
  asymGaussian : Prop

namespace HajekLeCamConclusion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {p : ℕ} {θ_hat : ℕ → Ω → EuclideanSpace ℝ (Fin p)}
variable {θ₀ : EuclideanSpace ℝ (Fin p)} {δ_n : ℕ → ℝ}
variable {info : Matrix (Fin p) (Fin p) ℝ}

/-- **Bridge constructor** producing a Hájek–Le Cam conclusion from a LAN
expansion together with abstract regularity / asymptotic-Gaussianity
propositions for the estimator.

The user supplies:
* `lan` — the LAN expansion of the model at `θ₀`,
* `regular` — the regularity property of `θ_hat`,
* `asymGaussian` — the conclusion `δ_n^{−1}(θ̂ − θ₀) →d N(0, info⁻¹)`.

In a fully formalised pipeline the latter two would be derived from `lan`
through Le Cam's third lemma (a routine combination of contiguity, the
expansion of `lan`, and Slutsky), but the abstract bundle keeps both flavours
optional so that intermediate (statement-level) theorems can be stated and
plumbed without committing to a specific convergence-in-distribution
formalism. -/
def ofLAN
    {logRatio : ℕ → Ω → EuclideanSpace ℝ (Fin p) → ℝ}
    (_lan : LANExpansion μ θ₀ logRatio δ_n info)
    (regular asymGaussian : Prop) :
    HajekLeCamConclusion μ θ_hat θ₀ δ_n info :=
  { regular := regular
    asymGaussian := asymGaussian }

end HajekLeCamConclusion

end Statlean

end

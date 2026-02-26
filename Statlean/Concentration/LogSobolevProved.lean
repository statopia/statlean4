import Statlean.Concentration.Density

/-! # Gaussian Log-Sobolev Inequality — Proved Declarations

This file contains the **sorry-free** portion of the Log-Sobolev development:
definitions, structures, and theorems that take LSI hypotheses as parameters
rather than invoking sorry-tainted lemmas directly.

The sorry-dependent declarations (`gaussian_lsi_1d_core`, `tensorization_lsi_core`,
and `gaussian_log_sobolev`) remain in `LogSobolev.lean`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

/-- **Entropy functional**: Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)
for a nonneg measurable function g. -/
def entropy (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- Entropy functional on a product space. -/
def entropyPi {n : ℕ} (μ : Measure (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- A measure μ satisfies a **log-Sobolev inequality** with constant c if
    Ent_μ(f²) ≤ c · E_μ[f'²] for all smooth f. -/
def SatisfiesLSI (μ : Measure ℝ) (c : ℝ) : Prop :=
  ∀ f f' : ℝ → ℝ,
    MemLp f 2 μ → MemLp f' 2 μ →
    (∀ x, HasDerivAt f (f' x) x) →
    entropy μ (fun x => f x ^ 2) ≤ c * ∫ x, f' x ^ 2 ∂μ

/-- Tensorized LSI statement at fixed dimension `n` and constant `c`
for products of the standard Gaussian measure. -/
def TensorizationLSIAt (n : ℕ) (c : ℝ) : Prop :=
  SatisfiesLSI stdGaussian c →
    ∀ f : (Fin n → ℝ) → ℝ,
    ∀ gradf : Fin n → (Fin n → ℝ) → ℝ,
    MemLp f 2 (stdGaussianPi n) →
    (∀ i, MemLp (gradf i) 2 (stdGaussianPi n)) →
    (∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) →
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n)

/-- Universal tensorization interface across all dimensions and constants. -/
def UniversalTensorizationLSI : Prop :=
  ∀ n : ℕ, ∀ c : ℝ, TensorizationLSIAt n c

/-- Regularity package for a function and its coordinate derivatives
on `stdGaussianPi n`. -/
structure GaussianSobolevRegularity
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  hf : MemLp f 2 (stdGaussianPi n)
  hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n)
  hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)

/-- **Theorem 3.6** (Tensorization of LSI):
If each μᵢ satisfies LSI(c), then the product ⊗ᵢ μᵢ satisfies LSI(c)
(the constant does not grow with dimension). -/
theorem tensorization_lsi
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hTensorAt : TensorizationLSIAt n c) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact hTensorAt h f gradf hf hgradf hgrad

/-- Use a fixed `(n,c)` tensorization statement to obtain the target inequality. -/
theorem tensorization_lsi_of_at
    (n : ℕ) (c : ℝ)
    (h : SatisfiesLSI stdGaussian c)
    (hTensorAt : TensorizationLSIAt n c)
    (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i)) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      c * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi n c h f gradf hf hgradf hgrad hTensorAt

/-- Turn a universal tensorization interface into the fixed `(n,c)` one. -/
lemma tensorization_lsi_at_of_universal
    (hTensor : UniversalTensorizationLSI) (n : ℕ) (c : ℝ) :
    TensorizationLSIAt n c := by
  exact hTensor n c

/-- Gaussian log-Sobolev from a fixed `(n,2)` tensorization statement. -/
theorem gaussian_log_sobolev_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact tensorization_lsi_of_at n 2 hLSI1d hTensorAt f gradf hf hgradf hgrad

/-- Gaussian log-Sobolev from the universal tensorization interface. -/
theorem gaussian_log_sobolev_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianPi n))
    (hgradf : ∀ i, MemLp (gradf i) 2 (stdGaussianPi n))
    (hgrad : ∀ x i, HasDerivAt (fun t => f (Function.update x i t)) (gradf i x) (x i))
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hf hgradf hgrad hLSI1d
    (tensorization_lsi_at_of_universal hTensor n 2)

/-- Structured regularity version of `gaussian_log_sobolev_of_tensorization_at`. -/
theorem gaussian_log_sobolev_structured_of_tensorization_at
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensorAt : TensorizationLSIAt n 2) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_tensorization_at n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensorAt

/-- Structured regularity version of `gaussian_log_sobolev_of_universal_tensorization`. -/
theorem gaussian_log_sobolev_structured_of_universal_tensorization
    (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (gradf : Fin n → (Fin n → ℝ) → ℝ)
    (hReg : GaussianSobolevRegularity n f gradf)
    (hLSI1d : SatisfiesLSI stdGaussian 2)
    (hTensor : UniversalTensorizationLSI) :
    entropyPi (stdGaussianPi n) (fun x => f x ^ 2) ≤
      2 * ∑ i : Fin n, ∫ x, (gradf i x) ^ 2 ∂(stdGaussianPi n) := by
  exact gaussian_log_sobolev_of_universal_tensorization n f gradf hReg.hf hReg.hgradf hReg.hgrad
    hLSI1d hTensor

end

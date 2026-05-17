import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Linarith

/-!
# Tapered Covariance Estimator (Furrer–Bengtsson 2007 / Bickel–Levina 2008)

The **tapered estimator** is a smooth version of the banded estimator
(see `Statlean/HDStats/BandedCovariance.lean`).  Instead of zeroing
entries outside the band, it multiplies each entry by a **taper
function** that decays smoothly from `w(0) = 1`:
```
  T_w^{(k)}(Σ̂)_{ij} := w(|i - j| / k) · Σ̂_{ij}.
```

Common choices for `w`:
* Rectangular `w(t) = 𝟙{|t| ≤ 1}` recovers banding.
* Linear `w(t) = max(0, 1 - |t|)` (Bickel–Levina).
* Cosine `w(t) = (1 + cos(π t)) / 2` for `|t| ≤ 1`.

Smooth tapers preserve more spectral structure than hard banding and
yield improved operator-norm rates.

## Main definitions

* `linearTaper t` — `max(0, 1 - |t|)`, a generic Lipschitz taper.
* `taperedMatrix w k M` — entry-wise tapering with bandwidth `k`.

## Main results

* `linearTaper_zero` — `w(0) = 1`.
* `linearTaper_nonneg` — `w(t) ≥ 0`.
* `linearTaper_far` — `w(t) = 0` for `|t| ≥ 1`.
* `linearTaper_close` — `w(t) = 1 - |t|` for `|t| ≤ 1`.
* `taperedMatrix_preserves_diagonal` — diagonal entries are unchanged
  when `w(0) = 1`.
* `tapered_covariance_consistency` — Furrer–Bengtsson / Bickel–Levina
  (axiom / R6).

## References

* R. Furrer, T. Bengtsson, *Estimation of high-dimensional prior and
  posterior covariance matrices in Kalman filter variants*,
  J. Multivariate Anal. 98 (2007).
* P. Bickel, E. Levina, *Regularized estimation of large covariance
  matrices*, Ann. Statist. 36 (2008).
* T. Cai, H. H. Zhou, *Optimal rates of convergence for sparse
  covariance matrix estimation*, Ann. Statist. 40 (2012).
-/

namespace Statlean.HDStats

variable {p : ℕ}

/-- The **linear taper function** `w(t) := max(0, 1 - |t|)`.
This is the simplest Lipschitz taper, vanishing for `|t| ≥ 1` and
equal to `1 - |t|` for `|t| ≤ 1`. -/
noncomputable def linearTaper (t : ℝ) : ℝ := max 0 (1 - |t|)

@[simp] lemma linearTaper_zero : linearTaper 0 = 1 := by
  unfold linearTaper
  simp

lemma linearTaper_nonneg (t : ℝ) : 0 ≤ linearTaper t := le_max_left _ _

/-- For `|t| ≥ 1`, the linear taper vanishes. -/
lemma linearTaper_far {t : ℝ} (h : 1 ≤ |t|) : linearTaper t = 0 := by
  unfold linearTaper
  have hle : 1 - |t| ≤ 0 := by linarith
  exact max_eq_left hle

/-- For `|t| ≤ 1`, the linear taper equals `1 - |t|`. -/
lemma linearTaper_close {t : ℝ} (h : |t| ≤ 1) : linearTaper t = 1 - |t| := by
  unfold linearTaper
  have hge : 0 ≤ 1 - |t| := by linarith
  exact max_eq_right hge

/-- The linear taper is bounded above by `1`. -/
lemma linearTaper_le_one (t : ℝ) : linearTaper t ≤ 1 := by
  unfold linearTaper
  have habs : 0 ≤ |t| := abs_nonneg t
  exact max_le (by norm_num) (by linarith)

/-- **Tapered matrix** with a user-supplied taper `w` and bandwidth
parameter `k > 0`.  The `(i, j)` entry is scaled by
`w(|i - j| / k)`. -/
noncomputable def taperedMatrix (w : ℝ → ℝ) (k : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ := fun i j =>
  w (|((i : ℝ) - j)| / k) * M i j

/-- The tapered matrix preserves diagonal entries, provided
`w(0) = 1`. -/
lemma taperedMatrix_preserves_diagonal
    {w : ℝ → ℝ} (hw : w 0 = 1) (k : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (i : Fin p) :
    taperedMatrix w k M i i = M i i := by
  unfold taperedMatrix
  have h0 : |((i : ℝ) - i)| / k = 0 := by
    rw [sub_self, abs_zero, zero_div]
  rw [h0, hw, one_mul]

/-- Tapering the zero matrix yields the zero matrix. -/
lemma taperedMatrix_zero (w : ℝ → ℝ) (k : ℝ) :
    taperedMatrix (p := p) w k 0 = 0 := by
  ext i j
  unfold taperedMatrix
  simp

/-- Tapering with the constant `w ≡ 1` is the identity (assuming
`k > 0` is irrelevant here — `w` ignores its argument). -/
lemma taperedMatrix_one (k : ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    taperedMatrix (fun _ => (1 : ℝ)) k M = M := by
  ext i j
  unfold taperedMatrix
  ring

/-- **Tapered covariance consistency (axiom / R6)** —
Furrer–Bengtsson / Bickel–Levina.  Under bandable-Σ structural
assumptions and a properly chosen taper bandwidth, the tapered sample
covariance is operator-norm consistent.  Placeholder statement; the
quantitative rate is the subject of a forthcoming module. -/
axiom tapered_covariance_consistency
    {p : ℕ} (w : ℝ → ℝ) (M_emp M_true : Matrix (Fin p) (Fin p) ℝ) (k : ℝ) :
    True

end Statlean.HDStats

import Mathlib

/-! # Variational Inference and the ELBO

Variational inference (Jordan-Ghahramani-Jaakkola-Saul 1999, Blei-
Kucukelbir-McAuliffe 2017): approximate the intractable posterior
`p(z|x)` by a tractable variational distribution `q(z)`, found by
minimizing `KL(q || p(·|x))`.

The optimization is equivalent to maximizing the **Evidence Lower
BOund** (ELBO):
  log p(x) = ELBO(q) + KL(q || p(·|x))
Since `log p(x)` does not depend on `q`, maximizing the ELBO is exactly
the same problem as minimizing the KL divergence to the true posterior.

## Contents

* `klDivergence` — KL(q || p), a placeholder built on `rnDeriv`.
* `elbo` — `E_q[log p(x,z)] - E_q[log q(z)]`.
* Algebraic identities for `elbo`: additivity in the joint log-density,
  zero/self values, scalar multiplication, gap identity.

## References

* Jordan, Ghahramani, Jaakkola, Saul (1999), *An introduction to
  variational methods for graphical models*, Machine Learning 37,
  183–233.
* Blei, Kucukelbir, McAuliffe (2017), *Variational inference: a review
  for statisticians*, JASA 112, 859–877.
-/

open MeasureTheory Real
open scoped ENNReal

namespace Statlean.VariationalInference

variable {Z : Type*} [MeasurableSpace Z]

/-- The **KL divergence** between two probability measures. Placeholder
definition: when `q` is absolutely continuous w.r.t. `p`, KL(q || p) =
`∫ log(dq/dp) dq`; otherwise `+∞`.

This is built on Mathlib's `Measure.rnDeriv`. The current Mathlib release
does not yet expose a top-level `ProbabilityTheory.klDiv`, so we use this
abstract wrapper for VI proofs. -/
noncomputable def klDivergence (q p : Measure Z) : ℝ≥0∞ := by
  classical
  exact if q ≪ p then
    ∫⁻ z, (q.rnDeriv p z) * ENNReal.ofReal (Real.log (q.rnDeriv p z).toReal) ∂q
  else ⊤

/-- The **ELBO (Evidence Lower BOund)** for a variational distribution
`q` against the joint log-density `logJoint = log p(x, z)`:
  `ELBO(q) = E_q[log p(x, z)] - E_q[log q(z)]`.

For a fixed observed `x`, this is a function of `q` (and the variational
log-density `logQDensity`) alone. Maximizing the ELBO is equivalent to
minimizing `KL(q || p(·|x))`.

References: Jordan-Ghahramani-Jaakkola-Saul (1999); Blei-Kucukelbir-
McAuliffe (2017). -/
noncomputable def elbo (q : Measure Z) (logJoint logQDensity : Z → ℝ) : ℝ :=
  ∫ z, logJoint z ∂q - ∫ z, logQDensity z ∂q

/-- ELBO is additive in `logJoint`: replacing `log p(x,z)` by
`logJoint1 + logJoint2` adds the integral of the second piece. -/
theorem elbo_add_logJoint (q : Measure Z)
    (logJoint1 logJoint2 logQDensity : Z → ℝ)
    (h1 : Integrable logJoint1 q) (h2 : Integrable logJoint2 q) :
    elbo q (logJoint1 + logJoint2) logQDensity
      = elbo q logJoint1 logQDensity + ∫ z, logJoint2 z ∂q := by
  unfold elbo
  rw [Pi.add_def]
  rw [integral_add h1 h2]
  ring

/-- ELBO at zero log-densities is zero. -/
theorem elbo_zero (q : Measure Z) :
    elbo q (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) = 0 := by
  unfold elbo
  simp

/-- Trivial reflexivity: under identical log-densities, ELBO = 0. This
is the analogue of `KL(q || q) = 0` on the ELBO side: the
`E_q[log p]` and `E_q[log q]` terms cancel. -/
theorem elbo_self (q : Measure Z) (logDensity : Z → ℝ) :
    elbo q logDensity logDensity = 0 := by
  unfold elbo
  ring

/-- ELBO is linear w.r.t. scalar multiplication of `logJoint`. -/
theorem elbo_const_smul_logJoint (q : Measure Z) (c : ℝ)
    (logJoint logQDensity : Z → ℝ) :
    elbo q (fun z => c * logJoint z) logQDensity
      = c * (∫ z, logJoint z ∂q) - ∫ z, logQDensity z ∂q := by
  unfold elbo
  rw [integral_const_mul]

/-- The **gap identity**: for two variational candidates `q₁, q₂` with
the same `logJoint`, the ELBO difference equals the difference of
entropies (negative `logQDensity` integrals). -/
theorem elbo_sub_elbo (q : Measure Z) (logJoint logQ1 logQ2 : Z → ℝ) :
    elbo q logJoint logQ1 - elbo q logJoint logQ2
      = ∫ z, logQ2 z ∂q - ∫ z, logQ1 z ∂q := by
  unfold elbo
  ring

end Statlean.VariationalInference

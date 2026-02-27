import Statlean.SPD.FrechetMean

/-! # SPD Determinant Identities

Log-determinant identities for SPD Fréchet means and their finite-sample analogues.

## Main results
- `logdet_frechet_mean` — log-det at Fréchet mean = mean of log-det
- `det_empirical_mean` — det of empirical mean = exp of mean log-det
- `det_averaging_equality` — determinant equality across three SPD averaging schemes
-/

namespace Statlean.SPD

/-- Abstract log-determinant identity at a Fréchet mean. -/
theorem logdet_frechet_mean
    {Q : Type*}
    (IsFrechetMean : Q → Prop)
    (meanOp : (Q → Real) → Real)
    (frechetMean : Q)
    (logDet : Q → Real)
    (traceLogDiag : Q → Real)
    (h_isFrechetMean : IsFrechetMean frechetMean)
    (h_logdet_eq_trace : ∀ q : Q, logDet q = traceLogDiag q)
    (h_trace_mean :
      IsFrechetMean frechetMean → logDet frechetMean = meanOp traceLogDiag) :
    logDet frechetMean = meanOp logDet := by
  have hfun : traceLogDiag = logDet := by
    funext q
    exact (h_logdet_eq_trace q).symm
  calc
    logDet frechetMean = meanOp traceLogDiag := h_trace_mean h_isFrechetMean
    _ = meanOp logDet := by
          simp [hfun]

/-- Determinant form of a finite-sample Log-Cholesky mean identity. -/
theorem det_empirical_mean
    {LPlus : Type*}
    {n : Nat}
    (samples : Fin n → LPlus)
    (empiricalMean : (Fin n → LPlus) → LPlus)
    (det : LPlus → Real)
    (logDet : LPlus → Real)
    (arithMean : (Fin n → Real) → Real)
    (h_logdet_mean :
      logDet (empiricalMean samples) =
        arithMean (fun i => logDet (samples i)))
    (h_logdet_eq_log_det : ∀ x : LPlus, logDet x = Real.log (det x))
    (h_det_pos : 0 < det (empiricalMean samples)) :
    det (empiricalMean samples) =
      Real.exp (arithMean (fun i => logDet (samples i))) := by
  have h_log_det_mean :
      Real.log (det (empiricalMean samples)) =
        arithMean (fun i => logDet (samples i)) := by
    calc
      Real.log (det (empiricalMean samples))
          = logDet (empiricalMean samples) := by
              symm
              exact h_logdet_eq_log_det (empiricalMean samples)
      _ = arithMean (fun i => logDet (samples i)) := h_logdet_mean
  calc
    det (empiricalMean samples)
        = Real.exp (Real.log (det (empiricalMean samples))) := by
            symm
            exact Real.exp_log h_det_pos
    _ = Real.exp (arithMean (fun i => logDet (samples i))) := by
          rw [h_log_det_mean]

/-- Determinant equality bridge between three SPD averaging schemes. -/
theorem det_averaging_equality
    {M : Type*}
    (det : M → Real)
    (logCholeskyAverage : M)
    (logEuclideanAverage : M)
    (affineInvariantAverage : M)
    (h_det_lc_eq_le :
      det logCholeskyAverage = det logEuclideanAverage)
    (h_det_lc_eq_ai :
      det logCholeskyAverage = det affineInvariantAverage) :
    det logEuclideanAverage = det affineInvariantAverage := by
  calc
    det logEuclideanAverage = det logCholeskyAverage := by
      symm
      exact h_det_lc_eq_le
    _ = det affineInvariantAverage := h_det_lc_eq_ai

end Statlean.SPD

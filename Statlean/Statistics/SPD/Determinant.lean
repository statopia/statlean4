import Statlean.Statistics.SPD.FrechetMean

/-! # SPD Statistical Layer — Determinant Identities

Determinant/log-determinant identities associated with SPD Fréchet means and
their finite-sample analogues.
-/

namespace Statlean.Statistics.SPD

/-- Abstract log-determinant identity at a Fréchet mean. -/
theorem proposition_010_proposition_11
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
theorem corollary_012_corollary_13
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
theorem corollary_013_corollary_13
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

end Statlean.Statistics.SPD

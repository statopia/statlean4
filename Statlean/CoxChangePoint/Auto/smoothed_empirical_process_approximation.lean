import Mathlib

/-!
# smoothed_empirical_process_approximation

Source: paper Lemma_S6 (Appendix A)

Under Assumptions (A8)–(A9): (S1) sup_{t,θ} |S_n^{(0)*}(t;θ) − S_n^{(0)}(t;θ)| = O_P(n^{-1/2}d_n^{3/2} + d_n^{-b} + d_n^{1−2b} log n); (S2) sup_{t,θ} ‖S_n^{(1)*}(t;θ) − S_n^{(1)}(t;θ)‖_∞ = O_P(n^{-1/2}d_n^{3/2} + d_n^{-b} + d_n^{1−2b} log n); (S3) sup_{t,θ} ‖S_n^{(2)*}(t;θ) − S_n^{(2)}(t;θ)‖_∞ = O_P(n^{-1/2}d_n^{3/2} + d_n^{-b} + d_n^{1−2b} log n).
-/

namespace Statlean.CoxChangePoint.Auto

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Parameter and function spaces -/

/-- The parameter space Θ for the Cox change-point model. -/
private structure CoxParam where
  α : ℕ → ℝ
  β : ℕ → ℝ
  η : ℝ

/-- Assumptions (A8)–(A9) for the smoothed empirical process approximation.
    A8: kernel smoothness — the covariance kernel eigenfunctions satisfy Hölder-type regularity.
    A9: bandwidth/truncation coupling — d_n grows with n at a controlled rate. -/
private structure AssumptionsA8A9 where
  /-- Smoothness exponent b > 1/2 controlling eigenvalue decay rate -/
  b : ℝ
  hb_pos : b > 1 / 2
  /-- Truncation dimension sequence d : ℕ → ℕ -/
  d : ℕ → ℕ
  hd_pos : ∀ n, 0 < d n
  hd_mono : Monotone d
  hd_tends : Filter.Tendsto d Filter.atTop Filter.atTop
  /-- Bandwidth coupling: n^{-1} d_n^3 → 0 (ensures d_n grows slower than n^{1/3}) -/
  bandwidth_coupling : Filter.Tendsto (fun n => (d n : ℝ) ^ 3 / (n : ℝ)) Filter.atTop (nhds 0)
  /-- Eigenvalue decay rate: λ_k ~ k^{-2b} -/
  eigenvalue_decay : ℕ → ℝ
  eigenvalue_decay_bound : ∀ k, 0 < k → eigenvalue_decay k ≤ (k : ℝ) ^ (-(2 * b))
  /-- Compact parameter space Θ -/
  Θ : Set CoxParam
  hΘ_nonempty : Θ.Nonempty
  /-- Time domain [0, τ] -/
  τ : ℝ
  hτ_pos : 0 < τ

/-- The approximation rate r_n = n^{-1/2} d_n^{3/2} + d_n^{-b} + d_n^{1-2b} log n. -/
private noncomputable def approxRate (A : AssumptionsA8A9) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 2) * (A.d n : ℝ) ^ ((3 : ℝ) / 2)
  + (A.d n : ℝ) ^ (-A.b)
  + (A.d n : ℝ) ^ (1 - 2 * A.b) * Real.log (n : ℝ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Lemma S6 (S1)**: The zeroth-order smoothed empirical process approximation.
    sup_{t,θ} |S_n^{(0)*}(t;θ) − S_n^{(0)}(t;θ)| = O_P(r_n). -/
theorem smoothed_empirical_process_approximation_S1
    (A : AssumptionsA8A9)
    (Sn0 : ℕ → ℝ → CoxParam → Ω → ℝ)
    (Sn0_star : ℕ → ℝ → CoxParam → Ω → ℝ)
    (hSn0 : ∀ n t θ, Measurable (Sn0 n t θ))
    (hSn0_star : ∀ n t θ, Measurable (Sn0_star n t θ)) :
    ∃ (C : ℝ) (hC : 0 < C), ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | ∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
        |Sn0_star n t θ ω - Sn0 n t θ ω| ≤ C * approxRate A n} ≥
      ENNReal.ofReal (1 - ε) := by sorry

/-- **Lemma S6 (S2)**: The first-order smoothed empirical process approximation.
    sup_{t,θ} ‖S_n^{(1)*}(t;θ) − S_n^{(1)}(t;θ)‖_∞ = O_P(r_n). -/
theorem smoothed_empirical_process_approximation_S2
    (A : AssumptionsA8A9)
    (Sn1 : ℕ → ℝ → CoxParam → Ω → ℕ → ℝ)
    (Sn1_star : ℕ → ℝ → CoxParam → Ω → ℕ → ℝ)
    (hSn1 : ∀ n t θ k, Measurable (fun ω => Sn1 n t θ ω k))
    (hSn1_star : ∀ n t θ k, Measurable (fun ω => Sn1_star n t θ ω k)) :
    ∃ (C : ℝ) (hC : 0 < C), ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | ∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
        ∀ j, j < A.d n →
          |Sn1_star n t θ ω j - Sn1 n t θ ω j| ≤ C * approxRate A n} ≥
      ENNReal.ofReal (1 - ε) := by sorry

/-- **Lemma S6 (S3)**: The second-order smoothed empirical process approximation.
    sup_{t,θ} ‖S_n^{(2)*}(t;θ) − S_n^{(2)}(t;θ)‖_∞ = O_P(r_n). -/
theorem smoothed_empirical_process_approximation_S3
    (A : AssumptionsA8A9)
    (Sn2 : ℕ → ℝ → CoxParam → Ω → ℕ → ℕ → ℝ)
    (Sn2_star : ℕ → ℝ → CoxParam → Ω → ℕ → ℕ → ℝ)
    (hSn2 : ∀ n t θ j k, Measurable (fun ω => Sn2 n t θ ω j k))
    (hSn2_star : ∀ n t θ j k, Measurable (fun ω => Sn2_star n t θ ω j k)) :
    ∃ (C : ℝ) (hC : 0 < C), ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | ∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
        ∀ j, j < A.d n → ∀ k, k < A.d n →
          |Sn2_star n t θ ω j k - Sn2 n t θ ω j k| ≤ C * approxRate A n} ≥
      ENNReal.ofReal (1 - ε) := by sorry

/-- **Lemma S6** (combined): All three parts (S1)–(S3) hold simultaneously. -/
theorem smoothed_empirical_process_approximation
    (A : AssumptionsA8A9)
    (Sn0 : ℕ → ℝ → CoxParam → Ω → ℝ)
    (Sn0_star : ℕ → ℝ → CoxParam → Ω → ℝ)
    (Sn1 : ℕ → ℝ → CoxParam → Ω → ℕ → ℝ)
    (Sn1_star : ℕ → ℝ → CoxParam → Ω → ℕ → ℝ)
    (Sn2 : ℕ → ℝ → CoxParam → Ω → ℕ → ℕ → ℝ)
    (Sn2_star : ℕ → ℝ → CoxParam → Ω → ℕ → ℕ → ℝ)
    (hSn0 : ∀ n t θ, Measurable (Sn0 n t θ))
    (hSn0_star : ∀ n t θ, Measurable (Sn0_star n t θ))
    (hSn1 : ∀ n t θ k, Measurable (fun ω => Sn1 n t θ ω k))
    (hSn1_star : ∀ n t θ k, Measurable (fun ω => Sn1_star n t θ ω k))
    (hSn2 : ∀ n t θ j k, Measurable (fun ω => Sn2 n t θ ω j k))
    (hSn2_star : ∀ n t θ j k, Measurable (fun ω => Sn2_star n t θ ω j k)) :
    ∃ (C : ℝ) (hC : 0 < C), ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      P {ω |
        (∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
          |Sn0_star n t θ ω - Sn0 n t θ ω| ≤ C * approxRate A n) ∧
        (∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
          ∀ j, j < A.d n →
            |Sn1_star n t θ ω j - Sn1 n t θ ω j| ≤ C * approxRate A n) ∧
        (∀ t ∈ Set.Icc 0 A.τ, ∀ θ ∈ A.Θ,
          ∀ j, j < A.d n → ∀ k, k < A.d n →
            |Sn2_star n t θ ω j k - Sn2 n t θ ω j k| ≤ C * approxRate A n)} ≥
      ENNReal.ofReal (1 - ε) := by sorry

end Statlean.CoxChangePoint.Auto
import Statlean.EmpiricalProcess.Dudley
open MeasureTheory Real Set Finset BigOperators intervalIntegral
noncomputable section

private lemma iv_int {f : ℝ → ℝ} {D : ℝ} (hf : IntegrableOn f (Icc 0 D))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ D) (hab : a ≤ b) :
    IntervalIntegrable f volume a b :=
  (hf.mono_set (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable

theorem dyadic_riemann_le_iv (K : ℕ) (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ)
    (hf_anti : AntitoneOn f (Icc 0 D)) (hf_int : IntegrableOn f (Icc 0 D)) :
    ∑ k ∈ range K, f (D / 2 ^ k) * (D / 2 ^ (k + 1)) ≤ ∫ x in (D / 2 ^ K)..D, f x := by
  induction K with
  | zero => simp [integral_same]
  | succ K ih =>
    rw [sum_range_succ]
    have h2K : (0:ℝ) < 2 ^ K := by positivity
    have hK : D / 2 ^ (K+1) ≤ D / 2 ^ K :=
      div_le_div_of_nonneg_left hD.le h2K (by norm_cast; exact Nat.pow_le_pow_right (by omega) (by omega))
    have hKD : D / 2 ^ K ≤ D := by
      rw [div_le_iff₀ h2K]
      nlinarith [show (1:ℝ) ≤ 2^K from by norm_cast; exact Nat.one_le_pow K 2 (by omega)]
    have hK0 : (0:ℝ) ≤ D / 2 ^ (K+1) := by positivity
    have hstep : f (D / 2 ^ K) * (D / 2 ^ (K+1)) ≤ ∫ x in (D / 2^(K+1))..(D / 2^K), f x := by
      rw [integral_of_le hK, ← integral_Icc_eq_integral_Ioc]
      have h := antitone_interval_bound hK (hf_anti.mono (Icc_subset_Icc hK0 hKD))
        (hf_int.mono_set (Icc_subset_Icc hK0 hKD))
      have hw : D / 2^K - D / 2^(K+1) = D / 2^(K+1) := by rw [pow_succ]; field_simp; try norm_num
      rw [hw] at h; exact h
    linarith [integral_add_adjacent_intervals (iv_int hf_int hK0 hKD hK)
      (iv_int hf_int (by linarith [div_pos hD h2K]) le_rfl hKD)]

theorem dyadic_sum_le_2x_iv (K : ℕ) (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ)
    (hf_anti : AntitoneOn f (Icc 0 D))
    (hf_nn : ∀ x ∈ Icc 0 D, 0 ≤ f x) (hf_int : IntegrableOn f (Icc 0 D)) :
    ∑ k ∈ range K, f (D / 2 ^ k) * (D / 2 ^ k) ≤ 2 * ∫ x in (0:ℝ)..D, f x := by
  simp_rw [show ∀ k, f (D / 2^k) * (D / 2^k) = 2 * (f (D / 2^k) * (D / 2^(k+1)))
    from fun k => by rw [pow_succ]; field_simp]
  rw [← mul_sum]; gcongr
  have hDK : D / 2 ^ K ≤ D := by
    rw [div_le_iff₀ (show (0:ℝ) < 2^K by positivity)]
    nlinarith [show (1:ℝ) ≤ 2^K from by norm_cast; exact Nat.one_le_pow K 2 (by omega)]
  calc ∑ k ∈ range K, f (D / 2^k) * (D / 2^(k+1))
      ≤ ∫ x in (D / 2^K)..D, f x := dyadic_riemann_le_iv K D hD f hf_anti hf_int
    _ ≤ ∫ x in (0:ℝ)..D, f x := by
        rw [integral_of_le hDK, integral_of_le (by linarith : (0:ℝ) ≤ D)]
        exact setIntegral_mono_set (hf_int.mono_set Set.Ioc_subset_Icc_self)
          (Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioc)
            fun x hx => hf_nn x (Set.Ioc_subset_Icc_self hx))
          (Filter.Eventually.of_forall
            fun x (hx : x ∈ Set.Ioc (D / 2^K) D) => Set.Ioc_subset_Ioc (by positivity) le_rfl hx)
end

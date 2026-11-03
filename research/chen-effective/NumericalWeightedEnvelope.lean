import NumericalWeightedMass

namespace ChenEffective
open Finset Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.Richert1969
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem numerical_true_li_bound {N : ℕ} (hN : 9 ≤ N) :
    |BombieriVinogradov.trueLogarithmicIntegral N| ≤ 10 * (N : ℝ) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hκ : (2 : ℝ) / Real.log 2 ≤ 4 := by
    apply (div_le_iff₀ (by linarith only [hlog2])).mpr
    linarith only [hlog2]
  have hc : LiuWeight.liuLogarithmicIntegralUpperConstant (2 / Real.log 2) ≤ 10 := by
    unfold LiuWeight.liuLogarithmicIntegralUpperConstant
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.log 2)]
    linarith only [hκ]
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega))
    linarith only [hh, one_le_log_three]
  have hh := LiuWeight.liuLogarithmicIntegral_abs_le (2 / Real.log 2)
    (show (2 : ℝ) ≤ N by exact_mod_cast (show 2 ≤ N by omega))
  exact hh.trans (by
    apply (div_le_iff₀ (by linarith only [hlog])).mpr
    have h1 := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)
    have h2 := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 10 * N by positivity)
    nlinarith only [h1, h2])

theorem numerical_totient_standard_error {N q : ℕ} (hN : 9 ≤ N)
    (hq : 0 < q) (hqN : q ≤ N) :
    (q.totient : ℝ) * BombieriVinogradov.standardPrimeAPMaxError N q ≤ 12 * (N : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have hpoint (l : ℕ) :
      (q.totient : ℝ) * |BombieriVinogradov.standardPrimeAPError N q l| ≤ 12 * (N : ℝ) := by
    have hc := primesInAP_le_div_add_one N q l hq
    have hcount : (q.totient : ℝ) * (BombieriVinogradov.primesInAP N q l : ℝ) ≤ 2 * N := by
      have hcR : (BombieriVinogradov.primesInAP N q l : ℝ) ≤ (N / q : ℕ) + 1 := by exact_mod_cast hc
      have hdiv : ((N / q : ℕ) : ℝ) * q ≤ N := by exact_mod_cast Nat.div_mul_le_self N q
      have ha := mul_le_mul_of_nonneg_left hcR hφ.le
      have hb := mul_le_mul_of_nonneg_right hφq (show (0 : ℝ) ≤ (N / q : ℕ) + 1 by positivity)
      nlinarith only [ha, hb, hdiv, hqNR]
    unfold BombieriVinogradov.standardPrimeAPError
    have ha := norm_sub_le (BombieriVinogradov.primesInAP N q l : ℝ)
      (BombieriVinogradov.trueLogarithmicIntegral N / q.totient)
    simp only [Real.norm_eq_abs] at ha
    have hcabs : |(BombieriVinogradov.primesInAP N q l : ℝ)| =
        (BombieriVinogradov.primesInAP N q l : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [hcabs, abs_div, abs_of_pos hφ] at ha
    have hb := mul_le_mul_of_nonneg_left ha hφ.le
    have he : (q.totient : ℝ) * (|BombieriVinogradov.trueLogarithmicIntegral N| / q.totient) =
        |BombieriVinogradov.trueLogarithmicIntegral N| := by field_simp
    nlinarith only [hb, he, hcount, numerical_true_li_bound hN]
  unfold BombieriVinogradov.standardPrimeAPMaxError
  dsimp only
  split_ifs with h
  · rw [mul_comm]
    apply (le_div_iff₀ hφ).mp
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, _hl, rfl⟩
    exact (le_div_iff₀ hφ).mpr (by simpa only [mul_comm] using hpoint l)
  · simp only [mul_zero]
    positivity

#print axioms numerical_totient_standard_error
end ChenEffective

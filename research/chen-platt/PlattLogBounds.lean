import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace ChenEffective.PlattWindow
open Real
set_option maxHeartbeats 1200000

theorem log_ten_lower : (23/10:ℝ) ≤ log 10 := by
  have h := sum_range_le_log_div (by norm_num : (0:ℝ) ≤ 9/11)
    (by norm_num : (9/11:ℝ) < 1) 16
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem log_three_lower : (12/11:ℝ) ≤ log 3 := by
  have h := sum_range_le_log_div (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem log_three_upper : log (3:ℝ) ≤ 7/5 := by
  have h : log (3:ℝ) ≤ log (4:ℝ) := log_le_log (by norm_num) (by norm_num)
  rw [show (4:ℝ)=2^2 by norm_num,log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h,log_two_lt_d9]

theorem log_power_ten_lower (n : ℕ) : (n:ℝ)*(23/10) ≤ log ((10:ℝ)^n) := by
  rw [log_pow]
  exact mul_le_mul_of_nonneg_left log_ten_lower (Nat.cast_nonneg n)

theorem log_power_three_lower : (24:ℝ) ≤ log ((3:ℝ)^22) := by
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [log_three_lower]

theorem log_far_upper : log ((3:ℝ)^512) ≤ 720 := by
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [log_three_upper]

theorem log_ratio_paid : log ((720:ℝ)/39) ≤ 3 := by
  apply (log_le_iff_le_exp (by norm_num : (0:ℝ) < 720/39)).mpr
  have h : (27/10:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) h 3
  rw [← exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith only [hp]

#print axioms log_ten_lower
end ChenEffective.PlattWindow

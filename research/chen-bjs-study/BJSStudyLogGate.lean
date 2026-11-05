import NumericalRealLogBounds

/-! Direct replacement for the oversized generic logarithmic cutoff. -/
namespace ChenEffective
open Real
set_option maxHeartbeats 1500000

theorem bjsStudy_log_six_sqrt {x : ℝ} (hx : (10:ℝ)^80 ≤ x) :
    log x^6 ≤ sqrt x := by
  have hx1 : 1 ≤ x := (by norm_num : (1:ℝ) ≤ 10^80).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hx1
  have hl := log_le_rpow_div hx0.le (by norm_num : (0:ℝ) < 1/16)
  have hp := pow_le_pow_left₀ (log_nonneg hx1) hl 6
  have hroot : (16:ℝ)^6 ≤ x^(1/8:ℝ) := by
    calc
      _ ≤ (10:ℝ)^10 := by norm_num
      _ = ((10:ℝ)^80)^(1/8:ℝ) := by
        rw [← rpow_natCast (10:ℝ) 80,← rpow_mul (by norm_num : (0:ℝ) ≤ 10)]
        norm_num
      _ ≤ _ := rpow_le_rpow (by positivity) hx (by norm_num)
  have he : (x^(1/16:ℝ))^6=x^(3/8:ℝ) := by
    rw [← rpow_natCast,← rpow_mul hx0.le]
    norm_num
  calc
    _ ≤ (16*x^(1/16:ℝ))^6 := by
      have heq : x^(1/16:ℝ)/(1/16)=16*x^(1/16:ℝ) := by ring
      rw [heq] at hp
      exact hp
    _ = 16^6*x^(3/8:ℝ) := by rw [mul_pow,he]
    _ ≤ x^(1/8:ℝ)*x^(3/8:ℝ) := mul_le_mul_of_nonneg_right hroot (rpow_nonneg hx0.le _)
    _ = sqrt x := by rw [← rpow_add hx0]; norm_num [sqrt_eq_rpow]

#print axioms bjsStudy_log_six_sqrt
end ChenEffective

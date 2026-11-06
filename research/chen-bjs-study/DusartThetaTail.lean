import OptimizedMertensPower

/-! A proved far-tail version of Dusart's log-squared theta estimate.
This uses the existing Dirichlet-conditional PNT, not Dusart's numerical
tables. It does not establish the missing range below `exp 3400`. -/
noncomputable section
namespace ChenEffective
open Real
set_option maxHeartbeats 2000000

theorem dusart_theta_tail_scalar {L : ℝ} (hL : 3400 ≤ L) :
    110000000000 * L ^ 3 * exp (-L / 68) ≤ 4 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ht := add_one_le_exp ((L - 3400) / 204)
  have hlin : L ≤ 3400 * exp ((L - 3400) / 204) := by
    nlinarith only [hL, ht]
  have hc := pow_le_pow_left₀ hL0 hlin 3
  have hex : (exp ((L - 3400) / 204)) ^ 3 = exp ((L - 3400) / 68) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, hex] at hc
  have hnum : (110000000000 : ℝ) * 3400 ^ 3 ≤ 4 * exp 50 := by
    have he : (27 / 10 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 50
    rw [← exp_nat_mul] at hh
    norm_num at hh ⊢
    linarith only [hh]
  have hpay := mul_le_mul_of_nonneg_right hnum (exp_pos (-50 : ℝ)).le
  have hcancel : exp (50 : ℝ) * exp (-50) = 1 := by
    rw [← exp_add]
    norm_num
  have hprod : exp ((L - 3400) / 68) * exp (-L / 68) = exp (-50 : ℝ) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    110000000000 * L ^ 3 * exp (-L / 68) ≤
        110000000000 * (3400 ^ 3 * exp ((L - 3400) / 68)) * exp (-L / 68) := by
      gcongr
    _ = 110000000000 * 3400 ^ 3 * exp (-50 : ℝ) := by
      calc
        _ = 110000000000 * 3400 ^ 3 *
            (exp ((L - 3400) / 68) * exp (-L / 68)) := by ring
        _ = _ := by rw [hprod]
    _ ≤ 4 := by nlinarith only [hpay, hcancel]

theorem dusart_theta_log_squared_tail {x : ℝ}
    (hx : 0 < x) (hlog : 3400 ≤ log x) :
    |Chebyshev.theta x - x| ≤ 4 * x / (log x) ^ 2 := by
  have hx9 : 9 ≤ x := by linarith only [hlog, log_le_sub_one_of_pos hx]
  have hL0 : 0 < log x := by linarith only [hlog]
  have hp := optimized_theta_power_error hx9
  have hs := dusart_theta_tail_scalar hlog
  have hr : x ^ (67 / 68 : ℝ) = x * exp (-log x / 68) := by
    calc
      _ = exp (log x + (-log x / 68)) := by
        rw [rpow_def_of_pos hx]
        congr 1
        ring
      _ = _ := by rw [exp_add, exp_log hx]
  apply hp.trans
  apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
  rw [hr]
  have hh := mul_le_mul_of_nonneg_left hs hx.le
  nlinarith only [hh]

#print axioms dusart_theta_tail_scalar
#print axioms dusart_theta_log_squared_tail
end ChenEffective

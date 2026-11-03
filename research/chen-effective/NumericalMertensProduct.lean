import NumericalMertens
import AnalyticNumberTheory.Mertens.FinitePart

namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def mertensProductThreshold (r : ℕ) : ℕ :=
  max (principalNumericalThreshold 1) (3 ^ (1800000000004 * r))

theorem numerical_mertens_product_log {n : ℕ}
    (hn : principalNumericalThreshold 1 ≤ n) :
    |Real.log (primeProduct n) + Real.log (Real.log (n : ℝ)) +
      Real.eulerMascheroniConstant| ≤ 900000000002 / Real.log (n : ℝ) := by
  have hn9 : 9 ≤ n := (logPowerCutoff_nine_le _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hm := numerical_mertens_second (show (principalNumericalThreshold 1 : ℝ) ≤ n by exact_mod_cast hn)
  rw [Nat.floor_natCast] at hm
  have hc := logarithmicCorrection_tail_norm_le_div n (show 1 ≤ n by omega)
  rw [Real.norm_eq_abs] at hc
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hci : 2 / (n : ℝ) ≤ 2 / Real.log (n : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hl hlog
  have hb := hc.trans hci
  rw [← mertensConstant_eq_eulerMascheroni, log_primeProduct_error_eq]
  have hh := abs_add_le (-(primeReciprocalSum n -
    (Real.log (Real.log (n : ℝ)) + mertensSecondConstant)))
    (logarithmicCorrectionLimit - logarithmicCorrection n)
  rw [abs_neg] at hh
  apply hh.trans
  simp only [div_eq_mul_inv] at hm hb ⊢
  linarith only [hm, hb]

/-- Relative Mertens product error with an explicit threshold for every budget. -/
theorem numerical_mertens_product {n r : ℕ} (hr : 0 < r)
    (hn : mertensProductThreshold r ≤ n) :
    |primeProduct n * Real.log (n : ℝ) * Real.exp Real.eulerMascheroniConstant - 1| ≤
      1 / (r : ℝ) := by
  have hnP := (le_max_left _ _).trans hn
  have hn9 : 9 ≤ n := (logPowerCutoff_nine_le _).trans hnP
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlarge := log_ge_power_three (b := 1800000000004 * r) ((le_max_right _ _).trans hn)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlarge
  let E := Real.log (primeProduct n) + Real.log (Real.log (n : ℝ)) + Real.eulerMascheroniConstant
  have he : |E| ≤ 900000000002 / Real.log (n : ℝ) := numerical_mertens_product_log hnP
  have hpay : 2 * (900000000002 / Real.log (n : ℝ)) ≤ 1 / (r : ℝ) := by
    apply (le_div_iff₀ (show (0 : ℝ) < r by linarith only [hrR])).mpr
    rw [show 2 * (900000000002 / Real.log (n : ℝ)) * (r : ℝ) =
      (1800000000004 * r) / Real.log (n : ℝ) by ring]
    exact (div_le_one hl).mpr hlarge
  have he1 : |E| ≤ 1 := by
    have hh : 1 / (r : ℝ) ≤ 1 := div_le_self (by norm_num) hrR
    linarith only [he, hpay, hh]
  have hb := (Real.abs_exp_sub_one_le he1).trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have hid : Real.exp E = primeProduct n * Real.log (n : ℝ) * Real.exp Real.eulerMascheroniConstant := by
    dsimp [E]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (primeProduct_pos n), Real.exp_log hl]
  rw [hid] at hb
  exact hb.trans hpay

#print axioms numerical_mertens_product
end ChenEffective

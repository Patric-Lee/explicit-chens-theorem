import OptimizedPrincipalPNT
import NumericalMertens

/-! Keep the power saving from the principal PNT through Abel summation.
No logarithmic-power cutoff or asymptotic witness is used. -/

namespace ChenEffective
open Real Set MeasureTheory
open AnalyticNumberTheory.LargeSieve AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem optimized_theta_power_error {x : ℝ} (hx : 9 ≤ x) :
    |Chebyshev.theta x - x| ≤ 110000000000 * x ^ (67 / 68 : ℝ) * log x := by
  let n := ⌊x⌋₊
  have hn : 9 ≤ n := Nat.le_floor hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hl : 1 ≤ log x := one_le_log_three.trans
    (log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ x))
  have hp := optimized_principal_pointwise_through hn n le_rfl
  have hpsi : |Chebyshev.psi x - x| ≤
      100000000000 * x ^ (67 / 68 : ℝ) * log x + 1 := by
    have hp' : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤
        100000000000 * x ^ (67 / 68 : ℝ) * log x := by
      apply hp.trans
      gcongr
    have hr : |(n : ℝ) - x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hh := abs_add_le (Chebyshev.psi (n : ℝ) - (n : ℝ)) ((n : ℝ) - x)
    rw [sub_add_sub_cancel] at hh
    rw [Chebyshev.psi_eq_psi_coe_floor x]
    exact hh.trans (add_le_add hp' hr)
  have hs : sqrt x ≤ x ^ (67 / 68 : ℝ) := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hP : 1 ≤ x ^ (67 / 68 : ℝ) := one_le_rpow hx1 (by norm_num)
  have hdelta := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hd : |Chebyshev.psi x - Chebyshev.theta x| ≤
      2 * x ^ (67 / 68 : ℝ) * log x := by
    apply hdelta.trans
    gcongr
  have hh := abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
  rw [sub_add_sub_cancel, abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at hh
  have hprod : 1 ≤ x ^ (67 / 68 : ℝ) * log x := by nlinarith only [hP, hl, mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hl)]
  nlinarith only [hh, hd, hpsi, hprod]

theorem optimized_theta_power_kernel {t : ℝ} (ht : 9 ≤ t) :
    ‖thetaErrorKernel t‖ ≤ 220000000000 * t ^ (-69 / 68 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ log t := one_le_log_three.trans
    (log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ t))
  have hl0 : 0 < log t := by linarith
  have he := optimized_theta_power_error ht
  have hf : (log t + 1) / (t * log t) ^ 2 ≤ 2 / (t ^ 2 * log t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (log t))]
  have hnorm : ‖thetaErrorKernel t‖ = |Chebyshev.theta t - t| *
      ((log t + 1) / (t * log t) ^ 2) := by
    unfold thetaErrorKernel
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by linarith : 0 ≤ log t + 1),
      abs_of_nonneg (sq_nonneg (t * log t))]
    ring
  rw [hnorm]
  calc
    _ ≤ (110000000000 * t ^ (67 / 68 : ℝ) * log t) *
        (2 / (t ^ 2 * log t)) := mul_le_mul he hf (by positivity) (by positivity)
    _ = 220000000000 * (t ^ (67 / 68 : ℝ) / t ^ (2 : ℝ)) := by
      rw [rpow_two]; field_simp; ring
    _ = _ := by rw [← rpow_sub ht0]; norm_num

theorem optimized_mertens_power {x : ℝ} (hx : 9 ≤ x) :
    |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
      30000000000000 * x ^ (-1 / 68 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hk := integrableOn_Ioi_rpow_of_lt (by norm_num : (-69 / 68 : ℝ) < -1) hx0
  have htail : ‖∫ t in Ioi x, thetaErrorKernel t‖ ≤
      14960000000000 * x ^ (-1 / 68 : ℝ) := by
    calc
      _ ≤ ∫ t in Ioi x, 220000000000 * t ^ (-69 / 68 : ℝ) := by
        apply norm_integral_le_of_norm_le (hk.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact optimized_theta_power_kernel (hx.trans ht.le)
      _ = _ := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx0]
        norm_num
        ring
  have hend : |(Chebyshev.theta x - x) / (x * log x)| ≤
      110000000000 * x ^ (-1 / 68 : ℝ) := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl)]
    calc
      _ ≤ (110000000000 * x ^ (67 / 68 : ℝ) * log x) / (x * log x) :=
        div_le_div_of_nonneg_right (optimized_theta_power_error hx) (by positivity)
      _ = 110000000000 * (x ^ (67 / 68 : ℝ) / x ^ (1 : ℝ)) := by
        rw [rpow_one]; field_simp
      _ = _ := by rw [← rpow_sub hx0]; norm_num
  rw [mertensSecond_error_decomposition (by linarith)]
  have hh := abs_sub ((Chebyshev.theta x - x) / (x * log x))
    (∫ t in Ioi x, thetaErrorKernel t)
  rw [Real.norm_eq_abs] at htail
  have hnonneg := rpow_nonneg hx0.le (-1 / 68 : ℝ)
  nlinarith only [hh, hend, htail, hnonneg]

#print axioms optimized_mertens_power
end ChenEffective

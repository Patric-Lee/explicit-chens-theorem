import NumericalPrincipalPNT
import AnalyticNumberTheory.Mertens.PartialSummation

namespace ChenEffective
open Real Set MeasureTheory
open AnalyticNumberTheory.LargeSieve AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A real-variable theta estimate with a numerical starting point. -/
theorem numerical_theta_error {x : ℝ}
    (hx : (principalNumericalThreshold 1 : ℝ) ≤ x) :
    |Chebyshev.theta x - x| ≤ 300000000000 * x / Real.log x := by
  let n := ⌊x⌋₊
  have hn : principalNumericalThreshold 1 ≤ n := Nat.le_floor hx
  have hn9 : 9 ≤ n := (logPowerCutoff_nine_le _).trans hn
  have hnR : (9 : ℝ) ≤ n := by exact_mod_cast hn9
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith only [hx,
    show (0 : ℝ) ≤ (principalNumericalThreshold 1 : ℕ) from Nat.cast_nonneg _])
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hx1 : 1 < x := by linarith only [hnR, hnx]
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith only [hnR])
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlcomp : Real.log x ≤ 2 * Real.log (n : ℝ) := by
    have hh := Real.log_le_log (by linarith only [hx1] : 0 < x)
      (show x ≤ (n : ℝ) ^ 2 by nlinarith only [hxn, hnR])
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hpsi : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤
      100000000000 * n / Real.log (n : ℝ) := by
    have hb := numerical_principal_prefix hn
    rw [principalLambdaPrefixMaxError_one_eq_psi_prefixMax] at hb
    simp only [pow_one] at hb
    apply le_trans ?_ hb
    exact Finset.le_max' ((Finset.range (n + 1)).image
      (fun y : ℕ => |Chebyshev.psi (y : ℝ) - (y : ℝ)|)) _ (Finset.mem_image.mpr ⟨n,
      Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩)
  have hpow : Real.log (n : ℝ) ^ 2 ≤ Real.sqrt n :=
    log_pow_le_sqrt_explicit_of_le (by norm_num : 2 ≤ 256) hn
  have hsqrt : Real.sqrt x ≤ 2 * Real.sqrt n := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hn0.le]
    nlinarith only [hxn, hnR]
  have hdelta := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1.le
  have hdelta' : |Chebyshev.psi x - Chebyshev.theta x| ≤
      8 * (n : ℝ) / Real.log (n : ℝ) := by
    apply hdelta.trans
    apply (le_div_iff₀ hln).mpr
    have hh : 2 * Real.sqrt x * Real.log x * Real.log (n : ℝ) ≤
        8 * Real.sqrt n * Real.log (n : ℝ) ^ 2 := by
      nlinarith only [mul_le_mul hsqrt hlcomp hlx.le (by positivity), hln]
    apply hh.trans
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 8 * Real.sqrt n by positivity)
    nlinarith only [hp, Real.sq_sqrt hn0.le]
  have hone : (1 : ℝ) ≤ n / Real.log (n : ℝ) := by
    apply (le_div_iff₀ hln).mpr
    have hh := Real.log_le_sub_one_of_pos hn0
    linarith only [hh]
  have hround : |(n : ℝ) - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [hnx, hxn]
  have hpReal : |Chebyshev.psi x - x| ≤
      100000000001 * n / Real.log (n : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor x]
    have hh := abs_add_le (Chebyshev.psi (n : ℝ) - (n : ℝ)) ((n : ℝ) - x)
    rw [sub_add_sub_cancel] at hh
    apply hh.trans
    simp only [mul_div_assoc] at hpsi ⊢
    linarith only [hpsi, hround, hone]
  have ht : |Chebyshev.theta x - x| ≤
      100000000009 * n / Real.log (n : ℝ) := by
    have hh := abs_add_le (Chebyshev.theta x - Chebyshev.psi x) (Chebyshev.psi x - x)
    rw [sub_add_sub_cancel, abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at hh
    apply hh.trans
    simp only [mul_div_assoc] at hdelta' hpReal ⊢
    linarith only [hdelta', hpReal]
  apply ht.trans
  apply (div_le_div_iff₀ hln hlx).mpr
  have hh := mul_le_mul_of_nonneg_left hlcomp (show 0 ≤ (100000000009 : ℝ) * n by positivity)
  have hh2 := mul_le_mul_of_nonneg_right hnx hln.le
  nlinarith only [hh, hh2, mul_nonneg hn0.le hln.le]

theorem numerical_mertens_log_one {x : ℝ}
    (hx : (principalNumericalThreshold 1 : ℝ) ≤ x) : 1 ≤ Real.log x := by
  have h9 : (9 : ℝ) ≤ x :=
    (show (9 : ℝ) ≤ (principalNumericalThreshold 1 : ℕ) by
      exact_mod_cast logPowerCutoff_nine_le 256).trans hx
  exact one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith only [h9]))

theorem numerical_theta_kernel {t : ℝ}
    (ht : (principalNumericalThreshold 1 : ℝ) ≤ t) :
    ‖thetaErrorKernel t‖ ≤ 600000000000 * (t⁻¹ / Real.log t ^ 2) := by
  have hl1 := numerical_mertens_log_one ht
  have hl0 : 0 < Real.log t := by linarith only [hl1]
  have ht0 : 0 < t := by
    have hh : (9 : ℝ) ≤ (principalNumericalThreshold 1 : ℕ) := by
      exact_mod_cast logPowerCutoff_nine_le 256
    linarith only [hh, ht]
  have he := numerical_theta_error ht
  have hf : (Real.log t + 1) / (t * Real.log t) ^ 2 ≤
      2 / (t ^ 2 * Real.log t) := by
    field_simp
    nlinarith only [hl1]
  rw [show ‖thetaErrorKernel t‖ = |Chebyshev.theta t - t| *
      ((Real.log t + 1) / (t * Real.log t) ^ 2) by
    unfold thetaErrorKernel
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (by linarith only [hl1] : 0 ≤ Real.log t + 1),
      abs_of_nonneg (sq_nonneg (t * Real.log t))]
    ring]
  calc
    _ ≤ (300000000000 * t / Real.log t) *
        ((Real.log t + 1) / (t * Real.log t) ^ 2) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ (300000000000 * t / Real.log t) * (2 / (t ^ 2 * Real.log t)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by field_simp; ring

/-- The Mertens constant is canonical; the error constant and cutoff are numerical. -/
theorem numerical_mertens_second {x : ℝ}
    (hx : (principalNumericalThreshold 1 : ℝ) ≤ x) :
    |primeReciprocalSum ⌊x⌋₊ - (Real.log (Real.log x) + mertensSecondConstant)| ≤
      900000000000 / Real.log x := by
  have hl1 := numerical_mertens_log_one hx
  have h9 : (9 : ℝ) ≤ x :=
    (show (9 : ℝ) ≤ (principalNumericalThreshold 1 : ℕ) by
      exact_mod_cast logPowerCutoff_nine_le 256).trans hx
  have hx0 : 0 < x := by linarith only [h9]
  have hl0 : 0 < Real.log x := by linarith only [hl1]
  have htail := norm_integral_Ioi_le_div_log (show 1 < x by linarith only [h9])
    (fun t ht => numerical_theta_kernel (hx.trans ht.le))
  have hend : |(Chebyshev.theta x - x) / (x * Real.log x)| ≤
      300000000000 / Real.log x := by
    rw [abs_div, abs_of_pos (mul_pos hx0 hl0)]
    apply (div_le_iff₀ (mul_pos hx0 hl0)).mpr
    have he := numerical_theta_error hx
    have hb : 300000000000 * x / Real.log x ≤ 300000000000 * x := by
      apply div_le_self (by positivity) hl1
    have hid : 300000000000 / Real.log x * (x * Real.log x) =
        300000000000 * x := by field_simp
    rw [hid]
    exact he.trans hb
  rw [mertensSecond_error_decomposition (by linarith only [h9])]
  have hh := abs_sub ((Chebyshev.theta x - x) / (x * Real.log x))
    (∫ t in Ioi x, thetaErrorKernel t)
  apply hh.trans
  rw [Real.norm_eq_abs] at htail
  simp only [div_eq_mul_inv] at hend htail ⊢
  linarith only [hend, htail]

/-- The unknown value of the canonical constant cancels from prime intervals. -/
theorem numerical_mertens_interval {w z : ℝ}
    (hw : (principalNumericalThreshold 1 : ℝ) ≤ w) (hwz : w ≤ z) :
    |(primeReciprocalSum ⌊z⌋₊ - primeReciprocalSum ⌊w⌋₊) -
      (Real.log (Real.log z) - Real.log (Real.log w))| ≤
        1800000000000 / Real.log w := by
  have hlw : 0 < Real.log w := lt_of_lt_of_le zero_lt_one (numerical_mertens_log_one hw)
  have hw9 : (9 : ℝ) ≤ w :=
    (show (9 : ℝ) ≤ (principalNumericalThreshold 1 : ℕ) by
      exact_mod_cast logPowerCutoff_nine_le 256).trans hw
  have hlog := Real.log_le_log (show 0 < w by linarith only [hw9]) hwz
  have hz := numerical_mertens_second (hw.trans hwz)
  have hew := numerical_mertens_second hw
  have hpay : 900000000000 / Real.log z ≤ 900000000000 / Real.log w :=
    div_le_div_of_nonneg_left (by norm_num) hlw hlog
  have hh := abs_sub (primeReciprocalSum ⌊z⌋₊ -
      (Real.log (Real.log z) + mertensSecondConstant))
    (primeReciprocalSum ⌊w⌋₊ - (Real.log (Real.log w) + mertensSecondConstant))
  have hid : (primeReciprocalSum ⌊z⌋₊ - (Real.log (Real.log z) + mertensSecondConstant)) -
      (primeReciprocalSum ⌊w⌋₊ - (Real.log (Real.log w) + mertensSecondConstant)) =
      (primeReciprocalSum ⌊z⌋₊ - primeReciprocalSum ⌊w⌋₊) -
        (Real.log (Real.log z) - Real.log (Real.log w)) := by ring
  rw [hid] at hh
  apply hh.trans
  have hh' := hz.trans hpay
  simp only [div_eq_mul_inv] at hh' hew ⊢
  linarith only [hh', hew]

theorem principalNumericalThreshold_one : principalNumericalThreshold 1 = 3 ^ 1056784 := by
  unfold principalNumericalThreshold logPowerCutoff
  congr 1

#print axioms numerical_theta_error
#print axioms numerical_mertens_second
#print axioms numerical_mertens_interval
end ChenEffective

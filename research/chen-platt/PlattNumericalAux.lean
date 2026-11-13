import PlattPrefixBridge
import PlattPlateauNorm
import PlattLogBounds

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 1024

def analyticTop : ℝ := (3:ℝ)^512

theorem analyticTop_log : 1 ≤ log analyticTop := by
  unfold analyticTop
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [log_three_lower]

theorem analyticTop_power : analyticTop^(-1/16:ℝ)=1/(3:ℝ)^32 := by
  unfold analyticTop
  rw [← rpow_natCast (3:ℝ) 512,← rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [rpow_neg]

theorem log_decimal (n : ℕ) : (n:ℝ)*(23/10) ≤ log ((10:ℝ)^n) :=
  log_power_ten_lower n

theorem neg_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) : x^(-1/2:ℝ)=1/sqrt x := by
  rw [show (-1/2:ℝ)=-(1/2) by ring,rpow_neg hx,← sqrt_eq_rpow]
  simp only [one_div]

theorem invsqrt_bound {x s : ℝ} (hs : 0 < s) (hsq : s^2 ≤ x) :
    x^(-1/2:ℝ) ≤ 1/s := by
  rw [neg_half_eq_inv_sqrt x ((sq_nonneg s).trans hsq)]
  exact one_div_le_one_div_of_le hs (le_sqrt_of_sq_le hsq)

theorem reference_power : ((10:ℝ)^10)^(-1/2:ℝ)=1/100000 := by
  rw [neg_half_eq_inv_sqrt _ (by positivity)]
  norm_num

theorem split_power : ((3:ℝ)^22)^(-1/2:ℝ)=1/(3:ℝ)^11 := by
  rw [← rpow_natCast (3:ℝ) 22,← rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [rpow_neg]

theorem norm_kernel_interval {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => ‖thetaErrorKernel t‖) volume a b := by
  constructor
  · exact (integrableOn_thetaErrorKernel.mono_set
      (fun t ht => lt_of_le_of_lt ha ht.1)).norm
  · simp [Ioc_eq_empty_of_le hab]

theorem analyticTop_endpoint
    (hθ : |Chebyshev.theta analyticTop-analyticTop| ≤ (3/4)*analyticTop^(15/16:ℝ)) :
    |thetaEndpoint analyticTop| ≤ (1/10^8:ℝ) := by
  have hx0 : 0 < analyticTop := by unfold analyticTop; positivity
  have hl := analyticTop_log
  have hl0 : 0 < log analyticTop := by linarith only [hl]
  have hend : |thetaEndpoint analyticTop| ≤
      (3/4)/log analyticTop*analyticTop^(-1/16:ℝ) := by
    unfold thetaEndpoint
    rw [abs_div,abs_of_pos (mul_pos hx0 hl0)]
    calc
      _ ≤ ((3/4)*analyticTop^(15/16:ℝ))/(analyticTop*log analyticTop) :=
        div_le_div_of_nonneg_right hθ (by positivity)
      _ = (3/4)/log analyticTop*(analyticTop^(15/16:ℝ)/analyticTop^(1:ℝ)) := by
        rw [rpow_one]; field_simp
      _ = _ := by rw [← rpow_sub hx0]; norm_num
  rw [analyticTop_power] at hend
  have hh : (3/4:ℝ)/log analyticTop ≤ 3/4 := by
    apply (div_le_iff₀ hl0).mpr
    nlinarith only [hl]
  calc
    _ ≤ ((3/4)/log analyticTop)*(1/(3:ℝ)^32) := hend
    _ ≤ (3/4:ℝ)*(1/(3:ℝ)^32) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ ≤ _ := by norm_num

theorem thetaEndpoint_sqrt {x C L s : ℝ} (hx : 0 < x)
    (hC : 0 ≤ C) (hL : 0 < L) (hs : 0 < s)
    (hlog : L ≤ log x) (hsq : s^2 ≤ x)
    (hθ : |Chebyshev.theta x-x| ≤ C*sqrt x) :
    |thetaEndpoint x| ≤ C/(s*L) := by
  have hl : 0 < log x := hL.trans_le hlog
  have hr : 0 < sqrt x := sqrt_pos.mpr hx
  unfold thetaEndpoint
  rw [abs_div,abs_of_pos (mul_pos hx hl)]
  calc
    _ ≤ (C*sqrt x)/(x*log x) := div_le_div_of_nonneg_right hθ (by positivity)
    _ = C/(sqrt x*log x) := by
      field_simp [hx.ne',hl.ne',hr.ne']
      linear_combination C*(sq_sqrt hx.le)
    _ ≤ _ := div_le_div_of_nonneg_left hC (mul_pos hs hL)
      (mul_le_mul (le_sqrt_of_sq_le hsq) hlog hL.le hr.le)

theorem plateau_log_difference :
    log (log analyticTop)-log (log ((10:ℝ)^17)) ≤ 3 := by
  have h17 : (39:ℝ) ≤ log ((10:ℝ)^17) := by
    have h := log_decimal 17
    norm_num at h ⊢ <;> linarith only [h]
  have hfar := log_far_upper
  have hl17 : 0 < log ((10:ℝ)^17) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 39) h17
  have hlf : 0 < log analyticTop := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) analyticTop_log
  rw [← log_div hlf.ne' hl17.ne']
  apply (log_le_log (div_pos hlf hl17) ?_).trans log_ratio_paid
  apply (div_le_div_iff₀ hl17 (by norm_num : (0:ℝ) < 39)).mpr
  change log analyticTop ≤ 720 at hfar
  nlinarith only [h17,hfar]

#print axioms analyticTop_endpoint
#print axioms thetaEndpoint_sqrt
end ChenEffective.PlattWindow

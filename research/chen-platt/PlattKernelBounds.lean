import PlattPrefixBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1200000

theorem log_kernel_ratio_le {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlt : L ≤ log t) :
    (log t+1)/(log t)^2 ≤ (L+1)/L^2 := by
  have hlog : 0 < log t := hL.trans_le hlt
  have h1 := one_div_le_one_div_of_le hL hlt
  have h2 := one_div_le_one_div_of_le (sq_pos_of_pos hL)
    (show L^2 ≤ (log t)^2 by nlinarith only [hL,hlt])
  have e1 : (log t+1)/(log t)^2=1/log t+1/(log t)^2 := by field_simp
  have e2 : (L+1)/L^2=1/L+1/L^2 := by field_simp
  rw [e1,e2]
  exact add_le_add h1 h2

theorem theta_kernel_sqrt {C L t : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (ht : 0 < t) (hlt : L ≤ log t)
    (hθ : |Chebyshev.theta t-t| ≤ C*sqrt t) :
    ‖thetaErrorKernel t‖ ≤ C*((L+1)/L^2)*t^(-3/2:ℝ) := by
  have hlog : 0 < log t := hL.trans_le hlt
  have hr := log_kernel_ratio_le hL ht hlt
  have heq : sqrt t/t^2=t^(-3/2:ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_two, ← rpow_sub ht]
    norm_num
  have hn : ‖thetaErrorKernel t‖ =
      |Chebyshev.theta t-t| * ((log t+1)/(t*log t)^2) := by
    unfold thetaErrorKernel
    rw [Real.norm_eq_abs,abs_div,abs_mul,
      abs_of_nonneg (by linarith only [hlog] : 0 ≤ log t+1),
      abs_of_nonneg (sq_nonneg (t*log t))]
    ring
  rw [hn]
  calc
    _ ≤ (C*sqrt t)*((log t+1)/(t*log t)^2) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    _ = C*((log t+1)/(log t)^2)*(sqrt t/t^2) := by field_simp
    _ ≤ C*((L+1)/L^2)*t^(-3/2:ℝ) := by rw [heq]; gcongr

theorem integral_sqrt_kernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, t^(-3/2:ℝ)) =
      2*(a^(-1/2:ℝ)-b^(-1/2:ℝ)) := by
  have hb : 0 < b := ha.trans_le hab
  rw [← intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) ha) hab,
    integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) ha,
    integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hb]
  norm_num
  ring

theorem theta_integral_sqrt {a b C L : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC : 0 ≤ C) (hL : 0 < L) (hlog : L ≤ log a)
    (hθ : ∀ t ∈ Ioc a b, |Chebyshev.theta t-t| ≤ C*sqrt t) :
    ‖∫ t in a..b, thetaErrorKernel t‖ ≤
      2*C*((L+1)/L^2)*(a^(-1/2:ℝ)-b^(-1/2:ℝ)) := by
  have hint := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-3/2:ℝ) < -1) ha).mono_set
    (show Ioc a b ⊆ Ioi a from fun t ht => ht.1)
  calc
    _ ≤ ∫ t in a..b, C*((L+1)/L^2)*t^(-3/2:ℝ) := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      apply norm_integral_le_of_norm_le (hint.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact theta_kernel_sqrt hC hL (ha.trans ht.1)
        (hlog.trans (log_le_log ha ht.1.le)) (hθ t ht)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_sqrt_kernel ha hab]
      ring

theorem theta_integral_norm_sqrt {a b C L : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC : 0 ≤ C) (hL : 0 < L) (hlog : L ≤ log a)
    (hθ : ∀ t ∈ Ioc a b, |Chebyshev.theta t-t| ≤ C*sqrt t) :
    (∫ t in a..b, ‖thetaErrorKernel t‖) ≤
      2*C*((L+1)/L^2)*(a^(-1/2:ℝ)-b^(-1/2:ℝ)) := by
  have hint := (integrableOn_Ioi_rpow_of_lt
    (by norm_num : (-3/2:ℝ) < -1) ha).mono_set
    (show Ioc a b ⊆ Ioi a from fun t ht => ht.1)
  calc
    _ ≤ ‖∫ t in a..b, ‖thetaErrorKernel t‖‖ := Real.le_norm_self _
    _ ≤ ∫ t in a..b, C*((L+1)/L^2)*t^(-3/2:ℝ) := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      apply norm_integral_le_of_norm_le (hint.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [norm_norm] using theta_kernel_sqrt hC hL (ha.trans ht.1)
        (hlog.trans (log_le_log ha ht.1.le)) (hθ t ht)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,integral_sqrt_kernel ha hab]
      ring

#print axioms theta_integral_sqrt
#print axioms theta_integral_norm_sqrt
end ChenEffective.PlattWindow

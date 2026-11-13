import PlattPlateauKernels

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1800000

theorem theta_kernel_plateau {δ A B L t : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 < L)
    (ht : 0 < t) (hlt : L ≤ log t)
    (hθ : |Chebyshev.theta t-t| ≤ δ*t+A*sqrt t+B) :
    ‖thetaErrorKernel t‖ ≤ δ*linearKernel t+
      A*((L+1)/L^2)*t^(-3/2:ℝ)+B*constantKernel t := by
  have hlog : 0 < log t := hL.trans_le hlt
  have hr := log_kernel_ratio_le hL ht hlt
  have heq : sqrt t/t^2=t^(-3/2:ℝ) := by
    rw [sqrt_eq_rpow,← rpow_two,← rpow_sub ht]
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
    _ ≤ (δ*t+A*sqrt t+B)*((log t+1)/(t*log t)^2) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    _ = δ*linearKernel t+A*((log t+1)/(log t)^2)*t^(-3/2:ℝ)+B*constantKernel t := by
      rw [← heq]
      unfold linearKernel constantKernel
      field_simp [ht.ne',hlog.ne']
      <;> ring
    _ ≤ _ := by gcongr

theorem theta_integral_norm_plateau {a b δ A B L : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 < L) (hlog : L ≤ log a)
    (hθ : ∀ t ∈ Ioc a b, |Chebyshev.theta t-t| ≤ δ*t+A*sqrt t+B) :
    (∫ t in a..b, ‖thetaErrorKernel t‖) ≤
      δ*(log (log b)-log (log a)+1/log a-1/log b)+
      2*A*((L+1)/L^2)*(a^(-1/2:ℝ)-b^(-1/2:ℝ))+
      B*(1/(a*log a)-1/(b*log b)) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hpow : IntervalIntegrable (fun t : ℝ => t^(-3/2:ℝ)) volume a b := by
    constructor
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) ha0).mono_set
        (fun t ht => ht.1)
    · simp [Ioc_eq_empty_of_le hab]
  have hlin := (linearKernel_integrable ha hab).const_mul δ
  have hroot := hpow.const_mul (A*((L+1)/L^2))
  have hconst := (constantKernel_integrable ha hab).const_mul B
  calc
    _ ≤ ‖∫ t in a..b, ‖thetaErrorKernel t‖‖ := Real.le_norm_self _
    _ ≤ ∫ t in a..b, (δ*linearKernel t+A*((L+1)/L^2)*t^(-3/2:ℝ))+B*constantKernel t := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      apply norm_integral_le_of_norm_le ((hlin.add hroot).add hconst).1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [norm_norm] using theta_kernel_plateau hδ hA hB hL (ha0.trans ht.1)
        (hlog.trans (log_le_log ha0 ht.1.le)) (hθ t ht)
    _ = _ := by
      rw [intervalIntegral.integral_add (hlin.add hroot) hconst,
        intervalIntegral.integral_add hlin hroot,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,integral_linearKernel ha hab,
        integral_sqrt_kernel ha0 hab,integral_constantKernel ha hab]
      ring

#print axioms theta_integral_norm_plateau
end ChenEffective.PlattWindow

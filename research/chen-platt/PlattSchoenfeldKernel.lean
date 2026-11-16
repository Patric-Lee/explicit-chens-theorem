import PlattNumericalAux
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace ChenEffective.PlattWindow.Schoenfeld
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem half_power_identity {x : ℝ} (hx : 0 < x) :
    x^(-1/2:ℝ)=x*x^(-3/2:ℝ) := by
  calc
    _ = x^((1:ℝ)+(-3/2:ℝ)) := by norm_num
    _ = x^(1:ℝ)*x^(-3/2:ℝ) := rpow_add hx _ _
    _ = _ := by rw [rpow_one]

theorem logroot_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => log t*t^(-1/2:ℝ))
      ((1-log x/2)*x^(-3/2:ℝ)) x := by
  have h := (hasDerivAt_log hx.ne').mul
    (hasDerivAt_rpow_const (p:=(-1/2:ℝ)) (Or.inl hx.ne'))
  convert h using 1
  have he := half_power_identity hx
  norm_num only [show (-1/2:ℝ)-1=-3/2 by norm_num] at he ⊢
  rw [he]
  field_simp
  <;> ring

theorem logroot_antitone {a : ℝ} (ha : 0 < a) (hla : 2 ≤ log a) :
    AntitoneOn (fun t : ℝ => log t*t^(-1/2:ℝ)) (Ici a) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
  · intro t ht
    have ht0 : 0 < t := ha.trans_le ht
    exact ((hasDerivAt_log ht0.ne').mul
      (hasDerivAt_rpow_const (p:=(-1/2:ℝ)) (Or.inl ht0.ne'))).continuousAt.continuousWithinAt
  · intro t ht
    exact (logroot_derivative (ha.trans_le (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := ha.trans_le (interior_subset ht)
    have hl : 2 ≤ log t := hla.trans (log_le_log ha (interior_subset ht))
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hl]) (rpow_nonneg ht0.le _)

theorem schoenfeld_primitive_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => -2*((log t+3)*t^(-1/2:ℝ)))
      ((log x+1)*x^(-3/2:ℝ)) x := by
  have h := (((hasDerivAt_log hx.ne').add_const 3).mul
    (hasDerivAt_rpow_const (p:=(-1/2:ℝ)) (Or.inl hx.ne'))).const_mul (-2)
  convert h using 1
  have he := half_power_identity hx
  norm_num only [show (-1/2:ℝ)-1=-3/2 by norm_num] at he ⊢
  rw [he]
  field_simp
  <;> ring

theorem schoenfeld_main_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (log t+1)*t^(-3/2:ℝ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  exact (((continuousAt_log ht0.ne').add continuousAt_const).mul
    (continuousAt_id.rpow_const (Or.inl ht0.ne'))).continuousWithinAt

theorem integral_schoenfeld_main {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b,(log t+1)*t^(-3/2:ℝ)) =
      2*((log a+3)*a^(-1/2:ℝ)-(log b+3)*b^(-1/2:ℝ)) := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt
      (fun t : ℝ => -2*((log t+3)*t^(-1/2:ℝ))) ((log t+1)*t^(-3/2:ℝ)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact schoenfeld_primitive_derivative (ha.trans_le ht.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (schoenfeld_main_integrable ha hab)]
  ring

theorem theta_kernel_schoenfeld {a t C : ℝ} (ha : 1 < a) (hat : a ≤ t) (hC : 0 ≤ C)
    (hθ : |Chebyshev.theta t-t| ≤ C*sqrt t*(log t)^2+log t/2) :
    ‖thetaErrorKernel t‖ ≤ C*((log t+1)*t^(-3/2:ℝ))+
      (1/2)*(1+1/log a)*t^(-2:ℝ) := by
  have ht0 : 0 < t := (by linarith only [ha] : 0 < a).trans_le hat
  have hla : 0 < log a := log_pos ha
  have hlt : 0 < log t := hla.trans_le (log_le_log (by linarith only [ha]) hat)
  have heq : sqrt t/t^2=t^(-3/2:ℝ) := by
    rw [sqrt_eq_rpow,← rpow_two,← rpow_sub ht0]
    norm_num
  have hi := one_div_le_one_div_of_le hla (log_le_log (by linarith only [ha]) hat)
  have hn : ‖thetaErrorKernel t‖ =
      |Chebyshev.theta t-t| * ((log t+1)/(t*log t)^2) := by
    unfold thetaErrorKernel
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (by linarith only [hlt] : 0 ≤ log t+1),
      abs_of_nonneg (sq_nonneg (t*log t))]
    ring
  rw [hn]
  calc
    _ ≤ (C*sqrt t*(log t)^2+log t/2)*((log t+1)/(t*log t)^2) :=
      mul_le_mul_of_nonneg_right hθ (by positivity)
    _ = C*((log t+1)*(sqrt t/t^2))+(1/2)*(1+1/log t)*(1/t^2) := by
      field_simp [ht0.ne',hlt.ne']
      <;> ring
    _ ≤ C*((log t+1)*(sqrt t/t^2))+(1/2)*(1+1/log a)*(1/t^2) := by gcongr
    _ = _ := by rw [heq]; norm_num [rpow_neg ht0.le,rpow_two]

theorem theta_integral_schoenfeld {a b C : ℝ} (ha : 1 < a) (hab : a ≤ b) (hC : 0 ≤ C)
    (hθ : ∀ t ∈ Ioc a b, |Chebyshev.theta t-t| ≤ C*sqrt t*(log t)^2+log t/2) :
    (∫ t in a..b, ‖thetaErrorKernel t‖) ≤
      2*C*((log a+3)*a^(-1/2:ℝ)-(log b+3)*b^(-1/2:ℝ))+
      (1/2)*(1+1/log a)*(1/a-1/b) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hint := (schoenfeld_main_integrable ha0 hab).const_mul C
  have hpow : IntervalIntegrable (fun t : ℝ => t^(-2:ℝ)) volume a b := by
    constructor
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) ha0).mono_set (fun t ht => ht.1)
    · simp [Ioc_eq_empty_of_le hab]
  have hpowint : (∫ t in a..b,t^(-2:ℝ))=1/a-1/b := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) ha0) hab,
      integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) ha0,
      integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) (ha0.trans_le hab)]
    norm_num [rpow_neg_one]
    <;> ring
  have hrest := hpow.const_mul ((1/2)*(1+1/log a))
  calc
    _ ≤ ‖∫ t in a..b, ‖thetaErrorKernel t‖‖ := Real.le_norm_self _
    _ ≤ ∫ t in a..b,C*((log t+1)*t^(-3/2:ℝ))+(1/2)*(1+1/log a)*t^(-2:ℝ) := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      apply norm_integral_le_of_norm_le (hint.add hrest).1
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [norm_norm] using theta_kernel_schoenfeld ha ht.1.le hC (hθ t ht)
    _ = _ := by
      rw [intervalIntegral.integral_add hint hrest,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,integral_schoenfeld_main ha0 hab,hpowint]
      ring

/-- Uniform endpoint control retains the logarithmic factor instead of
replacing it by log of the far endpoint. -/
theorem thetaEndpoint_schoenfeld {a x C : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hla : 2 ≤ log a) (hC : 0 ≤ C)
    (hθ : |Chebyshev.theta x-x| ≤ C*sqrt x*(log x)^2+log x/2) :
    |thetaEndpoint x| ≤ C*log a*a^(-1/2:ℝ)+1/(2*a) := by
  have hx0 : 0 < x := ha.trans_le hax
  have hlx : 0 < log x := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2)
    (hla.trans (log_le_log ha hax))
  have he : sqrt x=x*x^(-1/2:ℝ) := by
    rw [sqrt_eq_rpow]
    calc
      _ = x^((1:ℝ)+(-1/2:ℝ)) := by norm_num
      _ = x^(1:ℝ)*x^(-1/2:ℝ) := rpow_add hx0 _ _
      _ = _ := by rw [rpow_one]
  have hm := logroot_antitone ha hla (mem_Ici.mpr le_rfl) (mem_Ici.mpr hax) hax
  have hd := one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ) < 2) ha)
    (mul_le_mul_of_nonneg_left hax (by norm_num : (0:ℝ) ≤ 2))
  unfold thetaEndpoint
  rw [abs_div,abs_of_pos (mul_pos hx0 hlx)]
  calc
    _ ≤ (C*sqrt x*(log x)^2+log x/2)/(x*log x) := div_le_div_of_nonneg_right hθ (by positivity)
    _ = C*(log x*x^(-1/2:ℝ))+1/(2*x) := by
      rw [he]
      field_simp [hx0.ne',hlx.ne']
      <;> ring
    _ ≤ C*(log a*a^(-1/2:ℝ))+1/(2*a) := add_le_add (mul_le_mul_of_nonneg_left hm hC) hd
    _ = _ := by ring

#print axioms theta_integral_schoenfeld
#print axioms thetaEndpoint_schoenfeld
end ChenEffective.PlattWindow.Schoenfeld

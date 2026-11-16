import PlattSchoenfeldBudget
import PlattAnalyticEnvelope

/-! Assembly for the proposed2e9 reference. The source psi estimate is an
EXPLICIT UNDISCHARGED PREMISE, not an axiom or a theorem from Platt here.
Do not use this conditional module to advertise a completed new cutoff. -/
noncomputable section
namespace ChenEffective.PlattWindow.Schoenfeld
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 1024

def SourcePsiBound : Prop := ∀ x : ℝ, reference ≤ x → x ≤ analyticSplit →
  |Chebyshev.psi x-x| ≤ sqrt x*log x*(log x-3)/(8*Real.pi)+log x/2

def endpointCap : ℝ := (43/2)/(25*44721)+1/(2*2000000000)
def firstIntegralCap : ℝ := 2*(1/25)*((43/2)+3)/44721+(1/2)*(1+1/21)/2000000000
def middleIntegralCap : ℝ := 2*202*(37/36^2)/100000000

theorem theta_of_source (hsource : SourcePsiBound) {x : ℝ}
    (hx : reference ≤ x) (hxs : x ≤ analyticSplit) :
    |Chebyshev.theta x-x| ≤ (1/25:ℝ)*sqrt x*(log x)^2+log x/2 := by
  have h := theta_of_buthe_psi hx (hsource x hx hxs)
  have hc := mul_le_mul_of_nonneg_right schoenfeld_coefficient
    (by positivity : (0:ℝ) ≤ sqrt x*(log x)^2)
  have hc' : sqrt x*(log x)^2/(8*Real.pi) ≤ (1/25:ℝ)*sqrt x*(log x)^2 := by
    convert hc using 1 <;> ring
  exact h.trans (add_le_add hc' le_rfl)

theorem first_integral (hsource : SourcePsiBound) :
    (∫ t in reference..analyticSplit, ‖thetaErrorKernel t‖) ≤ firstIntegralCap := by
  have hpos : 0 < reference := by norm_num [reference]
  have hsplit : reference ≤ analyticSplit := by norm_num [reference,analyticSplit]
  have h := theta_integral_schoenfeld (C:=1/25)
    (by norm_num [reference] : 1 < reference) hsplit (by norm_num)
    (fun t ht => theta_of_source hsource ht.1.le ht.2)
  have hr := reference_invroot
  have hl := reference_log_upper
  have hlo := reference_log
  have hS : 0 ≤ (log analyticSplit+3)*analyticSplit^(-1/2:ℝ) := by
    have hlog : 0 ≤ log analyticSplit := log_nonneg (by norm_num [analyticSplit])
    exact mul_nonneg (by linarith only [hlog]) (rpow_nonneg (by norm_num [analyticSplit]) _)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 21) hlo
  have hInvS : (0:ℝ) ≤ 1/analyticSplit := by unfold analyticSplit; positivity
  have hroot := mul_le_mul (add_le_add_right hl 3) hr
    (rpow_nonneg hpos.le _) (by norm_num)
  have hlin : (1/2:ℝ)*(1+1/log reference)*(1/reference-1/analyticSplit) ≤
      (1/2)*(1+1/21)/reference := by
    have hlogpos : 0 < log reference := lt_of_lt_of_le (by norm_num : (0:ℝ) < 21) hlo
    calc
      _ ≤ (1/2:ℝ)*(1+1/log reference)*(1/reference) :=
        mul_le_mul_of_nonneg_left (sub_le_self _ hInvS) (by positivity)
      _ ≤ (1/2:ℝ)*(1+1/21)*(1/reference) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hi) (by norm_num)) (by positivity)
      _ = _ := by ring
  unfold firstIntegralCap
  simp only [reference] at h hroot hS hlin ⊢
  nlinarith only [h,hroot,hS,hlin]

variable [Fact TernaryGoldbach.PlattZetaRH]

theorem middle_integral :
    (∫ t in analyticSplit..(10:ℝ)^17, ‖thetaErrorKernel t‖) ≤ middleIntegralCap := by
  have hl : (36:ℝ) ≤ log analyticSplit := by
    have h := log_power_ten_lower 16
    change _ ≤ log analyticSplit at h
    linarith only [h]
  have hU : analyticSplit^(-1/2:ℝ) ≤ 1/100000000 := by
    unfold analyticSplit
    rw [neg_half_eq_inv_sqrt _ (by positivity)]
    norm_num
  have hV : (0:ℝ) ≤ ((10:ℝ)^17)^(-1/2:ℝ) := rpow_nonneg (by positivity) _
  have h := sqrt_piece_cap (C:=202) (L:=36)
    (by norm_num [analyticSplit] : (0:ℝ) < analyticSplit)
    (by norm_num [analyticSplit] : analyticSplit ≤ (10:ℝ)^17) (by norm_num) (by norm_num) hl
    (fun t ht => theta_fourth
      ((by norm_num [analyticSplit] : (10:ℝ)^15 ≤ analyticSplit).trans ht.1.le) ht.2) hU hV
  convert h using 1 <;> norm_num [middleIntegralCap] <;> ring

theorem endpoint_uniform (hsource : SourcePsiBound) {x : ℝ} (hx : reference ≤ x) :
    |thetaEndpoint x| ≤ endpointCap := by
  by_cases hxs : x ≤ analyticSplit
  · have h := thetaEndpoint_schoenfeld (C:=1/25) (by norm_num [reference] : 0 < reference)
      hx (by linarith only [reference_log]) (by norm_num) (theta_of_source hsource hx hxs)
    have hm := mul_le_mul (show log reference ≤ 43/2 from reference_log_upper) reference_invroot
      (rpow_nonneg (by norm_num [reference] : 0 ≤ reference) _) (by norm_num : (0:ℝ) ≤ 43/2)
    unfold endpointCap
    simp only [reference] at h hm
    nlinarith only [h,hm]
  · have hlarge : (10:ℝ)^10 ≤ x :=
      (by norm_num [analyticSplit] : (10:ℝ)^10 ≤ analyticSplit).trans (le_of_not_ge hxs)
    exact (thetaEndpoint_uniform hlarge).trans (by norm_num [ChenEffective.PlattWindow.endpointBudget,endpointCap])

theorem full_integral (hsource : SourcePsiBound) :
    (∫ t in reference..analyticTop, ‖thetaErrorKernel t‖) ≤ firstIntegralCap+middleIntegralCap+kernelBudget5 := by
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=reference) (b:=analyticSplit) (by norm_num [reference]) (by norm_num [reference,analyticSplit]))
    (norm_kernel_interval (a:=analyticSplit) (b:=analyticTop) (by norm_num [analyticSplit]) (by norm_num [analyticSplit,analyticTop]))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=analyticSplit) (b:=(10:ℝ)^17) (by norm_num [analyticSplit]) (by norm_num [analyticSplit]))
    (norm_kernel_interval (a:=(10:ℝ)^17) (b:=analyticTop) (by norm_num) (by norm_num [analyticTop]))
  linarith only [e1,e2,first_integral hsource,middle_integral,kernel_piece5]

theorem error_of_source_and_far (hsource : SourcePsiBound)
    (hfar : |reciprocalError analyticTop| ≤ (1/10^8:ℝ))
    (hθfar : |Chebyshev.theta analyticTop-analyticTop| ≤ (3/4)*analyticTop^(15/16:ℝ))
    {x : ℝ} (hx : reference ≤ x) (hxb : x ≤ analyticTop) :
    |reciprocalError x| ≤ analyticBudget := by
  have hx2 : 2 ≤ x := (by norm_num [reference] : (2:ℝ) ≤ reference).trans hx
  have e := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=reference) (b:=x) (by norm_num [reference]) hx)
    (norm_kernel_interval hx2 hxb)
  have hn : 0 ≤ ∫ t in reference..x, ‖thetaErrorKernel t‖ :=
    intervalIntegral.integral_nonneg hx (fun _ _ => norm_nonneg _)
  have hdom : |∫ t in x..analyticTop,thetaErrorKernel t| ≤
      ∫ t in x..analyticTop, ‖thetaErrorKernel t‖ := by
    rw [← Real.norm_eq_abs,intervalIntegral.integral_of_le hxb,intervalIntegral.integral_of_le hxb]
    exact norm_integral_le_integral_norm _
  have hj : |∫ t in x..analyticTop,thetaErrorKernel t| ≤ firstIntegralCap+middleIntegralCap+kernelBudget5 := by
    linarith only [e,hn,hdom,full_integral hsource]
  have h := theta_prefix_budget hx2 hxb hfar (endpoint_uniform hsource hx) (analyticTop_endpoint hθfar) hj
  have hp := referenceEnvelope_paid
  unfold referenceEnvelope at hp
  unfold endpointCap firstIntegralCap middleIntegralCap at h
  linarith only [h,hp]

#print axioms error_of_source_and_far
end ChenEffective.PlattWindow.Schoenfeld

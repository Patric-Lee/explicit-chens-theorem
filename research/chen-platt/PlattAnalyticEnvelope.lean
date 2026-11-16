import PlattNumericalPieces
import PlattUniformEndpoint

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 1024

variable [Fact TernaryGoldbach.PlattZetaRH]

theorem kernel_full_budget :
    (∫ t in (10:ℝ)^10..analyticTop, ‖thetaErrorKernel t‖) ≤
      kernelBudget1+kernelBudget2+kernelBudget3+kernelBudget4+kernelBudget5 := by
  have e1 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=(10:ℝ)^10) (b:=(3:ℝ)^22) (by norm_num) (by norm_num))
    (norm_kernel_interval (a:=(3:ℝ)^22) (b:=analyticTop) (by norm_num) (by norm_num [analyticTop]))
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=(3:ℝ)^22) (b:=(10:ℝ)^13) (by norm_num) (by norm_num))
    (norm_kernel_interval (a:=(10:ℝ)^13) (b:=analyticTop) (by norm_num) (by norm_num [analyticTop]))
  have e3 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=(10:ℝ)^13) (b:=(10:ℝ)^15) (by norm_num) (by norm_num))
    (norm_kernel_interval (a:=(10:ℝ)^15) (b:=analyticTop) (by norm_num) (by norm_num [analyticTop]))
  have e4 := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=(10:ℝ)^15) (b:=(10:ℝ)^17) (by norm_num) (by norm_num))
    (norm_kernel_interval (a:=(10:ℝ)^17) (b:=analyticTop) (by norm_num) (by norm_num [analyticTop]))
  linarith only [e1,e2,e3,e4,kernel_piece1,kernel_piece2,kernel_piece3,kernel_piece4,kernel_piece5]

theorem kernel_subinterval_budget {x : ℝ} (hx : (10:ℝ)^10 ≤ x) (hxb : x ≤ analyticTop) :
    ‖∫ t in x..analyticTop,thetaErrorKernel t‖ ≤
      kernelBudget1+kernelBudget2+kernelBudget3+kernelBudget4+kernelBudget5 := by
  have hx2 : 2 ≤ x := (by norm_num : (2:ℝ) ≤ 10^10).trans hx
  have e := intervalIntegral.integral_add_adjacent_intervals
    (norm_kernel_interval (a:=(10:ℝ)^10) (b:=x) (by norm_num) hx)
    (norm_kernel_interval hx2 hxb)
  have hn : 0 ≤ ∫ t in (10:ℝ)^10..x, ‖thetaErrorKernel t‖ :=
    intervalIntegral.integral_nonneg hx (fun _ _ => norm_nonneg _)
  have hdom : ‖∫ t in x..analyticTop,thetaErrorKernel t‖ ≤
      ∫ t in x..analyticTop,‖thetaErrorKernel t‖ := by
    rw [intervalIntegral.integral_of_le hxb,intervalIntegral.integral_of_le hxb]
    exact norm_integral_le_integral_norm _
  linarith only [e,hn,hdom,kernel_full_budget]

/-- Numerical analytic assembly. The two far-end inputs are proved in the
existing Dirichlet/Dusart branch and are supplied by the final glue module. -/
theorem analytic_envelope_of_far
    (hfar : |reciprocalError analyticTop| ≤ (1/10^8:ℝ))
    (hθfar : |Chebyshev.theta analyticTop-analyticTop| ≤ (3/4)*analyticTop^(15/16:ℝ))
    {x : ℝ} (hx : (10:ℝ)^10 ≤ x) (hxb : x ≤ analyticTop) :
    |reciprocalError x| ≤ analyticAllowance := by
  have hx2 : 2 ≤ x := (by norm_num : (2:ℝ) ≤ 10^10).trans hx
  have h := theta_prefix_budget hx2 hxb hfar (thetaEndpoint_uniform hx)
    (analyticTop_endpoint hθfar) (by
      simpa only [Real.norm_eq_abs] using kernel_subinterval_budget hx hxb)
  have hp := anchorEnvelope_paid
  unfold kernelBudget1 kernelBudget2 kernelBudget3 kernelBudget4 kernelBudget5 endpointBudget at h
  unfold anchorEnvelope at hp
  linarith only [h,hp]

#print axioms analytic_envelope_of_far
end ChenEffective.PlattWindow

import PlattNumericalAux
import PlattThetaInputs

noncomputable section
namespace ChenEffective.PlattWindow
open Real Set MeasureTheory AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 1024

def kernelBudget1 : ℝ := 2*(75/2)*(24/23^2)*(1/100000-1/(3:ℝ)^11)
def kernelBudget2 : ℝ := 2*(1177/25)*(25/24^2)/(3:ℝ)^11
def kernelBudget3 : ℝ := 2*74*(30/29^2)/3000000
def kernelBudget4 : ℝ := 2*202*(35/34^2)/30000000
def kernelBudget5 : ℝ := (1/2000000)*(3+1/39)+
  2*1147*(40/39^2)/300000000+(42*10^9)/(10^17*39)

theorem sqrt_piece_cap {a b C L U V : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC : 0 ≤ C) (hL : 0 < L) (hlog : L ≤ log a)
    (hθ : ∀ t ∈ Ioc a b, |Chebyshev.theta t-t| ≤ C*sqrt t)
    (hU : a^(-1/2:ℝ) ≤ U) (hV : V ≤ b^(-1/2:ℝ)) :
    (∫ t in a..b, ‖thetaErrorKernel t‖) ≤ 2*C*((L+1)/L^2)*(U-V) := by
  apply (theta_integral_norm_sqrt ha hab hC hL hlog hθ).trans
  exact mul_le_mul_of_nonneg_left (sub_le_sub hU hV) (by positivity)

variable [Fact TernaryGoldbach.PlattZetaRH]

theorem kernel_piece1 : (∫ t in (10:ℝ)^10..(3:ℝ)^22, ‖thetaErrorKernel t‖) ≤ kernelBudget1 := by
  have hl : (23:ℝ) ≤ log ((10:ℝ)^10) := by
    have h := log_decimal 10
    norm_num at h ⊢ <;> linarith only [h]
  have h := sqrt_piece_cap (C:=75/2) (L:=23) (by positivity : (0:ℝ) < 10^10)
    (by norm_num : (10:ℝ)^10 ≤ 3^22) (by norm_num) (by norm_num) hl
    (fun t ht => theta_first ht.1.le ht.2) reference_power.le split_power.ge
  convert h using 1 <;> norm_num [kernelBudget1]

theorem kernel_piece2 : (∫ t in (3:ℝ)^22..(10:ℝ)^13, ‖thetaErrorKernel t‖) ≤ kernelBudget2 := by
  have hl : (24:ℝ) ≤ log ((3:ℝ)^22) := by
    exact log_power_three_lower
  have hu : ((3:ℝ)^22)^(-1/2:ℝ) ≤ 1/(3:ℝ)^11 := by
    exact split_power.le
  have hv : (0:ℝ) ≤ ((10:ℝ)^13)^(-1/2:ℝ) := rpow_nonneg (by positivity) _
  have h := sqrt_piece_cap (C:=1177/25) (L:=24) (by positivity : (0:ℝ) < (3:ℝ)^22)
    (by norm_num : (3:ℝ)^22 ≤ (10:ℝ)^13) (by norm_num) (by norm_num) hl
    (fun t ht => theta_second ht.1.le ht.2) hu hv
  convert h using 1 <;> norm_num [kernelBudget2] <;> ring

theorem kernel_piece3 : (∫ t in (10:ℝ)^13..(10:ℝ)^15, ‖thetaErrorKernel t‖) ≤ kernelBudget3 := by
  have hl : (29:ℝ) ≤ log ((10:ℝ)^13) := by
    have h := log_decimal 13
    norm_num at h ⊢ <;> linarith only [h]
  have hu : ((10:ℝ)^13)^(-1/2:ℝ) ≤ 1/3000000 := by
    exact invsqrt_bound (by norm_num : (0:ℝ) < 3000000) (by norm_num)
  have hv : (0:ℝ) ≤ ((10:ℝ)^15)^(-1/2:ℝ) := rpow_nonneg (by positivity) _
  have h := sqrt_piece_cap (C:=74) (L:=29) (by positivity : (0:ℝ) < (10:ℝ)^13)
    (by norm_num : (10:ℝ)^13 ≤ (10:ℝ)^15) (by norm_num) (by norm_num) hl
    (fun t ht => theta_third ht.1.le ht.2) hu hv
  convert h using 1 <;> norm_num [kernelBudget3] <;> ring

theorem kernel_piece4 : (∫ t in (10:ℝ)^15..(10:ℝ)^17, ‖thetaErrorKernel t‖) ≤ kernelBudget4 := by
  have hl : (34:ℝ) ≤ log ((10:ℝ)^15) := by
    have h := log_decimal 15
    norm_num at h ⊢ <;> linarith only [h]
  have hu : ((10:ℝ)^15)^(-1/2:ℝ) ≤ 1/30000000 := by
    exact invsqrt_bound (by norm_num : (0:ℝ) < 30000000) (by norm_num)
  have hv : (0:ℝ) ≤ ((10:ℝ)^17)^(-1/2:ℝ) := rpow_nonneg (by positivity) _
  have h := sqrt_piece_cap (C:=202) (L:=34) (by positivity : (0:ℝ) < (10:ℝ)^15)
    (by norm_num : (10:ℝ)^15 ≤ (10:ℝ)^17) (by norm_num) (by norm_num) hl
    (fun t ht => theta_fourth ht.1.le ht.2) hu hv
  convert h using 1 <;> norm_num [kernelBudget4] <;> ring

theorem kernel_piece5 : (∫ t in (10:ℝ)^17..analyticTop, ‖thetaErrorKernel t‖) ≤ kernelBudget5 := by
  have hl : (39:ℝ) ≤ log ((10:ℝ)^17) := by
    have h := log_decimal 17
    norm_num at h ⊢ <;> linarith only [h]
  have hab : (10:ℝ)^17 ≤ analyticTop := by unfold analyticTop; norm_num
  have h := theta_integral_norm_plateau (δ:=1/2000000) (A:=1147) (B:=42*10^9) (L:=39)
    (by norm_num : (1:ℝ) < 10^17) hab (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hl (fun t ht => theta_plateau ht.1.le)
  have hp : ((10:ℝ)^17)^(-1/2:ℝ) ≤ 1/300000000 :=
    invsqrt_bound (by norm_num) (by norm_num)
  have hf : 0 ≤ analyticTop^(-1/2:ℝ) := rpow_nonneg (by unfold analyticTop; positivity) _
  have hl0 : 0 < log ((10:ℝ)^17) := by linarith only [hl]
  have hlf : 0 < log analyticTop := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) analyticTop_log
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 39) hl
  have hif : (0:ℝ) ≤ 1/log analyticTop := by positivity
  have hc : 1/((10:ℝ)^17*log ((10:ℝ)^17)) ≤ 1/(10^17*39) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hl (by positivity))
  have hcf : (0:ℝ) ≤ 1/(analyticTop*log analyticTop) := by unfold analyticTop; positivity
  have hd := plateau_log_difference
  unfold kernelBudget5
  apply h.trans
  have hlin : log (log analyticTop)-log (log ((10:ℝ)^17))+
      1/log ((10:ℝ)^17)-1/log analyticTop ≤ 3+1/39 := by
    exact (sub_le_self _ hif).trans (add_le_add hd hi)
  have hroot : ((10:ℝ)^17)^(-1/2:ℝ)-analyticTop^(-1/2:ℝ) ≤ 1/300000000 := by
    exact (sub_le_self _ hf).trans hp
  have hcst : 1/((10:ℝ)^17*log ((10:ℝ)^17))-1/(analyticTop*log analyticTop) ≤
      1/(10^17*39) := (sub_le_self _ hcf).trans hc
  calc
    _ ≤ (1/2000000)*(3+1/39)+2*1147*((39+1)/39^2)*(1/300000000)+
        (42*10^9)*(1/(10^17*39)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlin (by norm_num))
        (mul_le_mul_of_nonneg_left hroot (by norm_num)))
        (mul_le_mul_of_nonneg_left hcst (by norm_num))
    _ = _ := by ring

#print axioms kernel_piece1
#print axioms kernel_piece5
end ChenEffective.PlattWindow

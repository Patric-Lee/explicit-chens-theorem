import PlattSchoenfeldGeometry
import PlattSchoenfeldKernel
import PlattNumericalPieces

noncomputable section
namespace ChenEffective.PlattWindow.Schoenfeld
open Real
set_option autoImplicit false
set_option maxHeartbeats 1600000

def analyticBudget : ℝ := 65/1000000
def finiteBudget : ℝ := 46/1000000

theorem joint_budget_paid : analyticBudget+finiteBudget ≤ (1/9000:ℝ) := by
  norm_num [analyticBudget,finiteBudget]

theorem log_ten_upper : log (10:ℝ) ≤ 231/100 := by
  have h := log_div_le_sum_range_add (by norm_num : (0:ℝ) ≤ 1/9)
    (by norm_num : (1/9:ℝ) < 1) 3
  norm_num [Finset.sum_range_succ] at h
  have h2 := log_two_lt_d9
  rw [show (10:ℝ)=(5/4)*2^3 by norm_num,log_mul (by norm_num) (by norm_num),log_pow]
  norm_num
  linarith only [h,h2]

theorem reference_log_upper : log reference ≤ (43/2:ℝ) := by
  rw [show reference=2*(10:ℝ)^9 by norm_num [reference],log_mul (by norm_num) (by positivity),log_pow]
  have h := log_ten_upper
  have h2 := log_two_lt_d9
  norm_num
  linarith only [h,h2]

theorem reference_invroot : reference^(-1/2:ℝ) ≤ 1/44721 := by
  apply invsqrt_bound (by norm_num : (0:ℝ) < 44721)
  norm_num [reference]

theorem schoenfeld_coefficient : (1/(8*Real.pi):ℝ) ≤ 1/25 := by
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 25)
  have h := Real.pi_gt_d2
  linarith only [h]

/-- Conservative scalar envelope for the proposed reference2e9. This pays
the complete numerical allocation, but is not a producer of the source
psi/theta bound. In particular it does NOT change the production cutoff. -/
def referenceEnvelope : ℝ :=
  (3*(43/2)+6)/(25*44721)+1/(2*2000000000)+
  (1/2)*(1+1/21)/2000000000+
  2*202*(37/36^2)*(1/100000000)+kernelBudget5+2/10^8

theorem referenceEnvelope_paid : referenceEnvelope ≤ analyticBudget := by
  norm_num [referenceEnvelope,analyticBudget,kernelBudget5]

theorem absolute_of_relative {ex er : ℝ}
    (hr : |er| ≤ analyticBudget) (hx : |ex-er| ≤ finiteBudget) :
    |ex| ≤ (1/9000:ℝ) := by
  have h := (abs_add_le (ex-er) er).trans (add_le_add hx hr)
  rw [sub_add_cancel] at h
  have hp := joint_budget_paid
  linarith only [h,hp]

#print axioms referenceEnvelope_paid
#print axioms schoenfeld_coefficient
end ChenEffective.PlattWindow.Schoenfeld

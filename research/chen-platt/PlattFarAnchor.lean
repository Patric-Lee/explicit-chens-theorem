import PlattPrefixBridge
import DusartPort.Psi1Estimate
import BJSMertensThetaTarget

noncomputable section
namespace ChenEffective.PlattWindow
open Real
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1024

def farAnchor : ℝ := (3:ℝ)^512

theorem farAnchor_power : farAnchor^(-1/16:ℝ) = 1/(3:ℝ)^32 := by
  unfold farAnchor
  rw [← rpow_natCast (3:ℝ) 512, ← rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  norm_num [rpow_neg]

theorem farAnchor_log : 1 ≤ log farAnchor := by
  have hlog : log (2:ℝ) ≤ log (3:ℝ) := log_le_log (by norm_num) (by norm_num)
  unfold farAnchor
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hlog, log_two_gt_d9]

theorem farAnchor_large : (3:ℝ)^120 ≤ farAnchor := by
  unfold farAnchor
  norm_num

theorem farAnchor_error : |reciprocalError farAnchor| ≤ (1/10^8:ℝ) := by
  have h := bjsStudy_mertens_of_theta_target
    (x := farAnchor) (by unfold farAnchor; norm_num)
    (fun t ht => Dusart.numerical_theta_target (farAnchor_large.trans ht))
  have hl := farAnchor_log
  have hl0 : 0 < log farAnchor := by linarith only [hl]
  have hc : (17*log farAnchor+16)/(log farAnchor)^2 ≤ 33 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl0)).mpr
    nlinarith only [hl, sq_nonneg (log farAnchor-1)]
  have hm := mul_le_mul_of_nonneg_right hc
    (rpow_nonneg (by unfold farAnchor; positivity : (0:ℝ) ≤ farAnchor) (-1/16:ℝ))
  rw [farAnchor_power] at h hm
  change |reciprocalError farAnchor| ≤ _ at h
  have hp : (3/4:ℝ)*33*(1/(3:ℝ)^32) ≤ (1/10^8:ℝ) := by norm_num
  calc
    _ ≤ (3/4:ℝ)*((17*log farAnchor+16)/(log farAnchor)^2*(1/(3:ℝ)^32)) := by
      convert h using 1 <;> ring
    _ ≤ (3/4:ℝ)*(33*(1/(3:ℝ)^32)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ ≤ _ := by norm_num

#print axioms farAnchor_error
end ChenEffective.PlattWindow

import GRHSharpDivisorMoments

/-! Direct payment of the complete pre-sieve error envelope. The old
intermediate exponential decay rate is deliberately not required. -/
noncomputable section
namespace ChenEffective.GRH
open Real
set_option maxHeartbeats 3000000

theorem sharp_medium_truncation_payment {L : ℝ} (hL : 637000 ≤ L) :
    336*L^6*exp (1468+log 2/2-L/400) ≤ (1e-12:ℝ) := by
  have hLp : 0<L := by linarith only [hL]
  have he1 : (27/10:ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
  have he14 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 14
  rw [← exp_nat_mul] at he14
  norm_num only [Nat.cast_ofNat,mul_one] at he14
  have hn14 : (637000:ℝ) ≤ (27/10:ℝ)^14 := by norm_num
  have hlog14 : log (637000:ℝ) ≤ 14 := by
    have hx : (637000:ℝ)≤exp 14 := by norm_num at he14; linarith only [he14]
    have hh := log_le_log (by norm_num : (0:ℝ)<637000) hx
    rwa [log_exp] at hh
  have hratio := log_le_sub_one_of_pos (div_pos hLp (by norm_num : (0:ℝ)<637000))
  rw [log_div hLp.ne' (by norm_num)] at hratio
  have hlog : 6*log L ≤ L/10000+21 := by
    linarith only [hratio,hlog14,hL]
  have he6 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 6
  rw [← exp_nat_mul] at he6
  norm_num only [Nat.cast_ofNat,mul_one] at he6
  have hn6 : (336:ℝ) ≤ (27/10:ℝ)^6 := by norm_num
  have hc : (336:ℝ) ≤ exp 6 := by norm_num at he6; linarith only [he6]
  have hl2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hpoly : L^6=exp (6*log L) := by
    have hh := exp_nat_mul (log L) 6
    norm_num only [Nat.cast_ofNat] at hh
    rw [exp_log hLp] at hh
    exact hh.symm
  have he30 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he1 30
  rw [← exp_nat_mul] at he30
  norm_num only [Nat.cast_ofNat,mul_one] at he30
  have hn30 : (1e12:ℝ) ≤ (27/10:ℝ)^30 := by norm_num
  have hsmall : exp (-30:ℝ) ≤ (1e-12:ℝ) := by
    have hx : (1e12:ℝ)≤exp 30 := by norm_num at he30; linarith only [he30]
    have hh := mul_le_mul_of_nonneg_right hx (exp_pos (-30:ℝ)).le
    rw [← exp_add] at hh
    norm_num at hh
    linarith only [hh]
  calc
    _ ≤ exp 6*L^6*exp (1468+log 2/2-L/400) := by gcongr
    _ = exp (6+6*log L+1468+log 2/2-L/400) := by
      rw [hpoly,← exp_add,← exp_add]
      congr 1
      ring
    _ ≤ exp (-30:ℝ) := exp_le_exp.mpr (by linarith only [hlog,hl2,hL])
    _ ≤ _ := hsmall

#print axioms sharp_medium_truncation_payment
end ChenEffective.GRH

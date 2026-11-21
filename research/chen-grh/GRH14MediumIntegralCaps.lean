import GRH14MediumPrimeSum
import GRH14LowerFactor

noncomputable section
namespace ChenEffective.GRH14
open Real Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem medium_K_bounds : 0 ≤ jurkatRichertK ∧ jurkatRichertK ≤ (5/8:ℝ) := by
  have hpoint (u : ℝ) (hu : u∈Icc (3:ℝ) 4) :
      0 ≤ 10/(u*(5-u))*jurkatRichertInnerIntegral u ∧
      10/(u*(5-u))*jurkatRichertInnerIntegral u ≤ (5/8:ℝ) := by
    have hd : (4:ℝ) ≤ u*(5-u) := by
      nlinarith only [hu.1,hu.2,mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hu.2)]
    have hp := inner_integral_quarter hu.1 hu.2
    have hr : (10:ℝ)/(u*(5-u)) ≤ 5/2 :=
      (div_le_iff₀ (by linarith only [hd])).mpr (by linarith only [hd])
    constructor
    · exact mul_nonneg (by positivity) hp.1
    · exact (mul_le_mul hr hp.2 hp.1 (by norm_num)).trans (by norm_num)
  have hc : ContinuousOn (fun u : ℝ => 10/(u*(5-u))*jurkatRichertInnerIntegral u) (Icc 3 4) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      intro u hu
      have hu0 : 0<u := by linarith only [hu.1]
      have hu5 : 0<5-u := by linarith only [hu.2]
      exact (mul_pos hu0 hu5).ne'
    · apply continuousOn_jurkatRichertInnerIntegral_three_five.mono
      intro u hu
      exact ⟨hu.1,hu.2.trans (by norm_num)⟩
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (3:ℝ) ≤ 4) hc
  unfold jurkatRichertK
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => (hpoint u hu).1)
  · calc
      _ ≤ ∫ _u in (3:ℝ)..4, (5/8:ℝ) := intervalIntegral.integral_mono_on
        (by norm_num) hi intervalIntegrable_const (fun u hu => (hpoint u hu).2)
      _ = _ := by norm_num

theorem medium_integral_small_cap : 0 ≤ mediumPrimeIntegral ∧ mediumPrimeIntegral ≤ 3 := by
  have hI0 := numerical_medium_integral_caps.1
  have hK := medium_K_bounds
  have hlog0 : 0 ≤ log (8:ℝ) := log_nonneg (by norm_num)
  have hlog : log (8:ℝ) ≤ 21/10 := by
    rw [show (8:ℝ)=2^3 by norm_num,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_lt_d9]
  have hE : exp eulerMascheroniConstant ≤ 3 :=
    (exp_le_exp.mpr (eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num))).trans
      (exp_one_lt_d9.le.trans (by norm_num))
  have heq : mediumPrimeIntegral=(2*exp eulerMascheroniConstant/5)*(log 8+jurkatRichertK/2) :=
    jurkatRichertUpperLinearSieveFactor_zeroEpsilon_integral
  refine ⟨hI0,?_⟩
  rw [heq]
  apply (mul_le_mul (show 2*exp eulerMascheroniConstant/5 ≤ (6/5:ℝ) by linarith only [hE])
    (show log 8+jurkatRichertK/2 ≤ (5/2:ℝ) by linarith only [hlog,hK.2])
    (show 0 ≤ log 8+jurkatRichertK/2 by linarith only [hlog0,hK.1]) (by norm_num)).trans
  norm_num

#print axioms medium_integral_small_cap
end ChenEffective.GRH14

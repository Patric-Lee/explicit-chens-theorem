import NumericalSuzukiHat
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144LiteralAllDepthUniformInS

namespace ChenEffective
open Real MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem numerical_source_sigma_two : (1 / 2 : ℝ) ≤ sourceSigma 2 16 := by
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hl1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hp : Real.log 2 ≤ (Real.log 2) ^ (1 / 16 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (by norm_num : (1 / 16 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using hh
  have h54 : (3 : ℝ) ≤ Real.log 54 := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 27) (by norm_num : (27 : ℝ) ≤ 54)
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, one_le_log_three]
  have hll : (1 : ℝ) ≤ Real.log (Real.log 54) :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) h54)
  have hh := mul_le_mul (hlhalf.trans hp) hll (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ (Real.log 2) ^ (1 / 16 : ℝ))
  norm_num only [sourceSigma, show (27 : ℝ) * 2 = 54 by norm_num, one_mul] at hh ⊢
  exact hh

theorem numerical_claim_normalization {C : ℝ} (hC : 0 ≤ C) :
    claim145UniformNormalizationConstant C 16 ≤ 4 * C := by
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hs := numerical_source_sigma_two
  have hs0 : 0 ≤ sourceSigma 2 16 := by linarith only [hs]
  have hd : (1 / 4 : ℝ) ≤ Real.log 2 * sourceSigma 2 16 := by
    have hh := mul_le_mul hlhalf hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show 0 ≤ Real.log 2 by linarith only [hlhalf])
    norm_num at hh
    exact hh
  unfold claim145UniformNormalizationConstant
  apply (div_le_iff₀ (show 0 < Real.log 2 * sourceSigma 2 16 by linarith only [hd])).mpr
  have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * C by positivity)
  nlinarith only [hh]

theorem numerical_suzuki_base_constant : lemma144BaseOneGlobalConstant (1 / 2 : ℝ) ≤ 36 := by
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log 2) :=
    (Real.le_sqrt (by norm_num) hl0.le).mpr (by linarith only [hlhalf])
  have hi : (Real.sqrt (Real.log 2))⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀' (Real.sqrt_pos.mpr hl0)).mpr
    linarith only [hs]
  unfold lemma144BaseOneGlobalConstant
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg hl0.le, ← Real.sqrt_eq_rpow]
  linarith only [hi]

#print axioms numerical_claim_normalization
#print axioms numerical_suzuki_base_constant
end ChenEffective

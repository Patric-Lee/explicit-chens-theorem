import NumericalRealLogBounds
import NumericalPolynomialMiddle

namespace ChenEffective
open Real
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem strong_log_linear {x : ℝ} (hx : 17424 ≤ x) : log x ≤ x / 128 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hbase : log (17424 : ℝ) ≤ 100 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have hh := Real.pow_div_factorial_le_exp (100 : ℝ) (by norm_num) 3
    norm_num [Nat.factorial] at hh ⊢
    linarith only [hh]
  have ht := Real.log_le_sub_one_of_pos (div_pos hx0 (by norm_num : (0 : ℝ) < 17424))
  rw [Real.log_div hx0.ne' (by norm_num : (17424 : ℝ) ≠ 0)] at ht
  linarith only [ht, hbase, hx]

theorem strong_sourceSigma_gate {D : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ log D) :
    sourceSigma D 16 * (log D) ^ (-(1 / 8 : ℝ)) ≤ exp (-940 : ℝ) := by
  let L := log D
  let U := log L
  have hL0 : 0 < L := Real.log_pos hD
  have hU : 17424 ≤ U := by
    have hh := real_log_power_cutoff_log hcut
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hU0 : 0 < U := by linarith only [hU]
  have hL9 : 9 ≤ L := real_log_power_cutoff_nine hcut
  have hinner : 0 < log (27 * D) := Real.log_pos (by linarith only [hD])
  have h27 : log (27 : ℝ) ≤ 6 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hell : log (log (27 * D)) ≤ 2 * U := by
    have hi : log (27 * D) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) (by linarith only [hD] : D ≠ 0)]
      change log 27 + L ≤ 2 * L
      linarith only [h27, hL9]
    calc
      _ ≤ log (2 * L) := Real.log_le_log hinner hi
      _ = log 2 + U := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ 2 * U := by
        have hh := Real.log_two_lt_d9
        linarith only [hh, hU]
  have hlog2U : log (2 * U) ≤ 1 + U / 128 := by
    rw [Real.log_mul (by norm_num) hU0.ne']
    linarith only [strong_log_linear hU, Real.log_two_lt_d9]
  have hmain : (2 * U) * exp (-U / 16) ≤ exp (-940 : ℝ) := by
    calc
      _ = exp (log (2 * U) - U / 16) := by
        rw [Real.exp_sub, Real.exp_log (by positivity), show -U / 16 = -(U / 16) by ring, Real.exp_neg]
        ring
      _ ≤ exp (1 + U / 128 - U / 16) := Real.exp_le_exp.mpr (by linarith only [hlog2U])
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hU])
  have hroot : L ^ (1 / 16 : ℝ) * L ^ (-(1 / 8 : ℝ)) = exp (-U / 16) := by
    rw [← Real.rpow_add hL0]
    rw [Real.rpow_def_of_pos hL0]
    congr 1
    dsimp [U]
    ring
  have hp := mul_le_mul_of_nonneg_right hell
    (mul_nonneg (Real.rpow_nonneg hL0.le (1 / 16 : ℝ)) (Real.rpow_nonneg hL0.le (-(1 / 8 : ℝ))))
  unfold sourceSigma
  change L ^ (1 / 16 : ℝ) * log (log (27 * D)) * L ^ (-(1 / 8 : ℝ)) ≤ _
  calc
    _ ≤ (2 * U) * (L ^ (1 / 16 : ℝ) * L ^ (-(1 / 8 : ℝ))) := by nlinarith only [hp]
    _ = (2 * U) * exp (-U / 16) := by rw [hroot]
    _ ≤ _ := hmain

theorem strong_log_inverse_eighth {D : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ log D) :
    (log D) ^ (-(1 / 8 : ℝ)) ≤ exp (-940 : ℝ) := by
  have hh := real_log_power_cutoff_log hcut
  norm_num only [Nat.cast_ofNat] at hh
  rw [Real.rpow_def_of_pos (Real.log_pos hD)]
  exact Real.exp_le_exp.mpr (by linarith only [hh])

#print axioms strong_sourceSigma_gate
end ChenEffective

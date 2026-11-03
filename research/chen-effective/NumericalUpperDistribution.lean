import NumericalVaryingCorrections

namespace ChenEffective
open Finset Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def varyingNumericalBudget : ℕ := 3145728 * (1000478800000012180 + 1) + 3000

theorem varyingNumericalBudget_eq : (varyingNumericalBudget : ℝ) =
    weightedNumericalConstant 3 + 3000 := by
  norm_num [varyingNumericalBudget, weightedNumericalConstant, weightedSaving, numericalBVConstant,
    bvConstant, primitiveNumericalConstant, principalNumericalConstant, highBVConductorExponent]

def varyingNumericalThreshold (m d : ℕ) : ℕ :=
  max (max (weightedNumericalThreshold 3 m) (logPowerCutoff 100))
    (3 ^ (2 * varyingNumericalBudget * d + 1))

theorem numerical_varying_remainder_cube (m N : ℕ) (hm : 0 < m)
    (hN : max (weightedNumericalThreshold 3 m) (logPowerCutoff 100) ≤ N) (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1 / (m : ℝ)) ≤
      (varyingNumericalBudget : ℝ) * N / Real.log N ^ (3 : ℕ) := by
  have hw := numerical_weighted_distribution 3 m N hm ((le_max_left _ _).trans hN)
  have hcut : logPowerCutoff 100 ≤ N := (le_max_right _ _).trans hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := log_pow_le_rpow_inv_explicit (k := 10) (m := 10) (by norm_num) (by norm_num) hcut
  have hc := numerical_varying_correction hN9
    (show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity)
  have hc' : jurkatRichertSourceVaryingQUnconditionalCorrection N (1 / (m : ℝ)) ≤
      3000 * N / Real.log N ^ (3 : ℕ) := by
    apply hc.trans
    apply (le_div_iff₀ (pow_pos hl 3)).mpr
    have he : (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hp
      (show 0 ≤ 3000 * (N : ℝ) ^ (9 / 10 : ℝ) by positivity)
    norm_num only [Nat.cast_ofNat] at hh
    have he' : 3000 * (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = 3000 * N := by
      rw [mul_assoc, he]
    have ht : Real.log (N : ℝ) ^ (7 : ℕ) * Real.log N ^ (3 : ℕ) = Real.log N ^ (10 : ℕ) := by ring
    nlinarith only [hh, he', congrArg (fun x : ℝ => 3000 * (N : ℝ) ^ (9 / 10 : ℝ) * x) ht]
  have hf := jurkatRichertSourceVaryingQRemainderSum_le_weightedBV_add_correction
    N (1 / (m : ℝ)) hEven (by omega)
  rw [varyingNumericalBudget_eq]
  calc
    _ ≤ _ := hf
    _ ≤ weightedNumericalConstant 3 * N / Real.log N ^ (3 : ℕ) +
        3000 * N / Real.log N ^ (3 : ℕ) := add_le_add hw hc'
    _ = _ := by ring

theorem numerical_varying_upper_distribution (m d N : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hN : varyingNumericalThreshold m d ≤ N) (hEven : Even N) :
    jurkatRichertSourceVaryingQRemainderSum N (1 / (m : ℝ)) ≤
      (1 / (d : ℝ)) * SingularSeries.liuSingularSeries N * N / Real.log N ^ (2 : ℕ) := by
  have hcut : max (weightedNumericalThreshold 3 m) (logPowerCutoff 100) ≤ N :=
    (le_max_left _ _).trans hN
  have hb := numerical_varying_remainder_cube m N hm hcut hEven
  have hlog := log_ge_power_three ((le_max_right _ _).trans hN)
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le 100).trans ((le_max_right _ _).trans hcut)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog' : 2 * (varyingNumericalBudget : ℝ) * d ≤ Real.log N := by
    push_cast at hlog
    linarith only [hlog]
  have hs := half_le_liuSingularSeries N
  have hnum : (varyingNumericalBudget : ℝ) ≤
      ((1 / (d : ℝ)) * SingularSeries.liuSingularSeries N) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_right hs hl.le
    calc
      _ ≤ (SingularSeries.liuSingularSeries N * Real.log N) / d := by
        apply (le_div_iff₀ hdR).mpr
        nlinarith only [hh, hlog']
      _ = _ := by ring
  apply hb.trans
  apply (div_le_div_iff₀ (pow_pos hl 3) (pow_pos hl 2)).mpr
  have hh := mul_le_mul_of_nonneg_right hnum
    (show 0 ≤ (N : ℝ) * Real.log N ^ (2 : ℕ) by positivity)
  nlinarith only [hh]

#print axioms numerical_varying_upper_distribution
end ChenEffective

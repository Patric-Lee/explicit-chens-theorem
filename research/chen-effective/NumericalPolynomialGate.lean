import NumericalPolynomialCompact
import NumericalRealLogBounds

/-! Numerical logarithmic gates for polynomial transport. The level input is
the displayed integer `logPowerCutoff 32`, not a selected eventual threshold. -/

namespace ChenEffective
open Real
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem polynomial_sourceSigma_upper {D : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) :
    sourceSigma D 16 ≤ (Real.log D) ^ (1 / 8 : ℝ) := by
  let L := Real.log D
  have hL9 : 9 ≤ L := real_log_power_cutoff_nine hcut
  have hL0 : 0 < L := by linarith only [hL9]
  have hlogL := real_log_power_cutoff_log hcut
  norm_num only [Nat.cast_ofNat] at hlogL
  have hroot : Real.log L ≤ L ^ (1 / 32 : ℝ) := by
    have hh := real_log_pow_le_rpow_inv (k := 1) (m := 32) (t := 32)
      (by norm_num) (by norm_num) hcut
    simpa only [pow_one, Nat.cast_ofNat] using hh
  have htwo : 2 ≤ L ^ (1 / 32 : ℝ) := by
    rw [Real.rpow_def_of_pos hL0]
    have hh := Real.add_one_le_exp (Real.log L * (1 / 32 : ℝ))
    change (17424 : ℝ) ≤ Real.log L at hlogL
    nlinarith only [hh, hlogL]
  have h27 : Real.log (27 : ℝ) ≤ 6 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hinner : 0 < Real.log (27 * D) := Real.log_pos (by linarith only [hD])
  have hell : Real.log (Real.log (27 * D)) ≤ 2 * Real.log L := by
    have hi : Real.log (27 * D) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) (by linarith only [hD] : D ≠ 0)]
      change Real.log 27 + L ≤ 2 * L
      linarith only [h27, hL9]
    calc
      _ ≤ Real.log (2 * L) := Real.log_le_log hinner hi
      _ = Real.log 2 + Real.log L := Real.log_mul (by norm_num) hL0.ne'
      _ ≤ _ := by
        have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show 2 ≤ L by linarith only [hL9])
        linarith only [hh]
  have hpow : (L ^ (1 / 32 : ℝ)) ^ 2 = L ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have hellpow : Real.log (Real.log (27 * D)) ≤ L ^ (1 / 16 : ℝ) := by
    rw [← hpow]
    nlinarith only [hell, hroot, htwo,
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hL0.le (1 / 32 : ℝ))]
  unfold sourceSigma
  change L ^ (1 / (16 : ℝ)) * Real.log (Real.log (27 * D)) ≤ L ^ (1 / 8 : ℝ)
  calc
    _ ≤ L ^ (1 / 16 : ℝ) * L ^ (1 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hellpow (Real.rpow_nonneg hL0.le _)
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

theorem polynomial_sourceSigma_gate {D : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) :
    sourceSigma D 16 * (Real.log D) ^ (-(1 / 8 : ℝ)) ≤ 1 := by
  have hL : 0 < Real.log D := Real.log_pos hD
  have hh := mul_le_mul_of_nonneg_right (polynomial_sourceSigma_upper hD hcut)
    (Real.rpow_nonneg hL.le (-(1 / 8 : ℝ)))
  simpa only [← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero] using hh

theorem polynomial_transport_level_gate {D K : ℝ} (hD : 1 < D)
    (hcut : (logPowerCutoff 32 : ℝ) ≤ Real.log D) (hK : 2 ≤ K)
    (hKlevel : K ^ (7 : ℝ) ≤ Real.log D) :
    288 * K ^ 2 ≤ Real.log (D ^ (1 / sourceSigma D 16)) := by
  let L := Real.log D
  have hL9 : 9 ≤ L := real_log_power_cutoff_nine hcut
  have hL : 0 < L := by linarith only [hL9]
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hK4 : K ^ (4 : ℝ) ≤ L :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [hK] : 1 ≤ K)
      (by norm_num : (4 : ℝ) ≤ 7)).trans hKlevel
  have hKsq : K ^ 2 ≤ L ^ (1 / 2 : ℝ) := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hK4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul hK0] at hh
    norm_num at hh
    exact hh
  have h288 : 288 ≤ L ^ (3 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos hL]
    have hl := real_log_power_cutoff_log hcut
    norm_num only [Nat.cast_ofNat] at hl
    have hh := Real.add_one_le_exp (Real.log L * (3 / 8 : ℝ))
    change (17424 : ℝ) ≤ Real.log L at hl
    nlinarith only [hh, hl]
  have hσ0 : 0 < sourceSigma D 16 := by
    unfold sourceSigma
    have hi : 1 < Real.log (27 * D) := by
      rw [Real.log_mul (by norm_num) (by linarith only [hD] : D ≠ 0)]
      have hp : 1 ≤ Real.log (27 : ℝ) := one_le_log_three.trans
        (Real.log_le_log (by norm_num) (by norm_num))
      linarith only [hp, hL]
    exact mul_pos (Real.rpow_pos_of_pos hL _) (Real.log_pos hi)
  rw [Real.log_rpow (by linarith only [hD] : 0 < D)]
  change 288 * K ^ 2 ≤ (1 / sourceSigma D 16) * L
  have hh : 288 * K ^ 2 * sourceSigma D 16 ≤ L := by
    calc
      _ ≤ 288 * L ^ (1 / 2 : ℝ) * L ^ (1 / 8 : ℝ) := by
        gcongr
        exact polynomial_sourceSigma_upper hD hcut
      _ = 288 * L ^ (5 / 8 : ℝ) := by rw [mul_assoc, ← Real.rpow_add hL]; norm_num
      _ ≤ L ^ (3 / 8 : ℝ) * L ^ (5 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right h288 (Real.rpow_nonneg hL.le _)
      _ = L := by rw [← Real.rpow_add hL]; norm_num
  have hr : 288 * K ^ 2 ≤ L / sourceSigma D 16 := (le_div_iff₀ hσ0).mpr hh
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hr

#print axioms polynomial_sourceSigma_gate
#print axioms polynomial_transport_level_gate
end ChenEffective

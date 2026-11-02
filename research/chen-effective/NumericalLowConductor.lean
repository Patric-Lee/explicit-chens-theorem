import NumericalPrimitivePower
import MathlibNt.AnalyticNumberTheory.LargeSieve.PointwisePrimitivePrefixAmplitudeBridge

namespace ChenEffective
open Complex Real Set
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def primitiveNumericalConstant (C : ℕ) : ℝ := 100000000000 * (C + 1)
def primitiveNumericalThreshold (D : ℕ) : ℕ := logPowerCutoff (128 * (D + 1))

theorem numerical_low_prefix_power {N C q : ℕ} [NeZero q]
    (hN : 9 ≤ N) (hq : (q : ℝ) ≤ Real.log N ^ C)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℕ) (hy : y ≤ N) :
    ‖lambdaCharacterPrefix y q χ‖ ≤
      primitiveNumericalConstant C * (N : ℝ) ^ (127 / 128 : ℝ) * Real.log N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega))
    linarith only [hh, one_le_log_three]
  have hPow : (1 : ℝ) ≤ (N : ℝ) ^ (127 / 128 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  by_cases hy9 : 9 ≤ y
  · have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
    have hyN : (y : ℝ) ≤ N := by exact_mod_cast hy
    have hqN : (q : ℝ) ≤ (N : ℝ) ^ C := hq.trans
      (pow_le_pow_left₀ (by linarith only [hlog])
        ((Real.log_le_sub_one_of_pos hN0).trans (by linarith)) C)
    have ht : (y : ℝ) ^ (1 / 32 : ℝ) ≤ N := by
      calc
        _ ≤ (y : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
        _ = (y : ℝ) := Real.rpow_one _
        _ ≤ N := hyN
    have harg : 16 * (q : ℝ) * ((y : ℝ) ^ (1 / 32 : ℝ) + 4) ≤ (N : ℝ) ^ (C + 3) := by
      have hN9 : (9 : ℝ) ≤ N := by exact_mod_cast hN
      have hp0 : (0 : ℝ) ≤ (N : ℝ) ^ C := by positivity
      have harg' : 16 * (q : ℝ) * ((y : ℝ) ^ (1 / 32 : ℝ) + 4) ≤
          32 * (N : ℝ) ^ C * N := by
        calc
          _ ≤ 16 * (N : ℝ) ^ C * (2 * N) := by gcongr; linarith only [ht, hN9]
          _ = _ := by ring
      have hs : (32 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN9, sq_nonneg ((N : ℝ) - 9)]
      have hh := mul_le_mul_of_nonneg_right hs (mul_nonneg hp0 hN0.le)
      rw [pow_add]
      nlinarith only [harg', hh]
    have hL : Real.log (16 * (q : ℝ) * ((y : ℝ) ^ (1 / 32 : ℝ) + 4)) ≤
        (C + 3 : ℝ) * Real.log N := by
      have hh := Real.log_le_log (by positivity) harg
      rw [Real.log_pow] at hh
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
    have hyl : Real.log (y : ℝ) ≤ Real.log N := Real.log_le_log hy0 hyN
    have hh := numerical_primitive_prefix_power_bound χ hχ
      (show (9 : ℝ) ≤ y by exact_mod_cast hy9)
    simp only [Nat.floor_natCast] at hh
    have hcoef : 10000000000 + 200000000 *
        Real.log (16 * (q : ℝ) * ((y : ℝ) ^ (1 / 32 : ℝ) + 4)) + 60 * Real.log y ≤
        primitiveNumericalConstant C * Real.log N := by
      dsimp [primitiveNumericalConstant]
      have hc : (0 : ℝ) ≤ C := Nat.cast_nonneg C
      have hcL := mul_nonneg hc (show 0 ≤ Real.log N by linarith only [hlog])
      nlinarith only [hL, hyl, hlog, hcL]
    calc
      _ ≤ _ := hh
      _ ≤ (primitiveNumericalConstant C * Real.log N) *
          (N : ℝ) ^ (127 / 128 : ℝ) := by
        apply mul_le_mul hcoef (Real.rpow_le_rpow (by positivity) hyN (by norm_num))
          (by positivity) (by dsimp [primitiveNumericalConstant]; positivity)
      _ = _ := by ring
  · have he := norm_lambdaCharacterPrefix_le_const_mul_self y q χ
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    have hy8 : (y : ℝ) ≤ 8 := by exact_mod_cast (show y ≤ 8 by omega)
    have hbound : (Real.log 4 + 4) * y ≤ 48 := by
      have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
      nlinarith only [hlog4, hy8, hy0]
    apply he.trans (hbound.trans _)
    have hc : (1 : ℝ) ≤ (C : ℝ) + 1 := by have hh := Nat.cast_nonneg (α := ℝ) C; linarith
    have hh := mul_le_mul hPow hlog (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    dsimp [primitiveNumericalConstant]
    nlinarith only [hh, hc, mul_nonneg (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hh)]

theorem numerical_low_prefix {N C D q : ℕ} [NeZero q]
    (hN : primitiveNumericalThreshold D ≤ N) (hq : (q : ℝ) ≤ Real.log N ^ C)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℕ) (hy : y ≤ N) :
    ‖lambdaCharacterPrefix y q χ‖ ≤ primitiveNumericalConstant C * N / Real.log N ^ D := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hh := numerical_low_prefix_power hN9 hq χ hχ y hy
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := log_pow_le_rpow_inv_explicit (k := D + 1) (m := 128)
    (by norm_num) (le_refl _) hN
  have hc : 0 ≤ primitiveNumericalConstant C := by dsimp [primitiveNumericalConstant]; positivity
  apply hh.trans
  apply (le_div_iff₀ (pow_pos hl D)).mpr
  have hpay := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ primitiveNumericalConstant C * (N : ℝ) ^ (127 / 128 : ℝ) by positivity)
  have he : (N : ℝ) ^ (127 / 128 : ℝ) * (N : ℝ) ^ (1 / 128 : ℝ) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [pow_succ] at hpay
  norm_num only [Nat.cast_ofNat] at hpay
  have he' : primitiveNumericalConstant C * (N : ℝ) ^ (127 / 128 : ℝ) *
      (N : ℝ) ^ (1 / 128 : ℝ) = primitiveNumericalConstant C * N := by
    rw [mul_assoc, he]
  nlinarith only [hpay, he']

theorem numerical_primitive_low_conductor {N C D q : ℕ} [NeZero q]
    (hN : primitiveNumericalThreshold D ≤ N) (hq : (q : ℝ) ≤ Real.log N ^ C)
    (ψ : PrimitiveCharacter q) (hψ : ψ.1 ≠ 1) :
    primitivePrefixAmplitude vonMangoldtIntegerCoeff N q ψ ≤
      primitiveNumericalConstant C * N / Real.log N ^ D :=
  primitivePrefixAmplitude_vonMangoldt_le_of_pointwise_lambdaCharacterPrefix N q ψ _
    (fun y hy => numerical_low_prefix hN hq ψ.1 hψ y hy)

theorem numerical_primitive_low_conductor_cutoff {N C D q : ℕ} [NeZero q]
    (hN : primitiveNumericalThreshold D ≤ N) (hq : q ≤ logConductorThreshold N C)
    (ψ : PrimitiveCharacter q) (hψ : ψ.1 ≠ 1) :
    primitivePrefixAmplitude vonMangoldtIntegerCoeff N q ψ ≤
      primitiveNumericalConstant C * N / Real.log N ^ D := by
  apply numerical_primitive_low_conductor hN _ ψ hψ
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ N by omega))
  exact (show (q : ℝ) ≤ logConductorThreshold N C by exact_mod_cast hq).trans
    (Nat.floor_le (pow_nonneg hl C))

#print axioms numerical_primitive_low_conductor
end ChenEffective

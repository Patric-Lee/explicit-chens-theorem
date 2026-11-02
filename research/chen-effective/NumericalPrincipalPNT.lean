import NumericalPrincipalPower
import NumericalPrincipalElementary

namespace ChenEffective
open Complex Real Set
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def principalNumericalThreshold (D : ℕ) : ℕ := logPowerCutoff (128 * (D + 1))
def principalNumericalConstant : ℝ := 500000000000

theorem numerical_principal_pointwise_through {N : ℕ} (hN : 9 ≤ N)
    (y : ℕ) (hy : y ≤ N) :
    |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤
      100000000000 * (N : ℝ) ^ (127 / 128 : ℝ) * Real.log N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hN9 : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ N by exact_mod_cast (show 3 ≤ N by omega))
    linarith only [hh, one_le_log_three]
  have hPow : (1 : ℝ) ≤ (N : ℝ) ^ (127 / 128 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  by_cases hy9 : 9 ≤ y
  · have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
    have hyN : (y : ℝ) ≤ N := by exact_mod_cast hy
    have ht : (y : ℝ) ^ (1 / 32 : ℝ) ≤ N := by
      calc
        _ ≤ (y : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
        _ = (y : ℝ) := Real.rpow_one _
        _ ≤ N := hyN
    have harg : 32 * ((y : ℝ) ^ (1 / 32 : ℝ) + 6) ^ 2 ≤ (N : ℝ) ^ 5 := by
      have hs : (128 : ℝ) ≤ (N : ℝ) ^ 3 := by
        calc
          _ ≤ (9 : ℝ) ^ 3 := by norm_num
          _ ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hN9 3
      have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (N : ℝ))
      have ha : 32 * ((y : ℝ) ^ (1 / 32 : ℝ) + 6) ^ 2 ≤ 32 * (2 * N) ^ 2 := by
        gcongr
        linarith only [ht, hN9]
      nlinarith only [ha, hh]
    have hL : Real.log (32 * ((y : ℝ) ^ (1 / 32 : ℝ) + 6) ^ 2) ≤
        5 * Real.log N := by
      have hh := Real.log_le_log (by positivity) harg
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hyl : Real.log (y : ℝ) ≤ Real.log N := Real.log_le_log hy0 hyN
    have hh := numerical_principal_prefix_power_bound
      (show (9 : ℝ) ≤ y by exact_mod_cast hy9)
    simp only [Nat.floor_natCast, lambdaCharacterPrefix_one, coprimeLambdaPrefix_one_eq_psi,
      Complex.ofReal_natCast] at hh
    have he : ‖(Chebyshev.psi (y : ℝ) : ℂ) - (y : ℂ)‖ =
        |Chebyshev.psi (y : ℝ) - (y : ℝ)| := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [he] at hh
    have hcoef : 30000000000 + 200000000 *
        Real.log (32 * ((y : ℝ) ^ (1 / 32 : ℝ) + 6) ^ 2) + 60 * Real.log y ≤
        100000000000 * Real.log N := by nlinarith only [hL, hyl, hlog]
    calc
      _ ≤ _ := hh
      _ ≤ (100000000000 * Real.log N) * (N : ℝ) ^ (127 / 128 : ℝ) := by
        apply mul_le_mul hcoef (Real.rpow_le_rpow (by positivity) hyN (by norm_num))
          (by positivity) (by positivity)
      _ = _ := by ring
  · have hy8 : (y : ℝ) ≤ 8 := by exact_mod_cast (show y ≤ 8 by omega)
    have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    have he := Chebyshev.psi_le_const_mul_self hy0
    have hpsi0 : 0 ≤ Chebyshev.psi (y : ℝ) := Chebyshev.psi_nonneg _
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    have herr : |Chebyshev.psi (y : ℝ) - (y : ℝ)| ≤ 56 := by
      rw [abs_le]
      have hh := mul_le_mul_of_nonneg_right hlog4 hy0
      constructor <;> nlinarith only [he, hpsi0, hy8, hy0, hh]
    have hh := mul_le_mul hPow hlog (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    exact herr.trans (by nlinarith only [hh])

theorem numerical_principal_prefix_power {N : ℕ} (hN : 9 ≤ N) :
    principalLambdaPrefixMaxError N 1 ≤
      100000000000 * (N : ℝ) ^ (127 / 128 : ℝ) * Real.log N := by
  rw [principalLambdaPrefixMaxError_one_eq_psi_prefixMax]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact numerical_principal_pointwise_through hN y (by simpa using hy)

theorem numerical_principal_prefix {N D : ℕ} (hN : principalNumericalThreshold D ≤ N) :
    principalLambdaPrefixMaxError N 1 ≤ 100000000000 * N / Real.log N ^ D := by
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hh := numerical_principal_prefix_power hN9
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := log_pow_le_rpow_inv_explicit (k := D + 1) (m := 128)
    (by norm_num) (le_refl _) hN
  apply hh.trans
  apply (le_div_iff₀ (pow_pos hl D)).mpr
  have hpay := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 100000000000 * (N : ℝ) ^ (127 / 128 : ℝ) by positivity)
  have he : (N : ℝ) ^ (127 / 128 : ℝ) * (N : ℝ) ^ (1 / 128 : ℝ) = N := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [pow_succ] at hpay
  norm_num only [Nat.cast_ofNat] at hpay
  have he' : 100000000000 * (N : ℝ) ^ (127 / 128 : ℝ) * (N : ℝ) ^ (1 / 128 : ℝ) =
      100000000000 * N := by rw [mul_assoc, he]
  nlinarith only [hpay, he']

theorem numerical_global_principal_source {N D : ℕ} (hN : principalNumericalThreshold D ≤ N) :
    globalPartialSummationSource N ≤ principalNumericalConstant * N / Real.log N ^ D := by
  have hp := numerical_principal_prefix hN
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hP : 0 ≤ principalLambdaPrefixMaxError N 1 := by
    unfold principalLambdaPrefixMaxError
    have hm := Finset.max'_mem
      ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖))
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)
    rcases Finset.mem_image.mp hm with ⟨y, _hy, heq⟩
    rw [← heq]
    exact norm_nonneg _
  have hbudget : 1 ≤ (N : ℝ) / Real.log N ^ D := by
    have hh := log_pow_le_sqrt_explicit_of_le (show D ≤ 128 * (D + 1) by omega) hN
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    apply (le_div_iff₀ (pow_pos hl D)).mpr
    simpa only [one_mul] using hh.trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  unfold globalPartialSummationSource principalNumericalConstant
  have ha := mul_le_mul (numerical_discrete_abel_bound N) hp hP (by norm_num : (0 : ℝ) ≤ 4)
  have hl := numerical_global_li_discrete_bound N
  have ha' : discreteAbelAmplifierPrefixMax N * principalLambdaPrefixMaxError N 1 ≤
      400000000000 * ((N : ℝ) / Real.log N ^ D) := ha.trans_eq (by ring)
  calc
    _ ≤ 400000000000 * ((N : ℝ) / Real.log N ^ D) + 4 := add_le_add ha' hl
    _ ≤ 500000000000 * ((N : ℝ) / Real.log N ^ D) := by nlinarith only [hbudget]
    _ = _ := by ring

#print axioms numerical_global_principal_source
end ChenEffective

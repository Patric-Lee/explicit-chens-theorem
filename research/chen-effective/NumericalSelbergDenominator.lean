import NumericalSelbergMoments
import NumericalRealLogBounds

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory
open LiuWeight SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] logPowerCutoff mertensProductThreshold

private opaque selbergEulerExponentCertificate : {k : ℕ // k = 10^80} := ⟨10^80, rfl⟩

def selbergEulerExponent : ℕ := selbergEulerExponentCertificate.1

theorem selbergEulerExponent_eq : selbergEulerExponent = 10^80 :=
  selbergEulerExponentCertificate.2

@[irreducible] def selbergDenominatorThreshold : ℕ :=
  max selbergDivisorThreshold (3^selbergEulerExponent)

theorem selbergDenominatorThreshold_eq :
    selbergDenominatorThreshold = max selbergDivisorThreshold (3^(10^80)) := by
  rw [selbergDenominatorThreshold, selbergEulerExponent_eq]

theorem numerical_selberg_euler_error {N : ℕ} (hN : selbergDenominatorThreshold ≤ N)
    (hEven : Even N) :
    (2*liuSelbergAbsoluteLogMoment N+liuSelbergAbsoluteMass N)*liuSingularSeries N/
      Real.log (N : ℝ) ≤ 1/1000000000000 := by
  have hn := hN
  unfold selbergDenominatorThreshold at hn
  obtain ⟨hDiv,hPow⟩ := max_le_iff.mp hn
  have hX := log_ge_power_three hPow
  rw [selbergEulerExponent_eq] at hX
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hX
  have hX0 : 0 < Real.log (N : ℝ) := by linarith only [hX]
  obtain ⟨_,hcut,_⟩ := numerical_selberg_divisor_logs hDiv
  have hlog := real_log_power_cutoff_log hcut
  norm_num only [Nat.cast_ofNat] at hlog
  have hlog1 : 1 ≤ Real.log (Real.log (N : ℝ)) := by linarith only [hlog]
  have hroot : (10^40 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
    apply (Real.le_sqrt (by norm_num) hX0.le).mpr
    norm_num only [← pow_mul]
    exact hX
  have hp := real_log_pow_le_sqrt (k := 6) hcut
  have hNum := numerical_selberg_euler_numerator hDiv hEven
  have hpow : (1+Real.log (Real.log (N : ℝ)))^6 ≤ 64*Real.sqrt (Real.log (N : ℝ)) := by
    calc
      _ ≤ (2*Real.log (Real.log (N : ℝ)))^6 := by gcongr; linarith only [hlog1]
      _ = 64*Real.log (Real.log (N : ℝ))^6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  apply (div_le_iff₀ hX0).mpr
  have hh := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 10^24 by positivity)
  have hpay : (10^24 : ℝ)*64 ≤ Real.sqrt (Real.log (N : ℝ))/1000000000000 := by
    linarith only [hroot]
  have hpay' := mul_le_mul_of_nonneg_right hpay (Real.sqrt_nonneg (Real.log (N : ℝ)))
  have hs := Real.sq_sqrt hX0.le
  nlinarith only [hNum,hh,hpay',hs]

theorem numerical_selberg_log_floor {N : ℕ} (hN : 256 ≤ N) {β : ℝ} (hβ : 1/8 ≤ β) :
    β*Real.log (N : ℝ)-Real.log 2 ≤ Real.log (⌊(N : ℝ)^β⌋₊ : ℝ) ∧
      2 ≤ ⌊(N : ℝ)^β⌋₊ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow2 : (2 : ℝ) ≤ (N : ℝ)^(1/8 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2) hN0.le (by norm_num : (0 : ℝ) < 8)).mpr
    norm_num
    exact_mod_cast hN
  have hpow := hpow2.trans (Real.rpow_le_rpow_of_exponent_le hN1 hβ)
  have hfloor : (N : ℝ)^β/2 ≤ (⌊(N : ℝ)^β⌋₊ : ℝ) :=
    (by linarith only [hpow] : (N : ℝ)^β/2 ≤ (N : ℝ)^β-1).trans (Nat.sub_one_lt_floor _).le
  have hlog := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hN0 β) (by norm_num)) hfloor
  rw [Real.log_div (Real.rpow_pos_of_pos hN0 β).ne' (by norm_num),Real.log_rpow hN0] at hlog
  exact ⟨hlog,Nat.le_floor hpow⟩

theorem numerical_selberg_denominator {N : ℕ} (hN : selbergDenominatorThreshold ≤ N)
    (hEven : Even N) :
    Real.log N/((8+liuM1Delta)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon := by
  have hn := hN
  unfold selbergDenominatorThreshold at hn
  have hX := log_ge_power_three ((le_max_right _ _).trans hn)
  rw [selbergEulerExponent_eq] at hX
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hX
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hX
  have hX0 : 0 < Real.log (N : ℝ) := by linarith only [hX]
  have hNlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by exact_mod_cast hNpos)
  have hN256 : 256 ≤ N := by exact_mod_cast (by linarith only [hX,hNlog] : (256 : ℝ) ≤ N)
  have hβ : (1/8 : ℝ) ≤ 1/4-squareEpsilon/2 := by norm_num [squareEpsilon,squareEpsilonDenominator]
  obtain ⟨hlogR,hR⟩ := numerical_selberg_log_floor hN256 hβ
  change (1/4-squareEpsilon/2)*Real.log (N : ℝ)-Real.log 2 ≤ Real.log (paperQSourceCutoff N squareEpsilon) at hlogR
  change 2 ≤ paperQSourceCutoff N squareEpsilon at hR
  have hError := abs_liuSelbergArithmetic_sum_Icc_sub_log_main_le_uniform_reduction
    hEven hNpos hR
  rw [← liuSelbergDenominator_eq_sum_Icc hEven (by omega : 1 ≤ paperQSourceCutoff N squareEpsilon)] at hError
  have hLow := (abs_le.mp hError).1
  have hS := liuSingularSeries_pos N
  have hpay := (div_le_iff₀ hX0).mp (numerical_selberg_euler_error hN hEven)
  have hmain : liuSelbergDenominator N squareEpsilon*liuSingularSeries N ≥
      Real.log (paperQSourceCutoff N squareEpsilon)/2-
        (2*liuSelbergAbsoluteLogMoment N+liuSelbergAbsoluteMass N)*liuSingularSeries N := by
    have hh := mul_le_mul_of_nonneg_right hLow hS.le
    have he : Real.log (paperQSourceCutoff N squareEpsilon)/(2*liuSingularSeries N)*liuSingularSeries N =
        Real.log (paperQSourceCutoff N squareEpsilon)/2 := by field_simp
    nlinarith only [hh,he]
  have h8 : 0 < 8+liuM1Delta := by norm_num [liuM1Delta]
  apply (div_le_iff₀ (mul_pos h8 hS)).mpr
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  norm_num only [liuM1Delta,squareEpsilon,squareEpsilonDenominator,Nat.cast_ofNat] at *
  nlinarith only [hmain,hpay,hlogR,hX,hlog2]

#print axioms numerical_selberg_denominator
end ChenEffective

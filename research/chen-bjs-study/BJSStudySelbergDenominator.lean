import BJSStudyLogGate
import BJSStudySelbergMoments
import NumericalSelbergDenominator

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] logPowerCutoff

@[irreducible] def bjsStudyDenominatorThreshold : ℕ :=
  max bjsStudyDivisorThreshold (3^(10^80))

theorem bjsStudy_selberg_euler_error {N : ℕ} (hN : bjsStudyDenominatorThreshold ≤ N)
    (hEven : Even N) :
    (2*liuSelbergAbsoluteLogMoment N+liuSelbergAbsoluteMass N)*liuSingularSeries N/
      Real.log (N : ℝ) ≤ 1/1000000000000 := by
  have hn := hN
  unfold bjsStudyDenominatorThreshold at hn
  obtain ⟨hDiv,hPow⟩ := max_le_iff.mp hn
  have hX := log_ge_power_three hPow
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hX
  have hXpow : (10:ℝ)^80 ≤ Real.log (N:ℝ) := by norm_num only [Nat.reducePow] at *; exact hX
  have hX0 : 0 < Real.log (N : ℝ) := by linarith only [hX]
  have hlog : 1 ≤ Real.log (Real.log (N:ℝ)) := by
    apply one_le_log_three.trans
    exact Real.log_le_log (by norm_num) ((by norm_num : (3:ℝ) ≤ 10^80).trans hXpow)
  have hlog1 : 1 ≤ Real.log (Real.log (N : ℝ)) := by linarith only [hlog]
  have hroot : (10^40 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
    apply (Real.le_sqrt (by norm_num) hX0.le).mpr
    norm_num only [← pow_mul]
    exact hX
  have hp := bjsStudy_log_six_sqrt hXpow
  have hNum := bjsStudy_selberg_euler_numerator hDiv hEven
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

theorem bjsStudy_selberg_denominator {N : ℕ} (hN : bjsStudyDenominatorThreshold ≤ N)
    (hEven : Even N) :
    Real.log N/((8+liuM1Delta)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon := by
  have hn := hN
  unfold bjsStudyDenominatorThreshold at hn
  have hX := log_ge_power_three ((le_max_right _ _).trans hn)
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hX
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hX
  have hXpow : (10:ℝ)^80 ≤ Real.log (N:ℝ) := by norm_num only [Nat.reducePow] at *; exact hX
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
  have hpay := (div_le_iff₀ hX0).mp (bjsStudy_selberg_euler_error hN hEven)
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


#print axioms bjsStudy_selberg_denominator
end ChenEffective

import NumericalSelbergRoot
import NumericalSelbergDivisorLog

noncomputable section
namespace ChenEffective
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory
open LiuWeight SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem numerical_selberg_universal_euler : liuUniversalAbsEuler ≤ Real.exp 29 := by
  rw [← tsum_abs_liuSelbergCorrection_two_eq_liuUniversalAbsEuler]
  apply (Summable.tsum_le_tsum _
    (summable_abs_liuSelbergCorrection (N := 2) (by norm_num) (by norm_num))
    numerical_selberg_root_summable_mass.1).trans numerical_selberg_root_mass
  intro n
  by_cases hn : n=0
  · subst n; simp [selbergRootWeight]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hr : 1 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hn1)
    exact le_mul_of_one_le_right (abs_nonneg _) hr

theorem numerical_selberg_universal_moment : liuUniversalAbsLogMoment ≤ 4*Real.exp 29 := by
  have hlog (n : ℕ) : Real.log (n : ℝ) ≤ 4*Real.sqrt (Real.sqrt n) := by
    have hh := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1/4)
    have he : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ)^(1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    rw [he]
    linarith only [hh]
  have hh : liuUniversalAbsLogMoment ≤ ∑' n, 4*selbergRootWeight n := by
    apply Summable.tsum_le_tsum _ summable_liuUniversalAbsLogMoment
      (numerical_selberg_root_summable_mass.1.mul_left 4)
    intro n
    simpa only [selbergRootWeight,mul_left_comm] using
      mul_le_mul_of_nonneg_left (hlog n) (abs_nonneg (liuSelbergCorrection 2 n))
  rw [tsum_mul_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left numerical_selberg_root_mass (by norm_num))

theorem numerical_selberg_euler_numerator {N : ℕ} (hN : selbergDivisorThreshold ≤ N)
    (hEven : Even N) :
    (2*liuSelbergAbsoluteLogMoment N+liuSelbergAbsoluteMass N)*liuSingularSeries N ≤
      10^24*(1+Real.log (Real.log (N : ℝ)))^6 := by
  obtain ⟨_,_,hl⟩ := numerical_selberg_divisor_logs hN
  have hNpos : 0 < N := by
    by_contra hh
    have he : N=0 := by omega
    subst N
    norm_num at hl
  let u := 1+Real.log (Real.log (N : ℝ))
  have hu : 1 ≤ u := by
    have hh : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith only [hl])
    dsimp [u]; linarith only [hh]
  have hE := numerical_selberg_universal_euler
  have hM := numerical_selberg_universal_moment
  have hL := numerical_selberg_divisor_product hN
  have hD := numerical_selberg_divisor_logsum hN
  have hLn := (liuPrimeDivisorProduct_pos N).le
  have hDn : 0 ≤ liuPrimeDivisorLogSum N := by
    unfold liuPrimeDivisorLogSum
    exact sum_nonneg fun _ _ => div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hS := liuSingularSeries_le_liuPrimeDivisorProduct_cube N
  have hmass := tsum_abs_liuSelbergCorrection_le_uniform hEven hNpos
  have hmoment := liuSelbergAbsoluteLogMoment_le_uniform hEven hNpos
  have hmass' : liuSelbergAbsoluteMass N ≤ Real.exp 29*(54*u) := by
    exact hmass.trans (mul_le_mul hE hL hLn (Real.exp_pos _).le)
  have hmoment' : liuSelbergAbsoluteLogMoment N ≤
      (54*u)*(4*Real.exp 29+Real.exp 29*(3*u^2)) := by
    exact hmoment.trans (mul_le_mul hL (add_le_add hM
      (mul_le_mul hE hD hDn (Real.exp_pos _).le))
        (add_nonneg liuUniversalAbsLogMoment_nonneg (mul_nonneg liuUniversalAbsEuler_nonneg hDn))
        (by positivity))
  have hS' : liuSingularSeries N ≤ (54*u)^3 := hS.trans (pow_le_pow_left₀ hLn hL 3)
  have hu2 : 1 ≤ u^2 := one_le_pow₀ hu
  have hcoeff : 15*Real.exp 29*54^4 ≤ (10^24 : ℝ) := by
    have he1 : Real.exp (1 : ℝ) ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    have he29 : Real.exp (29 : ℝ) ≤ (3 : ℝ)^29 := by
      rw [show (29 : ℝ) = (29 : ℕ)*1 by norm_num,Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le he1 29
    calc
      _ ≤ 15*(3 : ℝ)^29*54^4 := by gcongr
      _ ≤ _ := by norm_num
  calc
    _ ≤ (2*((54*u)*(4*Real.exp 29+Real.exp 29*(3*u^2)))+Real.exp 29*(54*u))*
        (54*u)^3 := mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left hmoment' (by norm_num)) hmass')
          hS' (liuSingularSeries_pos N).le (by positivity)
    _ ≤ (15*Real.exp 29*54^4)*u^6 := by
      have hh := mul_le_mul_of_nonneg_left hu2
        (show 0 ≤ 9*Real.exp 29*54^4*u^4 by positivity)
      nlinarith only [hh]
    _ ≤ (10^24 : ℝ)*u^6 := mul_le_mul_of_nonneg_right hcoeff (by positivity)

#print axioms numerical_selberg_euler_numerator
end ChenEffective

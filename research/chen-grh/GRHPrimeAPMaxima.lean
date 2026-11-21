import GRHAPMaxima
import NumericalPrincipalElementary

/-! Transport to the production maximal prime-count error centered at the
true logarithmic integral. Abel amplification and higher prime powers are
paid explicitly. -/
namespace ChenEffective.GRH
open Real
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem prime_AP_max_numerical {N q : ℕ} (hN : 2 ≤ N)
    (hL : (10:ℝ) ≤ Real.log N) (hq : 0 < q) :
    MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
      (10^16:ℝ)*(Real.log q+Real.log N)^3*(N:ℝ)^(501/1000:ℝ) := by
  let A := Real.log (q:ℝ)+Real.log N
  let Y := (N:ℝ)^(501/1000:ℝ)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  have hA : 10 ≤ A := by dsimp only [A]; linarith only [hL,hlq]
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hLA : Real.log (N:ℝ) ≤ A := by dsimp only [A]; linarith only [hlq]
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 (by norm_num)
  have hY0 : 0 ≤ Y := by linarith only [hY1]
  have hroot : Real.sqrt (N:ℝ) ≤ Y := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hsqrt : (((N.sqrt+1:ℕ):ℝ)) ≤ 2*Y := by
    have hh := natSqrt_cast_le_realSqrt N
    push_cast
    linarith only [hh,hroot,hY1]
  have hlog : (Nat.log2 N+1:ℝ) ≤ 3*A := by
    have hh := natLog2_cast_le_two_log hN
    linarith only [hh,hLA,hA]
  have hpow : A^2*Y ≤ A^3*Y := by
    apply mul_le_mul_of_nonneg_right _ hY0
    nlinarith only [mul_nonneg (sq_nonneg A) (show 0 ≤ A-1 by linarith only [hA])]
  have hcorr : lambdaPrimePowerCorrectionPrefixMaxError N q ≤ 6*A^3*Y := by
    calc
      _ ≤ (((N.sqrt+1:ℕ):ℝ))*(Nat.log2 N+1:ℝ)*Real.log (N:ℝ) :=
        lambdaPrimePowerCorrectionPrefixMaxError_le_explicit N q
      _ ≤ (2*Y)*(3*A)*A := by gcongr
      _ = 6*(A^2*Y) := by ring
      _ ≤ _ := by nlinarith only [hpow]
  have hsum : lambdaAPPrefixMaxError N q+lambdaPrimePowerCorrectionPrefixMaxError N q ≤
      ((10^15:ℝ)+6)*A^3*Y := by
    have hh := chebyshev_AP_max_numerical hN hL hq
    change lambdaAPPrefixMaxError N q ≤ (10^15:ℝ)*A^3*Y at hh
    nlinarith only [hh,hcorr]
  have hprod : discreteAbelAmplifierPrefixMax N*
      (lambdaAPPrefixMaxError N q+lambdaPrimePowerCorrectionPrefixMaxError N q) ≤
      4*(((10^15:ℝ)+6)*A^3*Y) := by
    calc
      _ ≤ discreteAbelAmplifierPrefixMax N*(((10^15:ℝ)+6)*A^3*Y) :=
        mul_le_mul_of_nonneg_left hsum (discreteAbelAmplifierPrefixMax_nonneg N)
      _ ≤ _ := mul_le_mul_of_nonneg_right (numerical_discrete_abel_bound N) (by positivity)
  have hφ1 : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hi : (q.totient:ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hφ1
  have hglobal : (q.totient:ℝ)⁻¹*globalChebyshevToLiSourcePrefixMaxError N ≤ 4 := by
    calc
      _ ≤ (q.totient:ℝ)⁻¹*4 := mul_le_mul_of_nonneg_left
        (numerical_global_li_discrete_bound N) (by positivity)
      _ ≤ _ := by nlinarith only [hi]
  have hbudget : (1:ℝ) ≤ A^3*Y := by
    calc
      1 = (1:ℝ)*1 := by ring
      _ ≤ _ := mul_le_mul (one_le_pow₀ (by linarith only [hA] : (1:ℝ)≤A)) hY1
        (by norm_num) (by positivity)
  change _ ≤ (10^16:ℝ)*A^3*Y
  have hh := standardPrimeAPPrefixMaxError_le_lambda_bridge (N := N) hq
  nlinarith only [hh,hprod,hglobal,hbudget]

#print axioms prime_AP_max_numerical
end ChenEffective.GRH

import BJSStudyLower
import BJSStudySelbergDenominator
import NumericalNSquare

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LiuWeight SingularSeries SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff

private theorem bjsStudy_pow_mono (a b : ℕ) (h : a ≤ b) : (3 : ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

theorem bjsStudy_power_cap : 3^primePairPowerExponent ≤ bjsStudyGeometryThreshold := by
  have hh : primePairPowerExponent ≤ 10^80 := le_of_eq primePairPowerExponent_eq
  have hcap : bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  exact (bjsStudyCap_preSieve_fixed_power hh).trans (hcap.trans bjsStudy_finite_cap)

theorem bjsStudy_denominator_cap : bjsStudyDenominatorThreshold ≤ bjsStudyGeometryThreshold := by
  have hM : bjsStudyMertensEndpoint ≤ (3 : ℕ)^2700 :=
    (le_of_eq bjsStudyMertensEndpoint_eq).trans (bjsStudy_pow_mono 30 2700 (by norm_num))
  have hE : (10 : ℕ)^80 ≤ (3 : ℕ)^2700 :=
    (show (10 : ℕ)^80 ≤ 3^171 by norm_num).trans
      (bjsStudy_pow_mono 171 2700 (by norm_num))
  calc
    bjsStudyDenominatorThreshold =
        max (3^bjsStudyMertensEndpoint) (3^(10^80)) := by
      unfold bjsStudyDenominatorThreshold bjsStudyDivisorThreshold
      rfl
    _ ≤ 3^(3^2700) := max_le
      (bjsStudy_pow_mono bjsStudyMertensEndpoint (3^2700) hM)
      (bjsStudy_pow_mono (10^80) (3^2700) hE)
    _ = bjsStudyGeometryThreshold := bjsStudyGeometryThreshold_eq.symm

theorem bjsStudy_triple_bound {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/log (N : ℝ)^2+
        (numericalTripleErrorCap : ℝ)*N/log (N : ℝ)^3 := by
  have hSA : squareAnalyticThreshold ≤ N := (numerical_square_analytic_cap.trans bjsStudy_power_cap).trans hN
  have hres : tripleResidualThreshold ≤ 3^primePairPowerExponent := by
    unfold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hPair : primePairThreshold ≤ N :=
    (le_max_left primePairThreshold ((mediumPrimeBudget+2)^10)).trans
      (bjsStudyCap_preSieve_prime_sum.trans (bjsStudy_finite_cap.trans hN))
  exact numerical_triple_from_main_components N
    (max_le hSA ((hres.trans bjsStudy_power_cap).trans hN)) hEven
    (bjsStudy_selberg_denominator (bjsStudy_denominator_cap.trans hN) hEven)
    (numerical_prime_pair_main hPair)

#print axioms bjsStudy_triple_bound
end ChenEffective

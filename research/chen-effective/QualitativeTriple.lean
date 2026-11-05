import QualitativeLower
import QualitativeSelbergDenominator
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

private theorem qualitative_pow_mono (a b : ℕ) (h : a ≤ b) : (3 : ℕ)^a ≤ 3^b :=
  Nat.pow_le_pow_right (by norm_num) h

theorem qualitative_power_cap : 3^primePairPowerExponent ≤ qualitativeGeometryThreshold := by
  have hh : primePairPowerExponent ≤ 10^100 := by rw [primePairPowerExponent_eq]; norm_num
  have hcap : preSieveFiniteCap ≤ preSieveFiniteCap^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  exact (preSieve_fixed_power hh).trans (hcap.trans qualitative_finite_cap)

theorem qualitative_denominator_cap : qualitativeDenominatorThreshold ≤ qualitativeGeometryThreshold := by
  have hM : qualitativeMertensEndpoint ≤ (3 : ℕ)^6000 :=
    (le_of_eq qualitativeMertensEndpoint_eq).trans (qualitative_pow_mono 4096 6000 (by norm_num))
  have h6 : logPowerCutoff 6 ≤ (3 : ℕ)^6000 := by
    unfold logPowerCutoff
    exact qualitative_pow_mono _ _ (by norm_num)
  have hE : (10 : ℕ)^80 ≤ (3 : ℕ)^6000 :=
    (by norm_num : (10 : ℕ)^80 ≤ (3 : ℕ)^200).trans (qualitative_pow_mono 200 6000 (by norm_num))
  calc
    qualitativeDenominatorThreshold =
        max (3^(max qualitativeMertensEndpoint (logPowerCutoff 6))) (3^(10^80)) := by
      unfold qualitativeDenominatorThreshold qualitativeDivisorThreshold
      rfl
    _ ≤ 3^(3^6000) := max_le
      (qualitative_pow_mono _ _ (max_le hM h6)) (qualitative_pow_mono _ _ hE)
    _ = qualitativeGeometryThreshold := qualitativeGeometryThreshold_eq.symm

theorem qualitative_triple_bound {N : ℕ} (hN : qualitativeGeometryThreshold ≤ N) (hEven : Even N) :
    correctedChenTriplePenalty N ≤
      (3.94033 : ℝ)*liuSingularSeries N*N/log (N : ℝ)^2+
        (numericalTripleErrorCap : ℝ)*N/log (N : ℝ)^3 := by
  have hSA : squareAnalyticThreshold ≤ N := (numerical_square_analytic_cap.trans qualitative_power_cap).trans hN
  have hres : tripleResidualThreshold ≤ 3^primePairPowerExponent := by
    unfold tripleResidualThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hPair : primePairThreshold ≤ N :=
    (le_max_left primePairThreshold ((mediumPrimeBudget+2)^10)).trans
      (preSieve_prime_sum.trans (qualitative_finite_cap.trans hN))
  exact numerical_triple_from_main_components N
    (max_le hSA ((hres.trans qualitative_power_cap).trans hN)) hEven
    (qualitative_selberg_denominator (qualitative_denominator_cap.trans hN) hEven)
    (numerical_prime_pair_main hPair)

#print axioms qualitative_triple_bound
end ChenEffective

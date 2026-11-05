import QualitativeAggregate
import NumericalPreSieveCutoff

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem qualitative_finite_cap : preSieveFiniteCap^20 ≤ qualitativeGeometryThreshold := by
  rw [qualitativeGeometryThreshold_eq]
  unfold preSieveFiniteCap
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (3 : ℕ)^400 := by rw [preSieveFiniteExponent_eq]; norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem qualitative_endpoint {N : ℕ} (hN : qualitativeGeometryThreshold ≤ N) :
    lowerEndpointThreshold ≤ N := by
  have hh : preSieveFiniteCap ≤ preSieveFiniteCap^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  exact preSieve_lower_endpoint.trans (hh.trans (qualitative_finite_cap.trans hN))

/-- Existence needs room in the final margin, rather than near-asymptotic
accuracy in each individual sieve estimate. -/
theorem qualitative_weighted_lower {N : ℕ} (hN : qualitativeGeometryThreshold ≤ N)
    (hEven : Even N) :
    (2.3 : ℝ)*SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2 ≤ jurkatRichertWeightedCount N := by
  have h20 : preSieveFiniteCap^20 ≤ N := qualitative_finite_cap.trans hN
  have h1 : preSieveFiniteCap ≤ N :=
    (show preSieveFiniteCap ≤ preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)).trans h20
  have hBase := qualitative_base_candidates hN
    ((preSieve_source_mass (by norm_num [baseCandidateBudget])).trans h20)
    (preSieve_base_distribution.trans h1) hEven
  have hUpper := qualitative_medium_prime_aggregate hN (preSieve_prime_sum.trans h20)
    ((preSieve_upper_mass (by norm_num [mediumPrimeBudget])).trans h20)
    (preSieve_varying_threshold_cap.trans h1) hEven
  have hMain := jurkatRichert_mainCoefficient_ge_twoPoint6408
    jurkatRichertJ jurkatRichertK jurkatRichert_integralEstimate
  let M := SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hMainM := mul_le_mul_of_nonneg_right hMain hM
  have hSource : (2.30005 : ℝ)*M ≤ jurkatRichertSourceWeightedCount N := by
    rw [jurkatRichertSourceWeightedCount_eq]
    change (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/40)*M ≤ _ at hBase
    change _ ≤ (jurkatRichertQ1MainCoefficient jurkatRichertK+1/2)*M at hUpper
    nlinarith only [hBase,hUpper,hMainM,hM]
  have hEnd := qualitative_endpoint hN
  have hbig : 2^110 < N := by unfold lowerEndpointThreshold at hEnd; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := numerical_lower_endpoint_loss hEnd
  have he' : 60*(N : ℝ)^(9/10 : ℝ) ≤ (1/20000 : ℝ)*M := by
    convert he using 1
    dsimp [M]
    ring
  have hn : 0 ≤ (N : ℝ)^(9/10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    _ = (2.3 : ℝ)*M := by dsimp [M]; ring
    _ ≤ _ := by nlinarith only [hb,hp,he',hSource,hn]

#print axioms qualitative_weighted_lower
end ChenEffective

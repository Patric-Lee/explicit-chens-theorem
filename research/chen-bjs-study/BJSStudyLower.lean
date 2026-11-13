import BJSStudyAggregate
import BJSStudyFiniteCap

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory LinearSieve SwitchingPrinciple
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

private theorem finite_cap_power_bound {j : ℕ}
    (hj : 10^80*20 ≤ j) : bjsStudyCap_preSieveFiniteCap^20 ≤ 3^j := by
  unfold bjsStudyCap_preSieveFiniteCap
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  simpa only [bjsStudyCap_preSieveFiniteExponent_eq] using hj

theorem bjsStudy_finite_cap : bjsStudyCap_preSieveFiniteCap^20 ≤ bjsStudyGeometryThreshold := by
  rw [bjsStudyGeometryThreshold_eq]
  exact finite_cap_power_bound (by norm_num : 10^80*20 ≤ (3 : ℕ)^171)

theorem bjsStudy_endpoint {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N) :
    lowerEndpointThreshold ≤ N := by
  have hh : bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 := by
    simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  exact bjsStudyCap_preSieve_lower_endpoint.trans (hh.trans (bjsStudy_finite_cap.trans hN))

/-- Existence needs room in the final margin, rather than near-asymptotic
accuracy in each individual sieve estimate. -/
theorem bjsStudy_weighted_lower {N : ℕ} (hN : bjsStudyGeometryThreshold ≤ N)
    (hEven : Even N) :
    bjsStudyBudget.weighted*SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2 ≤ jurkatRichertWeightedCount N := by
  have h20 : bjsStudyCap_preSieveFiniteCap^20 ≤ N := bjsStudy_finite_cap.trans hN
  have h1 : bjsStudyCap_preSieveFiniteCap ≤ N :=
    (show bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 20 by norm_num)).trans h20
  have hBase := bjsStudy_base_candidates hN
    ((bjsStudyCap_preSieve_source_mass (by norm_num [baseCandidateBudget])).trans h20)
    (bjsStudyCap_preSieve_base_distribution.trans h1) hEven
  have hUpper := bjsStudy_medium_prime_aggregate hN (bjsStudyCap_preSieve_prime_sum.trans h20)
    ((bjsStudyCap_preSieve_upper_mass (by norm_num [mediumPrimeBudget])).trans h20)
    (bjsStudyCap_preSieve_varying_threshold_cap.trans h1) hEven
  let M := SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2
  have hEnd := bjsStudy_endpoint hN
  have hbig : 2^110 < N := by unfold lowerEndpointThreshold at hEnd; omega
  have hb := jurkatRichertSourceWeightedCount_sub_boundary_le_distinct N hbig hEven
  have hp := jurkatRichertDistinctWeightedCount_sub_proper_le N hbig hEven
  have he := numerical_lower_endpoint_loss hEnd
  have he' : 60*(N : ℝ)^(9/10 : ℝ) ≤ (1/20000 : ℝ)*M := by
    convert he using 1
    dsimp [M]
    ring
  have hn : 0 ≤ (N : ℝ)^(9/10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hboundary : jurkatRichertSourceWeightedCount N ≤ jurkatRichertWeightedCount N+
      bjsStudyBudget.endpointLoss*M := by
    norm_num only [bjsStudyBudget] at *
    nlinarith only [hb,hp,he',hn]
  have hh := chen_budget_weighted bjsStudyBudget hBase hUpper hboundary
  convert hh using 1
  ring

#print axioms bjsStudy_weighted_lower
end ChenEffective

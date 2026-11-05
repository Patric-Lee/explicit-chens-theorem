import ChenRouteSource
import BJSStudyChen

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem bjs_route_base (n : ℕ) (hn : bjsStudyGeometryThreshold ≤ n) (he : Even n) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/20)*routeSourceScale n ≤
      ((jurkatRichertSourceCandidates n).card:ℝ) := by
  have h20 := bjsStudy_finite_cap.trans hn
  have h1 : bjsStudyCap_preSieveFiniteCap ≤ n :=
    (show bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hh := bjsStudy_base_candidates hn
    ((bjsStudyCap_preSieve_source_mass (by norm_num [baseCandidateBudget])).trans h20)
    (bjsStudyCap_preSieve_base_distribution.trans h1) he
  simpa only [routeSourceScale,mul_div_assoc,mul_assoc] using hh

theorem bjs_route_medium (n : ℕ) (hn : bjsStudyGeometryThreshold ≤ n) (he : Even n) :
    jurkatRichertSourceMediumPrimeAggregate n ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+113/100)*routeSourceScale n := by
  have h20 := bjsStudy_finite_cap.trans hn
  have h1 : bjsStudyCap_preSieveFiniteCap ≤ n :=
    (show bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hh := bjsStudy_medium_prime_aggregate hn (bjsStudyCap_preSieve_prime_sum.trans h20)
    ((bjsStudyCap_preSieve_upper_mass (by norm_num [mediumPrimeBudget])).trans h20)
    (bjsStudyCap_preSieve_varying_threshold_cap.trans h1) he
  simpa only [routeSourceScale,mul_div_assoc,mul_assoc] using hh

theorem bjs_route_nine {n : ℕ} (hn : bjsStudyGeometryThreshold ≤ n) : 9 ≤ n := by
  have hh : 2^110+1 ≤ n := (le_max_left _ _).trans (bjsStudy_endpoint hn)
  omega

theorem bjs_route_triple (n : ℕ) (hn : bjsStudyGeometryThreshold ≤ n) (he : Even n) :
    correctedChenTriplePenalty n ≤
      (3.94033+routeSourceTripleErrors.eval n)*routeSourceScale n := by
  have ht := bjsStudy_triple_bound hn he
  have hr := route_source_triple_error (bjs_route_nine hn)
  dsimp [routeSourceScale] at hr ⊢
  simp only [mul_div_assoc,mul_assoc] at ht hr ⊢
  nlinarith only [ht,hr]

def bjsRoute : ChenRoute routeSourceModel :=
  routeSourceOfBounds bjsStudyGeometryThreshold bjsStudyGeometryThreshold
    lowerEndpointThreshold bjsStudyGeometryThreshold (1/20) (113/100)
    (by norm_num) (by norm_num) routeSourceTripleErrors
    bjs_route_base bjs_route_medium
    (fun _ hn he => route_source_boundary hn he) bjs_route_triple

theorem bjs_route_threshold : bjsRoute.threshold ≤ bjsStudyGeometryThreshold := by
  change max 9 (max (max bjsStudyGeometryThreshold bjsStudyGeometryThreshold)
    (max lowerEndpointThreshold bjsStudyGeometryThreshold)) ≤ bjsStudyGeometryThreshold
  exact max_le (bjs_route_nine le_rfl)
    (max_le (max_le le_rfl le_rfl) (max_le (bjsStudy_endpoint le_rfl) le_rfl))

theorem bjs_route_error_payment {n : ℕ} (hn : bjsStudyGeometryThreshold ≤ n) :
    routeSourceTripleErrors.eval n ≤ 1/100 := by
  have h20 := bjsStudy_finite_cap.trans hn
  have h1 : bjsStudyCap_preSieveFiniteCap ≤ n :=
    (show bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hpow : 3^(200*numericalTripleErrorCap+1) ≤ n :=
    (bjsStudyCap_preSieve_fixed_power (by norm_num [numericalTripleErrorCap])).trans h1
  have hl := log_ge_power_three hpow
  have hl0 : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n from lt_of_lt_of_le (by norm_num) (bjs_route_nine hn)))
  dsimp [routeSourceTripleErrors,ChenErrorBreakdown.eval,ChenErrorEnvelope.logPower,ChenErrorEnvelope.zero]
  simp only [add_zero,zero_add,pow_one]
  apply (div_le_iff₀ hl0).mpr
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hl
  nlinarith only [hl]

theorem bjs_route_margin (n : ℕ) :
    0.055585-routeSourceTripleErrors.eval n/2 ≤ bjsRoute.margin n := by
  have hh := route_source_margin_floor bjsStudyGeometryThreshold bjsStudyGeometryThreshold
    lowerEndpointThreshold bjsStudyGeometryThreshold (1/20) (113/100)
    (by norm_num) (by norm_num) routeSourceTripleErrors
    bjs_route_base bjs_route_medium
    (fun _ hn he => route_source_boundary hn he) bjs_route_triple n
  convert hh using 1 <;> first | rfl | ring

def bjsRouteCertificate : ChenRouteCertificate bjsRoute where
  cutoff := bjsStudyGeometryThreshold
  thresholds_paid := bjs_route_threshold
  margin_pos := by
    intro n hn _he
    have hm := bjs_route_margin n
    have he := bjs_route_error_payment hn
    linarith only [hm,he]

theorem bjs_route_original : Goldbach.ChenTheorem :=
  chen_route_original bjsRouteCertificate

def bjsPaidTriple : ChenUpperProducer routeSourceModel.scale routeSourceModel.triple where
  threshold := bjsStudyGeometryThreshold
  main := fun _ => 3.94033
  errors := {analytic:=ChenErrorEnvelope.constant (1/100) (by norm_num)}
  bound := by
    intro n hn he
    have ht := bjs_route_triple n hn he
    have hh := mul_le_mul_of_nonneg_right (bjs_route_error_payment hn)
      (routeSourceModel.scale_pos n (bjs_route_nine hn) he).le
    dsimp [ChenErrorBreakdown.eval,ChenErrorEnvelope.constant,ChenErrorEnvelope.zero]
    simp only [add_zero,zero_add]
    dsimp [routeSourceModel] at hh ⊢
    nlinarith only [ht,hh]

def bjsPaidRoute : ChenRoute routeSourceModel := bjsRoute.withTriple bjsPaidTriple

/-- At valid endpoints the variable remainder is at least as informative as
its old constant allocation. Both remain interchangeable actual producers. -/
theorem bjs_route_dominates_paid {n : ℕ} (hn : bjsStudyGeometryThreshold ≤ n) :
    bjsPaidRoute.margin n ≤ bjsRoute.margin n := by
  have hh := bjs_route_error_payment hn
  simp only [bjsPaidRoute,ChenRoute.withTriple,ChenRoute.margin,
    ChenLowerProducer.coefficient,ChenUpperProducer.coefficient,bjsPaidTriple,bjsRoute,
    routeSourceOfBounds,routeSourceErrors,routeSourceBoundaryErrors,routeSourceTripleErrors,
    ChenErrorBreakdown.eval,ChenErrorEnvelope.constant,ChenErrorEnvelope.logPower,
    ChenErrorEnvelope.zero,add_zero,zero_add,pow_one] at hh ⊢
  linarith only [hh]

#print axioms bjs_route_original
end ChenEffective

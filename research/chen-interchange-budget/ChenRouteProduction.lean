import ChenRouteSource
import QualitativeChen

noncomputable section
namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem production_route_base (n : ℕ) (hn : qualitativeGeometryThreshold ≤ n) (he : Even n) :
    (jurkatRichertBaseMainCoefficient jurkatRichertJ-1/25)*routeSourceScale n ≤
      ((jurkatRichertSourceCandidates n).card:ℝ) := by
  have h20 := qualitative_finite_cap.trans hn
  have h1 : preSieveFiniteCap ≤ n :=
    (show preSieveFiniteCap ≤ preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hh := qualitative_base_candidates hn
    ((preSieve_source_mass (by norm_num [baseCandidateBudget])).trans h20)
    (preSieve_base_distribution.trans h1) he
  simpa only [routeSourceScale,mul_div_assoc,mul_assoc] using hh

theorem production_route_medium (n : ℕ) (hn : qualitativeGeometryThreshold ≤ n) (he : Even n) :
    jurkatRichertSourceMediumPrimeAggregate n ≤
      (jurkatRichertQ1MainCoefficient jurkatRichertK+123/100)*routeSourceScale n := by
  have h20 := qualitative_finite_cap.trans hn
  have h1 : preSieveFiniteCap ≤ n :=
    (show preSieveFiniteCap ≤ preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hh := qualitative_medium_prime_aggregate hn (preSieve_prime_sum.trans h20)
    ((preSieve_upper_mass (by norm_num [mediumPrimeBudget])).trans h20)
    (preSieve_varying_threshold_cap.trans h1) he
  simpa only [routeSourceScale,mul_div_assoc,mul_assoc] using hh

theorem production_route_nine {n : ℕ} (hn : qualitativeGeometryThreshold ≤ n) : 9 ≤ n := by
  have hh : 2^110+1 ≤ n := (le_max_left _ _).trans (qualitative_endpoint hn)
  omega

theorem production_route_triple (n : ℕ) (hn : qualitativeGeometryThreshold ≤ n) (he : Even n) :
    correctedChenTriplePenalty n ≤
      (3.94033+routeSourceTripleErrors.eval n)*routeSourceScale n := by
  have ht := qualitative_triple_bound hn he
  have hr := route_source_triple_error (production_route_nine hn)
  dsimp [routeSourceScale] at hr ⊢
  simp only [mul_div_assoc,mul_assoc] at ht hr ⊢
  nlinarith only [ht,hr]

def productionRoute : ChenRoute routeSourceModel :=
  routeSourceOfBounds qualitativeGeometryThreshold qualitativeGeometryThreshold
    lowerEndpointThreshold qualitativeGeometryThreshold (1/25) (123/100)
    (by norm_num) (by norm_num) routeSourceTripleErrors
    production_route_base production_route_medium
    (fun _ hn he => route_source_boundary hn he) production_route_triple

theorem production_route_threshold : productionRoute.threshold ≤ qualitativeGeometryThreshold := by
  change max 9 (max (max qualitativeGeometryThreshold qualitativeGeometryThreshold)
    (max lowerEndpointThreshold qualitativeGeometryThreshold)) ≤ qualitativeGeometryThreshold
  exact max_le (production_route_nine le_rfl)
    (max_le (max_le le_rfl le_rfl) (max_le (qualitative_endpoint le_rfl) le_rfl))

theorem production_route_error_payment {n : ℕ} (hn : qualitativeGeometryThreshold ≤ n) :
    routeSourceTripleErrors.eval n ≤ 1/100 := by
  have h20 := qualitative_finite_cap.trans hn
  have h1 : preSieveFiniteCap ≤ n :=
    (show preSieveFiniteCap ≤ preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1≤20 by norm_num)).trans h20
  have hpow : 3^(200*numericalTripleErrorCap+1) ≤ n :=
    (preSieve_fixed_power (by norm_num [numericalTripleErrorCap])).trans h1
  have hl := log_ge_power_three hpow
  have hl0 : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1<n from lt_of_lt_of_le (by norm_num) (production_route_nine hn)))
  dsimp [routeSourceTripleErrors,ChenErrorBreakdown.eval,ChenErrorEnvelope.logPower,ChenErrorEnvelope.zero]
  simp only [add_zero,zero_add,pow_one]
  apply (div_le_iff₀ hl0).mpr
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hl
  nlinarith only [hl]

theorem production_route_margin (n : ℕ) :
    0.015585-routeSourceTripleErrors.eval n/2 ≤ productionRoute.margin n := by
  have hh := route_source_margin_floor qualitativeGeometryThreshold qualitativeGeometryThreshold
    lowerEndpointThreshold qualitativeGeometryThreshold (1/25) (123/100)
    (by norm_num) (by norm_num) routeSourceTripleErrors
    production_route_base production_route_medium
    (fun _ hn he => route_source_boundary hn he) production_route_triple n
  convert hh using 1 <;> first | rfl | ring

def productionRouteCertificate : ChenRouteCertificate productionRoute where
  cutoff := qualitativeGeometryThreshold
  thresholds_paid := production_route_threshold
  margin_pos := by
    intro n hn _he
    have hm := production_route_margin n
    have he := production_route_error_payment hn
    linarith only [hm,he]

theorem production_route_original : Goldbach.ChenTheorem :=
  chen_route_original productionRouteCertificate

def productionPaidTriple : ChenUpperProducer routeSourceModel.scale routeSourceModel.triple where
  threshold := qualitativeGeometryThreshold
  main := fun _ => 3.94033
  errors := {analytic:=ChenErrorEnvelope.constant (1/100) (by norm_num)}
  bound := by
    intro n hn he
    have ht := production_route_triple n hn he
    have hh := mul_le_mul_of_nonneg_right (production_route_error_payment hn)
      (routeSourceModel.scale_pos n (production_route_nine hn) he).le
    dsimp [ChenErrorBreakdown.eval,ChenErrorEnvelope.constant,ChenErrorEnvelope.zero]
    simp only [add_zero,zero_add]
    dsimp [routeSourceModel] at hh ⊢
    nlinarith only [ht,hh]

def productionPaidRoute : ChenRoute routeSourceModel := productionRoute.withTriple productionPaidTriple

/-- At valid endpoints the variable remainder is at least as informative as
its old constant allocation. Both remain interchangeable actual producers. -/
theorem production_route_dominates_paid {n : ℕ} (hn : qualitativeGeometryThreshold ≤ n) :
    productionPaidRoute.margin n ≤ productionRoute.margin n := by
  have hh := production_route_error_payment hn
  simp only [productionPaidRoute,ChenRoute.withTriple,ChenRoute.margin,
    ChenLowerProducer.coefficient,ChenUpperProducer.coefficient,productionPaidTriple,productionRoute,
    routeSourceOfBounds,routeSourceErrors,routeSourceBoundaryErrors,routeSourceTripleErrors,
    ChenErrorBreakdown.eval,ChenErrorEnvelope.constant,ChenErrorEnvelope.logPower,
    ChenErrorEnvelope.zero,add_zero,zero_add,pow_one] at hh ⊢
  linarith only [hh]

#print axioms production_route_original
end ChenEffective

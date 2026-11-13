import BJSH30SquareCap
import BJSH30FifthConstants
noncomputable section
namespace ChenEffective.H30
open NumericalPanHigh
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] logPowerCutoff
@[irreducible] def fifthAnalyticThreshold : ℕ := selbergRemainderThreshold 5 squareEpsilonDenominator

private theorem fifth_mertens_power_cap {r E : ℕ}
    (hlog : 16*(128*(1+1)+1)^2 ≤ E) (hpow : 1800000000004*r ≤ E) :
    ChenEffective.mertensProductThreshold r ≤ 3^E := by
  unfold ChenEffective.mertensProductThreshold principalNumericalThreshold
  exact max_le (numerical_log_cutoff_cap _ _ hlog)
    (Nat.pow_le_pow_right (by norm_num) hpow)

theorem fifth_analytic_cap : fifthAnalyticThreshold ≤ 3^primePairPowerExponent := by
  have hprefix : panPrimePrefixThreshold 72 ≤ 3^(primePairPowerExponent/4) := by
    unfold panPrimePrefixThreshold primitiveNumericalThreshold
    apply max_le
    all_goals
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hmove : panMovingPrimeThreshold 38 72 ≤ 3^primePairPowerExponent := by
    unfold panMovingPrimeThreshold
    apply numerical_quotient_cutoff_cap _ _ _ hprefix
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hlow : panLowThreshold 32 38 ≤ 3^primePairPowerExponent := by
    unfold panLowThreshold
    apply max_le
    · exact numerical_small_power_cap 9 primePairPowerExponent (by norm_num)
        (by rw [primePairPowerExponent_eq]; norm_num)
    · apply max_le hmove
      unfold panBudgetThreshold
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hreal : panRealDivPNTThreshold 34 ≤ 3^(primePairPowerExponent/4) := by
    unfold panRealDivPNTThreshold panPrimePNTThreshold numericalBVThreshold bvThreshold
      highBVThreshold primitiveNumericalThreshold principalNumericalThreshold
    apply max_le
    · exact numerical_small_power_cap 2 (primePairPowerExponent/4) (by norm_num)
        (by rw [primePairPowerExponent_eq]; norm_num)
    · repeat' apply max_le
      all_goals
        apply numerical_log_cutoff_cap
        rw [primePairPowerExponent_eq]
        norm_num [highBVConductorExponent,highBVExponent]
  have hpMove : panMovingPNTThreshold 34 ≤ 3^primePairPowerExponent := by
    unfold panMovingPNTThreshold
    apply numerical_quotient_cutoff_cap _ _ _ hreal
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hprincipal : panPrincipalThreshold 32 ≤ 3^primePairPowerExponent := by
    unfold panPrincipalThreshold
    apply max_le hpMove
    unfold panBudgetThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hledger : panLedgerThreshold 32 ≤ 3^primePairPowerExponent := by
    unfold panLedgerThreshold
    apply max_le hlow
    apply max_le
    · unfold panHighThreshold
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
    · apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hweighted : panWeightedThreshold 5 ≤ 3^primePairPowerExponent := by
    unfold panWeightedThreshold panUnweightedThreshold panWeightedSaving
    exact max_le hledger hprincipal
  have hsource : panSourceThreshold 5 squareEpsilonDenominator ≤ 3^primePairPowerExponent := by
    unfold panSourceThreshold
    apply max_le hweighted
    apply max_le
    · unfold panSourceSupportThreshold
      apply max_le
      · calc
          _ ≤ (3 : ℕ)^20 := Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) 20
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [primePairPowerExponent_eq]; norm_num)
      · apply numerical_log_cutoff_cap
        rw [primePairPowerExponent_eq]
        norm_num [panWeightedCutoff,panWeightedSaving]
    · apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num [squareEpsilonDenominator,panWeightedCutoff,panWeightedSaving]
  have hMertens : mertensProductThreshold 2 ≤ 3^primePairPowerExponent :=
    fifth_mertens_power_cap
      (by rw [primePairPowerExponent_eq]; norm_num)
      (by rw [primePairPowerExponent_eq]; norm_num)
  unfold fifthAnalyticThreshold selbergRemainderThreshold panCanonicalThreshold
  apply max_le
  · apply max_le hsource
    apply max_le hMertens
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  · apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num

#print axioms fifth_analytic_cap
end ChenEffective.H30

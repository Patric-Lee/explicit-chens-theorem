import NumericalGenuineLiSum

noncomputable section
namespace ChenEffective
open NumericalPanHigh
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
attribute [local irreducible] logPowerCutoff

theorem numerical_log_cutoff_cap (k E : ℕ) (h : 16*(k+1)^2 ≤ E) : logPowerCutoff k ≤ 3^E := by
  unfold logPowerCutoff
  exact Nat.pow_le_pow_right (by norm_num) h

theorem numerical_small_power_cap (c E : ℕ) (hc : c ≤ 4096) (hE : 8 ≤ E) : c ≤ 3^E :=
  hc.trans ((by norm_num : (4096 : ℕ) ≤ 3^8).trans (Nat.pow_le_pow_right (by norm_num) hE))

theorem numerical_quotient_cutoff_cap (b M E : ℕ) (hM : M ≤ 3^(E/4))
    (hE : 8 ≤ E) (hb : 4*4^b+1 ≤ E) : panQuotientThreshold b M ≤ 3^E := by
  unfold panQuotientThreshold
  apply max_le (numerical_small_power_cap 4096 E le_rfl hE)
  apply max_le
  · calc
      _ ≤ (3^(E/4))^4 := Nat.pow_le_pow_left hM 4
      _ = 3^((E/4)*4) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self E 4)
  · exact Nat.pow_le_pow_right (by norm_num) hb

theorem numerical_square_analytic_cap : squareAnalyticThreshold ≤ 3^primePairPowerExponent := by
  have hprefix : panPrimePrefixThreshold 64 ≤ 3^(primePairPowerExponent/4) := by
    unfold panPrimePrefixThreshold primitiveNumericalThreshold
    apply max_le
    all_goals
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hmove : panMovingPrimeThreshold 34 64 ≤ 3^primePairPowerExponent := by
    unfold panMovingPrimeThreshold
    apply numerical_quotient_cutoff_cap _ _ _ hprefix
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hlow : panLowThreshold 28 34 ≤ 3^primePairPowerExponent := by
    unfold panLowThreshold
    apply max_le
    · exact numerical_small_power_cap 9 primePairPowerExponent (by norm_num)
        (by rw [primePairPowerExponent_eq]; norm_num)
    · apply max_le hmove
      unfold panBudgetThreshold
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
  have hreal : panRealDivPNTThreshold 30 ≤ 3^(primePairPowerExponent/4) := by
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
  have hpMove : panMovingPNTThreshold 30 ≤ 3^primePairPowerExponent := by
    unfold panMovingPNTThreshold
    apply numerical_quotient_cutoff_cap _ _ _ hreal
    all_goals rw [primePairPowerExponent_eq]; norm_num
  have hprincipal : panPrincipalThreshold 28 ≤ 3^primePairPowerExponent := by
    unfold panPrincipalThreshold
    apply max_le hpMove
    unfold panBudgetThreshold
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  have hledger : panLedgerThreshold 28 ≤ 3^primePairPowerExponent := by
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
  have hweighted : panWeightedThreshold 3 ≤ 3^primePairPowerExponent := by
    unfold panWeightedThreshold panUnweightedThreshold panWeightedSaving
    exact max_le hledger hprincipal
  have hsource : panSourceThreshold 3 squareEpsilonDenominator ≤ 3^primePairPowerExponent := by
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
  have hMertens : mertensProductThreshold 2 ≤ 3^primePairPowerExponent := by
    unfold mertensProductThreshold principalNumericalThreshold
    apply max_le
    · apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
    · apply Nat.pow_le_pow_right (by norm_num)
      rw [primePairPowerExponent_eq]
      norm_num
  unfold squareAnalyticThreshold selbergRemainderThreshold panCanonicalThreshold
  apply max_le
  · apply max_le hsource
    apply max_le hMertens
    apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num
  · apply numerical_log_cutoff_cap
    rw [primePairPowerExponent_eq]
    norm_num

#print axioms numerical_square_analytic_cap
end ChenEffective

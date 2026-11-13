/- Threshold-specialized companion of research/chen-effective/NumericalSquareThresholdCap.lean.
The original producer is retained; all modified numerical statements are rechecked. -/
import BJSH30PrimePairMain
import BJSH30SquareConstants
import BJSH30Parameters

noncomputable section
namespace ChenEffective.H30
@[irreducible] def squareAnalyticThreshold : ℕ := selbergRemainderThreshold 3 squareEpsilonDenominator
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
    (hE : 8 ≤ E) (hb : 4*2^b+1 ≤ E) : panQuotientThreshold b M ≤ 3^E := by
  unfold panQuotientThreshold
  apply max_le (numerical_small_power_cap 4096 E le_rfl hE)
  apply max_le
  · calc
      _ ≤ (3^(E/4))^4 := Nat.pow_le_pow_left hM 4
      _ = 3^((E/4)*4) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self E 4)
  · exact Nat.pow_le_pow_right (by norm_num) hb

private theorem square_cap_hprefix {E : ℕ} (hE : E=5*10^12) : panPrimePrefixThreshold 64 ≤ 3^(E/4) := by
  unfold panPrimePrefixThreshold primitiveNumericalThreshold
  apply max_le
  all_goals
    apply numerical_log_cutoff_cap
    rw [hE]
    norm_num

private theorem square_cap_hmove {E : ℕ} (hE : E=5*10^12) : panMovingPrimeThreshold 34 64 ≤ 3^E := by
  unfold panMovingPrimeThreshold
  apply numerical_quotient_cutoff_cap _ _ _ (square_cap_hprefix hE)
  all_goals rw [hE]; norm_num

private theorem square_cap_hlow {E : ℕ} (hE : E=5*10^12) : panLowThreshold 28 34 ≤ 3^E := by
  unfold panLowThreshold
  apply max_le
  · exact numerical_small_power_cap 9 E (by norm_num)
      (by rw [hE]; norm_num)
  · apply max_le (square_cap_hmove hE)
    unfold panBudgetThreshold
    apply numerical_log_cutoff_cap
    rw [hE]
    norm_num

private theorem square_cap_hreal {E : ℕ} (hE : E=5*10^12) : panRealDivPNTThreshold 30 ≤ 3^(E/4) := by
  unfold panRealDivPNTThreshold panPrimePNTThreshold numericalBVThreshold bvThreshold
    highBVThreshold primitiveNumericalThreshold principalNumericalThreshold
  apply max_le
  · exact numerical_small_power_cap 2 (E/4) (by norm_num)
      (by rw [hE]; norm_num)
  · repeat' apply max_le
    all_goals
      apply numerical_log_cutoff_cap
      rw [hE]
      norm_num [highBVConductorExponent,highBVExponent]

private theorem square_cap_hpMove {E : ℕ} (hE : E=5*10^12) : panMovingPNTThreshold 30 ≤ 3^E := by
  unfold panMovingPNTThreshold
  apply numerical_quotient_cutoff_cap _ _ _ (square_cap_hreal hE)
  all_goals rw [hE]; norm_num

private theorem square_cap_hprincipal {E : ℕ} (hE : E=5*10^12) : panPrincipalThreshold 28 ≤ 3^E := by
  unfold panPrincipalThreshold
  apply max_le (square_cap_hpMove hE)
  unfold panBudgetThreshold
  apply numerical_log_cutoff_cap
  rw [hE]
  norm_num

private theorem square_cap_hledger {E : ℕ} (hE : E=5*10^12) : panLedgerThreshold 28 ≤ 3^E := by
  unfold panLedgerThreshold
  apply max_le (square_cap_hlow hE)
  apply max_le
  · unfold panHighThreshold
    apply numerical_log_cutoff_cap
    rw [hE]
    norm_num
  · apply numerical_log_cutoff_cap
    rw [hE]
    norm_num

private theorem square_cap_hweighted {E : ℕ} (hE : E=5*10^12) : panWeightedThreshold 3 ≤ 3^E := by
  unfold panWeightedThreshold panUnweightedThreshold panWeightedSaving
  exact max_le (square_cap_hledger hE) (square_cap_hprincipal hE)

private theorem square_cap_hsource {E : ℕ} (hE : E=5*10^12) : panSourceThreshold 3 squareEpsilonDenominator ≤ 3^E := by
  unfold panSourceThreshold
  apply max_le (square_cap_hweighted hE)
  apply max_le
  · unfold panSourceSupportThreshold
    apply max_le
    · calc
        _ ≤ (3 : ℕ)^20 := Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) 20
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [hE]; norm_num)
    · apply numerical_log_cutoff_cap
      rw [hE]
      norm_num [panWeightedCutoff,panWeightedSaving]
  · apply numerical_log_cutoff_cap
    rw [hE]
    norm_num [squareEpsilonDenominator,panWeightedCutoff,panWeightedSaving]

private theorem mertens_power_cap_symbolic {r E : ℕ}
    (hlog : 16*(128*(1+1)+1)^2 ≤ E) (hpow : 1800000000004*r ≤ E) :
    ChenEffective.mertensProductThreshold r ≤ 3^E := by
  unfold ChenEffective.mertensProductThreshold principalNumericalThreshold
  exact max_le (numerical_log_cutoff_cap _ _ hlog)
    (Nat.pow_le_pow_right (by norm_num) hpow)

private theorem square_cap_hMertens {E : ℕ} (hE : E=5*10^12) :
    ChenEffective.mertensProductThreshold 2 ≤ 3^E :=
  mertens_power_cap_symbolic (by rw [hE]; norm_num) (by rw [hE]; norm_num)

private theorem numerical_square_analytic_cap_symbolic {E : ℕ} (hE : E=5*10^12) :
    squareAnalyticThreshold ≤ 3^E := by
  unfold squareAnalyticThreshold selbergRemainderThreshold panCanonicalThreshold
  apply max_le
  · apply max_le (square_cap_hsource hE)
    apply max_le (square_cap_hMertens hE)
    apply numerical_log_cutoff_cap
    rw [hE]
    norm_num
  · apply numerical_log_cutoff_cap
    rw [hE]
    norm_num

theorem numerical_square_analytic_cap : squareAnalyticThreshold ≤ 3^primePairPowerExponent :=
  numerical_square_analytic_cap_symbolic primePairPowerExponent_eq

#print axioms numerical_square_analytic_cap
end ChenEffective.H30

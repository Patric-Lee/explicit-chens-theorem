import NumericalTowerCoefficient

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff mertensProductThreshold numericalBVThreshold

theorem tower_UH_nat : towerU ≤ towerH := by exact_mod_cast towerU_le_H
theorem tower_HV_nat : towerH ≤ towerV := by exact_mod_cast towerH_le_V
theorem tower_VF_nat : towerV ≤ towerF := by exact_mod_cast towerV_le_F
theorem tower_H_pow_nat {n : ℕ} (hn : n ≤ 100) : towerH^n ≤ towerV := by exact_mod_cast towerH_pow_le_V hn
theorem tower_H_one_nat : 1 ≤ towerH := by exact_mod_cast towerH_one
theorem tower_V_one_nat : 1 ≤ towerV := by exact_mod_cast towerV_one
theorem tower_H_large_nat : 10^100 ≤ towerH := towerU_large.trans tower_UH_nat
theorem tower_V_large_nat : 10^100 ≤ towerV := tower_H_large_nat.trans tower_HV_nat

theorem tower_fixed_power {n : ℕ} (hn : n ≤ 10^100) : 3^n ≤ towerH := by
  unfold towerH
  apply Nat.pow_le_pow_right (by norm_num)
  exact (hn.trans towerU_large).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ towerU by exact_mod_cast towerU_one) (show 1 ≤ 100 by norm_num))

theorem tower_log_power {k : ℕ} (hk : k ≤ 10^30) : logPowerCutoff k ≤ towerH := by
  unfold logPowerCutoff
  apply tower_fixed_power
  calc
    _ ≤ 16*(10^30+1)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem tower_BV {A : ℕ} (hA : A ≤ 24) : numericalBVThreshold A ≤ towerH := by
  rw [numerical_BV_threshold_closed]
  apply tower_fixed_power
  calc
    _ ≤ 16*(384*24+13569)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem tower_mertens {r : ℕ} (hr : r ≤ 10^12) : mertensProductThreshold r ≤ towerH := by
  unfold mertensProductThreshold
  apply max_le
  · rw [principalNumericalThreshold_one]
    exact tower_fixed_power (by norm_num)
  · apply tower_fixed_power
    calc
      _ ≤ 1800000000004*10^12 := Nat.mul_le_mul_left _ hr
      _ ≤ _ := by norm_num

theorem tower_H_add_one : towerH+1 ≤ towerH^2 := by
  have hh : 100 ≤ towerH := (by norm_num : 100 ≤ (10 : ℕ)^100).trans tower_H_large_nat
  nlinarith only [hh]

theorem tower_chen_product {r : ℕ} (hr : r ≤ 10^12) : chenProductThreshold r ≤ towerH^20 := by
  unfold chenProductThreshold
  calc
    _ ≤ (towerH+1)^10 := Nat.pow_le_pow_left (Nat.add_le_add_right (tower_mertens hr) 1) 10
    _ ≤ (towerH^2)^10 := Nat.pow_le_pow_left tower_H_add_one 10
    _ = _ := by rw [← pow_mul]

theorem tower_singular_normalization {r : ℕ} (hr : r ≤ 10^12) : singularNormalizationThreshold r ≤ towerH^20 := by
  have hh : 2^110+1 ≤ towerH := (by norm_num : 2^110+1 ≤ (10 : ℕ)^100).trans tower_H_large_nat
  have hbase : 80*r+3 ≤ towerH :=
    (show 80*r+3 ≤ 10^100 by nlinarith only [hr]).trans tower_H_large_nat
  unfold singularNormalizationThreshold
  exact max_le (hh.trans (by simpa only [pow_one] using Nat.pow_le_pow_right tower_H_one_nat (show 1 ≤ 20 by norm_num)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right tower_H_one_nat (by norm_num : 10 ≤ 20)))

theorem tower_source_mass {r : ℕ} (hr : r ≤ 10^12) : sourceMassThreshold r ≤ towerH^20 :=
  max_le (tower_chen_product hr) (tower_singular_normalization hr)

theorem tower_upper_mass {r : ℕ} (hr : r ≤ 10^12) : sourceUpperMassThreshold r ≤ towerH^20 := by
  have hH20 : towerH ≤ towerH^20 := by simpa only [pow_one] using Nat.pow_le_pow_right tower_H_one_nat (show 1 ≤ 20 by norm_num)
  have hbase : 2*r+1 ≤ towerH := (show 2*r+1 ≤ 10^100 by nlinarith only [hr]).trans tower_H_large_nat
  unfold sourceUpperMassThreshold
  exact max_le (tower_chen_product hr) (max_le
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right tower_H_one_nat (by norm_num : 10 ≤ 20)))
    (max_le ((tower_fixed_power (show 40*r+1 ≤ 10^100 by nlinarith only [hr])).trans hH20)
      ((tower_log_power (by norm_num : 2 ≤ 10^30)).trans hH20)))

theorem tower_base_distribution : baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget ≤ towerH := by
  have hhigh : highBVThreshold 3 ≤ towerH := tower_log_power (by norm_num [highBVThreshold])
  have hroot : logPowerCutoff ((60*baseCandidateBudget)*highBVExponent 3) ≤ towerH :=
    tower_log_power (by norm_num [baseCandidateBudget,highBVExponent])
  have hscalar : 3^(4*1000344400000012180*baseCandidateBudget+16*baseCandidateBudget+1) ≤ towerH :=
    tower_fixed_power (by norm_num [baseCandidateBudget])
  exact max_le (tower_BV (by norm_num : 3 ≤ 24)) (max_le hhigh (max_le hroot (max_le (tower_log_power (by norm_num : 4 ≤ 10^30)) hscalar)))

theorem tower_varying_distribution : varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget ≤ towerH := by
  have hw : weightedNumericalThreshold 3 (120*mediumPrimeBudget) ≤ towerH :=
    max_le (tower_BV (by norm_num [weightedSaving]))
      (tower_log_power (by norm_num [mediumPrimeBudget,weightedSaving,highBVExponent]))
  exact max_le (max_le hw (tower_log_power (by norm_num : 100 ≤ 10^30)))
    (tower_fixed_power (by norm_num [varyingNumericalBudget,mediumPrimeBudget]))

theorem tower_nSquare : nSquare ≤ towerH := by
  change numericalDenominatorThreshold ≤ towerH
  rw [numericalDenominatorThreshold,towerH]
  apply Nat.pow_le_pow_right (by norm_num)
  rw [towerU,← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  rw [towerSeed_eq,numericalDenominatorExponent_eq]
  norm_num
theorem tower_prime_sum : mediumPrimeSumThreshold ≤ towerH^20 := by
  have hPair : primePairThreshold ≤ towerH := numerical_prime_pair_threshold_le_denominator.trans tower_nSquare
  have hbase : mediumPrimeBudget+2 ≤ towerH := (by norm_num [mediumPrimeBudget] : mediumPrimeBudget+2 ≤ (10 : ℕ)^100).trans tower_H_large_nat
  exact max_le (hPair.trans (by simpa only [pow_one] using Nat.pow_le_pow_right tower_H_one_nat (show 1 ≤ 20 by norm_num)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right tower_H_one_nat (by norm_num : 10 ≤ 20)))

theorem tower_lower_endpoint : lowerEndpointThreshold ≤ towerH :=
  max_le ((by norm_num : 2^110+1 ≤ (10 : ℕ)^100).trans tower_H_large_nat)
    (max_le (tower_log_power (by norm_num : 30 ≤ 10^30)) (tower_fixed_power (by norm_num)))

private theorem tower_error_cutoff_symbolic {B : ℕ} (hB : 20000*B+1 ≤ 10^100) :
    errorCutoff B ≤ towerH := by
  unfold errorCutoff
  exact tower_fixed_power hB

theorem tower_final_error : errorCutoff numericalTripleErrorCap ≤ towerH :=
  tower_error_cutoff_symbolic (by norm_num [numericalTripleErrorCap])

#print axioms tower_varying_distribution
end ChenEffective

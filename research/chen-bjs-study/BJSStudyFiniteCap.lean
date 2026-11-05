import NumericalPreSieveAggregate

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff mertensProductThreshold numericalBVThreshold

private opaque bjsStudyCap_preSieveFiniteExponentCertificate : {n : ℕ // n=10^80} := ⟨10^80,rfl⟩
def bjsStudyCap_preSieveFiniteExponent : ℕ := bjsStudyCap_preSieveFiniteExponentCertificate.1
theorem bjsStudyCap_preSieveFiniteExponent_eq : bjsStudyCap_preSieveFiniteExponent=10^80 := bjsStudyCap_preSieveFiniteExponentCertificate.2
@[irreducible] def bjsStudyCap_preSieveFiniteCap : ℕ := 3^bjsStudyCap_preSieveFiniteExponent

theorem bjsStudyCap_preSieve_fixed_power {n : ℕ} (hn : n ≤ 10^80) : 3^n ≤ bjsStudyCap_preSieveFiniteCap := by
  unfold bjsStudyCap_preSieveFiniteCap
  apply Nat.pow_le_pow_right (by norm_num)
  rwa [bjsStudyCap_preSieveFiniteExponent_eq]

theorem bjsStudyCap_preSieve_H_large_nat : 10^80 ≤ bjsStudyCap_preSieveFiniteCap := by
  apply le_trans (show (10 : ℕ)^80 ≤ 3^300 by norm_num)
  exact bjsStudyCap_preSieve_fixed_power (by norm_num)

theorem bjsStudyCap_preSieve_H_one_nat : 1 ≤ bjsStudyCap_preSieveFiniteCap :=
  (by norm_num : 1 ≤ (10 : ℕ)^80).trans bjsStudyCap_preSieve_H_large_nat

theorem bjsStudyCap_preSieve_log_power {k : ℕ} (hk : k ≤ 10^30) : logPowerCutoff k ≤ bjsStudyCap_preSieveFiniteCap := by
  unfold logPowerCutoff
  apply bjsStudyCap_preSieve_fixed_power
  calc
    _ ≤ 16*(10^30+1)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem bjsStudyCap_preSieve_BV {A : ℕ} (hA : A ≤ 24) : numericalBVThreshold A ≤ bjsStudyCap_preSieveFiniteCap := by
  rw [numerical_BV_threshold_closed]
  apply bjsStudyCap_preSieve_fixed_power
  calc
    _ ≤ 16*(384*24+13569)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem bjsStudyCap_preSieve_mertens {r : ℕ} (hr : r ≤ 10^12) : mertensProductThreshold r ≤ bjsStudyCap_preSieveFiniteCap := by
  unfold mertensProductThreshold
  apply max_le
  · rw [principalNumericalThreshold_one]
    exact bjsStudyCap_preSieve_fixed_power (by norm_num)
  · apply bjsStudyCap_preSieve_fixed_power
    calc
      _ ≤ 1800000000004*10^12 := Nat.mul_le_mul_left _ hr
      _ ≤ _ := by norm_num

theorem bjsStudyCap_preSieve_H_add_one : bjsStudyCap_preSieveFiniteCap+1 ≤ bjsStudyCap_preSieveFiniteCap^2 := by
  have hh : 100 ≤ bjsStudyCap_preSieveFiniteCap := (by norm_num : 100 ≤ (10 : ℕ)^80).trans bjsStudyCap_preSieve_H_large_nat
  nlinarith only [hh]

theorem bjsStudyCap_preSieve_chen_product {r : ℕ} (hr : r ≤ 10^12) : chenProductThreshold r ≤ bjsStudyCap_preSieveFiniteCap^20 := by
  unfold chenProductThreshold
  calc
    _ ≤ (bjsStudyCap_preSieveFiniteCap+1)^10 := Nat.pow_le_pow_left (Nat.add_le_add_right (bjsStudyCap_preSieve_mertens hr) 1) 10
    _ ≤ (bjsStudyCap_preSieveFiniteCap^2)^10 := Nat.pow_le_pow_left bjsStudyCap_preSieve_H_add_one 10
    _ = _ := by rw [← pow_mul]

theorem bjsStudyCap_preSieve_singular_normalization {r : ℕ} (hr : r ≤ 10^12) : singularNormalizationThreshold r ≤ bjsStudyCap_preSieveFiniteCap^20 := by
  have hh : 2^110+1 ≤ bjsStudyCap_preSieveFiniteCap := (by norm_num : 2^110+1 ≤ (10 : ℕ)^80).trans bjsStudyCap_preSieve_H_large_nat
  have hbase : 80*r+3 ≤ bjsStudyCap_preSieveFiniteCap :=
    (show 80*r+3 ≤ 10^80 by nlinarith only [hr]).trans bjsStudyCap_preSieve_H_large_nat
  unfold singularNormalizationThreshold
  exact max_le (hh.trans (by simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 20 by norm_num)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (by norm_num : 10 ≤ 20)))

theorem bjsStudyCap_preSieve_source_mass {r : ℕ} (hr : r ≤ 10^12) : sourceMassThreshold r ≤ bjsStudyCap_preSieveFiniteCap^20 :=
  max_le (bjsStudyCap_preSieve_chen_product hr) (bjsStudyCap_preSieve_singular_normalization hr)

theorem bjsStudyCap_preSieve_upper_mass {r : ℕ} (hr : r ≤ 10^12) : sourceUpperMassThreshold r ≤ bjsStudyCap_preSieveFiniteCap^20 := by
  have hH20 : bjsStudyCap_preSieveFiniteCap ≤ bjsStudyCap_preSieveFiniteCap^20 := by simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  have hbase : 2*r+1 ≤ bjsStudyCap_preSieveFiniteCap := (show 2*r+1 ≤ 10^80 by nlinarith only [hr]).trans bjsStudyCap_preSieve_H_large_nat
  unfold sourceUpperMassThreshold
  exact max_le (bjsStudyCap_preSieve_chen_product hr) (max_le
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (by norm_num : 10 ≤ 20)))
    (max_le ((bjsStudyCap_preSieve_fixed_power (show 40*r+1 ≤ 10^80 by nlinarith only [hr])).trans hH20)
      ((bjsStudyCap_preSieve_log_power (by norm_num : 2 ≤ 10^30)).trans hH20)))

theorem bjsStudyCap_preSieve_base_distribution : baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget ≤ bjsStudyCap_preSieveFiniteCap := by
  have hhigh : highBVThreshold 3 ≤ bjsStudyCap_preSieveFiniteCap := bjsStudyCap_preSieve_log_power (by norm_num [highBVThreshold])
  have hroot : logPowerCutoff ((60*baseCandidateBudget)*highBVExponent 3) ≤ bjsStudyCap_preSieveFiniteCap :=
    bjsStudyCap_preSieve_log_power (by norm_num [baseCandidateBudget,highBVExponent])
  have hscalar : 3^(4*1000344400000012180*baseCandidateBudget+16*baseCandidateBudget+1) ≤ bjsStudyCap_preSieveFiniteCap :=
    bjsStudyCap_preSieve_fixed_power (by norm_num [baseCandidateBudget])
  exact max_le (bjsStudyCap_preSieve_BV (by norm_num : 3 ≤ 24)) (max_le hhigh (max_le hroot (max_le (bjsStudyCap_preSieve_log_power (by norm_num : 4 ≤ 10^30)) hscalar)))

theorem bjsStudyCap_preSieve_varying_threshold_cap : varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget ≤ bjsStudyCap_preSieveFiniteCap := by
  have hw : weightedNumericalThreshold 3 (120*mediumPrimeBudget) ≤ bjsStudyCap_preSieveFiniteCap :=
    max_le (bjsStudyCap_preSieve_BV (by norm_num [weightedSaving]))
      (bjsStudyCap_preSieve_log_power (by norm_num [mediumPrimeBudget,weightedSaving,highBVExponent]))
  exact max_le (max_le hw (bjsStudyCap_preSieve_log_power (by norm_num : 100 ≤ 10^30)))
    (bjsStudyCap_preSieve_fixed_power (by norm_num [varyingNumericalBudget,mediumPrimeBudget]))


theorem bjsStudyCap_preSieve_prime_sum : mediumPrimeSumThreshold ≤ bjsStudyCap_preSieveFiniteCap^20 := by
  have hM : selbergMertensEndpoint ≤ bjsStudyCap_preSieveFiniteCap := by
    rw [selbergMertensEndpoint_eq]
    exact bjsStudyCap_preSieve_mertens (by norm_num : 2 ≤ 10^12)
  have hPair : primePairThreshold ≤ bjsStudyCap_preSieveFiniteCap^10 := by
    unfold primePairThreshold
    apply max_le (Nat.pow_le_pow_left hM 10)
    rw [primePairPowerExponent_eq]
    exact (bjsStudyCap_preSieve_fixed_power (by norm_num : (10 : ℕ)^80 ≤ 10^80)).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (show 1 ≤ 10 by norm_num))
  have hbase : mediumPrimeBudget+2 ≤ bjsStudyCap_preSieveFiniteCap :=
    (by norm_num [mediumPrimeBudget] : mediumPrimeBudget+2 ≤ (10 : ℕ)^80).trans bjsStudyCap_preSieve_H_large_nat
  exact max_le (hPair.trans (Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (by norm_num : 10 ≤ 20)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right bjsStudyCap_preSieve_H_one_nat (by norm_num : 10 ≤ 20)))

theorem bjsStudyCap_preSieve_lower_endpoint : lowerEndpointThreshold ≤ bjsStudyCap_preSieveFiniteCap :=
  max_le ((by norm_num : 2^110+1 ≤ (10 : ℕ)^80).trans bjsStudyCap_preSieve_H_large_nat)
    (max_le (bjsStudyCap_preSieve_log_power (by norm_num : 30 ≤ 10^30)) (bjsStudyCap_preSieve_fixed_power (by norm_num)))


end ChenEffective

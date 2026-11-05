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

private opaque preSieveFiniteExponentCertificate : {n : ℕ // n=10^100} := ⟨10^100,rfl⟩
def preSieveFiniteExponent : ℕ := preSieveFiniteExponentCertificate.1
theorem preSieveFiniteExponent_eq : preSieveFiniteExponent=10^100 := preSieveFiniteExponentCertificate.2
@[irreducible] def preSieveFiniteCap : ℕ := 3^preSieveFiniteExponent

theorem preSieve_fixed_power {n : ℕ} (hn : n ≤ 10^100) : 3^n ≤ preSieveFiniteCap := by
  unfold preSieveFiniteCap
  apply Nat.pow_le_pow_right (by norm_num)
  rwa [preSieveFiniteExponent_eq]

theorem preSieve_H_large_nat : 10^100 ≤ preSieveFiniteCap := by
  apply le_trans (show (10 : ℕ)^100 ≤ 3^300 by norm_num)
  exact preSieve_fixed_power (by norm_num)

theorem preSieve_H_one_nat : 1 ≤ preSieveFiniteCap :=
  (by norm_num : 1 ≤ (10 : ℕ)^100).trans preSieve_H_large_nat

theorem preSieve_log_power {k : ℕ} (hk : k ≤ 10^30) : logPowerCutoff k ≤ preSieveFiniteCap := by
  unfold logPowerCutoff
  apply preSieve_fixed_power
  calc
    _ ≤ 16*(10^30+1)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem preSieve_BV {A : ℕ} (hA : A ≤ 24) : numericalBVThreshold A ≤ preSieveFiniteCap := by
  rw [numerical_BV_threshold_closed]
  apply preSieve_fixed_power
  calc
    _ ≤ 16*(384*24+13569)^2 := by gcongr
    _ ≤ _ := by norm_num

theorem preSieve_mertens {r : ℕ} (hr : r ≤ 10^12) : mertensProductThreshold r ≤ preSieveFiniteCap := by
  unfold mertensProductThreshold
  apply max_le
  · rw [principalNumericalThreshold_one]
    exact preSieve_fixed_power (by norm_num)
  · apply preSieve_fixed_power
    calc
      _ ≤ 1800000000004*10^12 := Nat.mul_le_mul_left _ hr
      _ ≤ _ := by norm_num

theorem preSieve_H_add_one : preSieveFiniteCap+1 ≤ preSieveFiniteCap^2 := by
  have hh : 100 ≤ preSieveFiniteCap := (by norm_num : 100 ≤ (10 : ℕ)^100).trans preSieve_H_large_nat
  nlinarith only [hh]

theorem preSieve_chen_product {r : ℕ} (hr : r ≤ 10^12) : chenProductThreshold r ≤ preSieveFiniteCap^20 := by
  unfold chenProductThreshold
  calc
    _ ≤ (preSieveFiniteCap+1)^10 := Nat.pow_le_pow_left (Nat.add_le_add_right (preSieve_mertens hr) 1) 10
    _ ≤ (preSieveFiniteCap^2)^10 := Nat.pow_le_pow_left preSieve_H_add_one 10
    _ = _ := by rw [← pow_mul]

theorem preSieve_singular_normalization {r : ℕ} (hr : r ≤ 10^12) : singularNormalizationThreshold r ≤ preSieveFiniteCap^20 := by
  have hh : 2^110+1 ≤ preSieveFiniteCap := (by norm_num : 2^110+1 ≤ (10 : ℕ)^100).trans preSieve_H_large_nat
  have hbase : 80*r+3 ≤ preSieveFiniteCap :=
    (show 80*r+3 ≤ 10^100 by nlinarith only [hr]).trans preSieve_H_large_nat
  unfold singularNormalizationThreshold
  exact max_le (hh.trans (by simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right preSieve_H_one_nat (by norm_num : 10 ≤ 20)))

theorem preSieve_source_mass {r : ℕ} (hr : r ≤ 10^12) : sourceMassThreshold r ≤ preSieveFiniteCap^20 :=
  max_le (preSieve_chen_product hr) (preSieve_singular_normalization hr)

theorem preSieve_upper_mass {r : ℕ} (hr : r ≤ 10^12) : sourceUpperMassThreshold r ≤ preSieveFiniteCap^20 := by
  have hH20 : preSieveFiniteCap ≤ preSieveFiniteCap^20 := by simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)
  have hbase : 2*r+1 ≤ preSieveFiniteCap := (show 2*r+1 ≤ 10^100 by nlinarith only [hr]).trans preSieve_H_large_nat
  unfold sourceUpperMassThreshold
  exact max_le (preSieve_chen_product hr) (max_le
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right preSieve_H_one_nat (by norm_num : 10 ≤ 20)))
    (max_le ((preSieve_fixed_power (show 40*r+1 ≤ 10^100 by nlinarith only [hr])).trans hH20)
      ((preSieve_log_power (by norm_num : 2 ≤ 10^30)).trans hH20)))

theorem preSieve_base_distribution : baseDistributionNumericalThreshold (60*baseCandidateBudget) baseCandidateBudget ≤ preSieveFiniteCap := by
  have hhigh : highBVThreshold 3 ≤ preSieveFiniteCap := preSieve_log_power (by norm_num [highBVThreshold])
  have hroot : logPowerCutoff ((60*baseCandidateBudget)*highBVExponent 3) ≤ preSieveFiniteCap :=
    preSieve_log_power (by norm_num [baseCandidateBudget,highBVExponent])
  have hscalar : 3^(4*1000344400000012180*baseCandidateBudget+16*baseCandidateBudget+1) ≤ preSieveFiniteCap :=
    preSieve_fixed_power (by norm_num [baseCandidateBudget])
  exact max_le (preSieve_BV (by norm_num : 3 ≤ 24)) (max_le hhigh (max_le hroot (max_le (preSieve_log_power (by norm_num : 4 ≤ 10^30)) hscalar)))

theorem preSieve_varying_threshold_cap : varyingNumericalThreshold (120*mediumPrimeBudget) mediumPrimeBudget ≤ preSieveFiniteCap := by
  have hw : weightedNumericalThreshold 3 (120*mediumPrimeBudget) ≤ preSieveFiniteCap :=
    max_le (preSieve_BV (by norm_num [weightedSaving]))
      (preSieve_log_power (by norm_num [mediumPrimeBudget,weightedSaving,highBVExponent]))
  exact max_le (max_le hw (preSieve_log_power (by norm_num : 100 ≤ 10^30)))
    (preSieve_fixed_power (by norm_num [varyingNumericalBudget,mediumPrimeBudget]))


theorem preSieve_prime_sum : mediumPrimeSumThreshold ≤ preSieveFiniteCap^20 := by
  have hM : selbergMertensEndpoint ≤ preSieveFiniteCap := by
    rw [selbergMertensEndpoint_eq]
    exact preSieve_mertens (by norm_num : 2 ≤ 10^12)
  have hPair : primePairThreshold ≤ preSieveFiniteCap^10 := by
    unfold primePairThreshold
    apply max_le (Nat.pow_le_pow_left hM 10)
    rw [primePairPowerExponent_eq]
    exact (preSieve_fixed_power (by norm_num : (10 : ℕ)^80 ≤ 10^100)).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 10 by norm_num))
  have hbase : mediumPrimeBudget+2 ≤ preSieveFiniteCap :=
    (by norm_num [mediumPrimeBudget] : mediumPrimeBudget+2 ≤ (10 : ℕ)^100).trans preSieve_H_large_nat
  exact max_le (hPair.trans (Nat.pow_le_pow_right preSieve_H_one_nat (by norm_num : 10 ≤ 20)))
    ((Nat.pow_le_pow_left hbase 10).trans (Nat.pow_le_pow_right preSieve_H_one_nat (by norm_num : 10 ≤ 20)))

theorem preSieve_lower_endpoint : lowerEndpointThreshold ≤ preSieveFiniteCap :=
  max_le ((by norm_num : 2^110+1 ≤ (10 : ℕ)^100).trans preSieve_H_large_nat)
    (max_le (preSieve_log_power (by norm_num : 30 ≤ 10^30)) (preSieve_fixed_power (by norm_num)))

theorem preSieve_finite_cap_geometry : preSieveFiniteCap^20 ≤ preSieveGeometryThreshold := by
  rw [preSieveGeometryThreshold_eq]
  unfold preSieveFiniteCap
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (3 : ℕ)^400 := by rw [preSieveFiniteExponent_eq]; norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- Both original Chen coefficients now hold above a fixed double exponential;
no density coefficient, source cutoff or eventual estimate remains. -/
theorem preSieve_weighted_lower {N : ℕ} (hN : preSieveGeometryThreshold ≤ N) (hEven : Even N) :
    (2.6407 : ℝ)*SingularSeries.liuSingularSeries N*N/log (N : ℝ)^2 ≤
      jurkatRichertWeightedCount N := by
  have h20 : preSieveFiniteCap^20 ≤ N := preSieve_finite_cap_geometry.trans hN
  have h1 : preSieveFiniteCap ≤ N :=
    (show preSieveFiniteCap ≤ preSieveFiniteCap^20 from by
      simpa only [pow_one] using Nat.pow_le_pow_right preSieve_H_one_nat (show 1 ≤ 20 by norm_num)).trans h20
  apply numerical_lower_from_density_bounds (preSieve_lower_endpoint.trans h1) hEven
  · exact preSieve_base_candidates hN
      ((preSieve_source_mass (by norm_num [baseCandidateBudget])).trans h20)
      (preSieve_base_distribution.trans h1) hEven
  · exact preSieve_medium_prime_aggregate hN (preSieve_prime_sum.trans h20)
      ((preSieve_upper_mass (by norm_num [mediumPrimeBudget])).trans h20)
      (preSieve_varying_threshold_cap.trans h1) hEven

#print axioms preSieve_weighted_lower
end ChenEffective
import BJSH30SourceMass
import BJSH30SourceUpperMass
import BJSH30Parameters
import NumericalSquareThresholdCap

noncomputable section
namespace ChenEffective.H30
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512

theorem source_product_cap {r : ℕ} (hr : r≤10^10) : chenProductThreshold r≤ squareClosedThreshold := by
  have hM : mertensProductThreshold r≤3^(primePairPowerExponent/20) := by
    unfold mertensProductThreshold
    apply max_le
    · apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num
    · apply Nat.pow_le_pow_right (by decide)
      rw [primePairPowerExponent_eq]
      omega
  have h2 : 2≤(3:ℕ)^(primePairPowerExponent/20) :=
    (by decide : 2≤(3:ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num))
  have hh : (3:ℕ)^(primePairPowerExponent/20)+1≤((3:ℕ)^(primePairPowerExponent/20))^2 := by nlinarith only [h2]
  unfold chenProductThreshold squareClosedThreshold
  calc
    _ ≤ ((3:ℕ)^(primePairPowerExponent/20)+1)^10 := Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 10
    _ ≤ (((3:ℕ)^(primePairPowerExponent/20))^2)^10 := Nat.pow_le_pow_left hh 10
    _ = 3^((primePairPowerExponent/20)*20) := by rw [← pow_mul,← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self _ _)

theorem small_tenth_power_cap {a : ℕ} (ha : a≤3^30) : a^10≤ squareClosedThreshold := by
  unfold squareClosedThreshold
  calc
    _ ≤ ((3:ℕ)^30)^10 := Nat.pow_le_pow_left ha 10
    _ = 3^300 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num)

theorem source_mass_caps {r : ℕ} (hr : r≤10^10) :
    sourceMassThreshold r≤ squareClosedThreshold ∧ sourceUpperMassThreshold r≤ squareClosedThreshold := by
  have hsmall : (2:ℕ)^110+1≤ squareClosedThreshold := by
    unfold squareClosedThreshold
    exact (by norm_num : (2:ℕ)^110+1≤3^100).trans
      (Nat.pow_le_pow_right (by decide) (by rw [primePairPowerExponent_eq]; norm_num))
  have hsing : singularNormalizationThreshold r≤ squareClosedThreshold := by
    unfold singularNormalizationThreshold
    apply max_le hsmall
    apply small_tenth_power_cap
    nlinarith only [hr]
  constructor
  · exact max_le (source_product_cap hr) hsing
  · unfold sourceUpperMassThreshold
    apply max_le (source_product_cap hr)
    apply max_le (small_tenth_power_cap (by nlinarith only [hr]))
    apply max_le
    · unfold squareClosedThreshold
      apply Nat.pow_le_pow_right (by decide)
      rw [primePairPowerExponent_eq]
      omega
    · unfold squareClosedThreshold
      apply numerical_log_cutoff_cap
      rw [primePairPowerExponent_eq]
      norm_num

theorem source_mass_at_closed_threshold {r N : ℕ} (hr : 0<r) (hrcap : r≤10^10)
    (hN : squareClosedThreshold≤N) (hEven : Even N) :
    (20*Real.exp (-Real.eulerMascheroniConstant)-40/(r:ℝ))*
      (SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2)≤
      (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ∧
    (jurkatRichertSourceBoundingSieve N).totalMass*
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N)≤
      (jurkatRichertMertensFactor+300/(r:ℝ))*
        (SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2) := by
  have hc := source_mass_caps hrcap
  constructor
  · convert numerical_source_mass_lower hr (hc.1.trans hN) hEven using 1
    ring
  · exact numerical_source_mass_upper hr (hc.2.trans hN) hEven

#print axioms source_mass_at_closed_threshold
end ChenEffective.H30

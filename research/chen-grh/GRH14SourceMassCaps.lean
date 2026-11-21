import GRH14SourceMass
import GRH14SourceUpperMass
import GRH14ErrorBudget

noncomputable section
namespace ChenEffective.GRH14
open Real
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 256

theorem small_power_le_target {a : ℕ} (ha : a ≤ 3^20) : a^10 ≤ targetCutoff := by
  rw [targetCutoff_eq]
  calc
    _ ≤ ((3:ℕ)^20)^10 := Nat.pow_le_pow_left ha 10
    _ = 3^200 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_product_threshold_cap {r : ℕ} (hr : r ≤ 20000000) :
    chenProductThreshold r ≤ targetCutoff := by
  have hm : mertensProductThreshold r ≤ 3^20000 := by
    unfold mertensProductThreshold
    apply max_le
    · unfold logPowerCutoff
      apply Nat.pow_le_pow_right (by norm_num)
      norm_num
    · apply Nat.pow_le_pow_right (by norm_num)
      have hs : Nat.sqrt (6*r) < 19999 := Nat.sqrt_lt.mpr (by nlinarith only [hr])
      omega
  have hplus : mertensProductThreshold r+1 ≤ 3^20001 := by
    have hp : 1 ≤ (3:ℕ)^20000 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [show (20001:ℕ)=20000+1 by norm_num,Nat.pow_succ]
    omega
  unfold chenProductThreshold
  rw [targetCutoff_eq]
  calc
    _ ≤ ((3:ℕ)^20001)^10 := Nat.pow_le_pow_left hplus 10
    _ = 3^200010 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_lower_mass_threshold_cap {r : ℕ} (hr : r ≤ 20000000) :
    sourceMassThreshold r ≤ targetCutoff := by
  unfold sourceMassThreshold
  apply max_le (source_product_threshold_cap hr)
  unfold singularNormalizationThreshold
  apply max_le
  · have hh : (2:ℕ)^110+1 ≤ 3^100 := by norm_num
    apply hh.trans
    rw [targetCutoff_eq]
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · apply small_power_le_target
    nlinarith only [hr]

theorem source_upper_mass_threshold_cap {r : ℕ} (hr : r ≤ 20000) :
    sourceUpperMassThreshold r ≤ targetCutoff := by
  unfold sourceUpperMassThreshold
  apply max_le (source_product_threshold_cap (by omega))
  apply max_le (small_power_le_target (by nlinarith only [hr]))
  apply max_le
  · rw [targetCutoff_eq]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  · rw [targetCutoff_eq]
    unfold logPowerCutoff
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem source_mass_at_target {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (20*exp (-eulerMascheroniConstant)-(1/500000:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) ≤
      (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ∧
    (jurkatRichertSourceBoundingSieve N).totalMass*
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors (jurkatRichertSourceBoundingSieve N) ≤
      (jurkatRichertMertensFactor+(3/200:ℝ))*
        (SingularSeries.liuSingularSeries N*N/log (N:ℝ)^2) := by
  constructor
  · have hh := numerical_source_mass_lower (r:=20000000) (by norm_num)
      ((source_lower_mass_threshold_cap (by norm_num)).trans hN) hEven
    convert hh using 1 <;> norm_num <;> ring
  · have hh := numerical_source_mass_upper (r:=20000) (by norm_num)
      ((source_upper_mass_threshold_cap (by norm_num)).trans hN) hEven
    convert hh using 1 <;> norm_num <;> ring

#print axioms source_mass_at_target
end ChenEffective.GRH14

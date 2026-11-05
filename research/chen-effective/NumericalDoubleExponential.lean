import NumericalTowerFinite
import NumericalSuzukiSharpBudget

noncomputable section
namespace ChenEffective
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option exponentiation.threshold 512
attribute [local irreducible] logPowerCutoff mertensProductThreshold numericalBVThreshold

private opaque doubleTopCertificate : {n : ℕ // n = 10 ^ 19} := ⟨10 ^ 19, rfl⟩
def numericalDoubleTop : ℕ := doubleTopCertificate.1
theorem numericalDoubleTop_eq : numericalDoubleTop = 10 ^ 19 := doubleTopCertificate.2

private opaque doubleBudgetCertificate : {n : ℕ // n = 10 ^ 18} := ⟨10 ^ 18, rfl⟩
def doubleBudgetExponent : ℕ := doubleBudgetCertificate.1
theorem doubleBudgetExponent_eq : doubleBudgetExponent = 10 ^ 18 := doubleBudgetCertificate.2

@[irreducible] def numericalDoubleExpCutoff : ℕ := 3 ^ (3 ^ numericalDoubleTop)
@[irreducible] def doubleAbsorptionBudget : ℕ := 3 ^ doubleBudgetExponent

theorem numericalDoubleExpCutoff_eq : numericalDoubleExpCutoff = 3 ^ (3 ^ (10 ^ 19)) := by
  rw [numericalDoubleExpCutoff, numericalDoubleTop_eq]

theorem double_budget_large : 10 ^ 100 ≤ doubleAbsorptionBudget := by
  unfold doubleAbsorptionBudget
  calc
    (10 : ℕ) ^ 100 ≤ (3 ^ 3) ^ 100 := Nat.pow_le_pow_left (by norm_num) _
    _ = 3 ^ 300 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [doubleBudgetExponent_eq]; norm_num)

theorem double_budget_one : 1 ≤ doubleAbsorptionBudget := (by norm_num : 1 ≤ (10 : ℕ) ^ 100).trans double_budget_large

theorem double_budget_tenth : doubleAbsorptionBudget ^ 10 ≤ 3 ^ numericalDoubleTop := by
  rw [doubleAbsorptionBudget, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  rw [doubleBudgetExponent_eq, numericalDoubleTop_eq]
  norm_num

theorem double_H_twenty : towerH ^ 20 ≤ numericalDoubleExpCutoff := by
  unfold towerH numericalDoubleExpCutoff
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  rw [towerU, ← pow_mul]
  calc
    _ ≤ 3 ^ (towerSeed * 100) * 3 ^ 3 := Nat.mul_le_mul_left _ (by norm_num : (20 : ℕ) ≤ 3 ^ 3)
    _ = 3 ^ (towerSeed * 100 + 3) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [towerSeed_eq, numericalDoubleTop_eq]; norm_num)

theorem double_H : towerH ≤ numericalDoubleExpCutoff :=
  (show towerH ≤ towerH ^ 20 by
    simpa only [pow_one] using Nat.pow_le_pow_right tower_H_one_nat (show 1 ≤ 20 by norm_num)).trans double_H_twenty

theorem double_base_C : baseSuzukiC ≤ doubleAbsorptionBudget := by
  have hh := exp_le_three_pow (n := doubleBudgetExponent) (x := (10 ^ 18 : ℝ))
    (by rw [doubleBudgetExponent_eq]; norm_num)
  have hc : numericalEffectiveSuzukiCoefficient ≤ (doubleAbsorptionBudget : ℝ) :=
    numericalEffectiveSuzukiCoefficient_sharp_cap.trans (by simpa only [doubleAbsorptionBudget, Nat.cast_pow, Nat.cast_ofNat] using hh)
  change ⌈max 1 numericalEffectiveSuzukiCoefficient⌉₊ ≤ doubleAbsorptionBudget
  exact Nat.ceil_le.mpr (max_le (by exact_mod_cast double_budget_one) hc)

theorem double_base_K : baseSuzukiK ≤ 10 ^ 12 := by rw [baseSuzukiK_eq]

theorem double_amplitude : sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK ≤ doubleAbsorptionBudget ^ 3 := by
  have h20 : 20 ≤ doubleAbsorptionBudget := (by norm_num : 20 ≤ (10 : ℕ) ^ 100).trans double_budget_large
  have hk : 3 ^ (Nat.sqrt baseSuzukiK + 1) ≤ doubleAbsorptionBudget := by
    unfold doubleAbsorptionBudget
    apply Nat.pow_le_pow_right (by norm_num)
    have hr : Nat.sqrt baseSuzukiK + 1 ≤ 10 ^ 7 := by
      have hh : Nat.sqrt baseSuzukiK < 10 ^ 7 := Nat.sqrt_lt'.mpr (by rw [baseSuzukiK_eq]; norm_num)
      omega
    exact hr.trans (by rw [doubleBudgetExponent_eq]; norm_num)
  unfold sqrtSuzukiAmplitudeCap
  calc
    _ ≤ doubleAbsorptionBudget * doubleAbsorptionBudget * doubleAbsorptionBudget :=
      Nat.mul_le_mul (Nat.mul_le_mul h20 double_base_C) hk
    _ = _ := by ring

theorem double_scalar_exponent_old {r : ℕ} (hr : r ≤ 10 ^ 12) :
    max 152587890625 (4096 * (sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK + 1) ^ 2 * r ^ 2) ≤
      doubleAbsorptionBudget ^ 9 := by
  have hJ : 2 ≤ doubleAbsorptionBudget := (by norm_num : 2 ≤ (10 : ℕ) ^ 100).trans double_budget_large
  have hJ3 : 1 ≤ doubleAbsorptionBudget ^ 3 := one_le_pow₀ double_budget_one
  have hp : 2 * doubleAbsorptionBudget ^ 3 ≤ doubleAbsorptionBudget ^ 4 := by
    calc
      _ ≤ doubleAbsorptionBudget * doubleAbsorptionBudget ^ 3 := Nat.mul_le_mul_right _ hJ
      _ = _ := by ring
  have ha : sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK + 1 ≤ doubleAbsorptionBudget ^ 4 := by
    nlinarith only [double_amplitude, hJ3, hp]
  have hc : 4096 * r ^ 2 ≤ doubleAbsorptionBudget :=
    (show 4096 * r ^ 2 ≤ 10 ^ 100 by nlinarith only [Nat.pow_le_pow_left hr 2]).trans double_budget_large
  apply max_le
  · exact (show 152587890625 ≤ doubleAbsorptionBudget by have hh := double_budget_large; omega).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right double_budget_one (show 1 ≤ 9 by norm_num))
  · calc
      _ = (4096 * r ^ 2) * (sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK + 1) ^ 2 := by ring
      _ ≤ doubleAbsorptionBudget * (doubleAbsorptionBudget ^ 4) ^ 2 := Nat.mul_le_mul hc (Nat.pow_le_pow_left ha 2)
      _ = _ := by ring

theorem double_scalar_exponent {r : ℕ} (hr : r ≤ 10 ^ 12) :
    max (logPowerCutoff 32) (max 152587890625 (4096 * (sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK + 1) ^ 2 * r ^ 2)) ≤
      doubleAbsorptionBudget ^ 9 := by
  have hg : logPowerCutoff 32 ≤ doubleAbsorptionBudget := by
    unfold logPowerCutoff doubleAbsorptionBudget
    apply Nat.pow_le_pow_right (by norm_num)
    rw [doubleBudgetExponent_eq]
    norm_num
  have hp : doubleAbsorptionBudget ≤ doubleAbsorptionBudget ^ 9 := by
    simpa only [pow_one] using Nat.pow_le_pow_right double_budget_one (show 1 ≤ 9 by norm_num)
  exact max_le (hg.trans hp) (double_scalar_exponent_old hr)
theorem double_suzuki_error {r : ℕ} (hr : r ≤ 10 ^ 12) :
    sqrtSuzukiErrorThreshold baseSuzukiC baseSuzukiK r ≤ numericalDoubleExpCutoff := by
  unfold sqrtSuzukiErrorThreshold numericalDoubleExpCutoff
  apply Nat.pow_le_pow_right (by norm_num)
  apply le_trans _ double_budget_tenth
  have h5 : 5 ≤ doubleAbsorptionBudget := (by norm_num : 5 ≤ (10 : ℕ) ^ 100).trans double_budget_large
  calc
    _ ≤ 5 * doubleAbsorptionBudget ^ 9 := Nat.mul_le_mul_left _ (double_scalar_exponent hr)
    _ ≤ doubleAbsorptionBudget * doubleAbsorptionBudget ^ 9 := Nat.mul_le_mul_right _ h5
    _ = _ := by ring

theorem double_upper_density {r : ℕ} (hr : r ≤ 10 ^ 12) :
    mediumUpperDensityThreshold r ≤ numericalDoubleExpCutoff := by
  let E := max (logPowerCutoff 32) (max 152587890625 (4096 * (sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK + 1) ^ 2 * r ^ 2))
  have hE : E ≤ doubleAbsorptionBudget ^ 9 := double_scalar_exponent hr
  have hJ9 : 1 ≤ doubleAbsorptionBudget ^ 9 := one_le_pow₀ double_budget_one
  have h20 : 20 ≤ doubleAbsorptionBudget := (by norm_num : 20 ≤ (10 : ℕ) ^ 100).trans double_budget_large
  have he : (E + 1) * 10 ≤ 3 ^ numericalDoubleTop := by
    apply le_trans _ double_budget_tenth
    calc
      _ ≤ 20 * doubleAbsorptionBudget ^ 9 := by nlinarith only [hE, hJ9]
      _ ≤ doubleAbsorptionBudget * doubleAbsorptionBudget ^ 9 := Nat.mul_le_mul_right _ h20
      _ = _ := by ring
  have hp : 3 ^ E + 1 ≤ 3 ^ (E + 1) := by
    have h1 : 1 ≤ 3 ^ E := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    omega
  change (3 ^ E + 1) ^ 10 ≤ numericalDoubleExpCutoff
  calc
    _ ≤ (3 ^ (E + 1)) ^ 10 := Nat.pow_le_pow_left hp 10
    _ = 3 ^ ((E + 1) * 10) := by rw [← pow_mul]
    _ ≤ 3 ^ (3 ^ numericalDoubleTop) := Nat.pow_le_pow_right (by norm_num) he
    _ = _ := by rw [numericalDoubleExpCutoff]

theorem double_base_density {r : ℕ} (hr : r ≤ 10 ^ 12) : baseDensityThreshold r ≤ numericalDoubleExpCutoff := by
  have h2 : 2 ≤ numericalDoubleExpCutoff :=
    (show 2 ≤ towerH by have hh := tower_H_large_nat; omega).trans double_H
  have hg : suzukiCoordinateThreshold ≤ towerH := tower_fixed_power (by norm_num)
  exact max_le h2 (max_le (hg.trans double_H) (double_suzuki_error hr))

theorem numerical_nLower_double_exp : nLower ≤ numericalDoubleExpCutoff :=
  nLower_le_nSquare.trans (tower_nSquare.trans double_H)

theorem numerical_N0_double_exp : N0 ≤ numericalDoubleExpCutoff := by
  have h9 : 9 ≤ numericalDoubleExpCutoff :=
    (show 9 ≤ towerH by have hh := tower_H_large_nat; omega).trans double_H
  exact max_le h9 (max_le numerical_nLower_double_exp
    (max_le (tower_nSquare.trans double_H) (tower_final_error.trans double_H)))

theorem numerical_chen_above_double_exp {N : ℕ} (hN : numericalDoubleExpCutoff ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q :=
  numerical_chen (numerical_N0_double_exp.trans hN) hEven

theorem numerical_count_above_double_exp {N : ℕ} (hN : numericalDoubleExpCutoff ≤ N) (hEven : Even N) :
    (0.67 : ℝ) * liuSingularSeries N * N / Real.log (N : ℝ) ^ 2 ≤
      ((chenGoodRepresentations N).card : ℝ) := by
  exact numerical_chen_representation_count (numerical_N0_double_exp.trans hN) hEven

#print axioms numerical_nLower_double_exp
#print axioms numerical_N0_double_exp
#print axioms numerical_chen_above_double_exp
end ChenEffective

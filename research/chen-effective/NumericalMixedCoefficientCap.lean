import NumericalMixedWindow
import NumericalC1SingleExponential

namespace ChenEffective
open Real
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem mixedSuzukiSeparator_cap : mixedSuzukiSeparator ≤ Real.exp (10 ^ 40 : ℝ) := by
  apply max_le numericalSuzukiC1_single_exp_cap
  exact mixedEndpointC1_budget.trans (Real.exp_le_exp.mpr (by norm_num))

theorem mixed_claim_coefficient_cap :
    mixedClaimCoefficient mixedSuzukiSeparator numericalLocalProductK ≤ Real.exp (10 ^ 45 : ℝ) := by
  apply max_le (Real.one_le_exp (by positivity))
  exact polynomialClaimConstant_single_exp_cap mixedSuzukiSeparator_cap
    (by linarith only [numerical_local_product_two]) numericalLocalProductK_lt.le

theorem mixed_low_strip_cap : lowStripNumericalConstant mixedSuzukiSeparator ≤ Real.exp (10 ^ 42 : ℝ) := by
  have hC10 : 0 ≤ mixedSuzukiSeparator :=
    zero_le_one.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hp := pow_le_pow_left₀ hC10 mixedSuzukiSeparator_cap 6
  have hfac : (9000 : ℝ) * (Nat.factorial 88 : ℝ) ≤ (10 : ℝ) ^ 210 := by norm_num
  have hten : (10 : ℝ) ≤ Real.exp 10 := by linarith only [Real.add_one_le_exp (10 : ℝ)]
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hten 210
  rw [← Real.exp_nat_mul] at hh
  unfold lowStripNumericalConstant
  calc
    _ = (9000 * (Nat.factorial 88 : ℝ)) * mixedSuzukiSeparator ^ 6 := by ring
    _ ≤ (10 : ℝ) ^ 210 * (Real.exp (10 ^ 40 : ℝ)) ^ 6 :=
      mul_le_mul hfac hp (by positivity) (by positivity)
    _ ≤ Real.exp ((210 : ℕ) * 10) * (Real.exp (10 ^ 40 : ℝ)) ^ 6 := by gcongr
    _ = Real.exp ((210 : ℕ) * 10 + 6 * (10 ^ 40 : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

theorem mixed_suzuki_coefficient_cap :
    mixedSuzukiCoefficient mixedSuzukiSeparator numericalLocalProductK ≤ Real.exp (10 ^ 46 : ℝ) := by
  have h4 : (4 : ℝ) ≤ Real.exp (10 ^ 45 : ℝ) := by
    linarith only [Real.add_one_le_exp (10 ^ 45 : ℝ)]
  have hclaim : 4 * mixedClaimCoefficient mixedSuzukiSeparator numericalLocalProductK ≤ Real.exp (10 ^ 46 : ℝ) := by
    calc
      _ ≤ Real.exp (10 ^ 45 : ℝ) * Real.exp (10 ^ 45 : ℝ) :=
        mul_le_mul h4 mixed_claim_coefficient_cap
          (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le
      _ = Real.exp (2 * (10 ^ 45 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  have hlow : 4 * lowStripNumericalConstant mixedSuzukiSeparator ≤ Real.exp (10 ^ 46 : ℝ) := by
    calc
      _ ≤ Real.exp (10 ^ 45 : ℝ) * Real.exp (10 ^ 42 : ℝ) :=
        mul_le_mul h4 mixed_low_strip_cap (by unfold lowStripNumericalConstant; positivity) (Real.exp_pos _).le
      _ = Real.exp ((10 ^ 45 : ℝ) + 10 ^ 42) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  exact max_le (by linarith only [Real.add_one_le_exp (10 ^ 46 : ℝ)]) (max_le hclaim hlow)

theorem numericalEffectiveSuzukiCoefficient_cap :
    numericalEffectiveSuzukiCoefficient ≤ Real.exp (10 ^ 47 : ℝ) := by
  have h2 : (2 : ℝ) ≤ Real.exp (10 ^ 46 : ℝ) := by linarith only [Real.add_one_le_exp (10 ^ 46 : ℝ)]
  unfold numericalEffectiveSuzukiCoefficient
  calc
    _ ≤ Real.exp (10 ^ 46 : ℝ) * Real.exp (10 ^ 46 : ℝ) :=
      mul_le_mul h2 mixed_suzuki_coefficient_cap
        ((by norm_num : (0 : ℝ) ≤ 36).trans (le_max_left _ _)) (Real.exp_pos _).le
    _ = Real.exp (2 * (10 ^ 46 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

#print axioms numericalEffectiveSuzukiCoefficient_cap
end ChenEffective

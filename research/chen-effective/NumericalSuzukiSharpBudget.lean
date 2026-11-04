import NumericalMixedCoefficientCap

namespace ChenEffective
open Real
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem refined_power_exp_bound (n : ℕ) : (10 : ℝ) ^ n ≤ exp (n * 10) := by
  have hh : (10 : ℝ) ≤ exp 10 := by linarith only [Real.add_one_le_exp (10 : ℝ)]
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hh n

theorem mixed_claim_coefficient_sharp_cap :
    mixedClaimCoefficient mixedSuzukiSeparator refinedLocalProductK ≤ exp (3 * (10 ^ 41 : ℝ)) := by
  let A := mixedSuzukiSeparator * refinedLocalProductK ^ (7 : ℝ)
  have hK : refinedLocalProductK ^ (7 : ℝ) ≤ exp 1000 := by
    norm_num only [refinedLocalProductK, Real.rpow_ofNat, ← pow_mul]
    have hh := (refined_power_exp_bound 84).trans (Real.exp_le_exp.mpr (by norm_num : (84 : ℝ) * 10 ≤ 1000))
    norm_num at hh
    exact hh
  have hA : A ≤ exp ((10 ^ 40 : ℝ) + 1000) := by
    calc
      _ ≤ exp (10 ^ 40 : ℝ) * exp 1000 :=
        mul_le_mul mixedSuzukiSeparator_cap hK (Real.rpow_nonneg (by norm_num [refinedLocalProductK]) _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hB : logarithmicBudget A ≤ exp ((10 ^ 40 : ℝ) + 1000) :=
    max_le (Real.one_le_exp (by positivity)) hA
  have hscale : 2 * (1 + 2 * refinedLocalProductK) ≤ exp 1000 := by
    have hh := (refined_power_exp_bound 14).trans (Real.exp_le_exp.mpr (by norm_num : (14 : ℝ) * 10 ≤ 1000))
    exact (by norm_num [refinedLocalProductK] : 2 * (1 + 2 * refinedLocalProductK) ≤ (10 : ℝ) ^ 14).trans hh
  have hR : logarithmicR A refinedLocalProductK ≤ exp ((10 ^ 40 : ℝ) + 2000) := by
    calc
      _ = logarithmicBudget A * (2 * (1 + 2 * refinedLocalProductK)) := by unfold logarithmicR; ring
      _ ≤ exp ((10 ^ 40 : ℝ) + 1000) * exp 1000 :=
        mul_le_mul hB hscale (by norm_num [refinedLocalProductK]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h1792 : (1792 : ℝ) ≤ exp 1792 := by linarith only [Real.add_one_le_exp (1792 : ℝ)]
  have hB0 : 0 ≤ logarithmicBudget A := zero_le_one.trans (le_max_left _ _)
  have hR0 : 0 ≤ logarithmicR A refinedLocalProductK := by
    unfold logarithmicR
    exact mul_nonneg (mul_nonneg (by norm_num) hB0) (by norm_num [refinedLocalProductK])
  have hpoly : polynomialClaimConstant A refinedLocalProductK ≤ exp (3 * (10 ^ 41 : ℝ)) := by
    unfold polynomialClaimConstant polynomialTerminalConstant polynomialCorrectionWeight
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    calc
      _ ≤ exp 1792 * (exp ((10 ^ 40 : ℝ) + 2000)) ^ 18 *
          (exp ((10 ^ 40 : ℝ) + 1000)) ^ 4 * exp 1000 := by
        gcongr
      _ = exp (1792 + 18 * ((10 ^ 40 : ℝ) + 2000) + 4 * ((10 ^ 40 : ℝ) + 1000) + 1000) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        norm_num
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  exact max_le (Real.one_le_exp (by positivity)) hpoly

theorem mixed_low_strip_sharp_cap : lowStripNumericalConstant mixedSuzukiSeparator ≤ exp (10 ^ 41 : ℝ) := by
  have hfac : (9000 : ℝ) * (Nat.factorial 88 : ℝ) ≤ exp 2100 :=
    (by norm_num : (9000 : ℝ) * (Nat.factorial 88 : ℝ) ≤ (10 : ℝ) ^ 210).trans
      (by simpa only [Nat.cast_ofNat, show (210 : ℝ) * 10 = 2100 by norm_num] using refined_power_exp_bound 210)
  have hC10 : 0 ≤ mixedSuzukiSeparator :=
    zero_le_one.trans ((le_max_left _ _).trans (le_max_left _ _))
  calc
    _ = (9000 * (Nat.factorial 88 : ℝ)) * mixedSuzukiSeparator ^ 6 := by unfold lowStripNumericalConstant; ring
    _ ≤ exp 2100 * (exp (10 ^ 40 : ℝ)) ^ 6 :=
      mul_le_mul hfac (pow_le_pow_left₀ hC10 mixedSuzukiSeparator_cap 6) (by positivity) (Real.exp_pos _).le
    _ = exp (2100 + 6 * (10 ^ 40 : ℝ)) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)

theorem numericalEffectiveSuzukiCoefficient_sharp_cap :
    numericalEffectiveSuzukiCoefficient ≤ exp (10 ^ 42 : ℝ) := by
  have h8 : (8 : ℝ) ≤ exp (10 ^ 41 : ℝ) := by linarith only [Real.add_one_le_exp (10 ^ 41 : ℝ)]
  have hclaim : 8 * mixedClaimCoefficient mixedSuzukiSeparator refinedLocalProductK ≤ exp (10 ^ 42 : ℝ) := by
    calc
      _ ≤ exp (10 ^ 41 : ℝ) * exp (3 * (10 ^ 41 : ℝ)) :=
        mul_le_mul h8 mixed_claim_coefficient_sharp_cap (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le
      _ = exp (4 * (10 ^ 41 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  have hlow : 8 * lowStripNumericalConstant mixedSuzukiSeparator ≤ exp (10 ^ 42 : ℝ) := by
    calc
      _ ≤ exp (10 ^ 41 : ℝ) * exp (10 ^ 41 : ℝ) :=
        mul_le_mul h8 mixed_low_strip_sharp_cap (by unfold lowStripNumericalConstant; positivity) (Real.exp_pos _).le
      _ = exp (2 * (10 ^ 41 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by norm_num)
  unfold numericalEffectiveSuzukiCoefficient mixedSuzukiCoefficient suzukiCoefficient
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply max_le
  · have hh := Real.add_one_le_exp (10 ^ 42 : ℝ)
    norm_num at hh ⊢
    linarith only [hh]
  · exact max_le (by simpa only [← mul_assoc, show (2 : ℝ) * 4 = 8 by norm_num] using hclaim)
      (by simpa only [← mul_assoc, show (2 : ℝ) * 4 = 8 by norm_num] using hlow)

#print axioms numericalEffectiveSuzukiCoefficient_sharp_cap
end ChenEffective

import NumericalMixedCoefficientCap
import NumericalTowerC1

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
attribute [local irreducible] logPowerCutoff mertensProductThreshold

theorem tower_local_exponent : localProductExponent ≤ towerU^4 := by
  have hu : 92 ≤ towerU := (by norm_num : 92 ≤ (10 : ℕ)^100).trans towerU_large
  have hu1 : 1 ≤ towerU := by omega
  norm_num only [localProductExponent,globalMertensBudget,Nat.reduceMul,Nat.reduceAdd]
  exact hu.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hu1 (show 1 ≤ 4 by norm_num))
theorem tower_local_K : numericalLocalProductK ≤ towerH := by
  have hu : 100 ≤ towerU := (by norm_num : 100 ≤ (10 : ℕ)^100).trans towerU_large
  have hu1 : 1 ≤ towerU := by omega
  have hE := tower_local_exponent
  have hu4 : 2 ≤ towerU^4 := (show 2 ≤ towerU by omega).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right hu1 (show 1 ≤ 4 by norm_num))
  have hp : 4*towerU^4 ≤ towerU^5 := by
    calc
      _ ≤ towerU*towerU^4 := Nat.mul_le_mul_right _ (by omega : 4 ≤ towerU)
      _ = _ := by ring
  have he : 3*localProductExponent+2 ≤ towerU^5 := by nlinarith only [hE,hu4,hp]
  have hf : (localProductExponent : ℝ)+2 ≤ (3 : ℝ)^(localProductExponent+2) := by
    exact_mod_cast self_le_three_pow (localProductExponent+2)
  have hK : numericalLocalProductK ≤ (3 : ℝ)^(3*localProductExponent+2) := by
    unfold numericalLocalProductK
    calc
      _ ≤ (3 : ℝ)^(localProductExponent+2)*(3 : ℝ)^(2*localProductExponent) :=
        mul_le_mul_of_nonneg_right hf (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbound : (3 : ℝ)^(3*localProductExponent+2) ≤ towerH := by
    unfold towerH
    rw [Nat.cast_pow,Nat.cast_ofNat]
    apply pow_le_pow_right₀ (by norm_num)
    exact he.trans (Nat.pow_le_pow_right hu1 (by norm_num : 5 ≤ 100))
  exact hK.trans hbound

theorem tower_base_K : baseSuzukiK ≤ towerH :=
  by rw [baseSuzukiK_eq]; exact (by norm_num : (10 : ℕ)^12 ≤ 10^100).trans (by exact_mod_cast towerH_large)

theorem tower_bounded_coefficient : boundedCaseAConstant numericalSuzukiC1 numericalLocalProductK ≤ towerV := by
  let H : ℝ := towerH
  let A := numericalSuzukiC1*numericalLocalProductK^(7 : ℝ)
  let B := logarithmicBudget A
  let R := logarithmicR A numericalLocalProductK
  let s := jointEnvelopeRadius A
  let E := 8*s*Real.log (6*s)
  let p := 7*R^3*B^4
  have hH1 : 1 ≤ H := towerH_one
  have hHbig : (10^100 : ℝ) ≤ H := towerH_large
  have hC1 : 1 ≤ numericalSuzukiC1 := le_max_left _ _
  have hK1 : 1 ≤ numericalLocalProductK := le_trans (by norm_num) numerical_local_product_two
  have hA1 : 1 ≤ A := by
    have hp := Real.one_le_rpow hK1 (by norm_num : (0 : ℝ) ≤ 7)
    dsimp [A]
    nlinarith only [mul_le_mul hC1 hp (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hC1)]
  have hA : A ≤ H^13 := by
    dsimp [A,H]
    have hp := Real.rpow_le_rpow (zero_le_one.trans hK1) tower_local_K (by norm_num : (0 : ℝ) ≤ 7)
    have hh := mul_le_mul tower_numerical_C1 hp (by positivity : 0 ≤ numericalLocalProductK^(7 : ℝ)) (by positivity : 0 ≤ (towerH : ℝ)^6)
    simpa only [Real.rpow_ofNat,← pow_add] using hh
  have hB : B ≤ H^13 := max_le (one_le_pow₀ hH1) hA
  have hB0 : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hR0 : 0 ≤ R := by dsimp [R,logarithmicR]; positivity
  have hR : R ≤ H^15 := by
    have hK : numericalLocalProductK ≤ H := tower_local_K
    have h3 : 1+2*numericalLocalProductK ≤ 3*H := by linarith only [hK,hH1]
    calc
      _ ≤ 2*H^13*(3*H) := by dsimp [R,logarithmicR]; gcongr
      _ = 6*H^14 := by ring
      _ ≤ H^15 := tower_poly_absorb hH1 (by linarith only [hHbig]) (by norm_num)
  have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 6).trans_le (jointEnvelopeRadius_six A)
  have hs : s ≤ H^15 := by
    have hb : 1+max 0 A ≤ H^14 := by
      have hmax : max 0 A ≤ H^13 := max_le (by positivity) hA
      have hp : 2*H^13 ≤ H^14 := tower_poly_absorb hH1 (by linarith only [hHbig]) (by norm_num)
      nlinarith only [hmax,hp,one_le_pow₀ hH1 (n := 13)]
    have hbase1 : 1 ≤ 1+max 0 A := le_add_of_nonneg_right (le_max_left _ _)
    have hp := Real.rpow_le_self_of_one_le hbase1 (by norm_num : (1/8 : ℝ) ≤ 1)
    calc
      _ = 6*(1+max 0 A)^(1/8 : ℝ) := rfl
      _ ≤ 6*H^14 := mul_le_mul_of_nonneg_left (hp.trans hb) (by norm_num)
      _ ≤ _ := tower_poly_absorb hH1 (by linarith only [hHbig]) (by norm_num)
  have hE : E ≤ H^31 := by
    have hl := tower_log_le_self (show 0 < 6*s by positivity)
    have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 8*s by positivity)
    have hp := pow_le_pow_left₀ hs0.le hs 2
    calc
      _ ≤ 48*s^2 := by dsimp [E]; nlinarith only [hh]
      _ ≤ 48*H^30 := by simpa only [← pow_mul] using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 48)
      _ ≤ _ := tower_poly_absorb hH1 (by linarith only [hHbig]) (by norm_num)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp : p ≤ H^98 := by
    calc
      _ ≤ 7*(H^15)^3*(H^13)^4 := by dsimp [p]; gcongr
      _ = 7*H^97 := by ring
      _ ≤ _ := tower_poly_absorb hH1 (by linarith only [hHbig]) (by norm_num)
  have hpExp : p ≤ Real.exp (H^98) := by
    have hh := Real.add_one_le_exp p
    exact (by linarith only [hh] : p ≤ Real.exp p).trans (Real.exp_le_exp.mpr hp)
  have hsqrt : Real.sqrt numericalLocalProductK ≤ H :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hK1)).trans tower_local_K
  have hsum : H^98+H^31+H ≤ H^99 := by
    have h31 : H^31 ≤ H^98 := pow_le_pow_right₀ hH1 (by norm_num)
    have h1 : H ≤ H^98 := by simpa only [pow_one] using pow_le_pow_right₀ hH1 (show 1 ≤ 98 by norm_num)
    have hp := tower_poly_absorb (n := 98) hH1 (show (3 : ℝ) ≤ H by linarith only [hHbig]) (by norm_num)
    norm_num only [Nat.reduceAdd] at hp
    nlinarith only [h31,h1,hp]
  have heq : boundedCaseAConstant numericalSuzukiC1 numericalLocalProductK = p*Real.exp E*Real.exp (Real.sqrt numericalLocalProductK) := by
    unfold boundedCaseAConstant logarithmicScalarConstant jointEnvelopeFloor
    change p/Real.exp (-8*s*Real.log (6*s))*Real.exp (Real.sqrt numericalLocalProductK) = _
    rw [show -8*s*Real.log (6*s)= -E by dsimp [E]; ring,Real.exp_neg]
    simp only [div_eq_mul_inv,inv_inv]
  rw [heq]
  calc
    _ ≤ Real.exp (H^98)*Real.exp (H^31)*Real.exp H := by gcongr
    _ = Real.exp (H^98+H^31+H) := by rw [Real.exp_add,Real.exp_add]
    _ ≤ Real.exp (H^99) := Real.exp_le_exp.mpr hsum
    _ ≤ _ := exp_H_pow_le_V (by norm_num : 99 ≤ 100) le_rfl

theorem tower_numerical_coefficient : numericalChenSuzukiCoefficient ≤ (towerV : ℝ)^2 := by
  have hVbig := towerV_large
  have hHbig := towerH_large
  have hFact : (Nat.factorial 88 : ℝ) ≤ (towerH : ℝ)^2 := by
    have hh : (Nat.factorial 88 : ℝ) ≤ (10^100 : ℝ)^2 := by norm_num
    exact hh.trans (pow_le_pow_left₀ (by positivity) hHbig 2)
  have hlow : 4*lowStripNumericalConstant numericalSuzukiC1 ≤ towerV := by
    have hC1 : 0 ≤ numericalSuzukiC1 := zero_le_one.trans (le_max_left _ _)
    calc
      _ = 36000*numericalSuzukiC1^6*(Nat.factorial 88 : ℝ) := by unfold lowStripNumericalConstant; ring
      _ ≤ 36000*((towerH : ℝ)^6)^6*(towerH : ℝ)^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC1 tower_numerical_C1 6) (by norm_num))
          hFact (by positivity) (by positivity)
      _ = 36000*(towerH : ℝ)^38 := by ring
      _ ≤ (towerH : ℝ)^39 := tower_poly_absorb towerH_one (by linarith only [hHbig]) (by norm_num)
      _ ≤ _ := towerH_pow_le_V (by norm_num)
  have hclaim : fixedClaimCoefficient numericalSuzukiC1 numericalLocalProductK ≤ towerV :=
    max_le towerV_one tower_bounded_coefficient
  have hVV : (towerV : ℝ) ≤ (towerV : ℝ)^2 := by nlinarith only [towerV_one]
  change max 36 (max (4*fixedClaimCoefficient numericalSuzukiC1 numericalLocalProductK)
    (4*lowStripNumericalConstant numericalSuzukiC1)) ≤ _
  exact max_le (by nlinarith only [hVbig,sq_nonneg ((towerV : ℝ)-1)])
    (max_le (by have hh := mul_le_mul_of_nonneg_left hclaim (by norm_num : (0 : ℝ) ≤ 4); nlinarith only [hh,hVbig,sq_nonneg ((towerV : ℝ)-2)]) (hlow.trans hVV))

theorem tower_base_C : baseSuzukiC ≤ towerV^2 := by
  have hx : (10 ^ 47 : ℝ) ≤ (towerH : ℝ) ^ 1 := by
    rw [pow_one]
    exact (by norm_num : (10 ^ 47 : ℝ) ≤ 10 ^ 100).trans towerH_large
  have hc := numericalEffectiveSuzukiCoefficient_cap.trans (exp_H_pow_le_V (by norm_num : 1 ≤ 100) hx)
  apply Nat.ceil_le.mpr
  rw [Nat.cast_pow]
  exact max_le (one_le_pow₀ towerV_one) (hc.trans (by nlinarith only [towerV_one]))
#print axioms tower_numerical_coefficient
end ChenEffective

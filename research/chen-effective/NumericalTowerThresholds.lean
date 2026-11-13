import NumericalTowerFinite

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
attribute [local irreducible] logPowerCutoff mertensProductThreshold

theorem tower_three_pow_F {n : ℕ} (hn : n ≤ towerV^100) : 3^n ≤ towerF := by
  unfold towerF
  exact Nat.pow_le_pow_right (by norm_num) hn

theorem tower_amplitude : sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK ≤ towerV^4 := by
  have hv : 20 ≤ towerV := (by norm_num : 20 ≤ (10 : ℕ)^100).trans tower_V_large_nat
  have hk : 3^(Nat.sqrt baseSuzukiK+1) ≤ towerV := by
    unfold towerV
    apply Nat.pow_le_pow_right (by norm_num)
    have hr : Nat.sqrt baseSuzukiK + 1 ≤ baseSuzukiK := by
      have hh := Nat.sqrt_lt_self (show 1 < baseSuzukiK by rw [baseSuzukiK_eq]; norm_num)
      omega
    exact hr.trans (tower_base_K.trans (by simpa only [pow_one] using Nat.pow_le_pow_right tower_H_one_nat (show 1 ≤ 100 by norm_num)))
  unfold sqrtSuzukiAmplitudeCap
  calc
    _ ≤ 20*(towerV^2)*towerV := Nat.mul_le_mul (Nat.mul_le_mul_left _ tower_base_C) hk
    _ = 20*towerV^3 := by ring
    _ ≤ towerV*towerV^3 := Nat.mul_le_mul_right _ hv
    _ = _ := by ring

theorem tower_scalar_exponent_old {r : ℕ} (hr : r ≤ 10^12) :
    max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2) ≤ towerV^11 := by
  have hv : 100 ≤ towerV := (by norm_num : 100 ≤ (10 : ℕ)^100).trans tower_V_large_nat
  have hv1 : 1 ≤ towerV^4 := one_le_pow₀ tower_V_one_nat
  have ha : sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1 ≤ towerV^5 := by
    have hh : 2*towerV^4 ≤ towerV^5 := by
      calc
        _ ≤ towerV*towerV^4 := Nat.mul_le_mul_right _ (by omega : 2 ≤ towerV)
        _ = _ := by ring
    nlinarith only [tower_amplitude,hv1,hh]
  have hc : 4096*r^2 ≤ towerV :=
    (show 4096*r^2 ≤ 10^100 by nlinarith only [Nat.pow_le_pow_left hr 2]).trans tower_V_large_nat
  apply max_le
  · exact (show 152587890625 ≤ towerV by have hh := tower_V_large_nat; omega).trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right tower_V_one_nat (show 1 ≤ 11 by norm_num))
  · calc
      _ = (4096*r^2)*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2 := by ring
      _ ≤ towerV*(towerV^5)^2 := Nat.mul_le_mul hc (Nat.pow_le_pow_left ha 2)
      _ = _ := by ring

theorem tower_scalar_exponent {r : ℕ} (hr : r ≤ 10^12) :
    max (logPowerCutoff 32) (max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2)) ≤ towerV^11 := by
  have hg : logPowerCutoff 32 ≤ towerV :=
    (tower_log_power (by norm_num : 32 ≤ 10^30)).trans tower_HV_nat
  have hp : towerV ≤ towerV ^ 11 := by
    simpa only [pow_one] using Nat.pow_le_pow_right tower_V_one_nat (show 1 ≤ 11 by norm_num)
  exact max_le (hg.trans hp) (tower_scalar_exponent_old hr)
theorem tower_suzuki_error {r : ℕ} (hr : r ≤ 10^12) : sqrtSuzukiErrorThreshold baseSuzukiC baseSuzukiK r ≤ towerF := by
  unfold sqrtSuzukiErrorThreshold
  apply tower_three_pow_F
  have hE := tower_scalar_exponent hr
  have hv : 5 ≤ towerV := (by norm_num : 5 ≤ (10 : ℕ)^100).trans tower_V_large_nat
  calc
    _ ≤ 5*towerV^11 := Nat.mul_le_mul_left _ hE
    _ ≤ towerV*towerV^11 := Nat.mul_le_mul_right _ hv
    _ = towerV^12 := by ring
    _ ≤ _ := Nat.pow_le_pow_right tower_V_one_nat (by norm_num)

theorem tower_upper_density {r : ℕ} (hr : r ≤ 10^12) : mediumUpperDensityThreshold r ≤ towerF := by
  let E := max (logPowerCutoff 32) (max 152587890625 (4096*(sqrtSuzukiAmplitudeCap baseSuzukiC baseSuzukiK+1)^2*r^2))
  have hE : E ≤ towerV^11 := tower_scalar_exponent hr
  have h1 : 1 ≤ 3^E := one_le_pow₀ (by norm_num)
  have hbase : 3^E+1 ≤ 3^(E+1) := by rw [pow_succ]; omega
  have hv : 20 ≤ towerV := (by norm_num : 20 ≤ (10 : ℕ)^100).trans tower_V_large_nat
  have hv1 : 1 ≤ towerV^11 := one_le_pow₀ tower_V_one_nat
  have h20 : 20*towerV^11 ≤ towerV^12 := by
    calc
      _ ≤ towerV*towerV^11 := Nat.mul_le_mul_right _ hv
      _ = _ := by ring
  have hExp : (E+1)*10 ≤ towerV^100 :=
    (show (E+1)*10 ≤ towerV^12 by nlinarith only [hE,hv1,h20]).trans
      (Nat.pow_le_pow_right tower_V_one_nat (by norm_num : 12 ≤ 100))
  change (3^E+1)^10 ≤ towerF
  calc
    _ ≤ (3^(E+1))^10 := Nat.pow_le_pow_left hbase 10
    _ = 3^((E+1)*10) := by rw [← pow_mul]
    _ ≤ _ := tower_three_pow_F hExp

theorem tower_base_density {r : ℕ} (hr : r ≤ 10^12) : baseDensityThreshold r ≤ towerF := by
  have hHF : towerH ≤ towerF := tower_HV_nat.trans tower_VF_nat
  have h2 : 2 ≤ towerF := (show 2 ≤ towerH by have hh := tower_H_large_nat; omega).trans hHF
  have hgate : suzukiCoordinateThreshold ≤ towerH := by
    rw [suzukiCoordinateThreshold_eq]
    exact tower_fixed_power (by norm_num)
  exact max_le h2 (max_le (hgate.trans hHF) (tower_suzuki_error hr))

theorem tower_nLower : nLower ≤ towerF :=
  nLower_le_nSquare.trans (tower_nSquare.trans (tower_HV_nat.trans tower_VF_nat))

theorem tower_N0 : N0 ≤ towerF := by
  have hHF : towerH ≤ towerF := tower_HV_nat.trans tower_VF_nat
  have h9 : 9 ≤ towerF := (show 9 ≤ towerH by have hh := tower_H_large_nat; omega).trans hHF
  exact max_le h9 (max_le tower_nLower (max_le (tower_nSquare.trans hHF) (tower_final_error.trans hHF)))

#print axioms tower_nLower
#print axioms tower_N0
end ChenEffective

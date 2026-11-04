import NumericalChenCutoff

noncomputable section
namespace ChenEffective
open Real Set Finset
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000
set_option exponentiation.threshold 512

private opaque towerSeedCertificate : {n : ℕ // n=10^12} := ⟨10^12,rfl⟩
def towerSeed : ℕ := towerSeedCertificate.1
theorem towerSeed_eq : towerSeed=10^12 := towerSeedCertificate.2
@[irreducible] def towerU : ℕ := 3^towerSeed
@[irreducible] def towerH : ℕ := 3^(towerU^100)
@[irreducible] def towerV : ℕ := 3^(towerH^100)
@[irreducible] def towerF : ℕ := 3^(towerV^100)

theorem towerU_large : 10^100 ≤ towerU := by
  unfold towerU
  calc
    (10 : ℕ)^100 ≤ (3^3)^100 := Nat.pow_le_pow_left (by norm_num) _
    _ = 3^300 := by rw [← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by rw [towerSeed_eq]; norm_num)

theorem towerU_real_large : (10^100 : ℝ) ≤ towerU := by exact_mod_cast towerU_large
theorem towerU_one : (1 : ℝ) ≤ towerU := (by norm_num : (1 : ℝ) ≤ 10^100).trans towerU_real_large
theorem towerU_pos : (0 : ℝ) < towerU := zero_lt_one.trans_le towerU_one

theorem exp_le_three_pow {x : ℝ} {n : ℕ} (hx : x ≤ n) : Real.exp x ≤ (3 : ℝ)^n := by
  calc
    _ ≤ Real.exp (n : ℝ) := Real.exp_le_exp.mpr hx
    _ = Real.exp 1^n := by rw [← Real.exp_nat_mul,mul_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le (Real.exp_one_lt_d9.le.trans (by norm_num)) n

theorem exp_seed_le_towerU : Real.exp (10^12 : ℝ) ≤ towerU := by
  have hh := exp_le_three_pow (n := towerSeed) (x := (10^12 : ℝ)) (by rw [towerSeed_eq]; norm_num)
  simpa only [towerU,Nat.cast_pow,Nat.cast_ofNat] using hh

theorem self_le_three_pow (n : ℕ) : n ≤ 3^n := by
  have h := (Real.add_one_le_exp (n : ℝ)).trans (exp_le_three_pow (n := n) le_rfl)
  have hh : (n : ℝ) ≤ (3 : ℝ)^n := by linarith only [h]
  exact_mod_cast hh

theorem towerU_pow_le_H {n : ℕ} (hn : n ≤ 100) : (towerU : ℝ)^n ≤ towerH := by
  have hh := (Nat.pow_le_pow_right (show 1 ≤ towerU by exact_mod_cast towerU_one) hn).trans (self_le_three_pow (towerU^100))
  simpa only [towerH,Nat.cast_pow,Nat.cast_ofNat] using (show ((towerU^n : ℕ) : ℝ) ≤ (3^(towerU^100) : ℕ) by exact_mod_cast hh)

theorem exp_U_pow_le_H {n : ℕ} {x : ℝ} (hn : n ≤ 100) (hx : x ≤ (towerU : ℝ)^n) : Real.exp x ≤ towerH := by
  have hh : x ≤ (towerU^100 : ℕ) := hx.trans (by exact_mod_cast (Nat.pow_le_pow_right (show 1 ≤ towerU by exact_mod_cast towerU_one) hn))
  simpa only [towerH,Nat.cast_pow,Nat.cast_ofNat] using exp_le_three_pow hh

theorem towerU_le_H : (towerU : ℝ) ≤ towerH := by simpa only [pow_one] using towerU_pow_le_H (n := 1) (by norm_num)
theorem towerH_large : (10^100 : ℝ) ≤ towerH := towerU_real_large.trans towerU_le_H
theorem towerH_one : (1 : ℝ) ≤ towerH := towerU_one.trans towerU_le_H
theorem towerH_pos : (0 : ℝ) < towerH := zero_lt_one.trans_le towerH_one

theorem towerH_pow_le_V {n : ℕ} (hn : n ≤ 100) : (towerH : ℝ)^n ≤ towerV := by
  have hh := (Nat.pow_le_pow_right (show 1 ≤ towerH by exact_mod_cast towerH_one) hn).trans (self_le_three_pow (towerH^100))
  simpa only [towerV,Nat.cast_pow,Nat.cast_ofNat] using (show ((towerH^n : ℕ) : ℝ) ≤ (3^(towerH^100) : ℕ) by exact_mod_cast hh)

theorem exp_H_pow_le_V {n : ℕ} {x : ℝ} (hn : n ≤ 100) (hx : x ≤ (towerH : ℝ)^n) : Real.exp x ≤ towerV := by
  have hh : x ≤ (towerH^100 : ℕ) := hx.trans (by exact_mod_cast (Nat.pow_le_pow_right (show 1 ≤ towerH by exact_mod_cast towerH_one) hn))
  simpa only [towerV,Nat.cast_pow,Nat.cast_ofNat] using exp_le_three_pow hh

theorem towerH_le_V : (towerH : ℝ) ≤ towerV := by simpa only [pow_one] using towerH_pow_le_V (n := 1) (by norm_num)
theorem towerV_large : (10^100 : ℝ) ≤ towerV := towerH_large.trans towerH_le_V
theorem towerV_one : (1 : ℝ) ≤ towerV := towerH_one.trans towerH_le_V
theorem towerV_pos : (0 : ℝ) < towerV := zero_lt_one.trans_le towerV_one

theorem towerV_pow_le_F {n : ℕ} (hn : n ≤ 100) : (towerV : ℝ)^n ≤ towerF := by
  have hh := (Nat.pow_le_pow_right (show 1 ≤ towerV by exact_mod_cast towerV_one) hn).trans (self_le_three_pow (towerV^100))
  simpa only [towerF,Nat.cast_pow,Nat.cast_ofNat] using (show ((towerV^n : ℕ) : ℝ) ≤ (3^(towerV^100) : ℕ) by exact_mod_cast hh)

theorem towerV_le_F : (towerV : ℝ) ≤ towerF := by simpa only [pow_one] using towerV_pow_le_F (n := 1) (by norm_num)

theorem tower_poly_absorb {u c : ℝ} {n : ℕ} (hu : 1 ≤ u) (hc : c ≤ u) (_hc0 : 0 ≤ c) : c*u^n ≤ u^(n+1) := by
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_le_one.trans hu) n) |>.trans_eq (mul_comm _ _)

theorem tower_rpow_le_nat {u a : ℝ} {n : ℕ} (hu : 1 ≤ u) (ha : a ≤ n) : u^a ≤ u^n := by
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hu ha

theorem tower_log_le_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x :=
  (Real.log_le_sub_one_of_pos hx).trans (by linarith)

#print axioms exp_U_pow_le_H
end ChenEffective

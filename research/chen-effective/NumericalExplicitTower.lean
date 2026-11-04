import NumericalTowerThresholds

noncomputable section
namespace ChenEffective
open MathlibNt.SieveTheory SwitchingPrinciple SingularSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 512

private opaque numericalTowerTopCertificate : {n : ℕ // n=10^15} := ⟨10^15,rfl⟩
def numericalTowerTop : ℕ := numericalTowerTopCertificate.1
theorem numericalTowerTop_eq : numericalTowerTop=10^15 := numericalTowerTopCertificate.2

/-- Four base-three exponentials, with the literal top exponent 10^15. -/
@[irreducible] def numericalTowerCutoff : ℕ := 3^(3^(3^(3^numericalTowerTop)))
theorem numericalTowerCutoff_eq : numericalTowerCutoff=3^(3^(3^(3^(10^15)))) := by
  rw [numericalTowerCutoff,numericalTowerTop_eq]

theorem towerF_le_explicit : towerF ≤ numericalTowerCutoff := by
  have hU1 : 1 ≤ towerU := by exact_mod_cast towerU_one
  have hU100 : 1 ≤ towerU^100 := one_le_pow₀ hU1
  have hUeq : towerU^100=3^(towerSeed*100) := by rw [towerU,← pow_mul]
  have hbottom : 5+towerSeed*100 ≤ numericalTowerTop := by
    rw [towerSeed_eq,numericalTowerTop_eq]
    norm_num
  have htop : 5+100*towerU^100 ≤ 3^numericalTowerTop := by
    calc
      _ ≤ 105*towerU^100 := by nlinarith only [hU100]
      _ ≤ (3^5)*towerU^100 := Nat.mul_le_mul_right _ (by norm_num : 105 ≤ 3^5)
      _ = 3^(5+towerSeed*100) := by rw [hUeq,pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hbottom
  have hmiddle : towerH^100*100 ≤ 3^(3^numericalTowerTop) := by
    rw [towerH,← pow_mul]
    calc
      _ ≤ (3^5)*3^(towerU^100*100) := by
        calc
          _ = 100*3^(towerU^100*100) := Nat.mul_comm _ _
          _ ≤ _ := Nat.mul_le_mul_right _ (show (100 : ℕ) ≤ 3^5 by norm_num)
      _ = 3^(5+100*towerU^100) := by rw [pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) htop
  unfold towerF numericalTowerCutoff
  apply Nat.pow_le_pow_right (by norm_num)
  rw [towerV,← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) hmiddle

theorem numerical_nLower_tower : nLower ≤ numericalTowerCutoff := tower_nLower.trans towerF_le_explicit
theorem numerical_N0_tower : N0 ≤ numericalTowerCutoff := tower_N0.trans towerF_le_explicit

/-- A concrete common integer choice for the lower and final Chen thresholds. -/
def numericalNLower : ℕ := numericalTowerCutoff
def numericalN0 : ℕ := numericalTowerCutoff

theorem numerical_lower_above_tower {N : ℕ} (hN : numericalNLower ≤ N) (hEven : Even N) :
    (2.6407 : ℝ)*liuSingularSeries N*N/Real.log (N : ℝ)^2 ≤ jurkatRichertWeightedCount N :=
  numerical_weighted_lower (numerical_nLower_tower.trans hN) hEven

theorem numerical_chen_above_tower {N : ℕ} (hN : numericalN0 ≤ N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧ (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  numerical_chen (numerical_N0_tower.trans hN) hEven

theorem numerical_count_above_tower {N : ℕ} (hN : numericalN0 ≤ N) (hEven : Even N) :
    (0.67 : ℝ)*liuSingularSeries N*N/Real.log (N : ℝ)^2 ≤ ((chenGoodRepresentations N).card : ℝ) :=
  numerical_chen_representation_count (numerical_N0_tower.trans hN) hEven

#print axioms numerical_nLower_tower
#print axioms numerical_N0_tower
#print axioms numerical_chen_above_tower
end ChenEffective

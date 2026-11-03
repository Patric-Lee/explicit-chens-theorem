import ExplicitLogBounds
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenParameterBridge

namespace ChenEffective
open Real
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def suzukiCoordinateThreshold : ℕ := 3 ^ 381469726563

theorem numerical_suzuki_coordinate_gate {N : ℕ} {ε : ℝ}
    (hN : suzukiCoordinateThreshold ≤ N) (hε0 : 0 ≤ ε) (hε : ε < 1 / 10) :
    chenS ε ≤ sourceSigma (chenLevel N ε : ℝ) 16 := by
  have hlog : (381469726563 : ℝ) ≤ Real.log (N : ℝ) :=
    log_ge_power_three (b := 381469726563) hN
  have hNpos : 0 < N := by
    have hh : 0 < suzukiCoordinateThreshold := by unfold suzukiCoordinateThreshold; positivity
    omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hB : max ((5 : ℝ) ^ (16 : ℕ)) (Real.exp 1) = (5 : ℝ) ^ (16 : ℕ) := by
    apply max_eq_left
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hβ : (2 / 5 : ℝ) ≤ 1 / 2 - ε := by linarith only [hε]
  have hpow : Real.exp ((5 : ℝ) ^ (16 : ℕ)) ≤ (N : ℝ) ^ (1 / 2 - ε) := by
    have hp : 0 < (N : ℝ) ^ (1 / 2 - ε) := Real.rpow_pos_of_pos hN0 _
    apply (Real.le_log_iff_exp_le hp).mp
    rw [Real.log_rpow hN0]
    have hh := mul_le_mul_of_nonneg_right hβ (show 0 ≤ Real.log (N : ℝ) by linarith only [hlog])
    norm_num at hh ⊢
    nlinarith only [hh, hlog]
  apply chenS_le_sourceSigma_sixteen hε0
  unfold chenSigmaThreshold
  rw [hB]
  exact hpow.trans (lt_cast_floor_add_one ((N : ℝ) ^ (1 / 2 - ε))).le

#print axioms numerical_suzuki_coordinate_gate
end ChenEffective

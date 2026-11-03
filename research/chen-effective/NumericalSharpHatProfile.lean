import NumericalHatBarrier
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerFinal

open scoped Classical BigOperators Interval
open Set Filter MeasureTheory Topology Real
namespace ChenEffective
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open Section10CanonicalXi
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem compactHatLower_log {m : ℕ} (hm : 3 ≤ m) :
    Real.log (compactHatLower m) = -Real.log 8 - 2 * (m : ℝ) * Real.log (2 * ((m : ℝ) + 1)) -
      2 * Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold compactHatLower
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by norm_num) (by norm_num), Real.log_one,
    Real.log_div (by norm_num) (by positivity), Real.log_one]
  push_cast
  ring

theorem numerical_barrier_floor_log : -(2000000000 : ℝ) ≤ Real.log numericalBarrierFloor := by
  unfold numericalBarrierFloor
  rw [Real.log_mul (by norm_num) (compactHatLower_pos (by norm_num : 3 ≤ (20000 : ℕ))).ne',
    compactHatLower_log (by norm_num : 3 ≤ (20000 : ℕ))]
  norm_num only [Nat.cast_ofNat]
  have h40002 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40002)
  have h20000 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20000)
  have h8 : Real.log 8 ≤ (3 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith only [h40002, h20000, h8, h2]

theorem numerical_phase_integral {s : ℝ} (hs : 20000 ≤ s) :
    (∫ t in (1 : ℝ)..s, xi t) ≤ s * Real.log s + s * Real.log (Real.log (3 * s)) + 18 * s := by
  have hs1 : 1 ≤ s := by linarith only [hs]
  have hs0 : 0 < s := by linarith only [hs]
  have hse : Real.exp 2 ≤ s := numerical_exp_two_le_nine.trans (by linarith only [hs])
  have hA : xi (Real.exp 2) + Real.log (xi (Real.exp 2) + 3) ≤ 18 := by
    have hx0 := xi_pos (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2))
    have hh := Real.log_le_sub_one_of_pos (show 0 < xi (Real.exp 2) + 3 by linarith only [hx0])
    linarith only [hh, numerical_xi_exp_two]
  let M := Real.log s + Real.log (Real.log (3 * s)) + 18
  have hpoint (t : ℝ) (ht : t ∈ Icc (1 : ℝ) s) : xi t ≤ M := by
    have hh := coarse_phase_uniform_on_Icc hse ht
    change xi t ≤ Real.log s + Real.log (Real.log (3 * s)) +
      (xi (Real.exp 2) + Real.log (xi (Real.exp 2) + 3)) at hh
    dsimp [M]
    linarith only [hh, hA]
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs1
  have hll : 0 ≤ Real.log (Real.log (3 * s)) := by
    apply Real.log_nonneg
    exact one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith only [hs]))
  have hM : 0 ≤ M := by dsimp [M]; linarith only [hl, hll]
  calc
    _ ≤ ∫ _t in (1 : ℝ)..s, M :=
      intervalIntegral.integral_mono_on hs1 (xi_continuous.intervalIntegrable _ _) intervalIntegrable_const hpoint
    _ = (s - 1) * M := by simp
    _ ≤ s * M := by nlinarith only [hM]
    _ = _ := by dsimp [M]; ring

/-- The source-strength leading coefficient one, with numerical C and starting point. -/
theorem numerical_sharp_hat_profile {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (sign : ErrorSign) {s : ℝ} (hs : 20000 ≤ s) :
    proposition131iiLowerProfile 60000000000 s ≤ H.T sign s := by
  have hs3 : 3 ≤ s := by linarith only [hs]
  have hs0 : 0 < s := by linarith only [hs]
  have hphase := numerical_phase_integral hs
  have hfloor := numerical_barrier_floor_log
  have hbar := numerical_Qhat_barrier hH hs
  have hcomp := numerical_Qhat_le_hat hH sign hs3
  have hlogarg := Real.log_le_sub_one_of_pos (show 0 < s + Real.exp 1 by positivity)
  have hlogK := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51200000000)
  have hExp : -s * Real.log s - s * Real.log (Real.log (3 * s)) - 60000000000 * s ≤
      Real.log numericalBarrierFloor - (∫ t in (1 : ℝ)..s, xi t) -
        12 * Real.log (s + Real.exp 1) - Real.log 51200000000 := by
    linarith only [hphase, hfloor, hlogarg, hlogK, Real.exp_one_lt_d9, hs]
  unfold proposition131iiLowerProfile
  calc
    _ ≤ Real.exp (Real.log numericalBarrierFloor - (∫ t in (1 : ℝ)..s, xi t) -
        12 * Real.log (s + Real.exp 1) - Real.log 51200000000) := Real.exp_le_exp.mpr hExp
    _ = (numericalBarrierFloor * Real.exp (-(∫ t in (1 : ℝ)..s, xi t) -
        12 * Real.log (s + Real.exp 1))) / 51200000000 := by
      rw [show Real.log numericalBarrierFloor - (∫ t in (1 : ℝ)..s, xi t) -
          12 * Real.log (s + Real.exp 1) - Real.log 51200000000 =
        (Real.log numericalBarrierFloor + (-(∫ t in (1 : ℝ)..s, xi t) -
          12 * Real.log (s + Real.exp 1))) - Real.log 51200000000 by ring,
        Real.exp_sub, Real.exp_add, Real.exp_log numericalBarrierFloor_pos, Real.exp_log (by norm_num : (0 : ℝ) < 51200000000)]
    _ ≤ section13Qhat H s / 51200000000 := div_le_div_of_nonneg_right hbar.le (by norm_num)
    _ ≤ _ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 51200000000)).mpr (by nlinarith only [hcomp])

#print axioms numerical_sharp_hat_profile
end ChenEffective

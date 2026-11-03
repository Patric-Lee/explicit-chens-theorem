import NumericalPanBudget
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPaidPrincipalReduction

namespace ChenEffective
open Real Finset
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanPrincipal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def panPrincipalConstant (s : ℕ) : ℝ := 2*panMovingPNTConstant (s+2)+2
@[irreducible] def panPrincipalThreshold (s : ℕ) : ℕ :=
  max (panMovingPNTThreshold (s+2)) (panBudgetThreshold s 0)

theorem panPrincipalConstant_pos (s : ℕ) : 0 < panPrincipalConstant s := by
  unfold panPrincipalConstant panMovingPNTConstant numericalBVConstant bvConstant
    primitiveNumericalConstant principalNumericalConstant
  positivity

/-- The actual principal Liu convolution, uniformly in its modulus and window. -/
theorem numerical_pan_principal_error (s N : ℕ) (hN : panPrincipalThreshold s ≤ N)
    (q A₁ A₂ : ℕ) (hq : 1 ≤ q) (hqN : (q : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)) :
    |principalError N A₁ A₂ q| ≤ panPrincipalConstant s * N/Real.log (N : ℝ)^s := by
  have hn := hN
  unfold panPrincipalThreshold at hn
  have hmove := (le_max_left _ _).trans hn
  have hpay := (le_max_right _ _).trans hn
  have hN9 : 9 ≤ N := by
    unfold panBudgetThreshold at hpay
    exact (logPowerCutoff_nine_le _).trans hpay
  have hAN : A₂ ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hK : 0 ≤ panMovingPNTConstant (s+2) := by
    unfold panMovingPNTConstant numericalBVConstant bvConstant
      primitiveNumericalConstant principalNumericalConstant
    positivity
  have hb := principalError_le_budget N A₁ A₂ q
    (panMovingPNTConstant (s+2)*N/Real.log (N : ℝ)^(s+2)) (by omega) hAN (by positivity) (by
      intro a ha
      exact numerical_primeCount_li_moving (s+2) N hmove a
        (by have hh := (mem_Ioc.mp ha).1; omega)
        ((show (a : ℝ) ≤ A₂ by exact_mod_cast (mem_Ioc.mp ha).2).trans hA))
  have hp := numerical_pan_budget s 0 N hpay (panMovingPNTConstant (s+2)) hK
    q A₂ 1 hq hqN hA (by simp)
  exact hb.trans (by simpa only [Nat.add_zero, Nat.cast_one, one_mul, panPrincipalConstant] using hp)

theorem numerical_pan_actual_paid_principal (s N : ℕ) (hN : panPrincipalThreshold s ≤ N)
    (B : ℝ) (q : ℕ) (hq : 1 ≤ q) (hqN : (q : ℝ) ≤ Real.sqrt N) :
    liuPanActualError (2/Real.log 2) N B q ≤
      (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
        (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) +
          panPrincipalConstant s*N/Real.log (N : ℝ)^s) / q.totient := by
  have hp := numerical_pan_principal_error s N hN q
    (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) hq hqN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  rw [principalError_eq_liuPanActualPrincipalRaw] at hp
  exact (liuWeight_intervalMaxL_le_nonprincipal_add_principal (2/Real.log 2)
    N (liuSourceZ10 N) (liuSourceY3 N) _ _ q hq).trans
      (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

#print axioms numerical_pan_principal_error
#print axioms numerical_pan_actual_paid_principal
end ChenEffective

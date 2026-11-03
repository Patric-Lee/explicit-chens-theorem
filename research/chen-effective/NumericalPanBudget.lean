import NumericalPanPrincipalPNT
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPayment

namespace ChenEffective
open Real
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

@[irreducible] def panBudgetThreshold (U b : ℕ) : ℕ := logPowerCutoff (3*(U+b+1))

/-- Numerical payment of the prime-deletion and harmonic losses in a Pan cell. -/
theorem numerical_pan_budget (U b N : ℕ) (hN : panBudgetThreshold U b ≤ N)
    (K : ℝ) (hK : 0 ≤ K) (m A₂ Q : ℕ)
    (hm : 1 ≤ m) (hmN : (m : ℝ) ≤ Real.sqrt N)
    (hA : (A₂ : ℝ) ≤ (N : ℝ)^(2/3 : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ)^b) :
    (Q : ℝ)*((K*N/Real.log (N : ℝ)^(U+b+2))*(1+Real.log N)+
      (A₂ : ℝ)*(m.primeFactors.card : ℝ)) ≤
        (2*K+2)*N/Real.log (N : ℝ)^U := by
  have hn := hN
  unfold panBudgetThreshold at hn
  have hN9 : 9 ≤ N := (logPowerCutoff_nine_le _).trans hn
  have hL : 1 ≤ Real.log (N : ℝ) := log_one_le_of_eight_le (by omega)
  have hlog := log_pow_le_rpow_inv_explicit (k := U+b+1) (m := 3)
    (by norm_num) (le_refl _) hn
  have hlog' : Real.log (N : ℝ)^((U : ℝ)+(b : ℝ)+1) ≤ (N : ℝ)^(1/3 : ℝ) := by
    rw [show (U : ℝ)+(b : ℝ)+1 = ((U+b+1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
    exact hlog
  have hmX : (m : ℝ) ≤ N := hmN.trans
    (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1 ≤ N by omega))))
  have hcard := PanLow.primeFactors_card_le_log_of_le (by omega : 0 < m) hmX
  have htwo : (Real.log 2)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀' (Real.log_pos (by norm_num))]
    linarith [Real.log_two_gt_d9]
  have hW : (m.primeFactors.card : ℝ) ≤ 2*Real.log (N : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right htwo (zero_le_one.trans hL))
  have hh := PanLow.low_budget_scalar
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) hL
    (Nat.cast_nonneg A₂) (Nat.cast_nonneg m.primeFactors.card) (Nat.cast_nonneg Q)
    hK (by norm_num : (0 : ℝ) ≤ 2) hA hW
    (show (Q : ℝ) ≤ Real.log (N : ℝ)^(b : ℝ) by simpa only [Real.rpow_natCast] using hQ) hlog'
  simpa only [show (U : ℝ)+(b : ℝ)+2 = ((U+b+2 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] using hh

#print axioms numerical_pan_budget
end ChenEffective

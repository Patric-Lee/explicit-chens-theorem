import DusartPort.Psi1Estimate
import BJSMertensThetaTarget
import DusartMertens

/-! The restricted Dusart estimate and the sharp prefix/interval estimates
needed for Chen. All analytic inputs are theorems; the only nonstandard
axiom is the existing Dirichlet seven-eighths hypothesis. -/
noncomputable section
namespace ChenEffective
open Real AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000

theorem dusart_theta_scalar_131 {L : ℝ} (hL : 131 ≤ L) :
    (3 / 4) * L ^ 2 * exp (-L / 16) ≤ 4 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ht := add_one_le_exp ((L - 131) / 32)
  have hlin : L ≤ 131 * exp ((L - 131) / 32) := by nlinarith only [hL, ht]
  have hs := pow_le_pow_left₀ hL0 hlin 2
  have hex : exp ((L - 131) / 32) ^ 2 = exp ((L - 131) / 16) := by
    rw [sq, ← exp_add]
    congr 1
    ring
  rw [mul_pow, hex] at hs
  have hn : (3 / 4 : ℝ) * 131 ^ 2 ≤ 4 * exp (131 / 16 : ℝ) := by
    have he : (2718 / 1000 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718 / 1000) he 8
    rw [← exp_nat_mul] at h8
    have hh := mul_le_mul h8 (add_one_le_exp (3 / 16 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 3 / 16 + 1) (exp_pos _).le
    rw [← exp_add] at hh
    norm_num at hh ⊢
    linarith only [hh]
  have hp : exp ((L - 131) / 16) * exp (-L / 16) = exp (-131 / 16 : ℝ) := by
    rw [← exp_add]
    congr 1
    ring
  have hpay := mul_le_mul_of_nonneg_right hn (exp_pos (-131 / 16 : ℝ)).le
  have hcancel : exp (131 / 16 : ℝ) * exp (-131 / 16) = 1 := by
    rw [← exp_add]
    norm_num
  calc
    _ ≤ (3 / 4) * (131 ^ 2 * exp ((L - 131) / 16)) * exp (-L / 16) := by gcongr
    _ = (3 / 4) * 131 ^ 2 * exp (-131 / 16 : ℝ) := by
      calc
        _ = (3 / 4) * 131 ^ 2 * (exp ((L - 131) / 16) * exp (-L / 16)) := by ring
        _ = _ := by rw [hp]
    _ ≤ 4 := by nlinarith only [hpay, hcancel]

theorem dusart_theta_from_presieve {x : ℝ} (hx : (3 : ℝ) ^ (120 : ℕ) ≤ x) :
    |Chebyshev.theta x - x| ≤ 4 * x / (log x) ^ 2 := by
  have hx0 : 0 < x := (pow_pos (by norm_num : (0 : ℝ) < 3) 120).trans_le hx
  have hthree : (131 / 120 : ℝ) ≤ log 3 := by
    have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  have hlogx := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) 120) hx
  rw [log_pow] at hlogx
  norm_num only [Nat.cast_ofNat] at hlogx
  have hL : 131 ≤ log x := by linarith only [hlogx, hthree]
  have hL0 : 0 < log x := by linarith only [hL]
  have he := dusart_theta_scalar_131 hL
  have hr : x ^ (15 / 16 : ℝ) = x * exp (-log x / 16) := by
    calc
      _ = exp (log x + (-log x / 16)) := by rw [rpow_def_of_pos hx0]; congr 1; ring
      _ = _ := by rw [exp_add, exp_log hx0]
  apply (Dusart.numerical_theta_target hx).trans
  apply (le_div_iff₀ (sq_pos_of_pos hL0)).mpr
  rw [hr]
  have hh := mul_le_mul_of_nonneg_left he hx0.le
  nlinarith only [hh]

theorem dusart_sharp_mertens {x : ℝ} (hx : (3 : ℝ) ^ (120 : ℕ) ≤ x) :
    |primeReciprocalSum ⌊x⌋₊ - (log (log x) + mertensSecondConstant)| ≤
      1 / (2 * (log x) ^ 2) :=
  bjsStudy_prefix_at_presieve_of_theta_target hx
    (fun _t ht => Dusart.numerical_theta_target (hx.trans ht))

theorem dusart_sharp_prime_interval (s : Finset ℕ) (a b : ℝ)
    (ha : (3 : ℝ) ^ (120 : ℕ) ≤ a) (hab : a ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1 / (p : ℝ)) ≤ log (log b / log a) + 1 / (log a) ^ 2 :=
  bjsStudy_presieve_interval_of_theta_target (fun _t ht => Dusart.numerical_theta_target ht)
    s a b ha hab hs

#print axioms dusart_theta_from_presieve
#print axioms dusart_sharp_mertens
#print axioms dusart_sharp_prime_interval
end ChenEffective

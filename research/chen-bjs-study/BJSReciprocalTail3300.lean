import BJSReciprocalLargeEndpoint

/-! A sharper explicit starting point for the power-saving Mertens tail.
The exponential decay is retained instead of absorbing logarithms by a
global power bound. No finite-prefix or BJS interval assumption is used.
-/
noncomputable section
namespace ChenEffective
open Real Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 0

theorem bjsStudy_power_error_log_squared_3300 {a : ℝ}
    (ha : 0 < a) (hlog : 3300 ≤ log a) :
    60000000000000*a^(-1/68 : ℝ) ≤ 1/(log a)^2 := by
  let L := log a
  have hL : 3300 ≤ L := hlog
  have hL0 : 0 < L := by linarith only [hL]
  have ht := add_one_le_exp ((L-3300)/136)
  have hlin : L ≤ 3300*exp ((L-3300)/136) := by nlinarith only [hL,ht]
  have hsq := pow_le_pow_left₀ hL0.le hlin 2
  have hexsq : (exp ((L-3300)/136))^2=exp ((L-3300)/68) := by
    rw [sq,← exp_add]
    congr 1
    ring
  rw [mul_pow,hexsq] at hsq
  have hnum : (60000000000000 : ℝ)*3300^2 ≤ exp 48 := by
    have he : (2718/1000 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000) he 48
    rw [← exp_nat_mul] at hh
    norm_num at hh ⊢
    linarith only [hh]
  have hprod : exp ((L-3300)/68)*exp (-L/68)=exp (-3300/68 : ℝ) := by
    rw [← exp_add]
    congr 1
    ring
  have hpay : 60000000000000*3300^2*exp (-3300/68 : ℝ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hnum (exp_pos (-3300/68 : ℝ)).le
    have hex : exp (48 : ℝ)*exp (-3300/68 : ℝ) ≤ 1 := by
      rw [← exp_add,← exp_zero]
      exact exp_le_exp.mpr (by norm_num)
    exact hh.trans hex
  have hrpow : a^(-1/68 : ℝ)=exp (-L/68) := by
    rw [rpow_def_of_pos ha]
    congr 1
    dsimp [L]
    ring
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < log a from hL0))).mpr
  rw [hrpow]
  calc
    60000000000000*exp (-L/68)*L^2 ≤
        60000000000000*exp (-L/68)*(3300^2*exp ((L-3300)/68)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 60000000000000*3300^2*exp (-3300/68 : ℝ) := by
      calc
        _ = 60000000000000*3300^2*(exp ((L-3300)/68)*exp (-L/68)) := by ring
        _ = _ := by rw [hprod]
    _ ≤ 1 := hpay

theorem bjsStudy_reciprocal_prefix_from_3300 {a : ℝ}
    (ha : 0 < a) (hlog : 3300 ≤ log a) :
    |primeReciprocalSum ⌊a⌋₊-(log (log a)+mertensSecondConstant)| ≤
      1/(2*(log a)^2) := by
  have ha9 : 9 ≤ a := by linarith only [hlog,log_le_sub_one_of_pos ha]
  have he := bjsStudy_power_error_log_squared_3300 ha hlog
  have hp := optimized_mertens_power ha9
  have hid : 2*(1/(2*(log a)^2))=1/(log a)^2 := by ring
  linarith only [he,hp,hid]

#print axioms bjsStudy_reciprocal_prefix_from_3300

theorem bjsStudy_log_three_lower : (13/12 : ℝ) ≤ log 3 := by
  have hh := sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1) 2
  norm_num [Finset.sum_range_succ] at hh
  linarith only [hh]

theorem bjsStudy_reciprocal_prefix_from_3072 {a : ℝ}
    (ha : (3 : ℝ)^(3072 : ℕ) ≤ a) :
    |primeReciprocalSum ⌊a⌋₊-(log (log a)+mertensSecondConstant)| ≤
      1/(2*(log a)^2) := by
  have ha0 : 0 < a := (pow_pos (by norm_num : (0 : ℝ) < 3) 3072).trans_le ha
  have hh := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) 3072) ha
  rw [log_pow] at hh
  have hlog : 3300 ≤ log a := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,bjsStudy_log_three_lower]
  exact bjsStudy_reciprocal_prefix_from_3300 ha0 hlog

theorem bjsStudy_interval_from_3072 (s : Finset ℕ) (a b : ℝ)
    (ha : (3 : ℝ)^(3072 : ℕ) ≤ a) (hab : a ≤ b)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p ∈ s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  have ha0 : 0 < a := (pow_pos (by norm_num : (0 : ℝ) < 3) 3072).trans_le ha
  have hh := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) 3072) ha
  rw [log_pow] at hh
  have hlog : 3300 ≤ log a := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,bjsStudy_log_three_lower]
  have ha9 : 9 < a := by linarith only [hlog,log_le_sub_one_of_pos ha0]
  have hp := bjsStudy_interval_power s ha9 hab hs
  have he := bjsStudy_power_error_log_squared_3300 ha0 hlog
  linarith only [hp,he]

end ChenEffective

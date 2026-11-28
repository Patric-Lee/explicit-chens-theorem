import GRHQuarterChenCore

noncomputable section
namespace ChenEffective.GRHQuarterChen
open Real Finset
set_option maxHeartbeats 3000000

theorem source_upper_accuracy_minimal {r : ℕ} (hr : 0<r)
    (hpay : (125/2:ℝ)/(r:ℝ)≤21/1000) : 2977≤r := by
  have hh := (div_le_iff₀ (show (0:ℝ)<r by exact_mod_cast hr)).mp hpay
  have hn : (2976:ℝ)<r := by linarith only [hh]
  have hnNat : 2976<r := by exact_mod_cast hn
  omega

/-- Minimal integer exponent for this source-mass accuracy package.
This does not assert optimality over all possible Chen sieve budgets. -/
theorem source_accuracy_exponent_minimal {r E : ℕ} (hr : 0<r)
    (hpay : (125/2:ℝ)/(r:ℝ)≤21/1000) (hE : 40*r+1≤E) : 119081≤E := by
  have hh := source_upper_accuracy_minimal hr hpay
  omega

theorem targetCutoff_lt_double_exp_11782 :
    (targetCutoff:ℝ)<exp (exp (5891/500:ℝ)) := by
  have he1 : (2718281828/1000000000:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have ht := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤99/1000) 6
  have hp : (0:ℝ)≤∑ i∈range 6,(99/1000:ℝ)^i/(i.factorial:ℝ) := by positivity
  have hh := mul_le_mul he1 ht hp (exp_pos 1).le
  rw [←exp_add] at hh
  norm_num [Finset.sum_range_succ] at hh
  have h3 : (3:ℝ)≤exp (1099/1000:ℝ) := by linarith only [hh]
  have hlog3 := log_le_log (by norm_num : (0:ℝ)<3) h3
  rw [log_exp] at hlog3
  have hlog : log (targetCutoff:ℝ)≤119081*(1099/1000:ℝ) := by
    rw [targetCutoff_eq,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlog3]
  have he11 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718281828/1000000000) he1 11
  rw [←exp_nat_mul] at he11
  norm_num only [Nat.cast_ofNat,mul_one] at he11
  have ht8 := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤391/500) 9
  have hp8 : (0:ℝ)≤∑ i∈range 9,(391/500:ℝ)^i/(i.factorial:ℝ) := by positivity
  have hm := mul_le_mul he11 ht8 hp8 (exp_pos 11).le
  rw [←exp_add] at hm
  norm_num [Finset.sum_range_succ] at hm
  have he : 119081*(1099/1000:ℝ)<exp (5891/500:ℝ) := by norm_num at hm ⊢;linarith only [hm]
  have hpos : (0:ℝ)<(targetCutoff:ℕ) := by unfold targetCutoff;positivity
  apply (log_lt_log_iff hpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

#print axioms targetCutoff_lt_double_exp_11782
end ChenEffective.GRHQuarterChen
end

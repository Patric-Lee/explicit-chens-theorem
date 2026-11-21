import GRHSharpTruncationPayment

/-! A smaller candidate cutoff. This proves numerical budget facts only;
it does not assert a Chen theorem at the new cutoff. -/
noncomputable section
namespace ChenEffective.GRHSharp
open Real
set_option maxHeartbeats 3000000
private opaque exponentCertificate : {n : ℕ // n=580000} := ⟨580000,rfl⟩
def targetExponent : ℕ := exponentCertificate.1
theorem targetExponent_eq : targetExponent=580000 := exponentCertificate.2
def targetCutoff : ℕ := 3^targetExponent

theorem target_log_lower {N : ℕ} (hN : targetCutoff≤N) :
    (637000:ℝ)≤log (N:ℝ) := by
  have hpow : (2:ℝ)^84 ≤ (3:ℝ)^53 := by norm_num
  have hh := log_le_log (by positivity : (0:ℝ)<(2:ℝ)^84) hpow
  rw [log_pow,log_pow] at hh
  have h3 : (637/580:ℝ) ≤ log 3 := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,log_two_gt_d9]
  have he : (0:ℝ)<(targetCutoff:ℕ) := by
    exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  have hl := log_le_log he (show (targetCutoff:ℝ)≤N by exact_mod_cast hN)
  simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow] at hl
  rw [targetExponent_eq] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl,h3]

theorem targetCutoff_lt_double_exp_13_37 :
    (targetCutoff:ℝ)<exp (exp (1337/100:ℝ)) := by
  have he1 : (2718/1000:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have he11 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 11
  rw [← exp_nat_mul] at he11
  norm_num only [Nat.cast_ofNat,mul_one] at he11
  have h311 : (3:ℝ)^10≤exp 11 := by norm_num at he11 ⊢; linarith only [he11]
  have hlog3 := log_le_log (by positivity : (0:ℝ)<(3:ℝ)^10) h311
  rw [log_pow,log_exp] at hlog3
  have hlog : log (targetCutoff:ℝ)≤638000 := by
    simp only [targetCutoff,Nat.cast_pow,Nat.cast_ofNat,log_pow]
    rw [targetExponent_eq]
    norm_num only [Nat.cast_ofNat] at hlog3 ⊢
    linarith only [hlog3]
  have he13 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) he1 13
  rw [← exp_nat_mul] at he13
  norm_num only [Nat.cast_ofNat,mul_one] at he13
  have he37 : (1446/1000:ℝ)≤exp (37/100:ℝ) := by
    have hh := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤37/100) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    linarith only [hh]
  have hm := mul_le_mul he13 he37 (by norm_num : (0:ℝ)≤1446/1000) (exp_pos _).le
  rw [← exp_add] at hm
  have hnum : (638000:ℝ)<(2718/1000:ℝ)^13*(1446/1000) := by norm_num
  have he : (638000:ℝ)<exp (1337/100:ℝ) := by
    norm_num at hnum hm ⊢
    linarith only [hnum,hm]
  have htpos : (0:ℝ)<(targetCutoff:ℕ) := by
    exact_mod_cast (show 0<targetCutoff by unfold targetCutoff; positivity)
  apply (log_lt_log_iff htpos (exp_pos _)).mp
  rw [log_exp]
  exact hlog.trans_lt he

#print axioms target_log_lower
#print axioms targetCutoff_lt_double_exp_13_37
end ChenEffective.GRHSharp

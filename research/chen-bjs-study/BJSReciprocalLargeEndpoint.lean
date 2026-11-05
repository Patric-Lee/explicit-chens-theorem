import BJSReciprocalIntervalBridge

/-! The requested interval error is proved above an explicit large endpoint.
This uses the existing Dirichlet axiom only, not bjsStudy_interval. The
range below this endpoint is still a separate proof obligation.
-/
noncomputable section
namespace ChenEffective
open Real Finset AnalyticNumberTheory.Mertens
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

theorem bjsStudy_power_error_log_squared {a : ℝ} (ha : 0 < a) (hlog : 8192 ≤ log a) :
    60000000000000*a^(-1/68 : ℝ) ≤ 1/(log a)^2 := by
  have hl0 : 0 < log a := by linarith only [hlog]
  have hl := log_le_rpow_div ha.le (by norm_num : (0 : ℝ)<1/272)
  have hbound : log a≤272*a^(1/272 : ℝ) := by
    convert hl using 1
    ring
  have hsq := pow_le_pow_left₀ hl0.le hbound 2
  have hpow : (a^(1/272 : ℝ))^2=a^(1/136 : ℝ) := by
    rw [← rpow_natCast,← rpow_mul ha.le]
    norm_num
  rw [mul_pow,hpow] at hsq
  have hnum : (60000000000000 : ℝ)*272^2 ≤ exp 60 := by
    have he : (5/2 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤5/2) he 60
    rw [← exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith only [hp]
  have heq : a^(-1/136 : ℝ)=exp (-log a/136) := by
    rw [rpow_def_of_pos ha]
    congr 1
    ring
  have hex : exp (-log a/136) ≤ exp (-60) := exp_le_exp.mpr (by linarith only [hlog])
  have hexid : exp (60 : ℝ)*exp (-60)=1 := by rw [← exp_add]; norm_num
  have hpay : 60000000000000*272^2*a^(-1/136 : ℝ)≤1 := by
    rw [heq]
    have hh := mul_le_mul hnum hex (exp_pos _).le (exp_pos _).le
    simpa only [hexid] using hh
  apply (le_div_iff₀ (sq_pos_of_pos hl0)).mpr
  calc
    _ ≤ (60000000000000*a^(-1/68 : ℝ))*(272^2*a^(1/136 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 60000000000000*272^2*a^(-1/136 : ℝ) := by
      rw [show (60000000000000*a^(-1/68 : ℝ))*(272^2*a^(1/136 : ℝ))=
        60000000000000*272^2*(a^(-1/68 : ℝ)*a^(1/136 : ℝ)) by ring,
        ← rpow_add ha]
      norm_num
    _ ≤ 1 := hpay

theorem bjsStudy_interval_large_endpoint (s : Finset ℕ) (a b : ℝ)
    (ha : (3 : ℝ)^(8192 : ℕ) ≤ a) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p∈s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  have ha0 : 0 < a := (pow_pos (by norm_num : (0 : ℝ)<3) 8192).trans_le ha
  have hh := log_le_log (pow_pos (by norm_num : (0 : ℝ)<3) 8192) ha
  rw [log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog : 8192 ≤ log a := by linarith only [hh,one_le_log_three]
  have ha9 : 9 < a := by linarith only [hlog,log_le_sub_one_of_pos ha0]
  have hp := bjsStudy_interval_power s ha9 hab hs
  have he := bjsStudy_power_error_log_squared ha0 hlog
  linarith only [hp,he]

theorem bjsStudy_reciprocal_prefix_large {a : ℝ} (ha : (3 : ℝ)^(8192 : ℕ) ≤ a) :
    |primeReciprocalSum ⌊a⌋₊-(log (log a)+mertensSecondConstant)| ≤ 1/(2*(log a)^2) := by
  have ha0 : 0 < a := (pow_pos (by norm_num : (0 : ℝ)<3) 8192).trans_le ha
  have hh := log_le_log (pow_pos (by norm_num : (0 : ℝ)<3) 8192) ha
  rw [log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog : 8192 ≤ log a := by linarith only [hh,one_le_log_three]
  have ha9 : 9 ≤ a := by linarith only [hlog,log_le_sub_one_of_pos ha0]
  have he := bjsStudy_power_error_log_squared ha0 hlog
  have hp := optimized_mertens_power ha9
  have hid : 2*(1/(2*(log a)^2))=1/(log a)^2 := by ring
  linarith only [he,hp,hid]

/-- Explicitly isolate the remaining bounded-endpoint input. Neither
premise is asserted or introduced as an axiom, and the study's final
theorem does not use this reduction to conceal its provisional assumption. -/
theorem bjsStudy_interval_of_middle_prefix
    (hL : ∀ x : ℝ, 1 < x → x<(3 : ℝ)^(8192 : ℕ) →
      log (log x)+mertensSecondConstant-1/(2*(log x)^2) ≤ primeReciprocalSum ⌊x⌋₊)
    (hU : ∀ x : ℝ, 286 ≤ x → x<(3 : ℝ)^(8192 : ℕ) →
      primeReciprocalSum ⌊x⌋₊ ≤ log (log x)+mertensSecondConstant+1/(2*(log x)^2))
    (s : Finset ℕ) (a b : ℝ) (ha : 1 < a) (hb : 286 ≤ b) (hab : a ≤ b)
    (hs : ∀ p∈s, p.Prime ∧ a≤(p : ℝ) ∧ (p : ℝ) ≤ b) :
    (∑ p∈s, 1/(p : ℝ)) ≤ log (log b/log a)+1/(log a)^2 := by
  apply bjsStudy_interval_of_half_log_squared_prefix (B:=mertensSecondConstant) ?_ ?_ s a b ha hb hab hs
  · intro x hx
    by_cases ht : (3 : ℝ)^(8192 : ℕ) ≤ x
    · have he := (abs_le.mp (bjsStudy_reciprocal_prefix_large ht)).1
      linarith only [he]
    · exact hL x hx (lt_of_not_ge ht)
  · intro x hx
    by_cases ht : (3 : ℝ)^(8192 : ℕ) ≤ x
    · have he := (abs_le.mp (bjsStudy_reciprocal_prefix_large ht)).2
      linarith only [he]
    · exact hU x hx (lt_of_not_ge ht)

#print axioms bjsStudy_interval_large_endpoint
#print axioms bjsStudy_interval_of_middle_prefix
end ChenEffective

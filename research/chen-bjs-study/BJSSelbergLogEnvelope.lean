import BJSSelbergSpecialization

/-! A numerical relaxed denominator with the complete logarithmic envelope
retained. This is a proved improvement to this component, not a new Chen N0. -/
noncomputable section
namespace ChenEffective
open Real
open MathlibNt.SieveTheory LiuWeight SingularSeries
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 512

theorem selberg_log_envelope_at_ninety {H : ℝ} (hH : 90 ≤ H) :
    (10^24 : ℝ)*(1+H)^6*exp (-H) ≤ 3/2000 := by
  have ht : 0 ≤ H-90 := by linarith
  have he := add_one_le_exp ((H-90)/6)
  have hlin : 1+H ≤ 91*exp ((H-90)/6) := by nlinarith only [he,ht]
  have hp := pow_le_pow_left₀ (by linarith only [hH] : 0 ≤ 1+H) hlin 6
  have hex : exp ((H-90)/6)^6=exp (H-90) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [mul_pow,hex] at hp
  have hc : exp (H-90)*exp (-H)=exp (-90 : ℝ) := by
    rw [← exp_add]
    congr 1
    ring
  have hn : (10^24 : ℝ)*91^6 ≤ (3/2000 : ℝ)*exp (90 : ℝ) := by
    have he1 : (27/10 : ℝ) ≤ exp 1 := by linarith only [exp_one_gt_d9]
    have he90 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he1 90
    rw [← exp_nat_mul] at he90
    norm_num only [Nat.cast_ofNat,mul_one] at he90
    have hsmall : (10^24 : ℝ)*91^6 ≤ (3/2000 : ℝ)*(27/10)^90 := by norm_num
    nlinarith only [hsmall,he90]
  have hc90 : exp (90 : ℝ)*exp (-90 : ℝ)=1 := by rw [← exp_add]; norm_num
  have hpaid := mul_le_mul_of_nonneg_right hn (exp_pos (-90:ℝ)).le
  calc
    _ ≤ (10^24 : ℝ)*(91^6*exp (H-90))*exp (-H) := by gcongr
    _ = (10^24 : ℝ)*91^6*(exp (H-90)*exp (-H)) := by ring
    _ = (10^24 : ℝ)*91^6*exp (-90 : ℝ) := by rw [hc]
    _ ≤ _ := by nlinarith only [hpaid,hc90]

private opaque jointSelbergCutoffCertificate : {n : ℕ // n=3^(3^83)} :=
  ⟨3^(3^83),rfl⟩
def jointSelbergDenominatorThreshold : ℕ := jointSelbergCutoffCertificate.1
theorem jointSelbergDenominatorThreshold_eq : jointSelbergDenominatorThreshold=3^(3^83) :=
  jointSelbergCutoffCertificate.2

private theorem joint_divisor_power_bound {b : ℕ} (hb : 30 ≤ b) :
    bjsStudyDivisorThreshold ≤ 3^(3^b) := by
  unfold bjsStudyDivisorThreshold
  apply Nat.pow_le_pow_right (by norm_num)
  rw [bjsStudyMertensEndpoint_eq]
  exact Nat.pow_le_pow_right (by norm_num) hb

theorem joint_selberg_log_parameters {N : ℕ} (hN : jointSelbergDenominatorThreshold ≤ N) :
    20000 ≤ log (N:ℝ) ∧ 90 ≤ log (log (N:ℝ)) ∧ bjsStudyDivisorThreshold ≤ N := by
  rw [jointSelbergDenominatorThreshold_eq] at hN
  have hL := log_ge_power_three hN
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hL
  have h20 : (20000 : ℝ) ≤ log (N:ℝ) := (by norm_num : (20000:ℝ) ≤ 3^83).trans hL
  have hH := log_le_log (by positivity : (0:ℝ) < 3^83) hL
  rw [log_pow] at hH
  norm_num only [Nat.cast_ofNat] at hH
  have hl3 : (109/100 : ℝ) ≤ log 3 := by
    have hh := sum_range_le_log_div (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1) 3
    norm_num [Finset.sum_range_succ] at hh
    linarith only [hh]
  refine ⟨h20,by linarith only [hl3,hH],?_⟩
  exact (joint_divisor_power_bound (by norm_num : 30 ≤ 83)).trans hN

theorem joint_selberg_denominator_81 {N : ℕ}
    (hN : jointSelbergDenominatorThreshold ≤ N) (hEven : Even N) :
    log (N:ℝ)/((81/10:ℝ)*liuSingularSeries N) ≤ liuSelbergDenominator N squareEpsilon := by
  obtain ⟨hL,hH,hDiv⟩ := joint_selberg_log_parameters hN
  have hNpos : 0 < N := by
    by_contra hh
    have : N=0 := by omega
    subst N
    norm_num at hL
  have hlogN := log_le_sub_one_of_pos (show (0:ℝ) < N by exact_mod_cast hNpos)
  have hN256 : 256 ≤ N := by exact_mod_cast (by linarith only [hL,hlogN] : (256:ℝ) ≤ N)
  have hp := selberg_log_envelope_at_ninety hH
  have hLp : 0 < log (N:ℝ) := by linarith only [hL]
  rw [exp_neg,exp_log hLp] at hp
  have hE : (10^24:ℝ)*(1+log (log (N:ℝ)))^6 ≤ (3/2000)*log (N:ℝ) := by
    exact (div_le_iff₀ hLp).mp (by simpa only [div_eq_mul_inv] using hp)
  apply selberg_denominator_from_current_envelope hN256 hDiv hEven
    (by norm_num [squareEpsilon,squareEpsilonDenominator]) (by norm_num)
  have hl2 : log (2:ℝ) ≤ 1 := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  norm_num [squareEpsilon,squareEpsilonDenominator,div_eq_mul_inv] at *
  nlinarith only [hE,hL,hl2]

#print axioms joint_selberg_denominator_81
end ChenEffective

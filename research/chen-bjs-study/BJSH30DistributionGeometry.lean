import BJSH30PrimeIntervals
import NumericalBV
import ExplicitChenLower

noncomputable section
namespace ChenEffective.H30
open Real
open MathlibNt.SieveTheory LiuWeight
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem log_ten_cap : log (10:ℝ)≤12/5 := by
  have he : (27/10:ℝ)≤exp 1 := by linarith only [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤27/10) he 12
  rw [← exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hn : (10:ℝ)^5≤exp 12 := (by norm_num : (10:ℝ)^5≤150094635296999121/1000000000000).trans hp
  have hl := log_le_log (by positivity : (0:ℝ)<10^5) hn
  rw [log_pow,log_exp] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

theorem log_linear_budget {L : ℝ} (hL : (10^13:ℝ)≤L) :
    (3*10^11:ℝ)*log L≤L := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hh := log_le_sub_one_of_pos (div_pos hLp (by norm_num : (0:ℝ)<10^13))
  rw [log_div hLp.ne' (by norm_num),log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have ht := log_ten_cap
  nlinarith only [hh,ht,hL]

theorem source_modulus_of_log (B m N : ℕ) (hm : 0 < m)
    (hL : (10^13:ℝ)≤log (N:ℝ)) (hBudget : m*B≤3*10^11) :
    liuSourceDEpsilon N (1/(m:ℝ)) ≤ panModulusCutoff N (B:ℝ) := by
  have hn9 := (numerical_prime_pair_parameters (show (10^12:ℝ)≤log (N:ℝ) by linarith only [hL])).1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hlogL : 0≤log (log (N:ℝ)) := log_nonneg (by linarith only [hL])
  have hb : ((m:ℝ)*B)*log (log (N:ℝ))≤log (N:ℝ) := by
    have hc : (m:ℝ)*B≤3*10^11 := by exact_mod_cast hBudget
    exact (mul_le_mul_of_nonneg_right hc hlogL).trans (log_linear_budget hL)
  have hpow : log (N:ℝ)^B≤(N:ℝ)^(1/(m:ℝ)) := by
    apply (log_le_log_iff (pow_pos hl _) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have he : (1/(m:ℝ))*log (N:ℝ)=log (N:ℝ)/(m:ℝ) := by ring
    rw [he]
    apply (le_div_iff₀ hmR).mpr
    nlinarith only [hb]
  unfold liuSourceDEpsilon panModulusCutoff
  apply Nat.floor_mono
  rw [rpow_sub hn,rpow_natCast]
  exact div_le_div_of_nonneg_left (rpow_nonneg hn.le _) (pow_pos hl _) hpow

private opaque distributionCertificate : {n : ℕ // n=10^13} := ⟨10^13,rfl⟩
def distributionExponent : ℕ := distributionCertificate.1
theorem distributionExponent_eq : distributionExponent=10^13 := distributionCertificate.2
@[irreducible] def distributionThreshold : ℕ := 3^distributionExponent

theorem distribution_log {N : ℕ} (hN : distributionThreshold≤N) : (10^13:ℝ)≤log (N:ℝ) := by
  unfold distributionThreshold at hN
  have hh := log_ge_power_three hN
  rw [distributionExponent_eq] at hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

theorem distribution_bv_cap {A : ℕ} (hA : A≤30) : numericalBVThreshold A≤distributionThreshold := by
  rw [numerical_BV_threshold_closed]
  unfold distributionThreshold
  apply Nat.pow_le_pow_right (by decide)
  rw [distributionExponent_eq]
  calc
    _ ≤ 16*(384*30+13569)^2 := by gcongr
    _ ≤ _ := by norm_num

#print axioms source_modulus_of_log
end ChenEffective.H30

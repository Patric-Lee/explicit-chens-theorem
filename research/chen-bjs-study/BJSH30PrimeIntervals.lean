import DusartPort.Application
import NumericalPrimePairInterval
import NumericalGenuineLiPointwise

/-! Sharp reciprocal-prime intervals at the endpoints used by Chen.
The existing Dusart producer is already applicable here at H <= 30. -/
noncomputable section
namespace ChenEffective.H30
open Real Finset
open MathlibNt.SieveTheory LiuWeight PrimeReciprocalLogScale
open AnalyticNumberTheory.Mertens
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem numerical_prime_pair_parameters {N : ℕ} (hL : (10^12:ℝ)≤log (N:ℝ)) :
    9≤N ∧ (10^12:ℝ)≤log (N:ℝ) ∧
      (logPowerCutoff 2:ℝ)≤(N:ℝ)^(1/10:ℝ) ∧
      (logPowerCutoff 2:ℝ)≤(N:ℝ)^(1/10:ℝ) := by
  have hn : 0<N := by
    by_contra h
    have he : N=0 := by omega
    subst N
    norm_num at hL
  have hnR : (0:ℝ)<N := by exact_mod_cast hn
  have hh := log_le_sub_one_of_pos hnR
  have hn9 : 9≤N := by exact_mod_cast (by linarith only [hL,hh] : (9:ℝ)≤N)
  have hroot : (logPowerCutoff 2:ℝ)≤(N:ℝ)^(1/10:ℝ) := by
    simp only [logPowerCutoff,Nat.cast_pow,Nat.cast_ofNat]
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hnR _)).mp
    rw [log_pow,log_rpow hnR]
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,Nat.reducePow,Nat.reduceMul]
    linarith only [hL,hl3]
  exact ⟨hn9,hL,hroot,hroot⟩

theorem numerical_prime_pair_prefix {N : ℕ} (hL : (10^12:ℝ)≤log (N:ℝ))
    {a : ℝ} (ha : 1/10≤a) :
    |MertensTheorem.primeReciprocalSum (rpowFloor N a)-
      (log a+log (log (N:ℝ))+mertensSecondConstant)|≤50/log (N:ℝ)^2 := by
  have hn9 := (numerical_prime_pair_parameters hL).1
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hl : 0<log (N:ℝ) := by linarith only [hL]
  have ha0 : 0<a := by linarith only [ha]
  have hx : (3:ℝ)^120≤(N:ℝ)^a := by
    apply (log_le_log_iff (by positivity) (rpow_pos_of_pos hn _)).mp
    rw [log_pow,log_rpow hn]
    have hla := mul_le_mul_of_nonneg_right ha hl.le
    have hl3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat]
    linarith only [hL,hla,hl3]
  have hh := dusart_sharp_mertens hx
  rw [log_rpow hn,log_mul ha0.ne' hl.ne'] at hh
  rw [MertensTheorem.primeReciprocalSum_eq_analyticNumberTheory,rpowFloor]
  apply hh.trans
  apply (div_le_div_iff₀ (by positivity : 0<2*(a*log (N:ℝ))^2) (sq_pos_of_pos hl)).mpr
  have hla := mul_le_mul_of_nonneg_right ha hl.le
  have hs := pow_le_pow_left₀ (show 0≤log (N:ℝ)/10 by positivity)
    (show log (N:ℝ)/10≤a*log (N:ℝ) by linarith only [hla]) 2
  nlinarith only [hs]

theorem numerical_prime_pair_interval {N : ℕ} (hL : (10^12:ℝ)≤log (N:ℝ))
    {a b : ℝ} (ha : 1/10≤a) (hab : a≤b) (_hb : b≤1) :
    primeReciprocalLogInterval N a b≤log (b/a)+100/log (N:ℝ)^2 := by
  have hn9 := (numerical_prime_pair_parameters hL).1
  have hpa := numerical_prime_pair_prefix hL ha
  have hpb := numerical_prime_pair_prefix hL (ha.trans hab)
  rw [primeReciprocalLogInterval_eq_sub N (by omega) hab,
    log_div (by linarith only [ha,hab] : b≠0) (by linarith only [ha] : a≠0)]
  simp only [div_eq_mul_inv] at hpa hpb ⊢
  linarith only [(abs_le.mp hpa).1,(abs_le.mp hpb).2]

#print axioms numerical_prime_pair_interval
end ChenEffective.H30

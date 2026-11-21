import GRH14MediumGrid
import GRH14MediumIntegralCaps

noncomputable section
namespace ChenEffective.GRH14
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

def mediumUpperProfile (a : ℝ) : ℝ :=
  (jurkatRichertMertensFactor+3/200)*mediumPrimeProfile a+
    (14413/4000:ℝ)*mediumKernelProfile a+(27533/40000:ℝ)*mediumHatProfile a

theorem medium_pointwise_budget {a s : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3))
    (hs : (3/2:ℝ) ≤ s) (hst : s ≤ 5-10*a) (hshift : 5-10*a-s ≤ 71/1000) :
    (jurkatRichertMertensFactor+3/200)*
      (jurkatRichertUpperLinearSieveFactor s+110*(1/2000:ℝ)*exp 2*sieveHat s) ≤ mediumUpperProfile a := by
  let B := jurkatRichertMertensFactor
  let X := jurkatRichertUpperLinearSieveFactor s-jurkatRichertUpperLinearSieveFactor (5-10*a)
  have hBmin : (1:ℝ) ≤ B := mertens_factor_lower_one
  have hBpos : 0 ≤ B := by linarith only [hBmin]
  have hK : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hstep : B*X ≤ (71/20:ℝ)*mediumKernelProfile a := by
    have hh := upper_factor_window hs hst (show 5-10*a ≤ (4:ℝ) by linarith only [ha.1]) hshift
    convert hh using 1 <;> dsimp only [B,X,mediumKernelProfile] <;> ring
  have hX : (B+3/200)*X ≤ (14413/4000:ℝ)*mediumKernelProfile a := by
    by_cases hx : 0 ≤ X
    · have hh := mul_le_mul_of_nonneg_right hBmin hx
      have hh' := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 203/200)
      nlinarith only [hh,hh',hstep]
    · have hx' : X ≤ 0 := le_of_not_ge hx
      have hh := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ B+3/200 by linarith only [hBpos]) hx'
      nlinarith only [hh,hK]
  have hHat : exp 2*sieveHat s ≤ mediumHatProfile a := by
    unfold mediumHatProfile
    apply mul_le_mul_of_nonneg_left _ (exp_pos 2).le
    apply sieveHat_antitone
    linarith only [hshift]
  have hHat0 : 0 ≤ exp 2*sieveHat s := mul_nonneg (exp_pos 2).le (sieveHat_pos s).le
  have hHatScaled := mul_le_mul
    (show B+3/200 ≤ (2503/200:ℝ) by have := budget_mertens_factor_cap; dsimp only [B]; linarith)
    hHat hHat0 (by norm_num : (0:ℝ) ≤ 2503/200)
  unfold mediumUpperProfile mediumPrimeProfile
  dsimp only [X,B] at *
  nlinarith only [hX,hHatScaled]

theorem medium_profile_nonneg {a : ℝ} (ha : a∈Icc (1/10:ℝ) (1/3)) :
    0 ≤ mediumUpperProfile a := by
  have hf := (numerical_medium_profile ha ha).1
  have hB : 0 ≤ jurkatRichertMertensFactor := by unfold jurkatRichertMertensFactor; positivity
  have hk : 0 ≤ mediumKernelProfile a := by unfold mediumKernelProfile; positivity
  have hh : 0 ≤ mediumHatProfile a := mul_nonneg (exp_pos 2).le (sieveHat_pos _).le
  unfold mediumUpperProfile
  positivity

theorem medium_profile_prime_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(27/25:ℝ) := by
  let B := jurkatRichertMertensFactor
  have hBpos : 0 ≤ B := by dsimp only [B]; unfold jurkatRichertMertensFactor; positivity
  have hbase := mul_le_mul_of_nonneg_left (numerical_medium_prime_unshifted hN)
    (show 0 ≤ B+3/200 by linarith only [hBpos])
  have hk := mul_le_mul_of_nonneg_left (medium_kernel_prime_sum hN) (by norm_num : (0:ℝ) ≤ 14413/4000)
  have hh := mul_le_mul_of_nonneg_left (medium_hat_prime_sum hN) (by norm_num : (0:ℝ) ≤ 27533/40000)
  have heq : MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) =
      (B+3/200)*MertensTheorem.weightedPrimeReciprocalLogSum mediumPrimeProfile N (1/10) (1/3)+
      (14413/4000:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumKernelProfile N (1/10) (1/3)+
      (27533/40000:ℝ)*MertensTheorem.weightedPrimeReciprocalLogSum mediumHatProfile N (1/10) (1/3) := by
    unfold MertensTheorem.weightedPrimeReciprocalLogSum
    rw [mul_sum,mul_sum,mul_sum,← sum_add_distrib,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    dsimp only [mediumUpperProfile,B]
    ring
  have hI := medium_integral_small_cap.2
  have hBc : B ≤ (25/2:ℝ) := budget_mertens_factor_cap
  have hmain := numerical_medium_integral_coefficient
  rw [heq]
  dsimp only [B] at *
  nlinarith only [hbase,hk,hh,hI,hBc,hmain]

theorem medium_prime_large {N q : ℕ} (hN : targetCutoff ≤ N)
    (hq : q∈jurkatRichertSourceMediumPrimes N) : 1000001 ≤ q := by
  have hr := (numerical_prime_pair_parameters hN).2.2.1
  have hc : (1000000:ℝ) ≤ (logPowerCutoff 2:ℝ) := by
    exact_mod_cast (show (1000000:ℕ) ≤ logPowerCutoff 2 by unfold logPowerCutoff; norm_num)
  have hqLower := (mem_filter.mp hq).2.2.1
  have hh : (1000000:ℝ)<q := (hc.trans hr).trans_lt hqLower
  exact_mod_cast hh

theorem medium_profile_source_sum {N : ℕ} (hN : targetCutoff ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1)) ≤ jurkatRichertQ1MainCoefficient jurkatRichertK+(1081/1000:ℝ) := by
  have hN9 := (numerical_prime_pair_parameters hN).1
  have hN1 : 1 ≤ N := by have := (numerical_prime_pair_parameters hN).1; omega
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) =
      MertensTheorem.weightedPrimeReciprocalLogSum mediumUpperProfile N (1/10) (1/3) := by
    rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor hN1]
    rfl
  have hpoint : ∀ q ∈ jurkatRichertSourceMediumPrimes N,
      mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)*(mediumUpperProfile (log (q:ℝ)/log (N:ℝ))/(q:ℝ)) := by
    intro q hq
    have hqBig : (1000001:ℝ) ≤ q := by exact_mod_cast medium_prime_large hN hq
    have hq0 : (0:ℝ)<q := by linarith only [hqBig]
    have hqm : 0<(q:ℝ)-1 := by linarith only [hqBig]
    have hf := medium_profile_nonneg (jurkatRichertSourceMediumPrime_log_mem (by omega : 1<N) hq)
    have hr : (1:ℝ)/((q:ℝ)-1) ≤ (1+1/1000000:ℝ)/(q:ℝ) :=
      (div_le_div_iff₀ hqm hq0).mpr (by nlinarith only [hqBig])
    have hh := mul_le_mul_of_nonneg_left hr hf
    convert hh using 1 <;> ring
  have hh := sum_le_sum hpoint
  rw [← mul_sum,hsum] at hh
  have hp := mul_le_mul_of_nonneg_left (medium_profile_prime_sum hN)
    (by norm_num : (0:ℝ) ≤ 1+1/1000000)
  have hQ : jurkatRichertQ1MainCoefficient jurkatRichertK ≤ (75/2:ℝ) := by
    rw [← numerical_medium_integral_coefficient]
    exact (mul_le_mul budget_mertens_factor_cap medium_integral_small_cap.2
      medium_integral_small_cap.1 (by norm_num)).trans (by norm_num)
  linarith only [hh,hp,hQ]

#print axioms medium_profile_source_sum
end ChenEffective.GRH14

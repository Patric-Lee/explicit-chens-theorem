/- Threshold-specialized companion to research/chen-bjs-study/BJSStudyMediumReciprocal.lean.
The original producer is retained. This companion rechecks its proof with
tighter numerical caps in the namespace ChenEffective.H30Conditional. -/
import BJSH30ConditionalMediumPrimeShift
import BJSH30ConditionalProducts
import BJSH30ConditionalMediumPrimeShift

noncomputable section
namespace ChenEffective.H30Conditional
open Real Set Finset
open MathlibNt.SieveTheory SwitchingPrinciple
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- A direct bound on the actual medium-prime reciprocal mass. This replaces
the old factor 22 in the density-error payment. -/
theorem bjsStudy_medium_reciprocal {N : ℕ} (hN : mediumPrimeSumThreshold ≤ N) :
    (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤ 8/5 := by
  have hPair : primePairThreshold ≤ N := hN
  obtain ⟨h9,hlog,_,_⟩ := numerical_prime_pair_parameters hPair
  have hcutN : (10+1)^10 ≤ N :=
    (Nat.pow_le_pow_left (by norm_num [mediumPrimeBudget] : 10+1 ≤ mediumPrimeBudget+2) 10).trans
      (medium_prime_root_cutoff.trans hN)
  have hcut := numerical_source_cutoff (by norm_num : 2 ≤ (10 : ℕ)) hcutN
  have hroot : (10 : ℝ) ≤ (N : ℝ)^(1/10 : ℝ) := by
    have hh : (10 : ℝ) ≤ (jurkatRichertSourceZ N-1 : ℕ) := by exact_mod_cast hcut
    apply hh.trans
    simpa only [jurkatRichertSourceZ,Nat.add_sub_cancel] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (1/10 : ℝ))
  have hsum : (∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/((q : ℝ)-1)) ≤
      (10/9)*PrimeReciprocalLogScale.primeReciprocalLogInterval N (1/10) (1/3) := by
    calc
      _ ≤ (10/9)*∑ q ∈ jurkatRichertSourceMediumPrimes N, 1/(q : ℝ) := by
        rw [Finset.mul_sum]
        apply sum_le_sum
        intro q hq
        have hq10 := hroot.trans_lt (mem_filter.mp hq).2.2.1
        have hq0 : (0 : ℝ) < q := by linarith only [hq10]
        have hqm : 0 < (q : ℝ)-1 := by linarith only [hq10]
        rw [show (10/9 : ℝ)*(1/(q : ℝ))=(10/9)/(q : ℝ) by ring,
          div_le_div_iff₀ hqm hq0]
        linarith only [hq10]
      _ = _ := by
        congr 1
        rw [jurkatRichertSourceMediumPrimes_eq_Ioc_rpowFloor (by omega : 1 ≤ N)]
        unfold PrimeReciprocalLogScale.primeReciprocalLogInterval
        rw [← numerical_prime_interval_carrier]
  have he : (100:ℝ)/log (N:ℝ)^2 ≤ 1/100 := by
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10^12) hlog 2
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith only [hlog]))).mpr
    linarith only [hs]
  have hm := numerical_prime_pair_interval hPair (a := 1/10) (b := 1/3)
    (by norm_num) (by norm_num) (by norm_num)
  have hl : log ((1/3 : ℝ)/(1/10)) ≤ 7/5 := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < (1/3 : ℝ)/(1/10))
      (show (1/3 : ℝ)/(1/10) ≤ 4 by norm_num)
    rw [show (4 : ℝ)=2^2 by norm_num,log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,log_two_lt_d9]
  nlinarith only [hsum,hm,hl,he]

#print axioms bjsStudy_medium_reciprocal
end ChenEffective.H30Conditional

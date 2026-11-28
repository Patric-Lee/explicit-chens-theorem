import GRHH10PrimeIntervals

/-! The actual medium-prime harmonic mass, with a numerical constant.
This removes the 4 (log N)^2 majorant from subsequent tail aggregation. -/
noncomputable section
namespace ChenEffective.H10Band
open Real Finset
open MathlibNt.SieveTheory.SwitchingPrinciple
set_option maxHeartbeats 3000000

theorem intervalError_small {L : ℝ} (hL : 2400≤L) : intervalError L≤1/1000 := by
  apply (intervalError_antitone (by norm_num : (0:ℝ)<2400) hL).trans
  rw [intervalError_closed (by norm_num : (0:ℝ)<2400)]
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤15) 3
  norm_num [Finset.sum_range_succ] at he
  have hm := mul_le_mul_of_nonneg_right he (exp_pos (-15:ℝ)).le
  rw [←exp_add] at hm
  norm_num at hm ⊢
  nlinarith only [hm]

theorem actual_medium_prime_mass_cap {N : ℕ} (hL : (2400:ℝ)≤log (N:ℝ)) :
    (∑ q∈jurkatRichertSourceMediumPrimes N,1/(q:ℝ))≤121/100 := by
  have he := sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤1209/1000) 7
  norm_num [Finset.sum_range_succ] at he
  have he' : (10/3:ℝ)≤exp (1209/1000:ℝ) := by linarith only [he]
  have hl := log_le_log (by norm_num : (0:ℝ)<10/3) he'
  rw [log_exp] at hl
  have hm := actual_medium_prime_mass hL
  have hs := intervalError_small hL
  linarith only [hl,hm,hs]

theorem medium_aggregate_of_reciprocal_majorant {N : ℕ}
    (hL : (2400:ℝ)≤log (N:ℝ)) {A : ℝ} (hA : 0≤A) (f : ℕ→ℝ)
    (hf : ∀ q∈jurkatRichertSourceMediumPrimes N, f q≤A/(q:ℝ)) :
    (∑ q∈jurkatRichertSourceMediumPrimes N,f q)≤(121/100:ℝ)*A := by
  have hh := sum_le_sum hf
  have heq : (∑ q∈jurkatRichertSourceMediumPrimes N,A/(q:ℝ))=
      A*(∑ q∈jurkatRichertSourceMediumPrimes N,1/(q:ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    ring
  rw [heq] at hh
  have hp := mul_le_mul_of_nonneg_left (actual_medium_prime_mass_cap hL) hA
  exact hh.trans (hp.trans_eq (by ring))

#print axioms intervalError_small
#print axioms actual_medium_prime_mass_cap
#print axioms medium_aggregate_of_reciprocal_majorant
end ChenEffective.H10Band
end

import BJSHybridSieveSums
import BJSHybridPrimeBlock

namespace ChenEffective.HybridProduct.BitSieve
open Finset
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem fixedSieveBlock_eq {n bits start len : ℕ} (hs : IsSieve n bits)
    (hend : start+len ≤ n+1) (scale : ℕ) :
    fixedSieveRange bits scale start len = fixedPrimeBlock scale start (start+len) := by
  rw [fixedSieveRange_eq]
  unfold fixedPrimeBlock blockPrimes
  apply Prod.ext
  · simp only [Finset.sum_filter,Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
    apply sum_congr rfl
    intro i hi
    have hp : start+i ≤ n := by have := mem_range.mp hi; omega
    have hf := primeFlag_iff hs hp
    by_cases hprime : (start+i).Prime
    · have hh := hf.mpr hprime
      simp [sieveTerm,hh,hprime]
    · have hh : primeFlag bits (start+i)=false := Bool.eq_false_iff.mpr (fun h => hprime (hf.mp h))
      simp [sieveTerm,hh,hprime]
  · simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel_left]
    apply sum_congr rfl
    intro i hi
    have hp : start+i ≤ n := by have := mem_range.mp hi; omega
    have hf := primeFlag_iff hs hp
    by_cases hprime : (start+i).Prime
    · have hh := hf.mpr hprime
      simp [sieveTerm,hh,hprime]
    · have hh : primeFlag bits (start+i)=false := Bool.eq_false_iff.mpr (fun h => hprime (hf.mp h))
      simp [sieveTerm,hh,hprime]

theorem reciprocal_block_of_sieve_certificate {n bits scale start len Q count : ℕ}
    (hs : IsSieve n bits) (hend : start+len ≤ n+1) (hscale : 0 < scale)
    (hcert : fixedSieveRange bits scale start len=(Q,count)) :
    (Q:ℝ)/scale ≤ ∑ p ∈ blockPrimes start (start+len),1/(p:ℝ) ∧
      (∑ p ∈ blockPrimes start (start+len),1/(p:ℝ)) ≤ ((Q:ℝ)+count)/scale := by
  exact prime_block_of_certificate hscale ((fixedSieveBlock_eq hs hend scale).symm.trans hcert)

#print axioms reciprocal_block_of_sieve_certificate
end ChenEffective.HybridProduct.BitSieve

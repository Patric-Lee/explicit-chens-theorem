import BJSHybridPrimeCertificate

namespace ChenEffective.HybridProduct
open Finset
set_option maxHeartbeats 1500000

def blockPrimes (lo hi : ℕ) : Finset ℕ := (Ico lo hi).filter Nat.Prime

def fixedPrimeBlock (scale lo hi : ℕ) : ℕ × ℕ :=
  ((blockPrimes lo hi).sum (fun p => scale/p),(blockPrimes lo hi).card)

theorem prime_block_of_certificate {scale lo hi Q count : ℕ} (hs : 0 < scale)
    (hcert : fixedPrimeBlock scale lo hi=(Q,count)) :
    (Q:ℝ)/scale ≤ ∑ p ∈ blockPrimes lo hi,1/(p:ℝ) ∧
      (∑ p ∈ blockPrimes lo hi,1/(p:ℝ)) ≤ ((Q:ℝ)+count)/scale := by
  have hq := congrArg Prod.fst hcert
  have hc := congrArg Prod.snd hcert
  change (blockPrimes lo hi).sum (fun p => scale/p)=Q at hq
  change (blockPrimes lo hi).card=count at hc
  have hp (p : ℕ) (h : p ∈ blockPrimes lo hi) : 0 < p :=
    ((Finset.mem_filter.mp h).2).pos
  constructor
  · have h := sum_le_sum (s:=blockPrimes lo hi) (fun p h =>
      (reciprocal_floor_bounds hs (hp p h)).1)
    simpa only [← Finset.sum_div,← Nat.cast_sum,hq] using h
  · have h := sum_le_sum (s:=blockPrimes lo hi) (fun p h =>
      (reciprocal_floor_bounds hs (hp p h)).2)
    simpa only [← Finset.sum_div,Finset.sum_add_distrib,← Nat.cast_sum,hq,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hc] using h

#print axioms prime_block_of_certificate
end ChenEffective.HybridProduct

import AnalyticNumberTheory.Mertens.Basic

namespace ChenEffective.HybridProduct
open Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1500000

def fixedPrimePrefix (scale n : ℕ) : ℕ × ℕ :=
  ((primesUpTo n).sum (fun p => scale/p),(primesUpTo n).card)

theorem reciprocal_floor_bounds {scale p : ℕ} (hs : 0 < scale) (hp : 0 < p) :
    ((scale/p:ℕ):ℝ)/scale ≤ 1/(p:ℝ) ∧
      1/(p:ℝ) ≤ (((scale/p:ℕ):ℝ)+1)/scale := by
  have hsR : (0:ℝ) < scale := by exact_mod_cast hs
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  constructor
  · apply (div_le_div_iff₀ hsR hpR).mpr
    norm_num only [one_mul]
    exact_mod_cast Nat.div_mul_le_self scale p
  · apply (div_le_div_iff₀ hpR hsR).mpr
    norm_num only [one_mul]
    exact_mod_cast (show scale ≤ (scale/p+1)*p by
      simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ scale hp).le)

/-- A computed certificate bounds the actual reciprocal-prime prefix.
The producer of hcert may use kernel reduction, but no compiler axiom. -/
theorem prime_prefix_of_certificate {scale n Q count : ℕ} (hs : 0 < scale)
    (hcert : fixedPrimePrefix scale n=(Q,count)) :
    (Q:ℝ)/scale ≤ primeReciprocalSum n ∧
      primeReciprocalSum n ≤ ((Q:ℝ)+count)/scale := by
  have hq : (primesUpTo n).sum (fun p => scale/p)=Q := congrArg Prod.fst hcert
  have hc : (primesUpTo n).card=count := congrArg Prod.snd hcert
  constructor
  · have h := sum_le_sum (s:=primesUpTo n) (fun p hp =>
      (reciprocal_floor_bounds hs (mem_primesUpTo.mp hp).1.pos).1)
    simpa only [primeReciprocalSum,← Finset.sum_div,← Nat.cast_sum,hq] using h
  · have h := sum_le_sum (s:=primesUpTo n) (fun p hp =>
      (reciprocal_floor_bounds hs (mem_primesUpTo.mp hp).1.pos).2)
    simpa only [primeReciprocalSum,← Finset.sum_div,Finset.sum_add_distrib,
      ← Nat.cast_sum,hq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hc] using h

#print axioms prime_prefix_of_certificate
end ChenEffective.HybridProduct

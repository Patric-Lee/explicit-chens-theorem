import BJSHybridSieveCorrect
import BJSHybridPrimeCertificate

namespace ChenEffective.HybridProduct.BitSieve
open Finset AnalyticNumberTheory.Mertens
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Read primality from a certified wheel bitset; no trial division is performed. -/
def primeFlag (bits p : ℕ) : Bool :=
  if p < 5 then (p == 2 || p == 3)
  else (p % 6 == 1 || p % 6 == 5) && testBitK bits (indexK p)

theorem primeFlag_iff {n bits p : ℕ} (hs : IsSieve n bits) (hp : p ≤ n) :
    primeFlag bits p = true ↔ p.Prime := by
  unfold primeFlag
  split
  · rename_i hsmall
    interval_cases p <;> norm_num
  · rename_i hlarge
    have hp5 : 5 ≤ p := by omega
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨hmod,hbit⟩
      have hcop := coprime6_mod.mpr hmod
      have hv := value_index hcop
      rw [testBitK_eq_testBit,indexK_eq_index] at hbit
      have hz : index p ≠ 0 := by have := index_pos (show 4 ≤ p by omega); omega
      have hh := (hs (index p) hz (by rw [hv]; exact hp)).mp hbit
      rwa [hv] at hh
    · intro hprime
      have hcop := hprime.coprime_six (by omega) (by omega)
      have hv := value_index hcop
      refine ⟨coprime6_mod.mp hcop,?_⟩
      rw [testBitK_eq_testBit,indexK_eq_index]
      exact (hs (index p) (by have := index_pos (show 4 ≤ p by omega); omega)
        (by rw [hv]; exact hp)).mpr (by rwa [hv])

def sieveTerm (bits scale p : ℕ) : ℕ × ℕ :=
  if primeFlag bits p then (scale/p,1) else (0,0)

/-- A bounded kernel-reducible fixed-point sum and prime count. -/
def fixedSieveRange (bits scale start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0,0)
  | len+1 =>
    let a := fixedSieveRange bits scale start len
    let b := sieveTerm bits scale (start+len)
    (a.1+b.1,a.2+b.2)

theorem fixedSieveRange_eq (bits scale start len : ℕ) :
    fixedSieveRange bits scale start len =
      (∑ i ∈ range len,(sieveTerm bits scale (start+i)).1,
       ∑ i ∈ range len,(sieveTerm bits scale (start+i)).2) := by
  induction len with
  | zero => simp [fixedSieveRange]
  | succ len ih => simp only [fixedSieveRange,ih,sum_range_succ]

/-- Join bounded sum certificates without replaying the full prefix. -/
theorem fixedSieveRange_add (bits scale start a b : ℕ) :
    fixedSieveRange bits scale start (a+b) =
      ((fixedSieveRange bits scale start a).1+
         (fixedSieveRange bits scale (start+a) b).1,
       (fixedSieveRange bits scale start a).2+
         (fixedSieveRange bits scale (start+a) b).2) := by
  induction b with
  | zero => simp [fixedSieveRange]
  | succ b ih =>
    simp only [fixedSieveRange]
    change ((fixedSieveRange bits scale start (a+b)).1+
      (sieveTerm bits scale (start+(a+b))).1,
      (fixedSieveRange bits scale start (a+b)).2+
      (sieveTerm bits scale (start+(a+b))).2) = _
    rw [ih]
    simp only [Nat.add_assoc]

/-- The computed pair equals the existing fixed-point reciprocal-prime prefix,
including completeness: no prime is omitted and no composite is included. -/
theorem fixedSievePrefix_eq {n bits : ℕ} (hs : IsSieve n bits) (scale : ℕ) :
    fixedSieveRange bits scale 0 (n+1)=fixedPrimePrefix scale n := by
  rw [fixedSieveRange_eq]
  unfold fixedPrimePrefix primesUpTo
  apply Prod.ext
  · simp only [Nat.zero_add,Finset.sum_filter]
    apply sum_congr rfl
    intro p hp
    have hi : p ≤ n := by have := mem_range.mp hp; omega
    have hf := primeFlag_iff hs hi
    by_cases hprime : p.Prime
    · have hh : primeFlag bits p=true := hf.mpr hprime
      simp [sieveTerm,hh,hprime]
    · have hh : primeFlag bits p=false := Bool.eq_false_iff.mpr (fun hh => hprime (hf.mp hh))
      simp [sieveTerm,hh,hprime]
  · simp only [Nat.zero_add,Finset.card_eq_sum_ones,Finset.sum_filter]
    apply sum_congr rfl
    intro p hp
    have hi : p ≤ n := by have := mem_range.mp hp; omega
    have hf := primeFlag_iff hs hi
    by_cases hprime : p.Prime
    · have hh : primeFlag bits p=true := hf.mpr hprime
      simp [sieveTerm,hh,hprime]
    · have hh : primeFlag bits p=false := Bool.eq_false_iff.mpr (fun hh => hprime (hf.mp hh))
      simp [sieveTerm,hh,hprime]

theorem reciprocal_prefix_of_sieve_certificate {n bits scale Q count : ℕ}
    (hs : IsSieve n bits) (hscale : 0 < scale)
    (hcert : fixedSieveRange bits scale 0 (n+1)=(Q,count)) :
    (Q:ℝ)/scale ≤ primeReciprocalSum n ∧
      primeReciprocalSum n ≤ ((Q:ℝ)+count)/scale := by
  exact prime_prefix_of_certificate hscale ((fixedSievePrefix_eq hs scale).symm.trans hcert)

#print axioms reciprocal_prefix_of_sieve_certificate
end ChenEffective.HybridProduct.BitSieve


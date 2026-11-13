import BJSHybridSieveBlocks

namespace ChenEffective.HybridProduct.BitSieve
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def packingBase : ℕ := 18446744073709551616

/-- The proof uses a symbolic base so elaboration never expands a symbolic
multiplication by the large fixed base into unary recursion. -/
def packedRangeBase (base bits scale start : ℕ) : ℕ → ℕ
  | 0 => 0
  | len+1 =>
    let prev := packedRangeBase base bits scale start len
    let p := start.add len
    if primeFlag bits p then prev.add (((scale.div p).mul base).succ) else prev

@[irreducible] def packedRange (bits scale start len : ℕ) : ℕ :=
  packedRangeBase packingBase bits scale start len

theorem packedRangeBase_eq (base bits scale start len : ℕ) :
    packedRangeBase base bits scale start len =
      (fixedSieveRange bits scale start len).1*base+(fixedSieveRange bits scale start len).2 := by
  induction len with
  | zero => simp [packedRangeBase,fixedSieveRange]
  | succ len ih =>
    simp only [packedRangeBase,fixedSieveRange]
    change (if primeFlag bits (start+len) then
      packedRangeBase base bits scale start len+(scale/(start+len))*base+1
      else packedRangeBase base bits scale start len) = _
    split <;> simp_all [sieveTerm,Nat.add_mul,Nat.add_assoc]
    omega

theorem packedRange_eq (bits scale start len : ℕ) :
    packedRange bits scale start len =
      (fixedSieveRange bits scale start len).1*packingBase+(fixedSieveRange bits scale start len).2 := by
  unfold packedRange
  exact packedRangeBase_eq packingBase bits scale start len

theorem fixedSieveRange_count_le (bits scale start len : ℕ) :
    (fixedSieveRange bits scale start len).2 ≤ len := by
  induction len with
  | zero => simp [fixedSieveRange]
  | succ len ih =>
    simp only [fixedSieveRange]
    unfold sieveTerm
    split <;> simp_all
    omega

theorem fixedSieveRange_of_packed {bits scale start len Q count : ℕ}
    (hlen : len < packingBase) (hcount : count < packingBase)
    (hcert : packedRange bits scale start len=Q*packingBase+count) :
    fixedSieveRange bits scale start len=(Q,count) := by
  rw [packedRange_eq] at hcert
  have hc := fixedSieveRange_count_le bits scale start len
  have hsmall : (fixedSieveRange bits scale start len).2 < packingBase := hc.trans_lt hlen
  have hmod := congrArg (fun k : ℕ => k % packingBase) hcert
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
    Nat.zero_add,Nat.mod_eq_of_lt hsmall,Nat.mod_eq_of_lt hcount] at hmod
  have hmul : (fixedSieveRange bits scale start len).1*packingBase=Q*packingBase := by
    rw [hmod] at hcert
    exact Nat.add_right_cancel hcert
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_right (show 0 < packingBase by decide) hmul
  · exact hmod

theorem packedRangeBase_add (base bits scale start a b : ℕ) :
    packedRangeBase base bits scale start (a+b)=
      packedRangeBase base bits scale start a+packedRangeBase base bits scale (start+a) b := by
  induction b with
  | zero => simp [packedRangeBase]
  | succ b ih =>
    simp only [packedRangeBase]
    change (if primeFlag bits (start+(a+b)) then
      packedRangeBase base bits scale start (a+b)+(scale/(start+(a+b)))*base+1
      else packedRangeBase base bits scale start (a+b)) = _
    rw [ih]
    simp only [show start+(a+b)=(start+a)+b by omega]
    split <;> simp_all [Nat.add_assoc]

theorem packedRange_add (bits scale start a b : ℕ) :
    packedRange bits scale start (a+b)=packedRange bits scale start a+packedRange bits scale (start+a) b := by
  unfold packedRange
  exact packedRangeBase_add packingBase bits scale start a b

/-- Assemble certificate summaries through an explicit length equality. This
keeps elaboration from unfolding a long numerical prefix merely to match an
arithmetic expression for its length. Kernel reduction remains available in
the bounded chunk checks. -/
theorem packedRange_join {bits scale start len a b qA qB : ℕ}
    (hlen : len=a+b)
    (hA : packedRange bits scale start a=qA)
    (hB : packedRange bits scale (start+a) b=qB) :
    packedRange bits scale start len=qA+qB := by
  subst len
  rw [packedRange_add,hA,hB]

theorem reciprocal_prefix_of_packed_certificate {n bits scale Q count : ℕ}
    (hs : IsSieve n bits) (hscale : 0 < scale)
    (hlen : n+1 < packingBase) (hcount : count < packingBase)
    (hcert : packedRange bits scale 0 (n+1)=Q*packingBase+count) :
    (Q:ℝ)/scale ≤ AnalyticNumberTheory.Mertens.primeReciprocalSum n ∧
      AnalyticNumberTheory.Mertens.primeReciprocalSum n ≤ ((Q:ℝ)+count)/scale := by
  exact reciprocal_prefix_of_sieve_certificate hs hscale (fixedSieveRange_of_packed hlen hcount hcert)

theorem reciprocal_block_of_packed_certificate {n bits scale start len Q count : ℕ}
    (hs : IsSieve n bits) (hend : start+len ≤ n+1) (hscale : 0 < scale)
    (hlen : len < packingBase) (hcount : count < packingBase)
    (hcert : packedRange bits scale start len=Q*packingBase+count) :
    (Q:ℝ)/scale ≤ ∑ p ∈ blockPrimes start (start+len),1/(p:ℝ) ∧
      (∑ p ∈ blockPrimes start (start+len),1/(p:ℝ)) ≤ ((Q:ℝ)+count)/scale := by
  exact reciprocal_block_of_sieve_certificate hs hend hscale (fixedSieveRange_of_packed hlen hcount hcert)

#print axioms reciprocal_prefix_of_packed_certificate
end ChenEffective.HybridProduct.BitSieve

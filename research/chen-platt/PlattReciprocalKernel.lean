import RSBounds.PsiFinite.Kernel

/-! Small-batch prime-count certificates. Only Init and the minimal kernel
sieve are imported. These counts are inputs to a separately proved real
reciprocal-sum enclosure; this file makes no analytic claim. -/
namespace ChenEffective.PlattWindow
open PsiFinite

def blockLeft (lo w k : Nat) : Nat := lo-1+2*2^w*k

def packedField (W Y k : Nat) : Nat := (Y >>> (W*k)) % 2^W

def reciprocalFloors (scale lo w Y k : Nat) : Nat × Nat :=
  let A := blockLeft lo w k
  let c := packedField (2^w) Y k
  (scale*c/(A+2*2^w),scale*c/A+1)

def segmentFixed (scale lo w Y : Nat) : Nat → Nat × Nat
  | 0 => (0,0)
  | n+1 =>
    let p := segmentFixed scale lo w Y n
    let q := reciprocalFloors scale lo w Y n
    (p.1+q.1,p.2+q.2)

/-- Counts of primes in consecutive blocks of 2*2^w integers, packed in
fields of 2^w bits. All prime powers are disabled (top=0). -/
noncomputable def segmentCounts (lo w B : Nat) : Nat :=
  let W := Nat.shiftLeft 1 w
  let L := Nat.mul W B
  let hi := Nat.sub (Nat.add lo (Nat.mul 2 L)) 2
  let all := Nat.sub (Nat.shiftLeft 1 L) 1
  let marked := (sieveK lo L hi 0 basePrimes 0 []).1
  let bits := Nat.xor all (Nat.land marked all)
  swarK L w bits 0

end ChenEffective.PlattWindow

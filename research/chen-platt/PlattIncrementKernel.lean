import PlattReciprocalKernel

namespace ChenEffective.PlattWindow
structure IncrementRow where
  a : Nat
  b : Nat
  lower : Nat
  upper : Nat

def IncrementCertified (r : IncrementRow) : Prop :=
  ∃ lo w B Y : Nat,
    r.a=lo-1 ∧ r.b=lo-1+2*2^w*B ∧ lo%2=1 ∧ 3≤lo ∧
    lo+2*2^w*B-1≤PsiFinite.baseCover ∧
    segmentCounts lo w B=Y ∧ segmentFixed (2^48) lo w Y B=(r.lower,r.upper)

/-- Build once with symbolic parameters, so adapters do not normalize the
closed sieve or reciprocal arithmetic while elaborating proof projections. -/
theorem certifyIncrement (lo w B Y lower upper : Nat)
    (hodd : lo%2=1) (hlo : 3≤lo)
    (htop : lo+2*2^w*B-1≤PsiFinite.baseCover)
    (hcount : Nat.beq (segmentCounts lo w B) Y = true)
    (harith : (Nat.beq (segmentFixed (2^48) lo w Y B).1 lower &&
      Nat.beq (segmentFixed (2^48) lo w Y B).2 upper) = true) :
    IncrementCertified ⟨lo-1,lo-1+2*2^w*B,lower,upper⟩ :=
  ⟨lo,w,B,Y,rfl,rfl,hodd,hlo,htop,Nat.eq_of_beq_eq_true hcount,
    let h := Bool.and_eq_true_iff.mp harith
    Prod.ext (Nat.eq_of_beq_eq_true h.1) (Nat.eq_of_beq_eq_true h.2)⟩

inductive CertifiedIncrements : List IncrementRow → Prop
  | nil : CertifiedIncrements []
  | cons {r : IncrementRow} {rs : List IncrementRow} :
    IncrementCertified r → CertifiedIncrements rs → CertifiedIncrements (r::rs)

def incrementTotals : List IncrementRow → Nat × Nat
  | [] => (0,0)
  | r::rs => let t := incrementTotals rs; (r.lower+t.1,r.upper+t.2)

def checkIncrementChain : Nat → Nat → List IncrementRow → Bool
  | a,b,[] => decide (a=b)
  | a,b,r::rs => decide (r.a=a ∧ r.a≤r.b) && checkIncrementChain r.b b rs

def checkIncrementSummary (a b lower upper : Nat) (rows : List IncrementRow) : Bool :=
  checkIncrementChain a b rows && decide (incrementTotals rows=(lower,upper))
end ChenEffective.PlattWindow

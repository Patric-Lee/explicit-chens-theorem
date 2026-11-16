import PlattAssemblyKernel

namespace ChenEffective.PlattWindow
abbrev PrimePoint := Nat × Nat × Nat

/-- Proof-bearing data can be opaque while its small numerical parameters
remain available to the carry checker. The initializer must supply all facts. -/
structure CheckedPointSegment (lo w B lower upper baseLower baseUpper : Nat)
    (cuts : List PrefixCut) (points : List PrimePoint) where
  packed : Nat
  odd : lo%2=1
  left_large : 3≤lo
  within_cover : lo+2*2^w*B-1≤PsiFinite.baseCover
  counts : Nat.beq (segmentCounts lo w B) packed = true
  arithmetic : (Nat.beq (segmentFixed (2^48) lo w packed B).1 lower &&
    Nat.beq (segmentFixed (2^48) lo w packed B).2 upper) = true
  checkpoints : checkPrefixCuts (2^48) lo w packed B cuts = true
  point_links : (cuts.take points.length).map (fun c =>
    (lo-1+2*2^w*c.k,baseLower+c.lower,baseUpper+c.upper)) = points

structure PointSegment where
  lo : Nat
  w : Nat
  B : Nat
  lower : Nat
  upper : Nat
  baseLower : Nat
  baseUpper : Nat
  cuts : List PrefixCut
  points : List PrimePoint
  certified : CheckedPointSegment lo w B lower upper baseLower baseUpper cuts points

def pointSegmentEnd (s : PointSegment) : Nat := s.lo-1+2*2^s.w*s.B

/-- Check incoming/outgoing cumulative offsets, not just geometric seams. -/
def checkPointChain : Nat → Nat → Nat → Nat → Nat → Nat → List PointSegment → Bool
  | a,l,u,b,L,U,[] => decide (a=b ∧ l=L ∧ u=U)
  | a,l,u,b,L,U,s::ss =>
    decide (s.lo-1=a ∧ s.baseLower=l ∧ s.baseUpper=u) &&
      checkPointChain (pointSegmentEnd s) (l+s.lower) (u+s.upper) b L U ss

inductive PointChainCertificate : Nat → Nat → Nat → Nat → Nat → Nat → List PrimePoint → Prop
  | leaf {a l u b L U : Nat} (segments : List PointSegment) :
    checkPointChain a l u b L U segments = true →
      PointChainCertificate a l u b L U (segments.flatMap PointSegment.points)
  | append {a l u b L U c v w : Nat} {xs ys : List PrimePoint} :
    PointChainCertificate a l u b L U xs → PointChainCertificate b L U c v w ys →
      PointChainCertificate a l u c v w (xs++ys)
  | relabel {a l u b L U : Nat} {xs ys : List PrimePoint} :
    xs=ys → PointChainCertificate a l u b L U xs → PointChainCertificate a l u b L U ys
end ChenEffective.PlattWindow

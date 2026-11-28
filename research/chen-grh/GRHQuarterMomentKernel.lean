import PlattReciprocalKernel

/-! Exact arithmetic for quarter-moment proposals. All checks reduce in
Lean's ordinary kernel; generators are not trusted. -/
namespace ChenEffective.H10Band.QuarterCert
def scale : Nat := 100000
def denominator : Nat := 1000000000000
def blockLo (lo w k : Nat) : Nat := lo+2*(2^w*k)
def majorantNumerator (lo u : Nat) : Nat :=
  (if lo≤100 then 126 else 101)*scale^3+
    (if lo=3 then 100*scale*u^2 else 0)
def majorantDenominator (u : Nat) : Nat := 100*u^3
def expNumerator (degree t : Nat) : Nat :=
  if degree=3 then
    6*t*denominator^2+3*t^2*denominator+t^3
  else
    5040*t*denominator^6+2520*t^2*denominator^5+
    840*t^3*denominator^4+210*t^4*denominator^3+
    42*t^5*denominator^2+7*t^6*denominator+t^7
def factorialFor (degree : Nat) : Nat := if degree=3 then 6 else 5040
def blockCheck (lo degree u t : Nat) : Bool :=
  decide (0<u ∧ u^4≤lo*scale^4 ∧
    factorialFor degree*denominator^degree*majorantNumerator lo u≤
      expNumerator degree t*majorantDenominator u)
def boundsCheckFrom (lo w degree : Nat) : List (Nat×Nat)→Bool
  | [] => true
  | (u,t)::data => blockCheck lo degree u t && boundsCheckFrom (lo+2*2^w) w degree data
def boundsCheck (lo w degree B : Nat) (data : List (Nat×Nat)) : Bool :=
  decide (data.length=B ∧ (degree=3 ∨ degree=7)) && boundsCheckFrom lo w degree data
def weightedSumFrom (w packed k : Nat) : List (Nat×Nat)→Nat
  | [] => 0
  | (_,t)::data => PlattWindow.packedField (2^w) packed k*t+weightedSumFrom w packed (k+1) data
def weightedSum (w packed : Nat) (data : List (Nat×Nat)) : Nat :=
  weightedSumFrom w packed 0 data
end ChenEffective.H10Band.QuarterCert

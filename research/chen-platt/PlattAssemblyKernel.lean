import PlattReciprocalKernel
import Init.Data.List.Scan.Lemmas

/-! Arithmetic-only assembly checks. These do not assert prime bounds: their
interpretation is proved in PlattAssemblySoundness. -/
namespace ChenEffective.PlattWindow

structure PrefixCut where
  k : Nat
  lower : Nat
  upper : Nat
  deriving DecidableEq

def prefixTable (scale lo w Y B : Nat) : List (Nat × Nat) :=
  (List.range B).scanl (fun p k =>
    let q := reciprocalFloors scale lo w Y k
    (p.1+q.1,p.2+q.2)) (0,0)

def checkCutsTable : Nat → List (Nat × Nat) → List PrefixCut → Bool
  | _,_,[] => true
  | _,[],_::_ => false
  | k,p::ps,c::cs =>
    if c.k=k then decide (p=(c.lower,c.upper)) && checkCutsTable (k+1) ps cs
    else if k<c.k then checkCutsTable (k+1) ps (c::cs) else false

def checkPrefixCuts (scale lo w Y B : Nat) (cuts : List PrefixCut) : Bool :=
  checkCutsTable 0 (prefixTable scale lo w Y B) cuts

structure AssemblyCell where
  a : Nat
  b : Nat
  aLower : Nat
  bUpper : Nat
  logaLower : Nat
  logbUpper : Nat
  deriving DecidableEq

/-- Scale times the two cell bounds, with signed subtraction. -/
def checkAssemblyCell (scale denominator rLower rUpper logRLower logRUpper : Nat)
    (c : AssemblyCell) : Bool := decide (
  1 < c.a ∧ c.a ≤ c.b ∧
  -(scale : Int) ≤ (denominator : Int)*
    ((c.aLower : Int)-rUpper-c.logbUpper+logRLower) ∧
  (denominator : Int)*((c.bUpper : Int)-rLower-c.logaLower+logRUpper) ≤ scale)

/-- Exact shared endpoints; no floating-point proximity test at seams. -/
def checkCellChain : Nat → Nat → List AssemblyCell → Bool
  | a,b,[] => decide (a=b)
  | a,b,c::cs => decide (c.a=a ∧ c.a≤c.b) && checkCellChain c.b b cs

end ChenEffective.PlattWindow

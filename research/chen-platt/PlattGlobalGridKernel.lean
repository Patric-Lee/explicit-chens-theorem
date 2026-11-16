import PlattPointPacketKernel
import PlattLogRows

namespace ChenEffective.PlattWindow

/-- Match the cumulative prime intervals and the certified log rows to each
cell. Both streams advance exactly once for each cell. -/
def CellLinked (c : AssemblyCell) (p q : PrimePoint)
    (r t : LogCertificate.LogRow) : Prop :=
  c.a=p.1 ∧ c.b=q.1 ∧ c.aLower=p.2.1 ∧ c.bUpper=q.2.2 ∧
  r.x=c.a ∧ t.x=c.b ∧ r.lower=c.logaLower ∧ t.upper=c.logbUpper

instance (c : AssemblyCell) (p q : PrimePoint) (r t : LogCertificate.LogRow) :
    Decidable (CellLinked c p q r t) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def checkGridLinks : List AssemblyCell → List PrimePoint → List LogCertificate.LogRow → Bool
  | [],_,_ => true
  | c::cs,p::q::ps,r::t::rs =>
    decide (CellLinked c p q r t) && checkGridLinks cs (q::ps) (t::rs)
  | _,_,_ => false

inductive CheckedLogRows : List LogCertificate.LogRow → Prop
  | checked {rows : List LogCertificate.LogRow} :
      rows.all LogCertificate.checkRow=true → CheckedLogRows rows
  | slice {rows : List LogCertificate.LogRow} (start count : Nat) :
      CheckedLogRows rows → CheckedLogRows ((rows.drop start).take count)
  | append {xs ys : List LogCertificate.LogRow} :
      CheckedLogRows xs → CheckedLogRows ys → CheckedLogRows (xs++ys)

/-- Checked integer cell budgets plus the original kernel-checked log rows.
The prime bounds are supplied by the independent global prefix certificate. -/
inductive GridWindowCertificate : Nat → Nat → List PrimePoint → Prop
  | leaf {a b : Nat} {points : List PrimePoint}
      (cells : List AssemblyCell) (logs : List LogCertificate.LogRow) :
      cells.all (checkAssemblyCell (2^48) 20000
        116863011702975 116863401833309 882879348526828 882879348527041) = true →
      CheckedLogRows logs →
      checkCellChain a b cells = true →
      checkGridLinks cells points logs = true →
      GridWindowCertificate a b points
  | append {a b c : Nat} {xs ys : List PrimePoint} :
      GridWindowCertificate a b xs → GridWindowCertificate b c ys →
      GridWindowCertificate a c (xs++ys)

/-- Linear merge check. Repeated seam points in the grid stream reuse the
same source point. A missing or changed triple makes the check fail. -/
def checkPointCoverAux : Nat → List PrimePoint → List PrimePoint → Bool
  | _,_,[] => true
  | 0,_,_::_ => false
  | _+1,[],_::_ => false
  | n+1,p::ps,q::qs =>
    if p=q then checkPointCoverAux n (p::ps) qs
    else checkPointCoverAux n ps (q::qs)

def checkPointCover (source target : List PrimePoint) : Bool :=
  checkPointCoverAux (source.length+target.length) source target

end ChenEffective.PlattWindow

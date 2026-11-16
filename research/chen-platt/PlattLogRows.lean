import PlattLogKernel
namespace ChenEffective.PlattWindow.LogCertificate
structure LogRow where
  x : Nat
  k : Nat
  lowerLog : Nat
  upperLog : Nat
  kl : Nat
  ku : Nat
  lower : Nat
  upper : Nat

def checkRow (r : LogRow) : Bool := decide (
  0 < r.x ∧ 2^r.k ≤ r.x ∧ r.x ≤ 2*2^r.k ∧
  rationalBounds r.x 1 r.k = (r.lowerLog,r.upperLog) ∧
  scale < r.lowerLog ∧
  scale*2^r.kl ≤ r.lowerLog ∧ r.lowerLog ≤ 2*(scale*2^r.kl) ∧
  scale*2^r.ku ≤ r.upperLog ∧ r.upperLog ≤ 2*(scale*2^r.ku) ∧
  (rationalBounds r.lowerLog scale r.kl).1 = r.lower ∧
  (rationalBounds r.upperLog scale r.ku).2 = r.upper)
end ChenEffective.PlattWindow.LogCertificate

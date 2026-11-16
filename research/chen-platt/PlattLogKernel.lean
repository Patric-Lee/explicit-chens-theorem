/-! Kernel-evaluable fixed-point logarithm arithmetic; no analytic imports. -/
namespace ChenEffective.PlattWindow.LogCertificate

def scale : Nat := 2^48

def floorSum (S a b : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => floorSum S a b j + S*a^(2*j+1)/((2*j+1)*b^(2*j+1))

/-- Valid for d ≤ n ≤ 2d, d > 0. The 33 units cover 32 rounding
units and at most one unit of geometric-series remainder. -/
def unitBounds (n d : Nat) : Nat × Nat :=
  let q := 2*floorSum scale (n-d) (n+d) 16
  (q,q+33)

/-- The normalization exponent is supplied as certificate data. -/
def rationalBounds (n d k : Nat) : Nat × Nat :=
  let a := unitBounds 2 1
  let b := unitBounds n (d*2^k)
  (k*a.1+b.1,k*a.2+b.2)

end ChenEffective.PlattWindow.LogCertificate

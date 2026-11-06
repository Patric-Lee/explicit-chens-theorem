$ErrorActionPreference='Stop'
$rows=for($j=1;$j -le 287;$j++){
 if($j -lt 3){'  (0, 0, 0, 0)'} else {
  $k=[int][Math]::Floor([Math]::Log2($j))
  $u=[int][Math]::Ceiling([Math]::Log($j)*10000)+1
  $k2=[int][Math]::Floor([Math]::Log2($u/10000.0))
  $v=[int][Math]::Ceiling([Math]::Log($u/10000.0)*10000)+1
  "  ($k, $u/10000, $k2, $v/10000)"
 }
}
$header=@'
import BJSFiniteLogBounds

/-! Candidate endpoint bounds generated from rounded approximations.
The theorem below checks every candidate by exact rational arithmetic in
the Lean kernel; the generator and floating-point operations are untrusted.
-/
namespace ChenEffective
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bjsSmallLogRows : Array (ℕ × ℚ × ℕ × ℚ) := #[
'@
$footer=@'
]

def bjsSmallPrefixQ (n : ℕ) : ℚ :=
  ∑ p ∈ range (n+1), if p.Prime then 1/(p : ℚ) else 0

def bjsSmallPrefixCertificate (n : ℕ) : Prop :=
  let (k,u,l,v) := bjsSmallLogRows[n]!
  (2 : ℚ)^k ≤ n+1 ∧ bjsLogUpper (n+1) k ≤ u ∧
  (2 : ℚ)^l ≤ u ∧ bjsLogUpper u l ≤ v ∧ 1 ≤ u ∧
  v+27/100-1/(2*u^2) ≤ bjsSmallPrefixQ n

instance (n : ℕ) : Decidable (bjsSmallPrefixCertificate n) := by
  unfold bjsSmallPrefixCertificate
  infer_instance

theorem bjsSmallPrefixCertificates :
    ∀ n : Fin 287, 2 ≤ n.val → bjsSmallPrefixCertificate n.val := by
  decide +kernel

end ChenEffective
'@
$content=$header+"`n"+($rows -join ",`n")+"`n"+$footer+"`n"
[IO.File]::WriteAllText((Join-Path $PSScriptRoot 'BJSSmallPrefixCertificate.lean'),$content)

import TernaryGoldbach.Statement
import GRHAssumption

namespace ChenEffective.PlattWindow

/-- Compatibility interface for the former Platt input. This is now a theorem
derived from full Dirichlet GRH, with no separate finite-RH axiom. -/
theorem platt_modulus_one_finite_RH : TernaryGoldbach.PlattZetaRH :=
  GRH.zeta_finite_RH 100000000

instance : Fact TernaryGoldbach.PlattZetaRH := ⟨platt_modulus_one_finite_RH⟩

end ChenEffective.PlattWindow

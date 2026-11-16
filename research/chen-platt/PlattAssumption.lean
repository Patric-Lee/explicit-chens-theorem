import TernaryGoldbach.Statement

namespace ChenEffective.PlattWindow

/-- Published external computational input: Platt's modulus-one verification
of RH through height 100,000,000, with exactly the predicate used by the
vendored calr3 analytic development. This makes no assertion about other
Dirichlet L-functions or zeta zeros above that height. -/
axiom platt_modulus_one_finite_RH : TernaryGoldbach.PlattZetaRH

instance : Fact TernaryGoldbach.PlattZetaRH := ⟨platt_modulus_one_finite_RH⟩

end ChenEffective.PlattWindow

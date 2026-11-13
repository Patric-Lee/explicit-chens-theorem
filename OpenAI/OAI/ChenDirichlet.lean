import OAI.NumberTheory.DirichletL.Nonvanishing

/-! Adapter with exactly the name and type of the current Chen axiom.
Activate it in ExplicitSiegel only after the complete proof and final Chen
dependency closures have compiled and passed their transitive audits. -/
namespace ChenEffective

theorem dirichlet_seven_eighths
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7/8:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
    χ.LFunction s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

end ChenEffective

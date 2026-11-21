import Lean.Util.CollectAxioms
import AuditGRH14NumericalLower
import GRH14ChenBridge
import Goldbach.Statement

noncomputable section
namespace ChenEffective.GRH14
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

/-- Actual prime plus at-most-two-prime-factor representation at the explicit
cutoff. The complete lower and upper counting estimates supply all premises. -/
theorem chen {N : ℕ} (hN : targetCutoff≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  exact chen_of_weighted_lower hN hEven (weighted_lower hN hEven)

theorem chen_implicit : ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → Even N →
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q :=
  ⟨targetCutoff,fun _ hN hEven => chen hN hEven⟩

/-- Literal recovery of the original repository's implicit Chen statement. -/
theorem original_chen : Goldbach.ChenTheorem :=
  ⟨targetCutoff,fun _ hN hEven => chen hN hEven⟩

theorem chen_of_double_exp_14 {N : ℕ}
    (hN : Real.exp (Real.exp (14:ℝ))≤N) (hEven : Even N) :
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q=r*s) ∧ N=p+q := by
  exact chen (target_of_double_exp_14 hN) hEven




end ChenEffective.GRH14


open Lean Meta
run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let roots := #[``ChenEffective.GRH14.weighted_lower,
    ``ChenEffective.GRH14.triple_upper,``ChenEffective.GRH14.chen,
    ``ChenEffective.GRH14.chen_implicit,``ChenEffective.GRH14.original_chen,
    ``ChenEffective.GRH14.chen_of_double_exp_14]
  let axs ← Lean.collectAxioms ``ChenEffective.GRH14.original_chen
  unless axs.contains ax && axs.all (standard.push ax).contains do
    throwError "Unexpected axiom closure of original Chen recovery: {axs}"
  logInfo m!"Original Chen axiom closure: {axs}"
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if #["sorryAx","Lean.ofReduceBool","Lean.trustCompiler"].contains n.toString then
      throwError "Forbidden proof dependency {n}"
    let some ci := (← getEnv).find? n | throwError "Missing dependency {n}"
    if ci.isUnsafe then throwError "Unsafe proof dependency {n}"
    if ci matches .axiomInfo _ then
      unless (standard.push ax).contains n do throwError "Unlisted axiom {n}"
    todo := todo ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      todo := todo ++ v.getUsedConstants
  logInfo m!"GRH H14 complete Chen audit passed: {seen.size} transitive constants."
  logInfo "Actual lower coefficient 2.02575 and triple coefficient 3.993 at 3^1000000."
  logInfo "Full explicit Chen existence and implicit recovery; sole added axiom is full Dirichlet GRH."






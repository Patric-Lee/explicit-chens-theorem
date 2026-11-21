import GRH14WeightedLower
import PlattCertifiedPrefixWindow
import PlattAssumption
import Lean.Util.CollectAxioms

namespace ChenEffective.GRH14
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple

private instance : Fact HybridProduct.HybridPrefixWindow :=
  ⟨PlattWindow.certified_prefix_window⟩

/-- Numerical Chen weighted lower count. The only nonstandard axiom is
full Dirichlet GRH; the finite-RH window is derived from it. -/
theorem weighted_lower {N : ℕ} (hN : targetCutoff ≤ N) (hEven : Even N) :
    (2.02575:ℝ)*(SingularSeries.liuSingularSeries N*N/Real.log (N:ℝ)^2) ≤
      jurkatRichertWeightedCount N := weighted_lower_of_window hN hEven

#print axioms weighted_lower
end ChenEffective.GRH14


open Lean Meta
run_elab do
  if debug.skipKernelTC.get (← getOptions) then
    throwError "Kernel type checking must be enabled"
  let standard := #[``propext,``Classical.choice,``Quot.sound]
  let ax := ``ChenEffective.GRH.alpoge_dirichlet_grh
  let root := ``ChenEffective.GRH14.weighted_lower
  let axs ← Lean.collectAxioms root
  unless axs.contains ax && axs.all (standard.push ax).contains do
    throwError "Unexpected axiom closure of final numerical lower theorem: {axs}"
  let mut todo := #[root]
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
  logInfo m!"GRH H14 numerical lower audit passed: {seen.size} transitive constants."
  logInfo "Actual weighted Chen lower count at 3^1000000; sole added axiom is full Dirichlet GRH."
  logInfo "No completed H14 Chen existence theorem is asserted: the complete square estimate is separate."
